#!/usr/bin/env python3

"""
 Script for automated experimental evaluation.
 @title bench-file.py
 @author Vojtech Havlena, December 2021
"""

import sys
import getopt
import subprocess
import string
import re
import os
import os.path
import resource

from enum import Enum
from dataclasses import dataclass
from typing import Any, Callable

TIMEOUT = 10 #in seconds
FORMULAS = 100000

class ToolType(Enum):
    NOODLER = 1
    Z3 = 2
    CVC4 = 3

@dataclass
class Tool:
    type : ToolType
    name : str
    run_parse_fnc : Callable

    def __str__(self):
        return self.name


def main():
    if len(sys.argv) < 2:
        help_err()
        sys.exit()
    try:
        opts, args = getopt.getopt(sys.argv[2:], "", [])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()

    bench = sys.argv[1]
    fhandle = open(bench, "r")

    tools = [
        Tool(ToolType.NOODLER, "Noodler", run_parse_noodler),
        Tool(ToolType.Z3, "Z3", run_parse_z3),
        Tool(ToolType.CVC4, "CVC4", run_parse_cvc4)
    ]

    sys.stdout.write("file;")
    print(*tools, sep = ";")
    for file in fhandle.readlines():
        file = file.strip()
        vals = [file] + [ t.run_parse_fnc(file) for t in tools ]
        print(*vals, sep = ";")


def run_parse_noodler(input):
    time = "time"
    bin = ["python3", "-m", "noodler"]
    args = []
    try:
        output = subprocess.check_output([time] + bin + [input]+args, \
            timeout=TIMEOUT, stderr=subprocess.STDOUT).decode("utf-8")
        parse = parse_time(output)
    except subprocess.CalledProcessError as e:
        parse = "FAIL"
    except subprocess.TimeoutExpired:
        parse = "TO"
    return parse

def run_parse_z3(input):
    time = "time"
    bin = "z3"
    args = []
    try:
        output = subprocess.check_output([time, bin, input]+args, \
            timeout=TIMEOUT, stderr=subprocess.STDOUT).decode("utf-8")
        parse = parse_time(output)
    except subprocess.TimeoutExpired:
        parse = "TO"
    return parse

def run_parse_cvc4(input):
    time = "time"
    bin = "cvc4"
    args = ["--strings-exp"]
    try:
        output = subprocess.check_output([time, bin, input]+args, \
            timeout=TIMEOUT, stderr=subprocess.STDOUT).decode("utf-8")
        parse = parse_time(output)
    except subprocess.TimeoutExpired:
        parse = "TO"
    return parse

def parse_time(out : str) -> str:
    match = re.search(r'([0-9\.]*)[\s]*real', out)
    return float(match.group(1))

def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./experimental [bin]"\
        "[formula folder] [--tex] [--formulas=X]\n")


if __name__ == "__main__":
    main()
