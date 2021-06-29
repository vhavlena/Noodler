import argparse
import sys

from .core import is_straightline
from .parser import SmtlibParserHackAbc
from .noodler import StraightlineNoodleMachine


def main(args: argparse.Namespace):
    filename = args.filename
    bidi = args.bidi

    smt_parser = SmtlibParserHackAbc(filename)
    q = smt_parser.parse_query()
    assert is_straightline(q.equations)
    noodler_machine = StraightlineNoodleMachine(q)

    if args.propagate_vars and not bidi:
        noodler_machine.propagate_constraints()

    if not args.parse_only:
        res = "sat" if noodler_machine.is_sat(bidi) else "unsat"
        print(res)


description = """Solves SAT problem for string constraints."""

# TODO add helper texts.
parser = argparse.ArgumentParser(description=description)
parser.add_argument("--parse_only", action="store_true")
parser.add_argument("--propagate-vars", action="store_true")
parser.add_argument("--bidi", action="store_true")
parser.add_argument("filename", type=str)

args = parser.parse_args()
main(args)
exit(0)