#!/usr/bin/env python3

import sys
import pandas as pd
import numpy as np
import matplotlib
import matplotlib.pyplot as plt

def noodler_analysis(no_fails, timeout):
    no_fails[no_fails["Noodler-NFA"] > timeout] = timeout
    no_fails[no_fails["Noodler-DFA"] > timeout] = timeout

    ax = no_fails.plot(kind='scatter', x='Noodler-NFA', y="Noodler-DFA", color='r')
    ax.set_xlabel("Noodler-NFA [s]")
    ax.set_ylabel("Noodler-DFA [s]")

    ax.axvline(timeout, linestyle="dashed", color="black", linewidth=0.5)
    ax.axhline(timeout, linestyle="dashed", color="black", linewidth=0.5)
    ax.axline((0.0, 0.0), (timeout, timeout), color="black", linewidth=0.5)

    plt.savefig("out.pdf")


def tools_analysis(no_fails, tool, timeout):
    no_fails[no_fails[tool] > timeout] = timeout
    no_fails[no_fails["Z3"] > timeout] = timeout
    no_fails[no_fails["CVC4"] > timeout] = timeout

    z3 = no_fails.plot(kind='scatter', x='Z3', y=tool, color='r', label="Z3")
    ax = no_fails.plot(kind='scatter', x='CVC4', y=tool,  color='g', label="CVC4", ax=z3)
    ax.set_xlabel("Z3/CVC4 [s]")
    ax.set_ylabel("{0} [s]".format(tool))

    ax.axvline(timeout, linestyle="dashed", color="black", linewidth=0.5)
    ax.axhline(timeout, linestyle="dashed", color="black", linewidth=0.5)
    ax.axline((0.0, 0.0), (timeout, timeout), color="black", linewidth=0.5)

    plt.legend(loc='lower right')
    plt.savefig("out.pdf")


def main():
    file = sys.argv[1]
    data = pd.read_csv(file, delimiter=";")
    tool = "Noodler-NFA"
    timeout = 20.0

    print("Unsolved instances:", data[data[tool] == "FAIL"].shape[0])

    no_fails = data[data[tool] != "FAIL"]
    no_fails = no_fails.replace("TO", timeout)
    no_fails = no_fails.astype({"file": str, "Noodler-NFA": np.float16, "Noodler-DFA": np.float16, "Z3": np.float16, "CVC4": np.float16})

    print("Timeouts:", no_fails[no_fails[tool] >= timeout].shape[0])

    noodler_analysis(no_fails, timeout)


if __name__ == "__main__":
    main()
