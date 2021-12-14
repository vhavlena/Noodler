#!/usr/bin/env python3

import sys
import pandas as pd
import numpy as np
import matplotlib
import matplotlib.pyplot as plt

def main():
    file = sys.argv[1]
    data = pd.read_csv(file, delimiter=";")

    print("Unsolved instances:", data[data["Noodler"] == "FAIL"].shape[0])

    no_fails = data[data["Noodler"] != "FAIL"]
    no_fails = no_fails.replace("TO", 10.0)

    no_fails = no_fails.astype({"file": str, "Noodler": np.float16, "Z3": np.float16, "CVC4": np.float16})

    z3 = no_fails.plot(kind='scatter', x='Z3', y='Noodler', color='r', label="Z3")
    ax = no_fails.plot(kind='scatter', x='CVC4', y='Noodler',  color='g', label="CVC4", ax=z3)
    ax.set_xlabel("Z3/CVC4 [s]")
    ax.set_ylabel("Noodler [s]")

    ax.axvline(10.0, linestyle="dashed", color="black", linewidth=0.5)
    ax.axhline(10.0, linestyle="dashed", color="black", linewidth=0.5)
    ax.axline((0.0, 0.0), (10.0, 10.0), color="black", linewidth=0.5)

    plt.savefig("out.pdf")


if __name__ == "__main__":
    main()
