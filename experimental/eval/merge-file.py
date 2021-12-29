#!/usr/bin/env python3

import sys
import pandas as pd
import numpy as np
import matplotlib
import matplotlib.pyplot as plt

def main():
    file1 = sys.argv[1]
    file2 = sys.argv[2]
    df1 = pd.read_csv(file1, delimiter=";")
    df2 = pd.read_csv(file2, delimiter=";")

    mrg = pd.merge(df1, df2, on="file")
    mrg.to_csv("out.csv", index=False, sep=";")


if __name__ == "__main__":
    main()
