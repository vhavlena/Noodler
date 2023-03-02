# Noodler

Solving string constraints via noodles, see [this paper](https://arxiv.org/abs/2212.02317)

## Requirements

 * Python 3.6+
 * [This branch of Mata](https://github.com/VeriFIT/mata/tree/python_noodler_final) with Python bindings installed (see README of that repo)
 * Python packages installed via `requirements.txt` (try running `pip install -r requirements.txt`)

 We recommend using [python virtual environments](https://docs.python.org/3/tutorial/venv.html).

## Run

To run Noodler, use the following command:

```
./noodler.py <filename>
```
where `filename` is a file containing a formula in smtlib2 format.

