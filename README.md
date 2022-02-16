# Noodler

Solving string constraints via segment-automata and noodles.
[![Binder_badge]][binder_link]

The notebook [example-full-algo](example-full-algo.ipynb) uses Noodler to
produce balanced and unified query for simple string equations.

See [pastry and noodles](pastry-and-noodles.ipynb) to understand noodlification and unification.

[Example-full-algo-long](example-full-algo-long.ipynb) contains equation that take
long time to solve (especially when starting from the right-hand side).

## Requirements

 * Python 3.6+
 * [Awali] with Python bindings (Awalipy) installed.
 * Python packages installed via `requirements.txt`

## Run

To run Noodler, use the following syntax:

```
./noodler.py <filename>
```
where `filename` is a file containing a formula in smtlib2 format.

[Awali]: http://vaucanson-project.org/Awali/
[Binder_badge]: https://mybinder.org/badge_logo.svg
[binder_link]: https://mybinder.org/v2/gh/xblahoud/noodler/HEAD?urlpath=lab
