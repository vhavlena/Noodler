# Noodler

Solving string constraints via segment-automata and noodles.

See [pastry and noodles](pastry-and-noodles.ipynb) to understand noodlification and unification.

The notebook [example-full-algo](example-full-algo.ipynb) demonstrates how Noodler can
produce balanced and unified system for simple string equations. 
[Example-full-algo-long](example-full-algo-long.ipynb) contains equation that take
long time to solve (especially when starting from the right-hand side).

If you want to play with this, you need to have [Awali](http://vaucanson-project.org/Awali/) with Python bindings installed.  I also import `display_inline` from [Spot](https://spot.lrde.epita.fr/). If you don't have [Spot](https://spot.lrde.epita.fr/) locally, you can reimplement or remove the function `display_inline`. It is only used to show a variable name before automaton representing it.