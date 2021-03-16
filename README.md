# Noodler

Solving string constraints via segment-automata and noodles.

See [example.ipynb](example.ipynb) to understand noodlification and unification.  The other notebook contains also the implementation and does not import from `noodler.py`. 

If you want to play with this, you need to have [Awali](http://vaucanson-project.org/Awali/) with Python bindings installed.  I also import `display_inline` from [Spot](https://spot.lrde.epita.fr/). If you don't have [Spot](https://spot.lrde.epita.fr/) locally, you can reimplement or remove the function `display_inline`. It is only used to show a variable name before automaton representing it.