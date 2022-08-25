"""
Additional (on top of `awalipy`) basic operations on automata

Public functions
----------------
* multiop: Apply binary operation on list of automata
* equivalent_all: Are given automata equivalent?
* chain_automata: Concatenate automata using ε-transitions
* eps_preserving_product: ε-NFA × NFA with ε-transitions preserved.
* eps_segmentation: compute levels of ε-transitions
* split_segment_aut: split segment automaton into segments
* single_final_init: restrict numbers of initial and final states to 1
"""
from typing import Callable, Sequence, Dict, Set

#import awalipy
import mata

from .core import Aut, SegAut, TransID


# Comments ###
# When splitting a segment automaton into segments
# I only trim the automata. Minimization can be run.


def multiop(automata: Sequence[Aut],
            operation: Callable[[Aut, Aut], Aut]) -> Aut:
    """
    Apply binary operation on multiple automata.

    Returns op(…op(op(A1, A2), A3), … An) where op is operation

    Parameters
    ----------
    automata : list of auts
        Must be non-empty.
    operation : function (aut × aut → aut)

    Returns
    -------
    res : aut
        op(…op(op(A1, A2), A3), … An)
    """
    if len(automata) == 0:
        raise ValueError("Sequence `automata` must be non-empty!")

    res = automata[0] #WARNING: REMOVED COPY
    for aut in automata[1:]:
        res = operation(res, aut)

    return res


def equivalent_all(auts: Sequence[Aut]) -> bool:
    """
    Check whether all automata are equivalent.

    Parameters
    ----------
    auts : iterable of auts

    Returns
    -------
        True if all automata from ``auts`` are equivalent.
        False otherwise.
    """
    if len(auts) <= 1:
        return True

    aut_l = list(auts)
    first_a = aut_l[0]
    for other in aut_l[1:]:
        if not mata.Nfa.equivalence_check(first_a, other):
            return False

    return True


def get_word_cycles(word: str) -> Set[str]:
    ret = set()
    for i in range(len(word)):
        ret.add(word[i:]+word[0:i])
    return ret
