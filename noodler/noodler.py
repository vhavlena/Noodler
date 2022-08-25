"""
Classes
-------
SimpleNoodler
    Creates unified noodles for AutSingleSEQuery instances. This is
    enough for simple equations (all variables that occur the
    right-hand side of the equation are unique).
QueueNoodler
    Seek solutions using noodlification for non-simple equations.

StraightlineNoodleMachine
    Solves Straight-line MiultiSEQueries with proved termination.
"""
#import awalipy
import itertools
import mata

from collections import deque
from typing import Sequence, Optional, List

# Classes
from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery
# Types
from .core import Aut, AutConstraints, SegAut

from .algos import multiop


def noodlify_query(query: SingleSEQuery) -> Sequence[SegAut]:
    """
    Make left-noodles from query.

    The noodles (result) are not necessary unified.

    Parameters
    ----------
    query : sequery.AutSingleSEQuery
        query to be noodlified

    Returns
    -------
    noodles : Sequence[Aut]
        left-noodles for ``query``
    """

    lefts: SegAut = query.automata_for_side("left")
    right: Aut = query.proper_aut("right")
    return mata.Nfa.noodlify_for_equation(lefts, right)


    # left: SegAut = query.seg_aut("left")
    # right: Aut = query.proper_aut("right")
    # assert left.alphabet() == right.alphabet()
    # product: SegAut = eps_preserving_product(left, right, history=True)
    # return noodlify(product)


def create_unified_query(equation: StringEquation,
                         left_auts: Sequence[Aut],
                         right_auts: Sequence[Aut]) -> \
                                    Optional[AutSingleSEQuery]:
    """
    Create unified query from equation and automata.

    Unify automata given by left_auts and right_auts
    with respect to equation. That is, for each variable v
    present in the equation, make a product of automata
    that correspond to a occurrence of `v`. The product
    automaton is a constraint for `v` in the resulting
    query.

    If the language (of the product) for some variable is
    empty, the query can't be unified.

    Parameters
    ----------
    equation: StringEquation
    left_auts, right_auts: list of auts
        list of automata of the same length as ``equation.left``
        resp. ``equation.right``.
    Returns
    -------
    AutSingleSEQuery
        Unified query for ``equation`` and None if the query cannot
        be unified.
    """
    if len(left_auts) != len(equation.left):
        raise ValueError(f"""
        The length of `left_auts` must agree with length of `equation.left`.
        Given len(left_auts) = {len(left_auts)} and
              len(equation.left) = {len(equation.left)}.""")
    if len(right_auts) != len(equation.right):
        raise ValueError(f"""
        The length of `right_auts` must agree with length of `equation.right`.
        Given len(right_auts) = {len(right_auts)} and
              len(equation.right) = {len(equation.right)}.""")

    const: AutConstraints = {}

    for var in equation.vars:
        aut_l = {left_auts[i] for i in equation.indices_l[var]}
        aut_r = {right_auts[i] for i in equation.indices_r[var]}
        var_auts = aut_l.union(aut_r)
        product: Aut = multiop(list(var_auts), lambda x,y: mata.intersection(x,y)[0])
        product.trim()
        const[var] = product
        if const[var].get_num_of_states() == 0:
            return None

    return AutSingleSEQuery(equation, const)


def is_unified(equation, auts_l, auts_r):
    """
    Check if query is unified.

    Check for each variable of equation whether
    all corresponding automata in auts_l and auts_r
    recognize the same language.

    The lengths of auts must correspond to lengths
    of equation sides.

    Parameters
    ----------
    equation : StringEquation
    auts_l, auts_r : list of auts
        Automata representing eq_l

    Returns
    -------
        False if two automata for the same variable recognize
        different languages. True otherwise.
    """
    pass


class SimpleNoodler:
    """
    Makes unified automata noodles for easy equations.

    This class is intended to work for one simple
    SingleSEquery. It creates segment automaton for the
    left-hand side, intersects it with the automaton for
    the right-hand side and creates all possible unified
    noodles.

    Restrictions on equation
    ------------------------
    All variables that appear on the right-hand side of
    the equation must have only one occurrence in the
    equation.

    Attributes
    ---------
    query : SingleSEQuery
    noodles : Sequence[SingleSEQuery]
        unified noodles for ``query``
    """

    def __init__(self, query: SingleSEQuery):
        self.query = query
        self.noodles = None

    def noodlify(self) -> Sequence[SingleSEQuery]:
        """
        Create all possible non-empty unified noodles for
        self.query.

        Returns
        -------
        self.noodles:
        """
        self.noodles = []

        noodles: Sequence[SegAut] = noodlify_query(self.query)
        for auts_l in noodles:
            #auts_l = split_segment_aut(noodle)
            auts_r = self.query.automata_for_side("right")
            unified = create_unified_query(self.query.eq,
                                           auts_l,
                                           auts_r)

            # Noodle cannot be unified
            if unified is not None:
                self.noodles.append(unified)

        return self.noodles
