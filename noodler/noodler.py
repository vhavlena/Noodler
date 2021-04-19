"""
Classes
-------
AutSingleSEQuery
    query of 1 string equation with regular constraints on
    variables given by automata
RESingleSEQuery
    query with constraints represented by regular expressions.
SimpleNoodler
    Creates unified noodles for AutSingleSEQuery instances. This is
    enough for simple equations (all variables that occur the
    right-hand side of the equation are unique).
QueueNoodler
    Seek solutions using noodlification for non-simple equations.
"""
import awalipy
import itertools

from collections import deque
from typing import Sequence

# Classes
from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery
# Types
from .core import Aut, AutConstraints, SegAut

from .algos import eps_preserving_product, \
    eps_segmentation, multiop, split_segment_aut


def noodlify(aut: SegAut,
             include_empty: bool = False) -> Sequence[SegAut]:
    """
    Create noodles from segment automaton.
    
    Segment automaton is a chain of automata connected
    via ε-transitions. A noodle is a copy of the segment
    automaton with exactly 1 ε-transition between each
    two consecutive segments. Noodlify return the list of
    all (non-empty) noodles.
    
    Parameters
    ----------
    aut : aut
        Segment automaton to noodlify.
    include_empty : Bool (default False)
        Include also empty noodles if True.
    """
    # Stores the noodles
    noodles = []

    # We need to make a copy of the automaton before running
    # segmentation to remove non-existent transitions.
    aut = aut.copy()
    # depth → list of ε-trans
    segments = eps_segmentation(aut)

    # For each combination of ε-transitions, create the automaton.
    for noodle_trans in itertools.product(*segments.values()):
        noodle = aut.copy()
        for i in reversed(range(len(noodle_trans))):
            # Remove all ε-tr. of depth i but noodle_trans[i]
            for tr in segments[i]:
                assert noodle.label_of(tr) == "\\e"
                if tr != noodle_trans[i]:
                    noodle.del_transition(tr)

        noodle = noodle.trim()
        if include_empty or noodle.num_states() > 0:
            noodles.append(noodle)

    return noodles


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
    left: SegAut = query.seg_aut("left")
    right: Aut = query.proper_aut("right")
    product: SegAut = eps_preserving_product(left, right, history=True)
    return noodlify(product)


def create_unified_query(equation: StringEquation,
                         left_auts: Sequence[Aut],
                         right_auts: Sequence[Aut]) -> AutSingleSEQuery:
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
        product: Aut = multiop(list(var_auts), awalipy.product)
        const[var] = product.minimal_automaton().trim()
        if const[var].num_states() == 0:
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
        for noodle in noodles:
            auts_l = split_segment_aut(noodle)
            auts_r = self.query.automata_for_side("right")
            unified = create_unified_query(self.query.eq,
                                           auts_l,
                                           auts_r)

            # Noodle cannot be unified
            if unified is not None:
                self.noodles.append(unified)

        return self.noodles


class QueueNoodler:
    """
    QueueNoodler makes and unifies automata noodles.

    Attributes
    ----------
    Q : deque
        Keep querys to be processed.
    """

    def __init__(self, query):
        """
        Create a noodler with an initialized queue.

        Parameters
        ----------
        query: AutSingleSEQuery
            query to start with
        """
        self.Q = deque([query])
        self.solutions = []

    def one_solution(self):
        """
        Attempts to find a solution.

        Take one query out of queue, noodlify it and then
        unify each noodle with the right-hand side automata.
        If this unified query is balanced, store it into
        self.solutions and return it. Otherwise, add it to
        queue and continue.

        No guarantees on termination.

        Returns
        -------
        Balanced and unified query or None
        """
        query = self.Q.popleft()
        if query.is_balanced():
            self.solutions.append(query)
            return query

        while query:
            noodles = noodlify_query(query)
            for noodle in noodles:
                auts_l = split_segment_aut(noodle)
                auts_r = query.automata_for_side("right")
                noodle_sys = create_unified_query(query.eq,
                                                  auts_l,
                                                  auts_r)
                # Noodle cannot be unified
                if noodle_sys is None:
                    continue

                if noodle_sys.is_balanced():
                    self.solutions.append(noodle_sys)
                    return noodle_sys
                else:
                    self.Q.append(noodle_sys.switched())

            query = self.Q.popleft()

        # Nothing was found
        return None

    def process_one(self, verbose=False):
        query = self.Q.popleft()

        if verbose:
            print(f"""
================================
Processing the following query:
{query.eq}
Constraints:
{query.constraints}
--------------------------------""")

        noodles: Sequence[SegAut] = noodlify_query(query)
        for noodle in noodles:
            auts_l = split_segment_aut(noodle)
            auts_r = query.automata_for_side("right")
            noodle_sys = create_unified_query(query.eq,
                                              auts_l,
                                              auts_r)

            noodle_sys.eq = noodle_sys.eq.switched
            self.Q.append(noodle_sys)

        if verbose:
            print(f"""Found {len(noodles)} non-empty noodles.
================================""")
