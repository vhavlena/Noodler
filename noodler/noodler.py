"""
Classes
-------
AutSESystem
    System of 1 string equation with regular constraints on
    variables given by automata
RESESystem
    System with constraints represented by regular expressions.
Noodler

"""
import awalipy
import itertools

from collections import deque
from typing import Dict, Sequence

# Classes
from .core import StringEquation, SESystem
# Types
from .core import Aut, AutConstraints, SegAut

from .algos import chain_automata, eps_preserving_product, \
    eps_segmentation, multiop, split_segment_aut
from .utils import show_automata


class AutSESystem(SESystem):
    """
    String equation with automata constraints.

    The system is specified by a string equation and regular
    constraints on variables defined by automata.

    Functions
    ---------
    automata_for_side : "left"/"right" → list of auts
    is_balanced : bool
    show_constraints
        In Jupyter, display automaton for each variable
    """

    def __init__(self, equation: StringEquation,
                 constraints: AutConstraints):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        super().__init__(equation, constraints)

    def automata_for_side(self, side: str,
                          make_copies: bool = False) -> Sequence[Aut]:
        """
        Return list of automata for left/right side of equation.

        Parameters
        ----------
        side : "left" or "right"
        make_copies : Bool, default False
            Create copies of constraints automata if True
        Returns
        -------
        list of auts
        """
        var_sequence = self.eq.get_side(side)
        automata = []

        for var in var_sequence:
            if make_copies:
                aut = self.constraints[var].copy()
            else:
                aut = self.constraints[var]
            automata.append(aut)

        return automata

    def is_balanced(self) -> bool:
        """
        Check if system is balanced.

        System is balanced if automata representing both
        sides recognize equivalent languages.

        Returns
        -------
        True if system is balanced
        """
        auts_l = self.automata_for_side("left")
        auts_r = self.automata_for_side("right")

        aut_l = multiop(auts_l, awalipy.concatenate)
        aut_r = multiop(auts_r, awalipy.concatenate)

        return awalipy.are_equivalent(aut_l, aut_r)

    def show_constraints(self):
        show_automata(self.constraints)


class RESESystem(SESystem):
    """
    String equation with regular expression constraints for variables.

    The system is specified by a string equation and constraints on
    variables defined by regular expressions.

    Functions
    ---------
    automata_for_side : "left"/"right" → list of auts
    is_balanced : bool
    show_constraints
        In Jupyter, display automaton for each variable
    """

    def __init__(self, equation: StringEquation,
                 constraints: Dict[str, str]):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        res = {
            var: awalipy.RatExp(c) for var, c in constraints.items()
        }
        super().__init__(equation, res)

    def automata_for_side(self, side: str,
                          make_copies: bool = False) -> Sequence[Aut]:
        """
        Return list of automata for left/right side of equation.

        Parameters
        ----------
        side : "left" or "right"
        make_copies : Bool, default False
            Create copies of constraints automata if True
        Returns
        -------
        list of auts
        """
        var_sequence = self.eq.get_side(side)
        aut_const = self._get_automata_constraints()
        automata = []

        for var in var_sequence:
            if make_copies:
                aut = aut_const[var].copy()
            else:
                aut = aut_const[var]
            automata.append(aut)

        return automata

    def _get_automata_constraints(self) -> AutConstraints:
        """
        Return dictionatry with constraints as automata.
        """
        return {var: c.exp_to_aut() for var, c in self.constraints.items()}

    def aut_system(self) -> AutSESystem:
        """
        Convert into system with automata constraints.

        Returns
        -------
        AutSESystem
        """
        aut_const = self._get_automata_constraints()
        return AutSESystem(self.eq, aut_const)


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


def noodlify_system(system: AutSESystem) -> Sequence[SegAut]:
    """
    Make left-noodles from system.

    Parameters
    ----------
    system : AutSESystem
        System to be noodlified

    Returns
    -------
    noodles : Sequence[Aut]
        left-noodles for ``system``
    """
    left_in = system.automata_for_side("left")
    right_in = system.automata_for_side("right")
    left_seg_aut = chain_automata(left_in)
    right_aut: awalipy.Automaton = multiop(right_in, awalipy.concatenate)
    right_aut = right_aut.minimal_automaton().trim()
    product = eps_preserving_product(left_seg_aut, right_aut,
                                     history=True)

    return noodlify(product)


def unify(eq_l, eq_r,
          auts_l: Sequence[Aut],
          auts_r: Sequence[Aut],
          **kwargs):
    """
    Unify automata system for string equation.
    
    The equation is given as ``eq_l = eq_r`` and the
    system consists of two list of automata. Each 
    automaton in ``auts_l`` must correspond to a 
    variable in ``eq_l`` and analogously for ``_r``.
    
    For each variable from ``eq_l`` and ``eq_r`` make
    an intersection of all automata corresponding to
    this variable. If x is at position 2 in ``eq_l``
    and at positions 0 and 3 in ``eq_r``, unify makes
    product of ``auts_l[2]`` with ``auts_r[0]`` and
    ``auts_r[3]``.
    
    Parameters
    ----------
    eq_l, eq_r : str or list of str
    auts_l, auts_r : list of auts
        Length of auts_l must agree with length of eq_l
    make_copies : Bool (default False)
        Do not share the automata for each variable, make
        copies instead, if True.
    Returns
    -------
    new_auts_l, new_auts_r : list of auts
        Sequence of automata where automata representing
        the same variable are the same.
    """
    if len(auts_l) != len(eq_l):
        raise ValueError(f"""
        The length of `auts_l` must agree with length of `eq_l`.
        Given len(auts_l) = {len(auts_l)} and len(eq_l) = {len(eq_l)}.""")
    if len(auts_r) != len(eq_r):
        raise ValueError(f"""
        The length of `auts_r` must agree with length of `eq_r`.
        Given len(auts_r) = {len(auts_r)} and len(eq_r) = {len(eq_r)}.""")

    make_copies = kwargs.get("make_copies", False)

    variables = set(eq_l).union(set(eq_r))
    res_l = list(auts_l)
    res_r = list(auts_r)

    for var in variables:
        indices_l = [i for i, v in enumerate(eq_l) if v == var]
        indices_r = [i for i, v in enumerate(eq_r) if v == var]

        if len(indices_l) + len(indices_r) <= 1:
            continue

        automata = []
        for i in indices_l:
            # Call to proper changes the automata not to contain
            # ε-transitions. This is needed for product to work
            # in Awalipy.
            automata.append(auts_l[i].proper().min_quotient())
        for i in indices_r:
            automata.append(auts_r[i].proper().min_quotient())

        var_aut = automata[0]
        for next_aut in automata[1:]:
            var_aut = awalipy.product(var_aut, next_aut).min_quotient()

        for i in indices_l:
            if make_copies:
                res_l[i] = var_aut.copy()
            else:
                res_l[i] = var_aut
        for i in indices_r:
            if make_copies:
                res_r[i] = var_aut.copy()
            else:
                res_r[i] = var_aut

    return res_l, res_r


def create_unified_system(equation: StringEquation,
                          left_auts: Sequence[Aut],
                          right_auts: Sequence[Aut]) -> AutSESystem:
    """
    Create unified system from equation and automata.

    Unify automata given by left_auts and right_auts
    with respect to equation. That is, for each variable v
    present in the equation, make a product of automata
    that correspond to a occurrence of `v`. The product
    automaton is a constraint for `v` in the resulting
    system.

    Parameters
    ----------
    equation: StringEquation
    left_auts, right_auts: list of auts
        list of automata of the same length as ``equation.left``
        resp. ``equation.right``.
    Returns
    -------
    AutSESystem
        Unified system for ``equation``.
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

    return AutSESystem(equation, const)


def is_unified(equation, auts_l, auts_r):
    """
    Check if system is unified.

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


class Noodler:
    """
    Noodler makes and unifies automata noodles.

    Attributes
    ----------
    Q : deque
        Keep systems to be processed.
    """

    def __init__(self, system):
        """
        Create a noodler with an initialized queue.

        Parameters
        ----------
        system: AutSESystem
            System to start with
        """
        self.Q = deque([system])

    def process_one(self, verbose=False):
        system = self.Q.popleft()

        if verbose:
            print(f"""
================================
Processing the following system:
{system.eq}
Constraints:
{system.constraints}
--------------------------------""")

        noodles: Sequence[SegAut] = noodlify_system(system)
        for noodle in noodles:
            auts_l = split_segment_aut(noodle)
            auts_r = system.automata_for_side("right")
            noodle_sys = create_unified_system(system.eq,
                                               auts_l,
                                               auts_r)

            noodle_sys.eq = noodle_sys.eq.switched
            self.Q.append(noodle_sys)

        if verbose:
            print(f"""Found {len(noodles)} non-empty noodles.
================================""")
