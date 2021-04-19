"""
Define basic data structures and types.

A **segment automaton** is a NFA with ε-transitions such
that no ε-transition is on a cycle. Segment automata are
concatenation of _segments_.

Classes
-------
String_equation
SingleSEQuery
    Abstract class for String-equation queries

Types
-----
Aut : awalipy.Automaton
    General type of automaton.
AutConstraints : Dict[str, Aut]
    Automata as constraints for SE queries.
SegAut : awalipy.Automaton
    Segment automaton.
TransID : int
    ID of transition in automaton
"""

from typing import Any, Dict, Sequence, Type

import awalipy

Aut = awalipy.Automaton
SegAut: Type[awalipy.Automaton] = awalipy.Automaton

TransID = int

AutConstraints = Dict[str, Aut]


class StringEquation:
    # noinspection PyUnresolvedReferences
    """
        The basic class of string equations.

        If ``self.left[i] == v`` then `v` _occurs_ on left at `i`.

        Attributes
        ----------
        variables : str or list of str
            Variables that appear in the equation.
        left, right : str over vars or iterable of vars
            Left and right side of the equation.
        indices_l, indices_r : dict (vars → list of ints)
            Sequence of occurrences of `v` on each side for each var `v`.
        switched : StringEquation
            Pointer to equation with a switched sides.


        Public functions
        ----------------
        get_side : {"left","right"} → str or iterable of vars
            Returns corresponding side of the equation

        Notes
        -----
        By default ``self.switched.switched == self``.
        """

    def __init__(self, left_side: str, right_side: str,
                 switched=None, variables=None):
        """
        Create a String_equation.

        If ``vars`` is string, each character of it is treated as
        a variable.

        If switched is not specified, create it.

        Parameters
        ----------
        left_side, right_side : str over vars or list of vars
        switched : String_equation, default None
            Equation with switched sides.
        variables : str or list of str
            The variables that appear in the equation.
        """
        if variables is None:
            variables = set(left_side).union(set(right_side))
        self.vars = variables
        self.left = left_side
        self.right = right_side

        # Set indices dicts
        ind_l = {}
        ind_r = {}
        for var in self.vars:
            ind_l[var] = [i for i, v in enumerate(self.left) if v == var]
            ind_r[var] = [i for i, v in enumerate(self.right) if v == var]
        self.indices_l = ind_l
        self.indices_r = ind_r

        # Setup switched equation
        if switched is None:
            switched = StringEquation(self.right, self.left,
                                      switched=self,
                                      variables=self.vars)
        self.switched = switched

    def get_side(self, side: str) -> str:
        """
        Return the left or right side of equation.

        Parameters
        ----------
        side : {"left", "right"}

        Returns
        -------
        self.left or self.right
        """
        if side not in ["left", "right"]:
            raise ValueError("side must be 'left' or 'right'."
                             f"Given {side}.")
        if side == "left":
            return self.left
        return self.right

    def __str__(self):
        """Print equation in the form of left=right."""
        return f"{self.left} = {self.right}"

    def __repr__(self):
        return f"{self.__class__.__name__}: {self.left} = {self.right}"


class SingleSEQuery:
    """
    Abstract class for string equation with constraints.

    The query is specified by a string equation and
    some (regular) constraints (typically on variables).

    Public functions
    ----------------
    automata_for_side : "left"/"right" → list of auts
    seg_aut : "left"/"right" → SegAut
        return segment automaton representing one side of ``eq``
    proper_aut : "left"/"right" → Aut
        return proper (without ε-trans.) automaton representing
        one side of ``eq``
    show_constraints
        Show constraints in Jupyter

    Attributes
    ----------
    eq : StringEquation
    constraints
    """

    def __init__(self, equation: StringEquation,
                 constraints: Any):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        self.eq = equation
        self.constraints = constraints

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
        raise NotImplementedError

    def seg_aut(self, side: str) -> SegAut:
        """
        Returns segment automaton for left/right side of equation

        Parameters
        ----------
        side : "left" or "right"

        Returns
        -------
        SegAut representing the language of one side of equation.
        """
        raise NotImplementedError

    def proper_aut(self, side: str,
                   minimize: bool) -> Aut:
        """
        Returns automaton without ε-transitions for left/right side
        of equation.

        Parameters
        ----------
        side : "left" or "right"
        minimize : return the minimal aut if True

        Returns
        -------
        Aut representing the language of one side of equation.
        """
        raise NotImplementedError

    def show_constraints(self):
        print(f"{self.constraints}")
