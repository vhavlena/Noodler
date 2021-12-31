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

from typing import Dict, Type, Union, Sequence
from enum import Enum

import awalipy
import itertools

Aut = awalipy.Automaton
SegAut: Type[awalipy.Automaton] = awalipy.Automaton
RE = awalipy.RatExp

TransID = int

AutConstraints = Dict[str, Aut]
REConstraints = Dict[str, RE]
StrConstraints = Dict[str, str]
Constraints = Union[AutConstraints, REConstraints, StrConstraints]


class ConstraintType(Enum):
    EQ = 0
    AND = 1
    OR = 2
    RE = 3


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


    def get_vars(self) -> str:
        return self.left + self.right


    def __str__(self):
        """Print equation in the form of left=right."""
        return f"{self.left} = {self.right}"

    def __repr__(self):
        return f"{self.__class__.__name__}: {self.left} = {self.right}"


class StringConstraint:

    def __init__(self, tp: ConstraintType, left_side: "StringConstraint", right_side: "StringConstraint" = None):
        self.op = tp
        self.left = left_side
        self.right = right_side


    def to_dnf(self):
        if self.op == ConstraintType.EQ or self.op == ConstraintType.RE:
            return self

        left_tmp = self.left.to_dnf()
        right_tmp = self.right.to_dnf()

        if self.op == ConstraintType.OR:
            return StringConstraint(ConstraintType.OR, left_tmp, right_tmp)

        left_or = left_tmp.gather_op(ConstraintType.OR)
        right_or = right_tmp.gather_op(ConstraintType.OR)

        top_and = []
        for l,r in itertools.product(left_or, right_or):
            top_and.append(StringConstraint(ConstraintType.AND, l, r))

        return StringConstraint.build_op(ConstraintType.OR, top_and)


    def gather_op(self, type: ConstraintType):
        if self.op != type:
            return [self]

        left_lst = self.left.gather_op(type)
        right_lst = self.right.gather_op(type)
        return left_lst + right_lst


    def get_vars(self):
        if self.op == ConstraintType.EQ:
            return self.left.get_vars()
        if self.op == ConstraintType.RE:
            return list(self.left.keys())

        left_lst = self.left.get_vars()
        right_lst = self.right.get_vars()
        return left_lst + right_lst


    def __str__(self):
        if self.op == ConstraintType.EQ or self.op == ConstraintType.RE:
            return " : " + str(self.left)
        if self.op == ConstraintType.AND:
            return "({0} AND {1})".format(str(self.left), str(self.right))
        if self.op == ConstraintType.OR:
            return "({0} OR {1})".format(str(self.left), str(self.right))


    def gather_leafs(self, type: ConstraintType):
        if self.op == type:
            return [self]
        if self.op == ConstraintType.EQ or self.op == ConstraintType.RE:
            return []
        left_lst = self.left.gather_leafs(type)
        right_lst = self.right.gather_leafs(type)
        return left_lst + right_lst


    def __repr__(self):
        return str(self)


    @staticmethod
    def build_op(type: ConstraintType, lst: Sequence["StringConstraint"]):
        if len(lst) == 0:
            raise Exception("The list must be non-empty")

        act = lst[0]
        for i in range(1, len(lst)):
            act = StringConstraint(type, act, lst[i])
        return act




def is_straightline(equations: Sequence[StringEquation]) -> bool:
    """
    Check if SE system is in Single Static Assignment (SSA) form.

    A system given as a sequence of equations belongs to the
    straight-line (a.k.a. Single Static Assignment) fragment
    if and only if:
     1. Left sides of the equations consist of 1 variable only.
        This is, the system can be written as:
          x₀ = uvw
          x₁ = ...
          ...
          x_n = ...
     2. x_i does not appear in any eq_j for j<i holds for all i.

    Parameters
    ----------
    equations

    Returns
    -------
    True is given SE system is in SSA form.
    """
    definitions = set()
    for eq in equations[::-1]:
        if len(eq.left) != 1 or eq.left[0] in definitions:
            return False
        definitions.add(eq.left[0])

        for var in eq.right:
            if var in definitions:
                return False

    return True


def create_automata_constraints(constraints: Constraints) -> AutConstraints:
    """
    Parse any constraints-like dictionary into automata constraints.

    Each entry in `constraints` is process independently and thus
    can be of a different type (even an automaton).

    Parameters
    ----------
    constraints: Constraints Dict[str,RE] or Dict[str,Aut]
        Dictionary var → Union[RE,Aut] (where RE is either string
        or awalipy.RatExp)

    Returns
    -------
    AutConstraint
        The automata representation of constraints
    """
    res = {}
    for var, const in constraints.items():
        if isinstance(const, Aut):
            res[var] = const
            continue

        if isinstance(const, str):
            const = awalipy.RatExp(const)

        if not isinstance(const, RE):
            raise TypeError("constraints must be a regular expression")

        # We use the Thompson's algorithm as the derivative-term-based one
        # often explodes with growing alphabet.
        res[var] = awalipy.Automaton(const).proper().minimal_automaton().trim()

    return res
