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

from .formula import StringEquation, StringConstraint, ConstraintType

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


def compare_aut_constraints(a1: AutConstraints, a2: AutConstraints) -> bool:
    if a1.keys() != a2.keys():
        return False

    for k1, v1 in a1.items():
        if not awalipy.are_equivalent(v1, a2[k1]):
            return False
    return True


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
