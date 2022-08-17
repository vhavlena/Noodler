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
Aut : mata.Nfa
    General type of automaton.
AutConstraints : Dict[str, Aut]
    Automata as constraints for SE queries.
SegAut : mata.Nfa
    Segment automaton.
TransID : int
    ID of transition in automaton
"""

from typing import Dict, Type, Union, Sequence, Set, Optional, Callable
from enum import Enum
from dataclasses import dataclass
from collections import defaultdict

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

import itertools


class ConstraintType(Enum):
    EQ = 0
    AND = 1
    OR = 2
    RE = 3
    TRUE = 4
    FALSE = 5


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


    def get_vars(self) -> Set[str]:
        """!
        Get variables of the equation
        """
        return set(self.left) | set(self.right)


    def get_vars_side(self, side: str) -> Set[str]:
        """!
        Get variables of the equation for a give side (left/right)
        """
        if side == "left":
            return set(self.left)
        return set(self.right)


    def more_occur_side(self, side: str) -> bool:
        """!
        Is there any variable occurring multiple times on a given side?
        """
        if side == "left":
            return len(set(self.left)) != len(self.left)
        return len(set(self.right)) != len(self.right)


    def is_straightline(self) -> bool:
        """!
        Is the equation of the form Xn = X1 X2 ... X(n-1)
        """

        if not len(self.get_vars_side("right") & self.get_vars_side("left")) == 0:
            return False
        return len(self.get_side("left")) == 1 or len(self.get_side("right")) == 1


    def is_solution(self, assignment) -> bool:
        left = "".join(list(map(lambda x: assignment[x], self.left)))
        right = "".join(list(map(lambda x: assignment[x], self.right)))
        return left == right


    def replace(self,repl_map):
        l = []
        r = []
        for sym in self.left:
            l.append(repl_map.get(sym, sym))
        for sym in self.right:
            r.append(repl_map.get(sym, sym))
        return StringEquation(l, r)

    def remove(self, rem):
        l = []
        r = []
        for sym in self.left:
            if sym not in rem:
                l.append(sym)
        for sym in self.right:
            if sym not in rem:
                r.append(sym)
        return StringEquation(l, r)


    def __str__(self):
        """Print equation in the form of left=right."""
        return f"{self.left} = {self.right}"

    def __repr__(self):
        return f"{self.__class__.__name__}: {self.left} = {self.right}"

    def __eq__(self, other):
        return self.left == other.left and self.right == other.right

    def __hash__(self):
        return hash((tuple(self.left), tuple(self.right)))




class StringConstraint:
    """!
    Class representing general string constraints. Currently supported types of
    constraints include positive combination of regular expressions and
    equations.
    """

    def __init__(self, tp: ConstraintType, left_side: "StringConstraint" = None, right_side: "StringConstraint" = None):
        """!
        Create a string constraint. Currently supported types of constraints
        include positive combination of regular expressions and equations.

        @param tp: Constraint type
        @param left_side: A string constraint on the left side
        @param right_side: A string constraint on the right side
        """
        self.op = tp
        self.left = left_side
        self.right = right_side


    def is_eq_restr(self) -> bool:
        """!
        Check if the formula is a conjunction of equation with a regular constraint
        """
        if self.op == ConstraintType.AND:
            if self.left.op == ConstraintType.EQ and self.right.op == ConstraintType.RE:
                return True
        return False


    def is_cnf(self) -> bool:
        """!
        Check if the formula is in CNF
        """
        for con in self.gather_op(ConstraintType.AND):
            for lf in con.gather_op(ConstraintType.OR):
                if not lf.is_leaf() and not lf.is_eq_restr():
                    return False
        return True


    def get_cnf_list(self) -> Optional[Sequence[Sequence[StringEquation]]]:
        """!
        Get clauses of the formula in CNF in a list (the regular constraints
        are omited).

        @return List of clauses (list) containing only equations
        """
        ret = []
        for con in self.gather_op(ConstraintType.AND):
            lst = []
            for lf in con.gather_op(ConstraintType.OR):
                if lf.op == ConstraintType.RE:
                    continue
                elif lf.op == ConstraintType.EQ:
                    lst.append(lf.left)
                elif lf.is_eq_restr():
                    lst.append(lf.left.left)
                elif lf.op in [ConstraintType.TRUE, ConstraintType.FALSE]:
                    continue
                else:
                    return None
            if len(lst) > 0:
                ret.append(lst)
        return ret


    def to_dnf(self) -> "StringConstraint":
        """!
        Convert a string constraint to DNF.

        @return Equivalent string constraint in DNF
        """
        if self.is_leaf():
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


    def gather_op(self, type: ConstraintType) -> Sequence["StringConstraint"]:
        """!
        Gather subformulae at the top of the formula connected by a given
        constraint type.

        @param type: The top-formula constraint type whose subformulae are gathered.

        @return: List of formulae s.t. type [f1, ..., fn] = self
        """
        if self.op != type:
            return [self]

        left_lst = self.left.gather_op(type)
        right_lst = self.right.gather_op(type)
        return left_lst + right_lst


    def get_vars(self) -> Set[str]:
        """!
        Get variables occurring in the constraint.

        @return: Set of variables (variable is represented by a string)
        """
        if self.op == ConstraintType.EQ:
            return self.left.get_vars()
        if self.op == ConstraintType.RE:
            return set(self.left.keys())
        if self.op in [ConstraintType.TRUE, ConstraintType.FALSE]:
            return set()

        left_lst = self.left.get_vars()
        right_lst = self.right.get_vars()
        return left_lst | right_lst


    def __str__(self) -> str:
        """!
        Convert the string constraint to a readable string representation.

        @return: String representation
        """
        if self.op == ConstraintType.EQ:
            return "EQ: " + str(self.left)
        if self.op == ConstraintType.RE:
            return "RE: " + str(self.left)
        if self.op == ConstraintType.TRUE:
            return "TRUE"
        if self.op == ConstraintType.FALSE:
            return "FALSE"
        if self.op == ConstraintType.AND:
            return "({0} AND {1})".format(str(self.left), str(self.right))
        if self.op == ConstraintType.OR:
            return "({0} OR {1})".format(str(self.left), str(self.right))


    def gather_leafs(self, type: ConstraintType) -> Sequence["StringConstraint"]:
        """!
        Gather all atoms based on a given type occurring in the string constraint
        (atom/leaf is an equation or regular membership query).

        @param type: Atom type
        @return: A list of atomic string constraints
        """
        if self.op == type:
            return [self]
        if self.is_leaf():
            return []
        left_lst = self.left.gather_leafs(type)
        right_lst = self.right.gather_leafs(type)
        return left_lst + right_lst


    def is_leaf(self) -> bool:
        """!
        Is the formula an atomic formula?
        """
        return self.op in [ConstraintType.EQ, ConstraintType.RE, ConstraintType.TRUE, ConstraintType.FALSE]


    def restrict_eq(self, eqs: Set[StringEquation]) -> "StringConstraint":
        """!
        Restrict the equation only to equations from eqs.

        @param eqs: Equations that are kept
        @return Formula keeping atomic equations from eqs.
        """
        fl = self._restrict_eq(eqs)
        if fl is None:
            return StringConstraint(ConstraintType.TRUE)
        return fl


    def _restrict_eq(self, eqs: Set[StringEquation]) -> Optional["StringConstraint"]:
        """!
        Restrict the equation only to equations from eqs -- Auxiliary method.

        @param eqs: Equations that are kept
        @return Formula keeping atomic equations from eqs or None.
        """
        if self.op == ConstraintType.EQ:
            if self.left in eqs:
                return self
            return None
        elif self.is_leaf():
            return None

        left = self.left._restrict_eq(eqs)
        right = self.right._restrict_eq(eqs)
        if left is not None and right is not None:
            return StringConstraint(self.op, left, right)
        elif left is not None and right is None:
            return left
        elif left is None and right is not None:
            return right
        else:
            return None


    def rename_eq(self, ren_func: Callable) -> None:
        if self.op == ConstraintType.EQ:
            self.left = ren_func(self.left)
        if self.is_leaf():
            return

        self.left.rename_eq(ren_func)
        self.right.rename_eq(ren_func)


    def eval(self, sat: Dict[StringEquation, bool]) -> bool:
        if self.op == ConstraintType.EQ:
            return sat[self.left]
        elif self.op == ConstraintType.TRUE:
            return True
        elif self.op == ConstraintType.FALSE:
            return False
        elif self.op == ConstraintType.RE:
            raise Exception("REs are not supported for evaluation")


        left = self.left.eval(sat)
        right = self.right.eval(sat)

        if self.op == ConstraintType.AND:
            return left and right
        else:
            return left or right


    def __repr__(self):
        return str(self)


    @staticmethod
    def build_op(type: ConstraintType, lst: Sequence["StringConstraint"]):
        """!
        Create a string constraint from a list of subformulae, connected
        """
        if len(lst) == 0:
            raise Exception("The list must be non-empty")

        act = lst[0]
        for i in range(1, len(lst)):
            act = StringConstraint(type, act, lst[i])
        return act
