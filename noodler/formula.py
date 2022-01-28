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

from typing import Dict, Type, Union, Sequence, Set
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
        return set(self.left) | set(self.right)


    def get_vars_side(self, side: str) -> Set[str]:
        if side == "left":
            return set(self.left)
        return set(self.right)


    def more_occur_side(self, side: str) -> bool:
        if side == "left":
            return len(set(self.left)) != len(self.left)
        return len(set(self.right)) != len(self.right)


    def is_sub_equation(self) -> bool:
        return (not self.more_occur_side("right")) and (len(self.get_vars_side("right") & self.get_vars_side("left")) == 0)


    def __str__(self):
        """Print equation in the form of left=right."""
        return f"{self.left} = {self.right}"

    def __repr__(self):
        return f"{self.__class__.__name__}: {self.left} = {self.right}"


class StringConstraint:
    """!
    Class representing general string constraints. Currently supported types of
    constraints include positive combination of regular expressions and
    equations.
    """

    def __init__(self, tp: ConstraintType, left_side: "StringConstraint", right_side: "StringConstraint" = None):
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


    def to_dnf(self) -> "StringConstraint":
        """!
        Convert a string constraint to DNF.

        @return Equivalent string constraint in DNF
        """
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

        left_lst = self.left.get_vars()
        right_lst = self.right.get_vars()
        return left_lst | right_lst


    def __str__(self) -> str:
        """!
        Convert the string constraint to a readable string representation.

        @return: String representation
        """
        if self.op == ConstraintType.EQ or self.op == ConstraintType.RE:
            return str(self.left)
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
        if self.op == ConstraintType.EQ or self.op == ConstraintType.RE:
            return []
        left_lst = self.left.gather_leafs(type)
        right_lst = self.right.gather_leafs(type)
        return left_lst + right_lst


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


@dataclass
class StringEqNode:
    succ : Sequence["StringEqNode"]
    eq : StringEquation
    id : int


class StringEqGraph:

    def __init__(self, vert: Sequence[StringEqNode], eqs: Set[StringEquation]):
        self.vertices = vert
        self.equations = eqs
        #self.sub_eqs = set()
        #self._compute_sub_eqs()


    def _compute_sub_eqs(self, vert):

        ret = set()
        disjoint = set()
        for v in vert:
            if v.is_sub_equation() and len(disjoint & v.get_vars_side("right")) == 0:
                ret.add(v)
                disjoint = disjoint.union(v.get_vars_side("right"))
        return ret


    def are_eq_sub(self, tmp: Set[StringEquation]) -> bool:
        return tmp <= self.sub_eqs


    def are_all_nontriv_sub(self) -> bool:
        for v in self.vertices:
            if len(v.succ) == 0:
                continue
            if not (v.eq in self.sub_eqs):
                return False
        return True

    def get_sccs(self) -> Sequence[Sequence[StringEqNode]]:
        n = len(self.vertices)
        graph = [[0]*n for i in range(n)]
        for v in self.vertices:
            for vp in v.succ:
                graph[vp.id][v.id] = 1

        mtx = csr_matrix(graph)
        k, labels = connected_components(csgraph=mtx, connection="strong", directed=True, return_labels=True)

        scc = [[] for i in range(n)]
        for i in range(n):
            scc[labels[i]].append(self.vertices[i])

        return scc


    def reduce(self):
        other_vars: dict[StringEquation, Set[str]] = defaultdict(lambda: set())

        for v1 in self.vertices:
            for v2 in self.vertices:
                if v1.eq == v2.eq:
                    continue
                other_vars[v1.eq] = other_vars[v1.eq].union(v2.eq.get_vars())

        # for v in self.vertices:
        #     if v.eq.is_sub_equation():
        #         v.succ = [s for s in v.succ if s.eq != v.eq.switched]

        for v in self.vertices:
            if v.eq.is_sub_equation():
                succp = []
                for prime in v.succ:
                    if len(prime.eq.get_vars() & v.eq.get_vars_side("left")) == 0:
                        continue
                    succp.append(prime)
                v.succ = succp


        for scc in self.get_sccs():
            rem = []
            for s in scc:
                if not s.eq.switched in rem:
                    rem.append(s.eq)
            if len(self._compute_sub_eqs(rem)) == len(rem):
                for v in scc:
                    v.succ = [s for s in v.succ if s.eq != v.eq.switched]




    def to_graphwiz(self):
        """!
        Convert the graph into the DOT format.
        """

        ret = "digraph \"Equation\" { rankdir=LR; \n"
        ret += "{ rank = LR }\n"
        ret += "node [shape = rectangle];\n"
        num: Dict[StringEquation, int] = dict()

        c = 0
        for eq in self.vertices:
            num[eq.eq] = c
            ret += "\"{0}\" [label=\"{1}\"]\n".format(c, eq.eq)
            c = c + 1

        for eq in self.vertices:
            for s in eq.succ:
                ret += "\"{0}\" -> \"{1}\";\n".format(num[eq.eq], num[s.eq])
        ret += "}\n";
        return ret
