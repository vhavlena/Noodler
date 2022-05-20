
from typing import Dict, Type, Union, Sequence, Set, Optional, Callable
from enum import Enum
from dataclasses import dataclass
from collections import defaultdict, deque

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery, AutConstraints, StringConstraintQuery
from .formula import StringConstraint, ConstraintType

import itertools
import copy
import awalipy
import z3


def side_opposite(side: str) -> str:
    if side == "left":
        return "right"
    return "left"


@dataclass(eq=True,frozen=True)
class VarNode:
    var: str
    eq_index: int
    pos: int



@dataclass
class EqNode:
    eq : StringEquation
    left: Sequence[VarNode]
    right: Sequence[VarNode]
    succ: Sequence["EqNode"]
    prev: Sequence["EqNode"]
    index: int

    def __eq__(self, other):
        return self.index == other.index

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.index)

    def __str__(self):
        return str(self.index) + ": " + str(self.eq)

    def __repr__(self):
        return str(self)

    def is_simple_redundant(self) -> bool:
        return self.eq.get_side("left") == self.eq.get_side("right")



class FormulaVarGraph:

    def __init__(self, cnf_eqs):
        """
        Constructor converting sequence of equations in CNF into the internal
        representation
        """
        self.edges = defaultdict(lambda: set())
        self.vertices = dict()
        eqs = set()
        i = 0
        indices_eq = []

        for clause in cnf_eqs:
            indices_cl = []
            for eq in clause:
                left, right = self._create_node_sides(eq, i)
                node = EqNode(eq, left, right, set(), set(), i)
                self.vertices[i] = node
                indices_cl.append(i)
                i += 1
                for varn in left + right:
                    self.edges[varn.var].add(varn)
            indices_eq.append(indices_cl)

        self.init = {self.vertices[i] for i in indices_eq[0]}
        for i in range(len(indices_eq) - 1):
            succ = set()
            for eq in indices_eq[i+1]:
                succ.add(self.vertices[eq])
            for eq in indices_eq[i]:
                self.vertices[eq].succ = copy.copy(succ)
        for _, node in self.vertices.items():
            for sc in node.succ:
                sc.prev.add(node)


    def _create_node_sides(self, eq: StringEquation, index:int) -> tuple[Sequence[EqNode], Sequence[EqNode]]:
        """
        Create left and right side of EqNode for a given equation and index
        @param eq: Equation
        @param index: Index of the equation
        @return Initialized left, right
        """
        left = list(map(lambda x: VarNode(x[1],index,-x[0]), enumerate(eq.get_side("left"), 1)))
        right = list(map(lambda x: VarNode(x[1],index,x[0]), enumerate(eq.get_side("right"), 1)))
        return left, right


    def __str__(self) -> str:
        """
        Convert FormulaVarGraph to string
        """
        def print_list_node(lst):
            ret = ""
            add = ""
            for np in lst:
                ret += str(np.eq) + add
                add = " OR "
            return ret

        if len(self.init) == 0:
            return ""

        ret = print_list_node(self.init) + "\n"
        node = list(self.init)[0]
        while len(node.succ) > 0:
            ret += print_list_node(node.succ) + "\n"
            node = list(node.succ)[0]

        return ret


    def __repr__(self) -> str:
        """
        Convert FormulaVarGraph to string
        """
        return str(self)

    def get_vars_count(self) -> Dict[str, int]:
        """
        Get count of occurrences of every variable in the formula
        @return Dict: variable -> int
        """
        v_cnt = dict()
        for k, v in self.edges.items():
            v_cnt[k] = len(v)
        return v_cnt


    def update_eq(self, node: EqNode, eq: StringEquation):
        """
        Update equation of the given node
        @param node: Node to be updated
        @param eq: New equation
        """
        for v in node.left + node.right:
            self.edges[v.var].remove(v)
        node.left, node.right = self._create_node_sides(eq, node.index)
        for varn in node.left + node.right:
            self.edges[varn.var].add(varn)
        node.eq = eq


    def remove_node(self, node: EqNode):
        """
        Remove node (equation) from the formula
        @param node: Node to be removed
        """
        for v in node.left + node.right:
            self.edges[v.var].remove(v)
        for pr in node.prev:
            pr.succ.remove(node)
            pr.succ = pr.succ | node.succ
        for s in node.succ:
            s.prev.remove(node)
            s.prev = s.prev | node.prev

        if node in self.init:
            self.init.remove(node)
            self.init = self.init.union(node.succ)
        del self.vertices[node.index]


    def filter_nodes(self, func: Callable) -> Set[EqNode]:
        """
        Filter nodes to those satisfying the given predicate
        @param func: Predicate over nodes
        @return Set of nodes s.t. func is evaluate to true for them
        """
        nodes = deque(self.init)
        visited = set()
        ret = set()
        while len(nodes) > 0:
            node = nodes.popleft()
            if node in visited:
                continue
            visited.add(node)
            if func(node):
                ret.add(node)
            nodes.extend(node.succ)
        return ret


    def map_equations(self, func: Callable):
        """
        Map equations in all nodes
        @param func: Equation transformer
        """
        self.edges = defaultdict(lambda: set())
        for _, node in self.vertices.items():
            node.eq = func(node.eq)
            node.left, node.right = self._create_node_sides(node.eq, node.index)
            for varn in node.left + node.right:
                self.edges[varn.var].add(varn)


    def get_side_regular_nodes(self) -> Set[EqNode]:
        """
        Get nodes whose equation form is X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula and |X| = 1
        """
        return self.filter_nodes(lambda x: self.is_node_side_regular(x))


    def is_node_side_regular(self, node: EqNode) -> bool:
        """
        Is the given node of the form X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula
        """
        return (all(len(self.edges[item.var]) <= 1 for item in node.left) and \
            len(node.eq.get_side("right")) == 1) or \
            (all(len(self.edges[item.var]) <= 1 for item in node.right) and \
            len(node.eq.get_side("left")) == 1)


    def _is_clause_regular_side(self, clause: Set[EqNode], lit: Set[str], side: str) -> bool:
        """
        Is the given clause of the form X = X_1 X_2 X_3 OR X = X_4 X_5 ... where each
        X_i occurs at most once in the formula and X_i occurs in the side given by side
        @param clause: Clause
        @param lit: Set of literals
        @param side: Side of the equation
        """
        lefts = { tuple(node.eq.get_side(side)) for node in clause }
        if len(lefts) > 1 or len(list(lefts)[0]) != 1:
            return False
        if side == "left":
            return all(self.is_seq_regular(cl.right, lit) for cl in clause)
        return all(self.is_seq_regular(cl.left, lit) for cl in clause)


    def is_clause_regular(self, clause: Set[EqNode], lit: Set[str]) -> bool:
        """
        Is the given clause of the form X = X_1 X_2 X_3 OR X = X_4 X_5 ... where each
        X_i occurs at most once in the formula
        @param clause: Clause
        @param lit: Set of literals
        """
        return self._is_clause_regular_side(clause, lit, "left") or\
            self._is_clause_regular_side(clause, lit, "right")


    def is_seq_regular(self, seq: Sequence[VarNode], lit: Set[str]) -> bool:
        """
        Is the given sequence of the form X_1 X_2 X_3 where each X_i occurs at most
        once in the formula (or it is a literal)
        """
        return all(len(self.edges[item.var]) <= 1 for item in seq if item.var not in lit)\
            and len(seq) == len(set(seq))


    def get_simple_nodes(self) -> Set[EqNode]:
        """
        Get all simple nodes of the form X = Y
        @return Set of simple nodes (X=Y)
        """
        return self.filter_nodes(lambda x: len(x.eq.get_side("left")) == 1 and len(x.eq.get_side("right")) == 1)


    def get_clause(self, node: EqNode) -> Set[EqNode]:
        """
        Get clause containing the given node
        @param node: Node
        @return Set of nodes representing a clause
        """
        clause = set()
        if not node.prev:
            return self.init
        for pr in node.prev:
            clause = clause | pr.succ
        return clause


    def is_conjunction(self) -> bool:
        """
        Is the formula disjuction-free?
        """
        nodes = self.init
        while len(nodes) > 0:
            if len(nodes) > 1:
                return False
            nodes = list(nodes)[0].succ
        return True

    def _get_edges(self) -> Dict[str, Set[VarNode]]:
        """
        Get edges describing connections between occurrences of variables.
        """
        return self.edges

    def _get_vertices(self) -> Dict[int, EqNode]:
        """
        Get all vertices (mapping indices of equations to the corresponding EqNode)
        """
        return self.vertices

    def _get_init(self) -> Set[EqNode]:
        """
        Get all initial nodes
        """
        return self.init



class FormulaPreprocess(FormulaVarGraph):

    def __init__(self, cnf_eqs, aut_constr, minimize: bool):
        super().__init__(cnf_eqs)
        self.aut_constr = aut_constr
        self.var_cnt = 0
        self.minimize = minimize


    def __str__(self):
        """
        String representation
        """
        return super().__str__()

    def __repr__(self):
        """
        String representation
        """
        return str(self)


    def get_eps_vars(self) -> Set[str]:
        """
        Get variables whose language contains only epsilon
        @return Set of variables containig only epsilon
        """
        ret = set()
        for v, aut in self.aut_constr.items():
            aut = aut.proper().minimal_automaton().trim()
            if len(aut.transitions()) == 0:
                ret.add(v)
        return ret


    def get_literals(self) -> Set[str]:
        """
        Get literals
        """
        lit = set()
        for var, aut in self.aut_constr.items():
            aut = aut.trim()
            if len(aut.states()) - 1 == len(aut.transitions()) and aut.num_initials() == 1:
                lit.add(var)
        return lit


    def _get_new_var(self) -> str:
        """
        Create a fresh variable
        """
        self.var_cnt += 1
        return "_reg_var{0}".format(self.var_cnt)


    def remove_id(self, node: EqNode):
        """
        Remove node containig identity X = Y
        @param node: Node to be removed
        """
        assert(len(node.eq.get_side("left")) == 1 and len(node.eq.get_side("right")) == 1)

        var1 = node.eq.get_side("left")[0]
        var2 = node.eq.get_side("right")[0]

        prod = awalipy.product(self.aut_constr[var1], self.aut_constr[var2]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not self.minimize else prod.minimal_automaton().trim()
        self.aut_constr[var1] = prod
        self.aut_constr[var2] = prod
        super().remove_node(node)


    def remove_eq(self, node: EqNode, lits: Set[str]):
        """
        Remove given node representing an equation
        @param node: Node to be removed
        """

        side = None
        if len(node.eq.get_side("left")) == 1 and super().is_seq_regular(node.right, lits):
            side = "right"
        elif len(node.eq.get_side("right")) == 1 and super().is_seq_regular(node.left, lits):
            side = "left"
        else:
            return

        super().remove_node(node)
        var = node.eq.get_side(side_opposite(side))[0]

        q = AutSingleSEQuery(node.eq, self.aut_constr)
        aut = q.automaton_for_side(side).trim() if not self.minimize else q.automaton_for_side(side).proper().minimal_automaton().trim()
        prod = awalipy.product(aut, self.aut_constr[var]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not self.minimize else prod.minimal_automaton().trim()
        self.aut_constr[var] = prod


    def remove_clause(self, clause: Set[EqNode], lits: Set[str]):
        """
        Remove a given clause
        @param clause: Clause containing nodes to be removed
        @param lits: Literals
        """
        for node in list(clause):
            self.remove_eq(node, lits)


    def update_eq_regular_part(self, node: EqNode, new_var: str, remove_side: str, lits: Sequence[str]):
        """
        Update equation s.t. the regular side is replaced by a fresh variable.
        @param node: Node
        @param new_var: A fresh variable
        @param remove_side: Which side should be removed (left/right)
        @param lits: Set of literals
        """
        q = AutSingleSEQuery(node.eq, self.aut_constr)
        aut = q.automaton_for_side(remove_side)
        for v in node.eq.get_vars_side(remove_side) - lits:
            self.aut_constr.pop(v, None)
        self.aut_constr[new_var] = aut

        super().update_eq(node, StringEquation([new_var], node.eq.get_side(side_opposite(remove_side))))


    def simplify_unique(self):
        """
        Simplify equations having unique variables on a side.
        """

        lits = self.get_literals()

        nodes = deque(super().get_side_regular_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()
            if not node.index in super()._get_vertices():
                continue

            clause = super().get_clause(node)
            if not super().is_clause_regular(clause, lits):
                continue

            vars = set().union(*[ node.eq.get_vars() for node in clause ])
            self.remove_clause(clause, lits)
            for v in vars:
                if len(super()._get_edges()[v]) == 1:
                    eq_ind = list(super()._get_edges()[v])[0].eq_index
                    nodes.append(super()._get_vertices()[eq_ind])


    def propagate_variables(self):
        """
        Propagate variables.
        """

        assert(super().is_conjunction())

        nodes = deque(super().get_simple_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()
            if node.is_simple_redundant():
                self.remove_eq(node, node.eq.get_vars())
                continue

            v_left = node.eq.get_side("left")[0]
            replace = { v_left: node.eq.get_side("right")[0] }
            self.remove_id(node)
            super().map_equations(lambda x: x.replace(replace))


    def propagate_eps(self):
        """
        Propagate variables whose language contains only epsilon
        """

        assert(super().is_conjunction())

        eps = self.get_eps_vars()
        visited = set()
        vert = super()._get_vertices()

        n_list = []
        aut_eps = None
        for v in eps:
            n_list.extend([vert[n.eq_index] for n in super()._get_edges()[v]])
            aut_eps = self.aut_constr[v] if aut_eps is None else aut_eps

        nodes = deque(n_list)
        while len(nodes) > 0:
            node = nodes.popleft()
            if node in visited:
                continue

            visited.add(node)
            add_var = set()
            if node.eq.get_vars_side("left") <= eps:
                add_var = node.eq.get_vars_side("right") - eps
            elif node.eq.get_vars_side("right") <= eps:
                add_var = node.eq.get_vars_side("left") - eps

            for v in add_var:
                nodes.extend([vert[n.eq_index] for n in super()._get_edges()[v]])
            eps = eps | add_var

        for var in eps:
            self.aut_constr[var] = awalipy.product(self.aut_constr[var], aut_eps)
        super().map_equations(lambda x: x.remove(eps))
        self.clean()


    def _replace_unique_side_fresh(self):
        """
        Replace equations with a regular side (all variables occurring at
        most once in the formula) with a fresh variable.
        """
        lits = self.get_literals()

        for _, node in super()._get_vertices().items():
            if super().is_seq_regular(node.left, lits):
                new_var = self._get_new_var()
                self.update_eq_regular_part(node, new_var, "left", lits)
            elif super().is_seq_regular(node.right, lits):
                new_var = self._get_new_var()
                self.update_eq_regular_part(node, new_var, "right", lits)


    def reduce_regular_eqs(self):
        """
        Remove nodes that can be reduced to a regular constraint.
        """
        self._replace_unique_side_fresh()
        self.simplify_unique()


    def clean(self):
        """
        Remove trivial equations of the form [] = [] or [] = ...
        """
        empty = super().filter_nodes(lambda x: (not x.eq.get_side("left")) or\
            (not x.eq.get_side("right")))
        for node in empty:
            super().remove_node(node)
