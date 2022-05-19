
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


    def get_side_dead_nodes(self) -> Set[EqNode]:
        """
        Get nodes whose equation form is X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula and |X| = 1
        """
        return self.filter_nodes(lambda x: self.is_node_side_dead(x))


    def is_node_side_dead(self, node: EqNode) -> bool:
        """
        Is the given node of the form X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula
        """
        return (all(len(self.edges[item.var]) <= 1 for item in node.left) and \
            len(node.eq.get_side("right")) == 1) or \
            (all(len(self.edges[item.var]) <= 1 for item in node.right) and \
            len(node.eq.get_side("left")) == 1)


    def get_simple_nodes(self) -> Set[EqNode]:
        """
        Get all simple nodes of the form X = Y
        @return Set of simple nodes (X=Y)
        """
        return self.filter_nodes(lambda x: len(x.eq.get_side("left")) == 1 and len(x.eq.get_side("right")) == 1)


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



class FormulaPreprocess(FormulaVarGraph):

    def __init__(self, cnf_eqs, aut_constr):
        super().__init__(cnf_eqs)
        self.aut_constr = aut_constr


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


    def remove_eq(self, node: EqNode, minimize: bool):
        """
        Remove given node representing an equation
        @param node: Node to be removed
        @param minimize: Minimize the modified automaton
        """
        super().remove_node(node)

        if (not node.eq.get_side("left")) or (not node.eq.get_side("right")):
            return
        side = "right" if len(node.eq.get_side("left")) == 1 else "left"
        var = node.eq.get_side(side_opposite(side))[0]

        q = AutSingleSEQuery(node.eq, self.aut_constr)
        aut = q.automaton_for_side(side).trim() if not minimize else q.automaton_for_side(side).proper().minimal_automaton().trim()
        prod = awalipy.product(aut, self.aut_constr[var]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not minimize else prod.minimal_automaton().trim()
        self.aut_constr[var] = prod


    def simplify_unique_light(self, minimize: bool = True):
        """
        Simplify equations having unique variables on a side.
        @param minimize: Minimize the created automata
        """

        assert(super().is_conjunction())

        nodes = deque(super().get_side_dead_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()
            if not super().is_node_side_dead(node):
                continue

            vars = node.eq.get_vars()
            self.remove_eq(node, minimize)
            for v in vars:
                if len(super()._get_edges()[v]) == 1:
                    eq_ind = list(super()._get_edges()[v])[0].eq_index
                    nodes.append(super()._get_vertices()[eq_ind])


    def propagate_variables(self, minimize: bool = True):
        """
        Propagate variables.
        @param minimize: Minimize the created automata
        """

        assert(super().is_conjunction())

        nodes = deque(super().get_simple_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()
            if node.is_simple_redundant():
                self.remove_eq(node, minimize)
                continue

            v_left = node.eq.get_side("left")[0]
            replace = { v_left: node.eq.get_side("right")[0] }
            self.remove_eq(node, minimize)
            super().map_equations(lambda x: x.replace(replace))


    def propagate_eps(self):
        """
        Propagate variables whose language contains only epsilon
        @param minimize: Minimize the created automata
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
        self.clean(True)


    def clean(self, minimize: bool):
        """
        Remove trivial equations of the form [] = [] or [] = ...
        @param minimize: Minimize the created automata
        """
        empty = super().filter_nodes(lambda x: (not x.eq.get_side("left")) or\
            (not x.eq.get_side("right")))
        for node in empty:
            self.remove_eq(node, minimize)
