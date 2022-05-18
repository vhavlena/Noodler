
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
        return self.eq == other.eq and self.index == other.index

    def __hash__(self):
        return hash((self.eq, self.index))

    def __str__(self):
        return str(index) + ": " + str(self.eq)

    def __repr__(self):
        return str(self)



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
                left = list(map(lambda x: VarNode(x[1],i,-x[0]), enumerate(eq.get_side("left"))))
                right = list(map(lambda x: VarNode(x[1],i,x[0]), enumerate(eq.get_side("right"))))
                node = EqNode(eq, left, right, [], [], i)
                self.vertices[i] = node
                indices_cl.append(i)
                i += 1
                for varn in left + right:
                    self.edges[varn.var].add(varn)
            indices_eq.append(indices_cl)

        self.init = [self.vertices[i] for i in indices_eq[0]]
        for i in range(len(indices_eq) - 1):
            succ = []
            for eq in indices_eq[i+1]:
                succ.append(self.vertices[eq])
            for eq in indices_eq[i]:
                self.vertices[eq].succ = copy.copy(succ)
        for _, node in self.vertices.items():
            for sc in node.succ:
                sc.prev.append(node)


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
        node = self.init[0]
        while len(node.succ) > 0:
            ret += print_list_node(node.succ) + "\n"
            node = node.succ[0]

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

        if node in self.init:
            self.init.remove(node)
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
            if func(node):
                ret.add(node)
            nodes.extend(node.succ)
        return ret


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


    def is_conjunction(self) -> bool:
        """
        Is the formula disjuction-free?
        """
        nodes = self.init
        while len(nodes) > 0:
            if len(nodes) > 1:
                return False
            nodes = nodes[0].succ
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
        return super().__str__()

    def __repr__(self):
        return str(self)


    def remove_eq(self, node: EqNode, minimize: bool):
        super().remove_node(node)

        side = "right" if len(node.eq.get_side("left")) == 1 else "left"
        var = node.eq.get_side(side_opposite(side))[0]

        q = AutSingleSEQuery(node.eq, self.aut_constr)
        aut = q.automaton_for_side(side).trim() if not minimize else q.automaton_for_side(side).proper().minimal_automaton().trim()
        prod = awalipy.product(aut, self.aut_constr[var]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not minimize else prod.minimal_automaton().trim()
        self.aut_constr[var] = prod


    def simplify_unique_light(self, minimize: bool = True):

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
