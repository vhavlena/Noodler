
from typing import Dict, Type, Union, Sequence, Set
from enum import Enum
from dataclasses import dataclass
from collections import defaultdict

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery

import itertools
import copy
import awalipy


@dataclass
class StringEqNode:
    """!
    Node with an equation
    """
    succ : Sequence["StringEqNode"]
    eq : StringEquation
    id : int


class StringEqGraph:
    """!
    Graph of equations
    """

    def __init__(self, vert: Sequence[StringEqNode]):
        """!
        Constructior

        @param vert: List of vertices
        """
        self.vertices = vert


    def copy(self) -> "StringEqGraph":
        """!
        Make a copy of the graph

        @return Copied graph
        """

        vert_n = []
        nodes: Dict[StringEquation, StringEqNode] = dict()
        for v in self.vertices:
            nn: StringEqNode = StringEqNode([], v.eq, v.id)
            nodes[v.eq] = nn
            vert_n.append(nn)

        for v in self.vertices:
            for s in v.succ:
                nodes[v.eq].succ.append(nodes[s.eq])

        return StringEqGraph(vert_n)


    def subgraph(self, restr: Set[StringEquation]) -> None:
        """!
        Get subgraph induced by a set of string equations (in place
        modification of the graph).

        @param restr: Set of equations to be kept in the graph
        """

        vert_n = []
        for v in self.vertices:
            if not v.eq in restr:
                continue

            vert_n.append(v)
            tmp = []
            for s in v.succ:
                if not s.eq in restr:
                    continue
                tmp.append(s)
            v.succ = tmp
        self.vertices = vert_n


    def rename_id(self) -> None:
        """!
        Rename ids of nodes (consecutive numbers from 0)
        """
        c = 0
        for v in self.vertices:
            v.id = c
            c += 1


    def get_sccs(self) -> Sequence[Sequence[StringEqNode]]:
        """!
        Get SCCs of the graph

        @return List of SCCs (each SCC is a list of nodes)
        """

        if len(self.vertices) == 0:
            return []

        self.rename_id()
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


    def remove_regular_nodes(self, aut_constraints) -> None:
        """!
        Remove nodes from the graph that can be reduced to a regular constraint.
        Implemented as a fixpoint evaluation.

        @param aut_constraints: Automata constraints to be updated
        """

        def _remove_reg_iter():
            other_vars: dict[StringEquation, Set[str]] = defaultdict(lambda: set())
            for v1 in self.vertices:
                for v2 in self.vertices:
                    if v1.eq == v2.eq or v1.eq == v2.eq.switched:
                        continue
                    other_vars[v1.eq] = other_vars[v1.eq].union(v2.eq.get_vars())

            stay = set()
            for v in self.vertices:
                if len(v.eq.get_side("right")) == 1 and len(other_vars[v.eq] & v.eq.get_vars_side("left")) == 0 and not v.eq.more_occur_side("left"):
                    var = v.eq.get_side("right")[0]
                    q = AutSingleSEQuery(v.eq, aut_constraints)
                    aut_constraints[var] = awalipy.product(q.automaton_for_side("left"), aut_constraints[var]).proper().minimal_automaton().trim()
                elif len(v.eq.get_side("left")) == 1 and len(other_vars[v.eq] & v.eq.get_vars_side("right")) == 0 and not v.eq.more_occur_side("right"):
                    var = v.eq.get_side("left")[0]
                    q = AutSingleSEQuery(v.eq, aut_constraints)
                    aut_constraints[var] = awalipy.product(q.automaton_for_side("right"), aut_constraints[var]).proper().minimal_automaton().trim()
                else:
                    stay.add(v.eq)
            self.subgraph(stay)

        b, a = 0, len(self.vertices)
        while b - a != 0:
            b = a
            _remove_reg_iter()
            a = len(self.vertices)



    def straight_line(self) -> "StringEqGraph":
        """!
        Reduce the equation graph to a straight line graph (only if it
        is possible).

        @return Reduced graph
        """

        cp = self.copy()
        # Assumes no equations of the form X = Y
        eqs = set()
        for v in cp.vertices:
            if v.eq.is_straightline():
                if not v.eq.switched in eqs and len(v.eq.get_side("left")) == 1:
                    eqs.add(v.eq)
            else:
                return None

        cp.subgraph(eqs)
        for v in cp.vertices:
            succp = []
            for prime in v.succ:
                if len(v.eq.get_vars() & prime.eq.get_vars_side("left")) == 0:
                    continue
                succp.append(prime)
            v.succ = succp

        for scc in cp.get_sccs():
            if len(scc) > 1:
                return None

        return cp


    def to_graphwiz(self) -> str:
        """!
        Convert the graph into the DOT format.

        @return DOT format
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


    @staticmethod
    def get_eqs_graph(equations: Sequence[Sequence[StringEquation]]) -> "StringEqGraph":
        """!
        Get graph of equations. Each node is an equation. We distinguish L=R and
        R=L. Two equations are adjacent if they share a variable.

        @param equations: Sequence of string equations representing a conjunction of equations
        @return String Equation Graph
        """

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        c = 0
        for clause in equations:
            for eq in clause:
                nn: StringEqNode = StringEqNode([], eq, c)
                nodes[eq] = nn
                nnpr: StringEqNode = StringEqNode([], eq.switched, c+1)
                nodes[eq.switched] = nnpr
                nn.succ.append(nnpr)
                nnpr.succ.append(nn)
                all_nodes.append(nn)
                all_nodes.append(nnpr)
                c += 2

        for v1 in all_nodes:
            for clause in equations:
                if v1.eq in clause or v1.eq.switched in clause:
                    continue
                for v2 in clause:
                    if len(v1.eq.get_vars() & v2.get_vars()) != 0:
                        v1.succ.append(nodes[v2])
                        v1.succ.append(nodes[v2.switched])

        return StringEqGraph(all_nodes)
