
from email.policy import default
from typing import Dict, Type, Union, Sequence, Set, Optional
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


@dataclass
class StringEqNode:
    """!
    Node with an equation
    """
    succ : Sequence["StringEqNode"]
    eval_formula : StringConstraint
    eq : Optional[StringEquation]
    id : int
    label : object

    def __init__(self, s, f, e, i):
        self.succ = s
        self.eval_formula = f
        self.eq = e
        self.id = i
        self.label = None

    def __eq__(self, other):
        if not isinstance(other, StringEqNode):
            return False

        if self.eq != other.eq or self.id != other.id:
            return False

        return { p.eq for p in self.succ } == { p.eq for p in other.succ }


class StringEqGraph:
    """!
    Graph of equations
    """

    def __init__(self, vert: Sequence[StringEqNode], ini: Sequence[StringEqNode], fin: Sequence[StringEqNode]):
        """!
        Constructior

        @param vert: List of vertices
        """
        self.vertices = vert
        self.initials = ini
        self.finals = fin

    def copy(self) -> "StringEqGraph":
        """!
        Make a copy of the graph

        @return Copied graph
        """

        vert_n = []
        nodes: Dict[StringEquation, StringEqNode] = dict()
        for v in self.vertices:
            nn: StringEqNode = StringEqNode([], StringConstraint(ConstraintType.TRUE), v.eq, v.id)
            nodes[v.eq] = nn
            vert_n.append(nn)

        for v in self.vertices:
            for s in v.succ:
                nodes[v.eq].succ.append(nodes[s.eq])
            nodes[v.eq].eval_formula = copy.copy(v.eval_formula)

        ini = [nodes[v.eq] for v in self.initials]
        fin = [nodes[v.eq] for v in self.finals]

        return StringEqGraph(vert_n, ini, fin)


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
            v.eval_formula = v.eval_formula.restrict_eq(restr)

        self.vertices = vert_n


    def rename_id(self) -> None:
        """!
        Rename ids of nodes (consecutive numbers from 0)
        """
        c = 0
        for v in self.vertices:
            v.id = c
            c += 1


    def get_scc_graph(self) -> "StringEqGraph":
        vert = []
        scc_map = dict()
        eq_map = dict()
        succ = defaultdict(lambda: set())
        cnt = 0

        for scc in self.get_sccs():
            if len(scc) == 0:
                continue
            new = StringEqNode([], StringConstraint(ConstraintType.TRUE), scc[0].eq, cnt)
            new.label = scc
            vert.append(new)
            scc_map[cnt] = new
            for v in scc:
                eq_map[v.eq] = cnt
            cnt += 1

        for v in self.vertices:
            for s in v.succ:
                succ[eq_map[v.eq]].add(eq_map[s.eq])

        for k, v in succ.items():
            scc_map[k].succ = [ scc_map[n] for n in v if n != k ]

        return StringEqGraph(vert, vert, [])


    def union(self, other):
        """
        Union two graphs (in place)
        @param other: Another graph
        """
        self.vertices = self.vertices + other.vertices
        self.initials = self.initials + other.initials
        self.finals = self.finals + other.finals


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


    def straight_line(self) -> "StringEqGraph":
        """!
        Reduce the equation graph to a straight line graph (only if it
        is possible).

        @return Reduced graph
        """

        cp = self.copy()
        var_order = defaultdict(lambda: 0)

        c = 1
        eqs = set()
        for v in cp.vertices:
            if v.eq.is_straightline():
                if not v.eq.switched in eqs and len(v.eq.get_side("left")) == 1:
                    var_order[v.eq.get_side("left")[0]] = c
                    c += 1
                    eqs.add(v.eq)
            else:
                return None

        for v in cp.vertices:
            if v.eq in eqs:
                c = var_order[v.eq.get_side("left")[0]]
                if c <= max([var_order[x] for x in v.eq.get_vars_side("right")]):
                    return None

        cp.subgraph(eqs)
        for v in cp.vertices:
            succp = []
            for prime in v.succ:
                if var_order[v.eq.get_side("left")[0]] < var_order[prime.eq.get_side("left")[0]]:
                    continue
                succp.append(prime)
            v.succ = succp
            v.eval_formula = v.eval_formula.restrict_eq(set([x.eq for x in succp]))

        for scc in cp.get_sccs():
            if len(scc) > 1:
                return None

        not_ini = set()
        cp.finals = []
        for v in cp.vertices:
            not_ini = not_ini.union(set([c.eq for c in v.succ]))
            if len(v.succ) == 0:
                cp.finals.append(v)
        cp.initials = [c for c in cp.vertices if c.eq not in not_ini]

        for v in cp.vertices:
            v.eq = v.eq.switched
            v.eval_formula.rename_eq(lambda x: x.switched)

        return cp

    
    def is_acyclic(self) -> bool:
        """
        Is the graph acyclic?
        """
        sccs = self.get_sccs()
        for scc in sccs:
            if len(scc) > 1:
                return False
        return True  


    def to_graphwiz(self) -> str:
        """!
        Convert the graph into the DOT format.

        @return DOT format
        """

        ret = "digraph \"Equation\" { rankdir=LR; \n forcelabels=true\n"
        ret += "{ rank = LR }\n"
        ret += "node [shape = rectangle];\n"
        num: Dict[StringEquation, int] = dict()

        c = 0
        for eq in self.vertices:
            num[eq.eq] = c

            attr = ""
            if eq in self.initials:
                attr += ", color=red"
            if eq in self.finals:
                attr += ", style=filled, fillcolor=lightgreen"

            ret += "\"{0}\" [label=\"{1}\", xlabel=\"{2}\"{3}]\n".format(c, eq.eq, eq.eval_formula, attr)
            c = c + 1

        for eq in self.vertices:
            for s in eq.succ:
                ret += "\"{0}\" -> \"{1}\";\n".format(num[eq.eq], num[s.eq])
        ret += "}\n";
        return ret


    def topological_sort(self, init: StringEqNode, seen: Set[StringEquation]):
        """!
        Topological sort of the graph. Modified from https://stackoverflow.com/questions/
        47192626/deceptively-simple-implementation-of-topological-sorting-in-python

        @param init: Initial vertex
        @param seen: All so-far seen vertices
        @return list of vertices matching topological order modulo cycles (that
            are allowed)
        """
        stack = []
        order = []
        q = [init]
        while q:
            v = q.pop()
            if v.eq not in seen:
                seen.add(v.eq)
                q.extend(v.succ)

                while stack and v.eq not in { s.eq for s in stack[-1].succ }:
                    order.append(stack.pop())
                stack.append(v)

        return stack + order[::-1]


    def linearize(self):
        """!
        Linearize the graph to a line graph with possible cycles (extending the
        topological order).
        """
        seen = set()
        order = {}
        c = 0
        ts = []

        scc_graph = self.get_scc_graph()
        eqs = { v.eq for v in scc_graph.vertices }
        for v in scc_graph.vertices:
            for s in v.succ:
                eqs.discard(s.eq)

        for ini in [v for v in scc_graph.initials if v.eq in eqs] + scc_graph.initials:
            sr =  self.topological_sort(ini, seen)
            seen = seen | {v.eq for v in sr}
            ts = sr + ts

        tslist = []
        for t in ts:
            for v in t.label:
                new = StringEqNode([], StringConstraint(ConstraintType.TRUE), v.eq.switched, 0)
                tslist.append(new)
            tslist.extend(t.label)

        ts = tslist
        self.vertices = ts

        for node in ts:
            order[node.eq] = c
            node.eval_formula = StringConstraint(ConstraintType.TRUE)
            c += 1

        for i in range(len(ts)):
            ts[i].succ = [] # [ s for s in ts[i].succ if order[s.eq] < order[ts[i].eq] ]
            if i != len(ts) - 1:
                ts[i].succ.append(ts[i+1])

            for s in ts[i].succ:
                ts[i].eval_formula = StringConstraint(ConstraintType.AND, s.eval_formula, StringConstraint(ConstraintType.EQ, s.eq))

        self.initials = [ts[0]]
        self.finals = [ts[-1]]


    @staticmethod
    def quick_unsat_check(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints, literals: Set[str]):
        for con in equations:
            unsat = True
            for eq in con:
                q = AutSingleSEQuery(eq, aut_constraints)
                if not q.unsat_check() and not q.unsat_pattern(literals):
                    unsat = False
                    break
            if unsat:
                return True
        return False


    @staticmethod
    def get_eqs_graph_ring(equations: Sequence[Sequence[StringEquation]]) -> "StringEqGraph":
        """!
        Get graph of equations. Each node is an equation. We distinguish L=R and
        R=L. Two equations are adjacent if they share a variable.

        @param equations: Sequence of string equations representing a conjunction of equations
        @return String Equation Graph
        """

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        eqs = []

        for clause in equations:
            cl = []
            assert(len(clause) == 1)
            for eq in clause:
                cl.append(eq.switched)
                cl.append(eq)
            eqs += cl

        nodes = { eq: StringEqNode([], StringConstraint(ConstraintType.TRUE), eq, 0) for eq in eqs }
        all_nodes = [ nodes[eq] for eq in eqs]

        for i in range(len(eqs)-1):
            nodes[eqs[i]].succ.append(nodes[eqs[i+1]])
            fl = StringConstraint(ConstraintType.EQ, eqs[i+1])
            nodes[eqs[i]].eval_formula = fl

        nodes[eqs[len(eqs)-1]].eval_formula = StringConstraint(ConstraintType.EQ, eqs[0])
        nodes[eqs[len(eqs)-1]].succ.append(nodes[eqs[0]])

        return StringEqGraph(all_nodes, [nodes[eqs[-1]]], list(nodes.values()))


    @staticmethod
    def get_eqs_graph_quick_sat(equations: Sequence[Sequence[StringEquation]]) -> "StringEqGraph":
        """!
        Get graph of equations suitable for quick satisfiability checking. Underapproximates
        the behaviour (If the noodler says sat, it is indeed sat. If unsat it is not conclusive).

        @param equations: Sequence of string equations representing a conjunction of equations
        @return String Equation Graph
        """

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        eqs = []

        for clause in equations:
            cl = []
            assert(len(clause) == 1)

            for eq in clause:
                eqp = eq
                if len(eq.get_side("right")) == 1:
                    eqp = eq.switched
                eqs.append(eqp)

        nodes = { eq: StringEqNode([], StringConstraint(ConstraintType.TRUE), eq, 0) for eq in eqs }
        all_nodes = [ nodes[eq] for eq in eqs]

        for eq in eqs:
            # nodes[eq.switched] = StringEqNode([nodes[eq]], StringConstraint(ConstraintType.TRUE), eq.switched, 0)
            # all_nodes.append(nodes[eq.switched])
            # nodes[eq].succ.append(nodes[eq.switched])

            for eq_target in eqs:
                if eq == eq_target:
                    continue
                if len(eq.get_vars_side("left") & eq_target.get_vars()) != 0 or len(eq.get_vars_side("right") & eq_target.get_vars_side("right")) != 0:
                    nodes[eq].succ.append(nodes[eq_target])
                    nodes[eq_target].eval_formula = StringConstraint(ConstraintType.AND, nodes[eq_target].eval_formula, StringConstraint(ConstraintType.EQ,eq))

        return StringEqGraph(all_nodes, list(nodes.values()), list(nodes.values()))


    @staticmethod
    def get_eqs_graph(equations: Sequence[Sequence[StringEquation]]) -> "StringEqGraph":
        """!
        Get graph of equations. Each node is an equation. We distinguish L=R and
        R=L. Two equations are adjacent if they share a variable.

        @param equations: Sequence of string equations representing a conjunction of equations
        @return String Equation Graph
        """

        def join_succ(eqs_sw, eqs_lst, nodes):
            for i in range(len(eqs_sw)-1):
                for eq_prev in eqs_sw[i]:
                    fl_clause = []
                    for eq_succ in eqs_lst[i+1]:
                        nodes[eq_prev].succ.append(nodes[eq_succ])
                        nodes[eq_prev].succ.append(nodes[eq_succ.switched])
                        fl = StringConstraint(ConstraintType.AND, StringConstraint(ConstraintType.EQ, eq_succ), StringConstraint(ConstraintType.EQ, eq_succ.switched))
                        fl_clause.append(fl)

                    if len(fl_clause) > 0:
                        nodes[eq_prev].eval_formula = StringConstraint(ConstraintType.AND, nodes[eq_prev].eval_formula, StringConstraint.build_op(ConstraintType.OR, fl_clause))

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        eqs_switch = []
        eqs = []

        for clause in equations:
            cl = []
            for eq in clause:
                cl.append(eq)
                cl.append(eq.switched)
            eqs += cl
            eqs_switch.append(cl)

        nodes = { eq: StringEqNode([], StringConstraint(ConstraintType.TRUE), eq, 0) for eq in eqs }
        all_nodes = [ nodes[eq] for eq in eqs]

        for eq in eqs:
            nodes[eq].succ.append(nodes[eq.switched])
            nodes[eq].eval_formula = StringConstraint(ConstraintType.EQ, eq.switched)

        join_succ(eqs_switch, equations, nodes)
        eqs_switch.reverse()
        equations.reverse()
        join_succ(eqs_switch, equations, nodes)

        return StringEqGraph(all_nodes, list(nodes.values()), list(nodes.values()))


    @staticmethod
    def check_length_compatible(cnf: Sequence[Sequence[StringEquation]], auts) -> bool:
        """!
        Check length-compatibility. Convert a system of string equations into a system of
        linear equations s.t. if the linear system is unsat, so are the string equations.
        """
        vars = {}
        formula = []
        for clause in cnf:
            f_or = []
            for eq in clause:
                for v in eq.get_vars():
                    aut = auts[v].trim()
                    if len(aut.states()) - 1 == len(aut.transitions()):
                        vars[v] = len(aut.transitions())
                    else:
                        vars[v] = z3.Int(v)
                f_or.append(z3.Sum([ vars[v] for v in eq.get_side("left")]) == z3.Sum([ vars[v] for v in eq.get_side("right")]) )
            formula.append(z3.Or(f_or))

        formula += [v >= 0 for _,v in vars.items()]

        s = z3.Solver()
        s.add(formula)
        return s.check() == z3.sat


    @staticmethod
    def get_conj_graphs_succ(equations: Sequence[Sequence[StringEquation]]) -> Sequence["StringEqGraph"]:
        """!
        Get a list of independent graphs (ring topology) (variables do not affecting each other).

        @param equations: Sequence of string equations representing a conjunction of equations
        @return String Equation Graph
        """

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        eqs = []

        for clause in equations:
            cl = []
            assert(len(clause) == 1)
            for eq in clause:
                cl.append(eq)
            eqs += cl

        nodes = { eq: StringEqNode([], StringConstraint(ConstraintType.TRUE), eq, 0) for eq in eqs }
        all_nodes = [ nodes[eq] for eq in eqs]

        for eq in eqs:
            for eq_dst in eqs:
                if len(eq.get_vars() & eq_dst.get_vars()) != 0:
                    nodes[eq].succ.append(nodes[eq_dst])
                    nodes[eq_dst].succ.append(nodes[eq])

        graph = StringEqGraph(all_nodes, list(nodes.values()), list(nodes.values()))
        sccs = graph.get_sccs()

        ret = []
        for scc in sccs:
            cnf = [[node.eq] for node in scc]
            if len(cnf) == 0:
                continue
            ret.append(StringEqGraph.get_eqs_graph_ring(cnf))

        return ret


    def get_inclusion_graph(equations: Sequence[Sequence[StringEquation]]):
        """
        Get inclusion graph of the conjunction of string constraints.
        """

        nodes: Dict[StringEquation, StringEqNode] = dict()
        all_nodes = []
        eqs = set()

        for clause in equations:
            cl = set()
            assert(len(clause) == 1)
            for eq in clause:
                cl.add(eq)
                cl.add(eq.switched)
            eqs = eqs | cl

        if len(eqs) == 0:
            return StringEqGraph([], [], [])

        nodes = { eq: StringEqNode([], StringConstraint(ConstraintType.TRUE), eq, 0) for eq in eqs }
        all_nodes = [ nodes[eq] for eq in eqs]
        prev_eq = defaultdict(lambda: set())

        for eq in eqs:
            for eq_dst in eqs:
                if eq.switched == eq_dst and (len(eq.get_vars_side("left") & eq.get_vars_side("right")) == 0 and not eq.more_occur_side("right")):
                    continue

                if len(eq.get_vars_side("left") & eq_dst.get_vars_side("right")) != 0:
                    nodes[eq_dst].succ.append(nodes[eq])
                    prev_eq[eq].add(eq_dst)

        
        graph = StringEqGraph(all_nodes, list(nodes.values()), list(nodes.values()))
        if not graph.is_acyclic():
            return StringEqGraph.get_eqs_graph_ring(equations)

        chain_free = []
        empty = deque([eq for eq in eqs if len(nodes[eq].succ) == 0])

        while len(empty) > 0:
            eq = empty.popleft()

            if eq.switched not in chain_free:
                chain_free.append(eq)

            for prev in prev_eq[eq]:
                nodes[prev].succ.remove(nodes[eq])
                if len(nodes[prev].succ) == 0:
                    empty.append(prev)

        rights = []
        for eq in chain_free:
            rights.extend(eq.get_side("right"))
        assert(not StringEquation([], rights).more_occur_side("right"))

        for i in range(len(chain_free) - 1):
            nodes[chain_free[i]].succ = [nodes[chain_free[i+1]]]
            nodes[chain_free[i]].eval_formula = StringConstraint(ConstraintType.EQ, chain_free[i+1])

        graph = StringEqGraph([ nodes[eq] for eq in chain_free], [nodes[chain_free[0]]], [nodes[chain_free[-1]]])
        return graph
