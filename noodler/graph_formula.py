
from typing import Dict, Type, Union, Sequence, Set
from enum import Enum
from dataclasses import dataclass
from collections import defaultdict

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery
from .formula import StringConstraint, ConstraintType

import itertools
import copy
import awalipy


@dataclass
class StringEqNode:
    """!
    Node with an equation
    """
    succ : Sequence["StringEqNode"]
    eval_formula : StringConstraint
    eq : StringEquation
    id : int

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
                    if c <= max([var_order[x] for x in v.eq.get_vars_side("right")]):
                        return None
                    c += 1
                    eqs.add(v.eq)
            else:
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


    @staticmethod
    def reduce_regular_eqs(equations: Sequence[Sequence[StringEquation]], aut_constraints) -> Sequence[Sequence[StringEquation]]:
        """!
        Remove nodes from CNF that can be reduced to a regular constraint.
        Implemented as a fixpoint evaluation.

        @equations: CNF list of the formula
        @param aut_constraints: Automata constraints to be updated
        @return Reduced CNF list with updated automata constraints
        """

        def _get_other_vars(eqs):
            other_vars: dict[int, Set[str]] = defaultdict(lambda: set())

            lit = set()
            for var, aut in aut_constraints.items():
                aut = aut.trim()
                if len(aut.states()) - 1 == len(aut.transitions()):
                    lit.add(var)

            vars: dict[int, Set[str]] = dict()
            for i in range(len(eqs)):
                vars[i] = set().union(*[c.get_vars() for c in eqs[i]])
                vars[i] = vars[i] - lit
            for i in range(len(eqs)):
                other_vars[i] = set().union(*[vars[l] for l in range(len(eqs)) if l != i])

            return other_vars


        def _new_var(var_cnt):
            return "_reg_var{0}".format(var_cnt)


        def _remove_unique_vars(eqs):
            other_vars = _get_other_vars(eqs)
            var_cnt = 0

            modif = []
            for i in range(len(eqs)):
                modif.append([])
                for eq in eqs[i]:
                    if (len(other_vars[i] & eq.get_vars_side("right")) == 0) and (len(eq.get_vars_side("left") & eq.get_vars_side("right")) == 0):
                        right = eq.get_vars_side("right")
                        q = AutSingleSEQuery(eq, aut_constraints)
                        aut = q.automaton_for_side("right")
                        for v in right:
                            aut_constraints.pop(v, None)

                        new_var = _new_var(var_cnt)
                        var_cnt += 1
                        aut_constraints[new_var] = aut
                        modif[i].append(StringEquation(eq.get_side("left"), [new_var]))
                    else:
                        modif[i].append(eq)
            return modif


        def _remove_reg_iter(eqs):
            other_vars = _get_other_vars(eqs)

            modif = []
            for i in range(len(eqs)):

                if len(eqs[i]) == 0:
                    continue

                eq = eqs[i][0]
                cond_left = lambda x: (x.get_side("left") == eq.get_side("left")) and len(x.get_side("left")) == 1 and\
                    (not x.more_occur_side("right")) and len(other_vars[i] & x.get_vars_side("right")) == 0 and \
                    len(x.get_vars_side("left") & x.get_vars_side("right")) == 0
                cond_right = lambda x: x.get_side("right") == eq.get_side("right") and len(x.get_side("right")) == 1 and\
                    (not x.more_occur_side("left")) and len(other_vars[i] & x.get_vars_side("left")) == 0 and \
                    len(x.get_vars_side("left") & x.get_vars_side("right")) == 0

                s1, s2 = None, None
                if all(cond_left(x) for x in eqs[i]):
                    s1, s2 = "left", "right"
                elif all(cond_right(x) for x in eqs[i]):
                    s1, s2 = "right", "left"
                else:
                    modif.append(eqs[i])
                    continue

                aut = None
                for eq in eqs[i]:
                    var = eq.get_side(s1)[0]
                    q = AutSingleSEQuery(eq, aut_constraints)

                    if aut is None:
                        aut = q.automaton_for_side(s2)
                    else:
                        aut = awalipy.sum(q.automaton_for_side(s2), aut).proper().trim()
                aut_constraints[var] = awalipy.product(aut, aut_constraints[var]).proper().trim()

            return modif


        equations = _remove_unique_vars(equations)
        b, a = 0, len(equations)
        eq_new = equations
        while b - a != 0:
            b = a
            eq_new = _remove_reg_iter(eq_new)
            a = len(eq_new)

        return eq_new


    @staticmethod
    def reduce_common_sub(equations: Sequence[Sequence[StringEquation]], aut_constraints) -> Sequence[Sequence[StringEquation]]:

        def _replace_side(find, replace, side):
            ret = []
            i = 0
            while i < len(side):
                if find[0] == side[i] and side[i:i+len(find)] == list(find):
                    ret += list(replace)
                    i += len(find)
                else:
                    ret.append(side[i])
                    i += 1

            return ret


        def _update_str(succ, side):
            for i in range(len(side)-1):

                aut = aut_constraints[side[i]].trim()
                if len(aut.states()) - 1 == len(aut.transitions()):
                    continue

                succ[side[i]].add(side[i+1])
            succ[side[-1]].add("")

        succ: Dict[str, Set[str]] = defaultdict(lambda: set())
        for eqs in equations:

            assert(len(eqs) == 1)

            eq = eqs[0]
            _update_str(succ, eq.get_side("left"))
            _update_str(succ, eq.get_side("right"))


        sublst: Dict[Tuple[str], int] = defaultdict(lambda: 0)
        for eqs in equations:
            eq = eqs[0]
            add = []
            for var in eq.get_side("left") + eq.get_side("right"):
                if len(succ[var]) <= 1 and not "" in succ[var]:
                    add.append(var)
                if len(add) > 0 and (len(succ[var]) > 1 or "" in succ[var]):
                    add.append(var)
                    sublst[tuple(add)] += 1
                    add = []

        sl: Dict[Tuple[str], int] = defaultdict(lambda: 0)
        for sub, cnt in sublst.items():
            sl[sub] = cnt
            for sub2, cnt2 in sublst.items():
                if sub == sub2:
                    continue
                if set(sub) <= set(sub2):
                    sl[sub] += cnt2


        eqprime = []
        replace = [ k for k, v in sl.items() if v >= 2]
        replace_map = dict()
        for i in range(len(replace)):
            var = "_sub_var_{0}".format(i)
            replace_map[replace[i]] = [var]
            eqprime.append([StringEquation([var], list(replace[i]))])

        for eqs in equations:
            eq = eqs[0]

            l_side = eq.get_side("left")
            r_side = eq.get_side("right")
            for k,v in replace_map.items():
                l_side = _replace_side(k, v, l_side)
                r_side = _replace_side(k, v, r_side)
            eqprime.append([StringEquation(l_side, r_side)])

        #TODO: modify automata constraints

        return []




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
                cl.append(eq)
                cl.append(eq.switched)
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
