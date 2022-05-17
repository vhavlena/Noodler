
from typing import Dict, Type, Union, Sequence, Set, Optional
from enum import Enum
from dataclasses import dataclass
from collections import defaultdict

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



    def simplify_unique_light(equations: Sequence[Sequence[StringEquation]], aut_constraints, minimize: bool) -> Sequence[Sequence[StringEquation]]:

        def get_vars_count(eqs):
            vars_count =  defaultdict(lambda: 0)

            for clause in eqs:
                for eq in clause:
                    for v in eq.get_vars():
                        vars_count[v] += 1
            return vars_count


        def remove_eq(var, eq, side):
            q = AutSingleSEQuery(eq, aut_constraints)
            aut = q.automaton_for_side(side).trim() if not minimize else q.automaton_for_side(side).proper().minimal_automaton().trim()
            prod = awalipy.product(aut, aut_constraints[var]).proper().trim()
            if prod.num_states() != 0:
                prod = prod.trim() if not minimize else prod.minimal_automaton().trim()
            aut_constraints[var] = prod


        vars_cnt = get_vars_count(equations)
        rem = set()
        a = None
        while len(rem) != a:
            a = len(rem)

            modif = []
            for clause in equations:
                assert(len(clause) == 1)
                eq = clause[0]

                if len(eq.get_side("left")) == 1 and all(vars_cnt[x] == 1 for x in eq.get_vars_side("right")):
                    remove_eq(eq.get_side("left")[0], eq, "right")
                    rem.add(eq)
                    for v in eq.get_vars():
                        vars_cnt[v] -= 1
                else:
                    modif.append([eq])

            equations = modif

        return equations




    @staticmethod
    def reduce_regular_eqs(equations: Sequence[Sequence[StringEquation]], aut_constraints, minimize: bool) -> Sequence[Sequence[StringEquation]]:
        """!
        Remove nodes from CNF that can be reduced to a regular constraint.
        Implemented as a fixpoint evaluation.

        @equations: CNF list of the formula
        @param aut_constraints: Automata constraints to be updated
        @return Reduced CNF list with updated automata constraints
        """

        global var_cnt
        var_cnt = 0

        def _get_other_vars(eqs):
            other_vars: dict[int, Set[str]] = defaultdict(lambda: set())

            lit = set()
            for var, aut in aut_constraints.items():
                aut = aut.trim()
                if len(aut.states()) - 1 == len(aut.transitions()):
                    lit.add(var)

            vars: dict[StringEquation, Set[str]] = dict()
            all_eq = [eq for t in eqs for eq in t]
            for eq in all_eq:
                vars[eq] = eq.get_vars() - lit #set().union(*[c.get_vars() for c in eqs[i]])
                #vars[eq] = vars[eq] - lit
            for eq in all_eq:
                other_vars[eq] = set().union(*[vars[l] for l in all_eq if l != eq])

            return other_vars, lit


        def _new_var():
            global var_cnt
            var_cnt += 1
            return "_reg_var{0}".format(var_cnt)

        def _remove_unique_vars_side(eq, lit, side1, side2, modif, check_sub):
            right = eq.get_vars_side(side1)
            q = AutSingleSEQuery(eq, aut_constraints)
            aut = q.automaton_for_side(side1)
            for v in right - lit:
                aut_constraints.pop(v, None)

            new_var = _new_var()
            aut_constraints[new_var] = aut
            aut_side = q.automaton_for_side(side2)

            if check_sub:
                comp = aut.proper().minimal_automaton().complement()
                tmp = aut_side.product(comp).trim()
                if len(tmp.useful_states()) != 0:
                    modif.append(StringEquation(eq.get_side(side2), [new_var]))
            else:
                modif.append(StringEquation(eq.get_side(side2), [new_var]))


        def _remove_unique_vars(eqs):
            other_vars, lit = _get_other_vars(eqs)

            modif = []
            for i in range(len(eqs)):
                modif.append([])
                for eq in eqs[i]:

                    side1, side2 = "right", "left"
                    if (len(other_vars[eq] & eq.get_vars_side(side1)) == 0) and (len(eq.get_vars_side(side2) & eq.get_vars_side(side1)) == 0):
                        _remove_unique_vars_side(eq, lit, side1, side2, modif[i], len(eqs[i])==1)
                    elif (len(other_vars[eq] & eq.get_vars_side(side2)) == 0) and (len(eq.get_vars_side(side1) & eq.get_vars_side(side2)) == 0):
                        _remove_unique_vars_side(eq, lit, side2, side1, modif[i],len(eqs[i])==1)
                    else:
                        modif[i].append(eq)
            return modif


        def _remove_reg_iter(eqs):
            other_vars, _ = _get_other_vars(eqs)

            modif = []
            for i in range(len(eqs)):

                if len(eqs[i]) == 0:
                    continue

                eq = eqs[i][0]
                cond_left = lambda x: (x.get_side("left") == eq.get_side("left")) and len(x.get_side("left")) == 1 and\
                    (not x.more_occur_side("right")) and len(other_vars[x] & x.get_vars_side("right")) == 0 and \
                    len(x.get_vars_side("left") & x.get_vars_side("right")) == 0
                cond_right = lambda x: x.get_side("right") == eq.get_side("right") and len(x.get_side("right")) == 1 and\
                    (not x.more_occur_side("left")) and len(other_vars[x] & x.get_vars_side("left")) == 0 and \
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
                        aut = q.automaton_for_side(s2).trim() if not minimize else q.automaton_for_side(s2).proper().minimal_automaton().trim()
                    else:
                        aut = awalipy.sum(q.automaton_for_side(s2), aut).proper().trim() if not minimize else  awalipy.sum(q.automaton_for_side(s2), aut).proper().minimal_automaton().trim()
                prod = awalipy.product(aut, aut_constraints[var]).proper().trim()
                if prod.num_states() != 0:
                    prod = prod.trim() if not minimize else prod.minimal_automaton().trim()
                aut_constraints[var] = prod

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
    def remove_extension(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints, scq: StringConstraintQuery):

        occur = defaultdict(lambda: 0)
        vars = set()
        begin_map = defaultdict(lambda: [])
        end_map = defaultdict(lambda: [])
        begin_star_vars = set()
        end_star_vars = set()

        for con in equations:
            assert(len(con) == 1)
            for v in con[0].get_vars():
                occur[v] += 1
            vars = vars | con[0].get_vars()

        for v in vars:
            star = scq.sigma_star_aut()
            star = star.concatenate(aut_constraints[v]).proper().trim()
            if awalipy.are_equivalent(star, aut_constraints[v]):
                begin_star_vars.add(v)
            star = scq.sigma_star_aut()
            star = aut_constraints[v].concatenate(star).proper().trim()
            if awalipy.are_equivalent(star, aut_constraints[v]):
                end_star_vars.add(v)

        for con in equations:
            assert(len(con) == 1)
            eq = con[0]

            if len(eq.get_side("left")) == 1:
                v = eq.get_side("left")[0]
                r = eq.get_side("right")
                if len(r) > 1 and r[1] in begin_star_vars and occur[r[1]] == 1:
                    begin_map[r[0]].append(v)
                if len(r) > 1 and r[-2] in end_star_vars and occur[r[-2]] == 1:
                    end_map[r[-1]].append(v)

        remove_beg = set()
        remove_end = set()
        for k, v in begin_map.items():
            if occur[k] == len(v) and len(set(v)) == 1:
                remove_beg.add((v[0], k))
        for k, v in end_map.items():
            if occur[k] == len(v) and len(set(v)) == 1:
                remove_end.add((v[0], k))

        eqs = []
        for con in equations:
            eq = copy.copy(con[0])
            for l, r in remove_beg:
                if eq.get_side("left") == [l] and eq.get_side("right")[0] == r and len(eq.get_side("right")) > 1:
                    eq = StringEquation(eq.get_side("left"), eq.get_side("right")[1:])
                    break
            for l, r in remove_end:
                if eq.get_side("left") == [l] and eq.get_side("right")[-1] == r and len(eq.get_side("right")) > 1:
                    eq = StringEquation(eq.get_side("left"), eq.get_side("right")[0:-1])
                    break
            eqs.append([eq])

        return eqs


    @staticmethod
    def propagate_variables(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints, scq: StringConstraintQuery):

        def _remove_id(equations, free_vars):
            replace = dict()
            def_eqs = []
            for con in equations:
                eq = copy.copy(con[0])
                if len(eq.get_side("left")) == 1 and len(eq.get_side("right")) == 1:
                    l = eq.get_side("left")[0]
                    r = eq.get_side("right")[0]
                    if r in free_vars:
                        replace[r] = l
                        break
                    elif l in free_vars:
                        replace[l] = r
                        break

            eqs = []
            eq_set = set()
            for con in equations:
                eq = con[0]
                eq = eq.replace(replace)
                if eq.get_side("left") == eq.get_side("right"):
                    continue
                if eq not in eq_set:
                    eqs.append([eq])
                    eq_set.add(eq)
            return eqs

        vars = set()
        free_vars = set()
        for con in equations:
            assert(len(con) == 1)
            vars = vars | con[0].get_vars()

        for v in vars:
            star = scq.sigma_star_aut()
            if awalipy.are_equivalent(star, aut_constraints[v]):
                free_vars.add(v)

        prev = equations
        next = _remove_id(prev, free_vars)
        while prev != next:
            prev = next
            next = _remove_id(prev, free_vars)

        return next


    @staticmethod
    def generate_identities(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints, scq: StringConstraintQuery):
        eqs = []
        for con in equations:
            assert(len(con) == 1)
            eq = con[0]

            for con2 in equations:
                eq2 = con2[0]
                if eq == eq2:
                    continue

                rem1, rem2 = eq.get_side("right"), eq2.get_side("right")
                if eq.get_side("left") == eq2.get_side("left") and eq.get_side("right")[0] == eq2.get_side("right")[0]:
                    rem1 = rem1[1:]
                    rem2 = rem2[1:]

                if eq.get_side("left") == eq2.get_side("left") and eq.get_side("right")[-1] == eq2.get_side("right")[-1]:
                    rem1 = rem1[0:-1]
                    rem2 = rem2[0:-1]

                if len(rem1) == 1 and len(rem2) == 1 and rem1 != eq.get_side("right"):
                    eqs.append([StringEquation(rem1, rem2)])

            eqs.append([eq])
        return eqs


    @staticmethod
    def quick_unsat_check(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints):
        for con in equations:
            unsat = True
            for eq in con:
                q = AutSingleSEQuery(eq, aut_constraints)
                if not q.unsat_check():
                    unsat = False
                    break
            if unsat:
                return True
        return False



    @staticmethod
    def propagate_eps(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints, scq: StringConstraintQuery):

        def _is_eps(var, aut):
            aut = aut.proper().minimal_automaton().trim()
            return len(aut.transitions()) == 0

        vars = set()
        for con in equations:
            assert(len(con) == 1)
            vars = vars | con[0].get_vars()

        eps = set()

        aut_eps = None
        for v in vars:
            if _is_eps(v, aut_constraints[v]):
                eps.add(v)
                aut_eps = aut_constraints[v]

        eps_prev = set()
        while eps_prev != eps:
            eps_prev = eps
            for con in equations:
                assert(len(con) == 1)
                eq = con[0]
                if all(v in eps for v in eq.get_side("left")):
                    eps = eps | eq.get_vars_side("right")
                if all(v in eps for v in eq.get_side("right")):
                    eps = eps | eq.get_vars_side("left")

        eqs = []
        for con in equations:
            eq = con[0]
            eq = eq.remove(eps)
            if eq.get_side("left") == eq.get_side("right"):
                continue
            eqs.append([eq])

        for var in eps:
            aut_constraints[var] = awalipy.product(aut_constraints[var], aut_eps)

        return eqs




    @staticmethod
    def reduce_common_sub(equations: Sequence[Sequence[StringEquation]], aut_constraints: AutConstraints) \
        -> (Sequence[Sequence[StringEquation]], AutConstraints):
        """
        Find common parts of each equation and replace them with a fresh equation
        replacing the common parts.

        @param equations: Equations without disjunctions
        @param aut_constraints: Regular constraints
        @return Pair of new equations together with modified regular constraints
        """

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

        for r, var in replace_map.items():
            aut_query = AutSingleSEQuery(StringEquation(list(r), list(r)), aut_constraints)
            aut = aut_query.automaton_for_side("left")
            aut_constraints[var[0]] = aut

        return (eqprime, aut_constraints)




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
                f_or.append(z3.Sum([ vars[v] for v in eq.get_vars_side("left")]) == z3.Sum([ vars[v] for v in eq.get_vars_side("right")]) )
            formula.append(z3.Or(f_or))

        formula += [v >= 0 for _,v in vars.items()]

        s = z3.Solver()
        s.add(formula)
        return s.check() == z3.sat
