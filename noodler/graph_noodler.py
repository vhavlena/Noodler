#import awalipy
import itertools
import mata

from collections import deque, defaultdict
from typing import Sequence, Optional, List, Dict, Set, Tuple
from dataclasses import dataclass
from enum import Enum

# Classes
from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery, compare_aut_constraints, compare_aut_constraints_str
# Types
from .core import Aut, AutConstraints, SegAut

from .graph_formula import StringEqNode, StringEqGraph
from .noodler import SimpleNoodler


class StrategyType(Enum):
    BFS = 1,
    DFS = 2


@dataclass
class GraphNoodlerSettings:
    balance_check : bool = True
    strategy : StrategyType = StrategyType.BFS
    use_cache : bool = False
    both_side : bool = False
    use_retrieval : bool = False
    prod_pruning : bool = False


class GraphNoodler:

    def __init__(self, vert: StringEqGraph, ini_constr: AutConstraints, lits: Set[str], uni: Set[str]):
        """!
        Create a new Graph noodler
        """
        self.aut_constr = ini_constr
        self.graph = vert
        self.literals = lits
        self.unique_vars = uni


    def is_graph_stable(self, constr: AutConstraints, balance_check: bool, both_side: bool):
        """!
        Is a graph of string equations stable (=each node is stable)?

        @param constr: Automata constraint of each variable
        @return stability
        """

        def _check_sat():
            changed = True
            while changed:
                changed = False
                for v in self.graph.vertices:
                    val = sat[v.eq]
                    if not val:
                        continue
                    sat[v.eq] = val and v.eval_formula.eval(sat)
                    if sat[v.eq] != val:
                        changed = True


        sat: Dict[StringEquation, bool] = dict()

        if not balance_check:
            return all(len(v.get_useful_states()) > 0 for k, v in constr.items()), None


        for v in self.graph.vertices:
            aux = AutSingleSEQuery(v.eq, constr)
            sat[v.eq] = aux.is_balanced() if both_side else aux.is_sub_balanced()


        failed = [ v for v in self.graph.vertices if not sat[v.eq] ]
        _check_sat()
        for ini in self.graph.initials:
            if not sat[ini.eq]:
                return False, failed
        return True, None


    def is_sat(self, sett : GraphNoodlerSettings):
        """!
        Check whether the string constraint is satisfiable

        @param is_sl: Is the constraint in straight-line fragment?
        @return True: Satisfiable, otherwise False
        """

        if len(self.graph.vertices) == 0:
            return self.is_graph_stable(self.aut_constr, sett.balance_check, sett.both_side)[0]

        for v, aut in self.aut_constr.items():
            if len(aut.get_useful_states()) == 0:
                return False

        cache: Dict[StringEquation, Sequence[AutConstraints]] = defaultdict(lambda: [])
        #cache_map = defaultdict(lambda: defaultdict(lambda: set()))
        fin_eq = { c.eq for c in self.graph.finals }

        Q = deque([])
        for node in self.graph.initials:
            Q.append((node, self.aut_constr))

        while len(Q) > 0:
            if sett.strategy == StrategyType.DFS:
                node, query = Q.pop()
            elif sett.strategy == StrategyType.BFS:
                node, query = Q.popleft()

            #query_str = { k:get_shortest_strings_bfs(v) for k, v in query.items() }
            cur_query = AutSingleSEQuery(node.eq, query)
            noodler = SimpleNoodler(cur_query)
            noodles: Sequence[SingleSEQuery] = noodler.noodlify()

            if len(noodles) > 1:
                distr, var = self._is_node_distributive(node.eq)
                if distr:
                    noodles = [SingleSEQuery(node.eq, constr) for constr in self._distribute_noodles(noodles, query, var)]

            for noodle in noodles:
                cur_constraints: AutConstraints = query.copy()
                cur_constraints.update(noodle.constraints)

                if sett.prod_pruning:
                    tmp = AutSingleSEQuery(node.eq, cur_constraints)
                    if tmp.has_empty_product():
                        continue

                if (node.eq in fin_eq):
                    st, failed = self.is_graph_stable(cur_constraints, sett.balance_check, sett.both_side)
                    if st:
                        return True
                    elif sett.use_retrieval and failed is not None:
                        for v in failed:
                            if sett.strategy == StrategyType.DFS:
                                Q.insert(0, (v, cur_constraints))
                            elif sett.strategy == StrategyType.BFS:
                                Q.append((v, cur_constraints))

                for s in node.succ:
                    Q.append((s, cur_constraints))

        return False


    def _distribute_noodles(self, noodles: Sequence[SingleSEQuery], query: AutConstraints, var: Optional[str]) -> Sequence[AutConstraints]:
        """!
        Distribute noodles. In the case a left side of the equation contains only
        one variable (the others are literals), the noodles corresponding to the
        variable are unified (automata union) to a single noodle.

        @param noodles: Original noodles
        @param query: Aut Constraint query of the current node
        @param var: Unified variable
        @return Sequence of AutConstraints
        """

        aut_union = None
        if var is None:
            return [query.copy()]
        for noodle in noodles:
            if aut_union is None:
                aut_union = noodle.constraints[var]
            else:
                aut_union = mata.Nfa.union(aut_union, noodle.constraints[var])
                aut_union.trim()
        if aut_union is None:
            return []

        aut_union = mata.Nfa.minimize(aut_union)
        aut_union.trim()
        cur_constraints: AutConstraints = query.copy()
        cur_constraints.update({var: aut_union})
        return [cur_constraints]


    def _check_node_vars(self, eq: StringEquation, vars_s: Set[str]) -> Tuple[bool, str]:
        """!
        Is a given equation distributive (=allows unification of noodles) wrt given set of variables?

        @param eq: StringEquation of the current node
        @param vars_s: Set of vars that should be ignored
        @return Pair: is node distributive, variable allowing unification
            (None if it does not exist)
        """
        vars = eq.get_vars_side("left") - vars_s
        if len(vars) > 1:
            return False, None
        if len(vars) == 0:
            return True, None

        var = list(vars)[0]
        return eq.get_side("left").count(var) == 1, var


    def _is_node_distributive(self, eq: StringEquation) -> Tuple[bool, str]:
        """!
        Is a given equation distributive (=allows unification of noodles)?

        @param eq: StringEquation of the current node
        @return Pair: is node distributive, variable allowing unification
            (None if it does not exist)
        """

        distr1, var1 = self._check_node_vars(eq, self.literals)
        distr2, var2 = self._check_node_vars(eq, self.unique_vars)

        if distr1:
            return distr1, var1
        elif distr2:
            return distr2, var2
        else:
            return False, None
