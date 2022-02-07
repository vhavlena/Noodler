import awalipy
import itertools

from collections import deque, defaultdict
from typing import Sequence, Optional, List, Dict, Set

# Classes
from .core import StringEquation, compare_aut_constraints
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery
# Types
from .core import Aut, AutConstraints, SegAut

from .graph_formula import StringEqNode, StringEqGraph
from .algos import eps_preserving_product, eps_segmentation, multiop, single_final_init, split_segment_aut
from .noodler import noodlify, noodlify_query, create_unified_query, is_unified, SimpleNoodler


class GraphNoodler:

    def __init__(self, vert: StringEqGraph, ini_constr: AutConstraints):
        """!
        Create a new Graph noodler
        """
        self.aut_constr = ini_constr
        self.graph = vert


    def is_graph_stable(self, constr: AutConstraints, straight_line: bool):
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


        if straight_line:
            return all(len(v.useful_states()) > 0 for k, v in constr.items())


        for v in self.graph.vertices:
            aux = AutSingleSEQuery(v.eq, constr)
            sat[v.eq] = aux.is_sub_balanced()

        _check_sat()
        for ini in self.graph.initials:
            if sat[ini.eq]:
                return True
        return False


    def is_sat(self, is_sl: bool):
        """!
        Check whether the string constraint is satisfiable

        @param is_sl: Is the constraint in straight-line fragment?
        @return True: Satisfiable, otherwise False
        """

        if len(self.graph.vertices) == 0:
            return self.is_graph_stable(self.aut_constr, is_sl)

        cache: Dict[StringEquation, Sequence[AutConstraints]] = defaultdict(lambda: [])
        fin_eq = { c.eq for c in self.graph.finals }

        Q = deque([])
        for node in self.graph.initials:
            Q.append((node, self.aut_constr))

        while len(Q) > 0:
            node, query = Q.popleft()

            # if any(compare_aut_constraints(query, i) for i in cache[node.eq]):
            #     continue
            # cache[node.eq].append(query)

            cur_query = AutSingleSEQuery(node.eq, query)

            noodler = SimpleNoodler(cur_query)
            noodles: Sequence[SingleSEQuery] = noodler.noodlify()

            for noodle in noodles:
                cur_constraints: AutConstraints = query.copy()
                cur_constraints.update(noodle.constraints)

                if node.eq in fin_eq and self.is_graph_stable(cur_constraints, is_sl):
                   return True

                for s in node.succ:
                    Q.append((s, cur_constraints))

        return False
