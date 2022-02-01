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


    def is_graph_stable(self, constr: AutConstraints):
        """!
        Is a graph of string equations stable (=each node is stable)?

        @param constr: Automata constraint of each variable
        @return stability
        """

        subset = self.graph.are_all_nontriv_sub()

        for v in self.graph.vertices:
            if len(v.succ) == 0:
                continue

            aux = AutSingleSEQuery(v.eq, constr)
            if (not subset) and (not aux.is_balanced()):
                return False
            if subset and (not aux.is_sub_balanced()):
                return False

        return True


    def is_sat(self):

        cache: Dict[StringEquation, Sequence[AutConstraints]] = defaultdict(lambda: [])

        Q = deque([])
        for node in self.graph.vertices:
            Q.append((node, self.aut_constr))

        while len(Q) > 0:

            node, query = Q.popleft()
            if self.is_graph_stable(query):
               return True

            if any(compare_aut_constraints(query, i) for i in cache[node.eq]):
                continue
            cache[node.eq].append(query)

            cur_query = AutSingleSEQuery(node.eq, query)

            noodler = SimpleNoodler(cur_query)
            noodles: Sequence[SingleSEQuery] = noodler.noodlify()

            for noodle in noodles:

                cur_constraints: AutConstraints = query.copy()
                cur_constraints.update(noodle.constraints)

                for s in node.succ:
                    Q.append((s, cur_constraints))



        for v in self.graph.vertices:
            print()
            print("---------------------------------------------------")
            print(v.eq)
            for c in cache[v.eq]:
                for var in v.eq.get_vars():
                    print(var, c[var])
            print()

        return False
