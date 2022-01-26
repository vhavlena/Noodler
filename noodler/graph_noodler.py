import awalipy
import itertools

from collections import deque
from typing import Sequence, Optional, List

# Classes
from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery
# Types
from .core import Aut, AutConstraints, SegAut

from .formula import StringEqNode
from .algos import eps_preserving_product, eps_segmentation, multiop, single_final_init, split_segment_aut
from .noodler import noodlify, noodlify_query, create_unified_query, is_unified


class GraphNoodler:

    def __init__(self, start: StringEqNode, ini_constr: AutConstraints):
        """!
        Create a new Graph noodler
        """
        self.aut_constr = ini_constr
        self.start_node = start


    def is_graph_stable(self, constr: AutConstraints):
        """!
        Is a graph of string equations stable (=each node is stable)?

        @param constr: Automata constraint of each variable
        @return stability
        """

        Q = deque([self.start_node])
        visited = set()

        while len(Q) > 0:
            node = Q.popleft()
            visited.insert(node)

            aux = AutSingleSEQuery(node.eq, constr)
            if not aux.is_balanced():
                return False

            for s in node.succ:
                if not s.eq in visited:
                    Q.append(s)

        return True


    def is_sat(self):
        Q = deque([(self.start_node, self.aut_const)])

        while len(Q) > 0:

            node, query = self.Q.popleft()
            if self.is_graph_stable(query):
                return True

            cur_query = AutSingleSEQuery(node.eq, query)

            noodler = SimpleNoodler(cur_query)
            noodles: Sequence[SingleSEQuery] = noodler.noodlify()

            for noodle in noodles:
                cur_constraints: AutConstraints = query.copy()
                cur_constraints.update(noodle.constraints)

                for s in node.succ:
                    Q.append((s, cur_constraints))
        return False
