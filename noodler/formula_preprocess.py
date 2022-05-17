
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


@dataclass(eq=True,frozen=True)
class VarNode:
    var: str
    eq: StringEquation
    pos: int



@dataclass
class EqNode:
    eq : StringEquation
    left: Sequence[VarNode]
    right: Sequence[VarNode]
    succ: Sequence["EqNode"]
    prev: Sequence["EqNode"]

    def __eq__(self, other):
        return self.eq == other.eq



class FormulaVarGraph:

    def __init__(self, cnf_eqs):
        self.edges = defaultdict(lambda: set())
        self.vertices = dict()

        for clause in cnf_eqs:
            for eq in clause:
                left = list(map(lambda x: VarNode(x[1],eq,-x[0]), enumerate(eq.get_side("left"))))
                right = list(map(lambda x: VarNode(x[1],eq,x[0]), enumerate(eq.get_side("right"))))
                node = EqNode(eq, left, right, [], [])
                self.vertices[eq] = node
                for varn in left + right:
                    self.edges[varn.var].add(varn)

        self.init = [self.vertices[eq] for eq in cnf_eqs[0]]
        for i in range(len(cnf_eqs) - 1):
            succ = []
            for eq in cnf_eqs[i+1]:
                succ.append(self.vertices[eq])
            for eq in cnf_eqs[i]:
                self.vertices[eq].succ = copy.copy(succ)
        for _, node in self.vertices.items():
            for sc in node.succ:
                sc.prev.append(node)


    def __str__(self):

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


    def __repr__(self):
        return str(self)

    def get_vars_count(self):
        v_cnt = dict()
        for k, v in self.edges.items():
            v_cnt[k] = len(v)
        return v_cnt


    def remove_node(self, node):
        for v in node.left + node.right:
            self.edges[v.var].remove(v)
        for pr in node.prev:
            pr.succ.remove(node)
        del self.vertices[node.eq]




class FormulaPreprocess(FormulaVarGraph):

    def __init__(self):
        pass
