
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
        return self.index == other.index

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.index)

    def __str__(self):
        return str(self.index) + ": " + str(self.eq)

    def __repr__(self):
        return str(self)

    def is_simple_redundant(self) -> bool:
        return self.eq.get_side("left") == self.eq.get_side("right")



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
                left, right = self._create_node_sides(eq, i)
                node = EqNode(eq, left, right, set(), set(), i)
                self.vertices[i] = node
                indices_cl.append(i)
                i += 1
                for varn in left + right:
                    self.edges[varn.var].add(varn)
            indices_eq.append(indices_cl)

        self.init = {self.vertices[i] for i in indices_eq[0]}
        for i in range(len(indices_eq) - 1):
            succ = set()
            for eq in indices_eq[i+1]:
                succ.add(self.vertices[eq])
            for eq in indices_eq[i]:
                self.vertices[eq].succ = copy.copy(succ)
        for _, node in self.vertices.items():
            for sc in node.succ:
                sc.prev.add(node)


    def _create_node_sides(self, eq: StringEquation, index:int) -> tuple[Sequence[EqNode], Sequence[EqNode]]:
        """
        Create left and right side of EqNode for a given equation and index
        @param eq: Equation
        @param index: Index of the equation
        @return Initialized left, right
        """
        left = list(map(lambda x: VarNode(x[1],index,-x[0]), enumerate(eq.get_side("left"), 1)))
        right = list(map(lambda x: VarNode(x[1],index,x[0]), enumerate(eq.get_side("right"), 1)))
        return left, right


    def __str__(self) -> str:
        """
        Convert FormulaVarGraph to string
        """
        def print_list_node(lst):
            ret = ""
            add = ""
            for np in lst:
                ret += add + str(np.eq)
                add = " OR "
            return ret

        if len(self.init) == 0:
            return ""

        ret = print_list_node(self.init) + "\n"
        node = list(self.init)[0]
        while len(node.succ) > 0:
            ret += print_list_node(node.succ) + "\n"
            node = list(node.succ)[0]

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


    def update_eq(self, node: EqNode, eq: StringEquation):
        """
        Update equation of the given node
        @param node: Node to be updated
        @param eq: New equation
        """
        for v in node.left + node.right:
            self.edges[v.var].remove(v)
        node.left, node.right = self._create_node_sides(eq, node.index)
        for varn in node.left + node.right:
            self.edges[varn.var].add(varn)
        node.eq = eq


    def remove_node(self, node: EqNode):
        """
        Remove node (equation) from the formula
        @param node: Node to be removed
        """
        for v in node.left + node.right:
            self.edges[v.var].remove(v)
        for pr in node.prev:
            pr.succ.remove(node)
            pr.succ = pr.succ | node.succ
        for s in node.succ:
            s.prev.remove(node)
            s.prev = s.prev | node.prev

        if node in self.init:
            self.init.remove(node)
            self.init = self.init.union(node.succ)
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
            visited.add(node)
            if func(node):
                ret.add(node)
            nodes.extend(node.succ)
        return ret


    def map_equations(self, func: Callable):
        """
        Map equations in all nodes
        @param func: Equation transformer
        """
        self.edges = defaultdict(lambda: set())
        for _, node in self.vertices.items():
            node.eq = func(node.eq)
            node.left, node.right = self._create_node_sides(node.eq, node.index)
            for varn in node.left + node.right:
                self.edges[varn.var].add(varn)


    def get_side_regular_nodes(self) -> Set[EqNode]:
        """
        Get nodes whose equation form is X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula and |X| = 1
        """
        return self.filter_nodes(lambda x: self.is_node_side_regular(x) or self.is_node_regular_assignment(x))


    def is_node_regular_assignment(self, node: EqNode) -> bool:
        """
        Is given node a regular assignment? Equation of the form X = Y1 Y2 ...
        where X does not occur multiple time.
        @param node: Node
        @return Is node regular assignment?
        """
        return (len(node.left) == 1 and len(self.edges[node.left[0]]) <= 1) or\
            (len(node.right) == 1 and len(self.edges[node.right[0]]) <= 1)


    def is_node_side_regular(self, node: EqNode) -> bool:
        """
        Is the given node of the form X = X_1 X_2 X_3 where each X_i occurs at most
        once in the formula
        """
        return (all(len(self.edges[item.var]) <= 1 for item in node.left) and \
            len(node.eq.get_side("right")) == 1) or \
            (all(len(self.edges[item.var]) <= 1 for item in node.right) and \
            len(node.eq.get_side("left")) == 1)


    def is_clause_assignment(self, clause: Set[EqNode], side: str) -> bool:
        """
        Is the given clause of the form X = X_1 X_2 X_3 OR X = X_4 X_5 ...
        and X occurs in the side given by side.
        @param clause: Clause
        @param side: Side of the equation
        """
        lefts = { tuple(node.eq.get_side(side)) for node in clause }
        if len(lefts) > 1 or len(list(lefts)[0]) != 1:
            return False
        return True


    def _is_clause_regular_side(self, clause: Set[EqNode], lit: Set[str], side: str) -> bool:
        """
        Is the given clause of the form X = X_1 X_2 X_3 OR X = X_4 X_5 ... where each
        X_i occurs at most once in the formula and X occurs in the side given by side
        @param clause: Clause
        @param lit: Set of literals
        @param side: Side of the equation
        """
        lefts = { tuple(node.eq.get_side(side)) for node in clause }
        if len(lefts) > 1 or len(list(lefts)[0]) != 1:
            return False
        if side == "left":
            return all(self.is_seq_regular(cl.right, lit) for cl in clause)
        return all(self.is_seq_regular(cl.left, lit) for cl in clause)


    def is_clause_regular(self, clause: Set[EqNode], lit: Set[str]) -> bool:
        """
        Is the given clause of the form X = X_1 X_2 X_3 OR X = X_4 X_5 ... where each
        X_i occurs at most once in the formula
        @param clause: Clause
        @param lit: Set of literals
        """
        return self._is_clause_regular_side(clause, lit, "left") or\
            self._is_clause_regular_side(clause, lit, "right")


    def is_seq_regular(self, seq: Sequence[VarNode], lit: Set[str]) -> bool:
        """
        Is the given sequence of the form X_1 X_2 X_3 where each X_i occurs at most
        once in the formula (or it is a literal)
        """
        return all(len(self.edges[item.var]) <= 1 for item in seq if item.var not in lit)\
            and len(seq) == len(set(seq))


    def get_simple_nodes(self) -> Set[EqNode]:
        """
        Get all simple nodes of the form X = Y
        @return Set of simple nodes (X=Y)
        """
        return self.filter_nodes(lambda x: len(x.eq.get_side("left")) == 1 and len(x.eq.get_side("right")) == 1)


    def get_clause(self, node: EqNode) -> Set[EqNode]:
        """
        Get clause containing the given node
        @param node: Node
        @return Set of nodes representing a clause
        """
        clause = set()
        if not node.prev:
            return self.init
        for pr in node.prev:
            clause = clause | pr.succ
        return clause


    def get_variables_succ(self, lits: Set[str]) -> Dict[str, Set[str]]:
        """
        Get successors for each variable (except literals) occurring in every equation.
        @param lits: Literals
        @return Dictionary where a variable contains a set of variables that occur
        in some equation right after the variable. We use empty string to denote
        the variable is at the end of an equation.
        """

        ret = defaultdict(lambda: set())
        for _, eq in self.vertices.items():
            sides = [eq.eq.get_side("left"), eq.eq.get_side("right")]
            for side in sides:
                for i in range(len(side) - 1):
                    if side[i] in lits:
                        continue
                    ret[side[i]].add(side[i+1])
                ret[side[-1]].add("")
        return ret


    def get_minimal_unique_sublists(self, lits: Set[str]) -> Dict[tuple[str], int]:
        """
        Get minimal unique sublists occurring in the formula.
        @param lits: Set of literals
        @return Dictionary mapping each minimal sublist to the number of occurrences
        """

        var_succ = self.get_variables_succ(lits)
        sublst = defaultdict(lambda: 0)
        subset = set()
        ret = defaultdict(lambda: 0)

        for _, eq in self.vertices.items():
            sub = []
            for var in eq.eq.get_side("left") + eq.eq.get_side("right"):
                if len(var_succ[var]) <= 1 and not "" in var_succ[var]:
                    sub.append(var)
                if len(sub) > 0 and (len(var_succ[var]) > 1 or "" in var_succ[var]):
                    sub.append(var)
                    sublst[tuple(sub)] += 1
                    subset.add(frozenset(sub))
                    sub = []

        smallest = set()
        for item in subset:
            sm = { v for v in subset if v < item }
            if not sm:
                smallest.add(item)

        for sl1, cnt1 in sublst.items():
            if frozenset(sl1) not in smallest:
                continue
            ret[sl1] = cnt1
            for sl2, cnt2 in sublst.items():
                if sl1 == sl2:
                    continue
                if set(sl1) <= set(sl2):
                    ret[sl1] += cnt2

        return ret


    def _replace_side(self, find: Sequence[str], replace: Sequence[str], side: Sequence[str]) -> Sequence[str]:
        """
        Replace subsequences in a given equation side.
        @param find: Sequence to be found
        @param replace: Replacement
        @param side: Sequnce of variable representing an equation side.
        """

        ret = []
        i = 0
        while i < len(side):
            if find[0] == side[i] and side[i:i+len(find)] == find:
                ret += replace
                i += len(find)
            else:
                ret.append(side[i])
                i += 1

        return ret


    def _replace_eq(self, eq: StringEquation, replace: Dict[tuple[str], tuple[str]]) -> StringEquation:
        """
        Replace all subsequences in a given equation
        @param eq: Equation
        @param replace: Dictionary containing find -> replace
        @return Modified equation
        """

        left, right = eq.get_side("left"), eq.get_side("right")
        for k, v in replace.items():
            left = self._replace_side(list(k), list(v), left)
            right = self._replace_side(list(k), list(v), right)
        return StringEquation(left, right)


    def replace_eq_sublist(self, replace: Dict[tuple[str], tuple[str]]):
        """
        Replace all subsequences in all equations
        @param replace: Dictionary containing find -> replace
        """
        self.map_equations(lambda x: self._replace_eq(x, replace))


    def add_equation(self, index: int, eq: StringEquation, prev: EqNode) -> EqNode:
        """
        Add equation to the formula
        @param index: Index of the new equation
        @param eq: New equation
        @param prev: Previous node (as a successor it will contain the new equation node)
        @return New equation node
        """

        left, right = self._create_node_sides(eq, index)
        node = EqNode(eq, left, right, set(), set([prev]), index)
        prev.succ.add(node)

        for varn in node.left + node.right:
            self.edges[varn.var].add(varn)
        self.vertices[index] = node
        return node


    def get_last_node(self) -> Optional[EqNode]:
        """
        Get a node without successors (last node)
        @return Last node or None
        """
        for _, node in self.vertices.items():
            if len(node.succ) == 0:
                return node
        return None



    def is_conjunction(self) -> bool:
        """
        Is the formula disjuction-free?
        """
        nodes = self.init
        while len(nodes) > 0:
            if len(nodes) > 1:
                return False
            nodes = list(nodes)[0].succ
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

    def _get_init(self) -> Set[EqNode]:
        """
        Get all initial nodes
        """
        return self.init



class FormulaPreprocess(FormulaVarGraph):

    def __init__(self, cnf_eqs, aut_constr, minimize: bool):
        super().__init__(cnf_eqs)
        self.aut_constr = aut_constr
        self.var_cnt = 0
        self.minimize = minimize


    def __str__(self):
        """
        String representation
        """
        return super().__str__()

    def __repr__(self):
        """
        String representation
        """
        return str(self)


    def get_eps_vars(self) -> Set[str]:
        """
        Get variables whose language contains only epsilon
        @return Set of variables containig only epsilon
        """
        ret = set()

        for v, aut in self.aut_constr.items():
            if aut.num_states() == 0:
                continue
            aut = aut.proper().minimal_automaton().trim()
            if len(aut.transitions()) == 0:
                ret.add(v)
        return ret


    def get_literals(self) -> Set[str]:
        """
        Get literals
        """
        lit = set()
        for var, aut in self.aut_constr.items():
            if aut.num_states() == 0:
                continue
            aut = aut.trim()
            if len(aut.states()) - 1 == len(aut.transitions()) and aut.num_initials() == 1:
                lit.add(var)
        return lit


    def _get_new_var(self) -> str:
        """
        Create a fresh variable
        """
        self.var_cnt += 1
        return "_reg_var{0}".format(self.var_cnt)


    def remove_id(self, node: EqNode):
        """
        Remove node containig identity X = Y
        @param node: Node to be removed
        """
        assert(len(node.eq.get_side("left")) == 1 and len(node.eq.get_side("right")) == 1)

        var1 = node.eq.get_side("left")[0]
        var2 = node.eq.get_side("right")[0]

        prod = awalipy.product(self.aut_constr[var1], self.aut_constr[var2]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not self.minimize else prod.minimal_automaton().trim()
        self.aut_constr[var1] = prod
        self.aut_constr[var2] = prod
        super().remove_node(node)


    def remove_eq(self, node: EqNode, lits: Set[str]):
        """
        Remove given node representing an equation
        @param node: Node to be removed
        """

        self.remove_clause(set([node]), lits)
        #return
        #
        # side = None
        # if len(node.eq.get_side("left")) == 1:
        #     side = "right"
        # elif len(node.eq.get_side("right")) == 1:
        #     side = "left"
        # else:
        #     raise Exception("Equation cannot be removed")
        #
        # super().remove_node(node)
        # var = node.eq.get_side(side_opposite(side))[0]
        #
        # q = AutSingleSEQuery(node.eq, self.aut_constr)
        # side_aut = q.automaton_for_side(side)
        # if side_aut.num_states() == 0:
        #     aut = side_aut
        # else:
        #     aut = q.automaton_for_side(side).trim() if not self.minimize else q.automaton_for_side(side).proper().minimal_automaton().trim()
        # prod = awalipy.product(aut, self.aut_constr[var]).proper().trim()
        # if prod.num_states() != 0:
        #     prod = prod.trim() if not self.minimize else prod.minimal_automaton().trim()
        # self.aut_constr[var] = prod
        # if len(node.eq.get_side(side)) == 1:
        #     self.aut_constr[node.eq.get_side(side)[0]] = prod


    def remove_clause(self, clause: Set[EqNode], lits: Set[str]):
        """
        Remove given node representing an equation
        @param node: Node to be removed
        """

        side = None
        if self.is_clause_assignment(clause, "left"):  #len(node.eq.get_side("left")) == 1:
            side = "right"
        elif self.is_clause_assignment(clause, "right"):
            side = "left"
        else:
            raise Exception("Clause cannot be removed")


        var = list(clause)[0].eq.get_side(side_opposite(side))[0]
        aut_union = None
        for node in list(clause):
            super().remove_node(node)
            q = AutSingleSEQuery(node.eq, self.aut_constr)
            if self.minimize:
                side_aut = q.automaton_for_side_minimal(side)
            else:
                side_aut = q.automaton_for_side(side)
            if side_aut.num_states() == 0:
                aut = side_aut
            else:
                aut = q.automaton_for_side(side).trim() if not self.minimize else q.automaton_for_side_minimal(side).proper().minimal_automaton().trim()
            if aut_union is None:
                aut_union = aut
            else:
                aut_union = awalipy.sum(aut_union, aut).proper().trim()

        prod = awalipy.product(aut_union, self.aut_constr[var]).proper().trim()
        if prod.num_states() != 0:
            prod = prod.trim() if not self.minimize else prod.minimal_automaton().trim()
        self.aut_constr[var] = prod
        if len(clause) == 1 and len(list(clause)[0].eq.get_side(side)) == 1:
            self.aut_constr[list(clause)[0].eq.get_side(side)[0]] = prod


    def update_eq_regular_part(self, node: EqNode, new_var: str, remove_side: str, lits: Sequence[str]):
        """
        Update equation s.t. the regular side is replaced by a fresh variable.
        @param node: Node
        @param new_var: A fresh variable
        @param remove_side: Which side should be removed (left/right)
        @param lits: Set of literals
        """
        q = AutSingleSEQuery(node.eq, self.aut_constr)
        aut = q.automaton_for_side(remove_side)
        for v in node.eq.get_vars_side(remove_side) - lits:
            self.aut_constr.pop(v, None)
        self.aut_constr[new_var] = aut

        if remove_side == "left":
            super().update_eq(node, StringEquation([new_var], node.eq.get_side(side_opposite(remove_side))))
        else:
            super().update_eq(node, StringEquation(node.eq.get_side(side_opposite(remove_side)), [new_var]))


    def is_clause_subset_side(self, clause: Set[EqNode], side: str) -> bool:
        """
        Is clause of the form: X = R_1 OR X = R_2 OR ... where X does not occur
        anywhere else and L(X) >= L(R_i) and X occurs on side side. In that case,
        we can later remove this clause.
        @param clause: Clause
        @param side: Side of the equations in the clause
        """
        lefts = { tuple(node.eq.get_side(side)) for node in clause }

        if len(lefts) > 1 or len(list(lefts)[0]) != 1:
            return False
        left_var = list(lefts)[0][0]

        if len(super()._get_edges()[left_var]) != len(clause):
            return False

        aut_var = self.aut_constr[left_var].copy()
        for node in clause:
            q = AutSingleSEQuery(node.eq, self.aut_constr)
            aut = q.automaton_for_side(side_opposite(side)).proper()
            comp = aut_var.proper().minimal_automaton().complement()
            tmp = aut.product(comp).trim()
            if len(tmp.useful_states()) != 0:
                return False
        return True


    def is_clause_subset(self, clause: Set[EqNode]) -> bool:
        """
        Is clause of the form: X = R_1 OR X = R_2 OR ... where X does not occur
        anywhere else and L(X) >= L(R_i). In that case, we can later remove
        this clause.
        @param clause: Clause
        """
        return self.is_clause_subset_side(clause, "left") or self.is_clause_subset_side(clause, "right")


    def simplify_unique(self):
        """
        Simplify equations having unique variables on a side.
        """

        lits = self.get_literals()

        nodes = deque(super().get_side_regular_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()

            if not node.index in super()._get_vertices():
                continue

            clause = super().get_clause(node)
            if not super().is_clause_regular(clause, lits):
                if not self.is_clause_subset(clause):
                    continue

            vars = set().union(*[ node.eq.get_vars() for node in clause ])
            self.remove_clause(clause, lits)
            for v in vars:
                if len(super()._get_edges()[v]) == 1:
                    eq_ind = list(super()._get_edges()[v])[0].eq_index
                    nodes.append(super()._get_vertices()[eq_ind])


    def propagate_variables(self):
        """
        Propagate variables.
        """

        nodes = deque(super().get_simple_nodes())
        while len(nodes) > 0:
            node = nodes.popleft()

            if len(super().get_clause(node)) != 1:
                continue

            if node.is_simple_redundant():
                self.remove_eq(node, node.eq.get_vars())
                continue

            v_left = node.eq.get_side("left")[0]
            replace = { v_left: node.eq.get_side("right")[0] }
            self.remove_id(node)
            super().map_equations(lambda x: x.replace(replace))
        self.remove_duplicates()


    def propagate_eps(self):
        """
        Propagate variables whose language contains only epsilon
        """

        assert(super().is_conjunction())

        eps = self.get_eps_vars()
        visited = set()
        vert = super()._get_vertices()

        n_list = []
        aut_eps = None
        for v in eps:
            n_list.extend([vert[n.eq_index] for n in super()._get_edges()[v]])
            aut_eps = self.aut_constr[v] if aut_eps is None else aut_eps

        nodes = deque(n_list)
        while len(nodes) > 0:
            node = nodes.popleft()
            if node in visited:
                continue

            visited.add(node)
            add_var = set()
            if node.eq.get_vars_side("left") <= eps:
                add_var = node.eq.get_vars_side("right") - eps
            elif node.eq.get_vars_side("right") <= eps:
                add_var = node.eq.get_vars_side("left") - eps

            for v in add_var:
                nodes.extend([vert[n.eq_index] for n in super()._get_edges()[v]])
            eps = eps | add_var

        for var in eps:
            self.aut_constr[var] = awalipy.product(self.aut_constr[var], aut_eps)
        super().map_equations(lambda x: x.remove(eps))
        self.clean()


    def _replace_unique_side_fresh(self):
        """
        Replace equations with a regular side (all variables occurring at
        most once in the formula) with a fresh variable.
        """
        lits = self.get_literals()

        for _, node in super()._get_vertices().items():
            if super().is_seq_regular(node.left, lits):
                new_var = self._get_new_var()
                self.update_eq_regular_part(node, new_var, "left", lits)
            elif super().is_seq_regular(node.right, lits):
                new_var = self._get_new_var()
                self.update_eq_regular_part(node, new_var, "right", lits)


    def reduce_regular_eqs(self):
        """
        Remove nodes that can be reduced to a regular constraint.
        """
        self._replace_unique_side_fresh()
        self.simplify_unique()


    def reduce_common_sub(self):
        """
        Find common parts of each equation and replace them with a fresh equation
        replacing the common parts.
        """

        if len(super()._get_vertices()) == 0:
            return

        lits = self.get_literals()
        sl = super().get_minimal_unique_sublists(lits)

        replace = [ k for k, v in sl.items() if v >= 2]
        replace_map = dict()
        last = super().get_last_node()
        index = max(super()._get_vertices().keys()) + 1

        new_eqs = []
        for i in range(len(replace)):
            var = self._get_new_var()
            replace_map[replace[i]] = tuple([var])
            eq = StringEquation([var], list(replace[i]))
            new_eqs.append(eq)

        self.replace_eq_sublist(replace_map)

        for eq in new_eqs:
            last = super().add_equation(index, eq, last)
            index += 1

        for r, var in replace_map.items():
            aut_query = AutSingleSEQuery(StringEquation(list(r), list(r)), self.aut_constr)
            aut = aut_query.automaton_for_side("left")
            self.aut_constr[var[0]] = aut


    def generate_identities(self):
        """
        Generate identities s.t. if X = Y_1 B Y_2 AND X = Y_1 C Y_2 we can deduce B = C.
        """

        assert(super().is_conjunction())

        add_eq = []
        for _, eq1 in super()._get_vertices().items():
            for _, eq2 in super()._get_vertices().items():
                if eq1 == eq2:
                    continue

                if eq1.eq.get_side("left") == eq2.eq.get_side("left") and len(eq1.eq.get_side("right")) == 1 and len(eq2.eq.get_side("right")) == 1:
                    add_eq.append(StringEquation(eq1.eq.get_side("right"), eq2.eq.get_side("right")))
                if eq1.eq.get_side("right") == eq2.eq.get_side("right") and len(eq1.eq.get_side("left")) == 1 and len(eq2.eq.get_side("left")) == 1:
                    add_eq.append(StringEquation(eq1.eq.get_side("left"), eq2.eq.get_side("left")))

                rem1, rem2 = eq1.eq.get_side("right"), eq2.eq.get_side("right")
                if eq1.eq.get_side("left") == eq2.eq.get_side("left") and eq1.eq.get_side("right")[0] == eq2.eq.get_side("right")[0]:
                    rem1 = rem1[1:]
                    rem2 = rem2[1:]

                if eq1.eq.get_side("left") == eq2.eq.get_side("left") and eq1.eq.get_side("right")[-1] == eq2.eq.get_side("right")[-1]:
                    rem1 = rem1[0:-1]
                    rem2 = rem2[0:-1]

                if len(rem1) == 1 and len(rem2) == 1 and rem1 != eq1.eq.get_side("right"):
                    add_eq.append(StringEquation(rem1, rem2))

        last = super().get_last_node()

        if last is None:
            return

        index = max(super()._get_vertices().keys()) + 1
        for eq in add_eq:
            last = super().add_equation(index, eq, last)
            index += 1


    def remove_extension(self, scq: StringConstraintQuery):
        """
        Remove extensions from the formula. If X = Y_1 Y_2 and we know that
        L(SigStar . Y_2) = L(SigStar) and Y_2 does not occur elsewhere, we can
        remove Y_1 (Y_2 cen be expanded to cover Y_1).
        @param scq: String constraint query (for sigma star automaton)
        """

        assert(super().is_conjunction())

        occur = super().get_vars_count()
        vars = super()._get_edges().keys()
        begin_map = defaultdict(lambda: [])
        end_map = defaultdict(lambda: [])
        begin_star_vars = set()
        end_star_vars = set()

        for v in vars:
            if len(super()._get_edges()[v]) == 0:
                continue
            star = scq.sigma_star_aut()
            aut_v = self.aut_constr[v].copy()
            sigma_star = star.concatenate(aut_v).proper().minimal_automaton().trim()
            if awalipy.are_equivalent(sigma_star, aut_v):
                begin_star_vars.add(v)
            star = scq.sigma_star_aut()
            star = aut_v.concatenate(star).proper().trim()
            if awalipy.are_equivalent(sigma_star, aut_v):
                end_star_vars.add(v)

        for _,node in super()._get_vertices().items():
            eq = node.eq
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

        for _,node in super()._get_vertices().items():
            eq = copy.copy(node.eq)
            for l, r in remove_beg:
                if eq.get_side("left") == [l] and eq.get_side("right")[0] == r and len(eq.get_side("right")) > 1:
                    eq = StringEquation(eq.get_side("left"), eq.get_side("right")[1:])
                    break
            for l, r in remove_end:
                if eq.get_side("left") == [l] and eq.get_side("right")[-1] == r and len(eq.get_side("right")) > 1:
                    eq = StringEquation(eq.get_side("left"), eq.get_side("right")[0:-1])
                    break
            if eq != node.eq:
                super().update_eq(node, eq)




    def clean(self):
        """
        Remove trivial equations of the form [] = [] or [] = ...
        """
        empty = super().filter_nodes(lambda x: (not x.eq.get_side("left")) or\
            (not x.eq.get_side("right")))
        for node in empty:
            super().remove_node(node)


    def remove_duplicates(self):
        """
        Remove duplicated equations.
        """

        nodes = deque(super()._get_init())
        visited = set()
        singletons = set()
        remove = set()
        while len(nodes) > 0:
            node = nodes.popleft()
            if node in visited:
                continue
            visited.add(node)

            if node.eq.get_side("left") == node.eq.get_side("right"):
                remove.add(node)

            clause = super().get_clause(node)

            if len(clause) == 1:
                if node.eq in singletons:
                    remove.add(node)
                singletons.add(node.eq)
            nodes.extend(node.succ)

        for node in remove:
            super().remove_node(node)


    def get_aut_constraint(self):
        """
        Get automata constraints
        """
        return self.aut_constr


    def get_cnf(self) -> Sequence[Sequence[StringEquation]]:
        """
        Get formula back to cnf representation (each clause is a list).
        """

        def _get_eqs(nodes: Set[EqNode]) -> Sequence[StringEquation]:
            return list(map(lambda x: x.eq, nodes))

        cnf = []
        inits = super()._get_init()

        if len(inits) == 0:
            return cnf

        ret = cnf.append(_get_eqs(inits))
        node = list(inits)[0]
        while len(node.succ) > 0:
            cnf.append(_get_eqs(node.succ))
            node = list(node.succ)[0]
        return cnf
