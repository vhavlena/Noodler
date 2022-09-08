
from collections import defaultdict, deque
from typing import Set

from .sequery import AutSingleSEQuery, StringConstraintQuery
from .core import StringEquation, AutConstraints

import mata

class Nielsen:

    def __init__(self, eq: StringEquation, aut: AutConstraints, lits: Set[str]):
        self.eq = eq
        self.aut = aut
        self.lits = lits


    def create_sym_var(self, sym) -> str:
        return "__quad_sym_{0}".format(sym)


    def extend_literals(self):
        query = AutSingleSEQuery(self.eq, self.aut)
        
        def _extend_side(side):
            res = []
            for var in side:
                if var not in self.lits:
                    res.append(var)
                    continue
                for sym in query.get_word(var):
                    new_var = self.create_sym_var(sym)
                    self.lits.add(new_var)
                    res.append(new_var)
            return res
        
        left = _extend_side(self.eq.get_side("left"))
        right = _extend_side(self.eq.get_side("right"))
        self.eq = StringEquation(left, right)

    
    def is_quadratic(self, scq: StringConstraintQuery) -> bool:
        cnt = defaultdict(lambda: 0)
        for var in self.eq.get_side("left") + self.eq.get_side("right"):
            cnt[var] += 1
        
        for var, cnt in cnt.items():
            if cnt > 2 and var not in self.lits:
                return False

        sigmastar = scq.sigma_star_aut()
        for var in self.eq.get_vars():
            if var in self.lits:
                continue
            if not mata.Nfa.equivalence_check(sigmastar, self.aut[var], alphabet=None):
                return False

        return True


    def apply_transform(self, eq: StringEquation, left, right) -> StringEquation:

        def _apply(side):
            res = []
            for sym in side:
                if sym == left:
                    if right is None:
                        continue
                    res += right
                else:
                    res.append(sym)
            return res
        
        left_s = _apply(eq.get_side("left"))
        right_s = _apply(eq.get_side("right"))
        return StringEquation(left_s, right_s)

    
    def trim(self, eq: StringEquation) -> StringEquation:

        left = eq.get_side("left")
        right = eq.get_side("right")
        end = 0
        for i in range(min(len(left), len(right))):
            if left[i] != right[i]:
                break
            end += 1
        
        return StringEquation(left[end:], right[end:])


    def is_sat(self):
        self.extend_literals()
        visited = set([self.eq])
        new = deque([self.eq])

        while len(new) > 0:
            eq = new.popleft()
            

            sym_1 = eq.get_side("left")[0] if len(eq.get_side("left")) > 0 else None
            sym_2 = eq.get_side("right")[0] if len(eq.get_side("right")) > 0 else None

            if sym_1 is None and sym_2 is None:
                return True
            if sym_1 is None and sym_2 in self.lits:
                continue
            if sym_2 is None and sym_1 in self.lits:
                continue

            eqs = set()
            if sym_1 is not None and sym_2 is not None and sym_1 not in self.lits:
                ret = self.apply_transform(eq, sym_1, [sym_2, sym_1])
                eqs.add(self.trim(ret))
            if sym_2 is not None and sym_1 is not None and sym_2 not in self.lits:
                ret = self.apply_transform(eq, sym_2, [sym_1, sym_2])
                eqs.add(self.trim(ret))
            if sym_1 is not None and sym_1 not in self.lits:
                ret = self.apply_transform(eq, sym_1, None)
                eqs.add(self.trim(ret))
            if sym_2 is not None and sym_2 not in self.lits:
                ret = self.apply_transform(eq, sym_2, None)
                eqs.add(self.trim(ret))

            for e in eqs:
                if e not in visited:
                    new.append(e)
                    visited.add(e)

        return False

    

    

