"""
Contains various implementations of queries build upon
string equations (SE) or upon systems of SE.

SingleSEQuery
    Abstract class for queries
AutSingleSEQuery
    query of 1 string equation with regular constraints on
    variables given by automata
RESingleSEQuery
    query with constraints represented by regular expressions.
MultiSEQuery
    system (sequence) of equations with constraints for
    variables.
"""
from typing import Sequence, Dict, Collection, Optional, Set

import mata
import copy

from .utils import show_automata
from .algos import multiop, get_word_cycles
#types
from .core import AutConstraints, Aut, Constraints, SegAut, RE
# classes
from .core import StringEquation, StringConstraint, ConstraintType
# functions
from .core import create_automata_constraints


DEFAULTALPHABET = "abc"


def compare_aut_constraints(a1: AutConstraints, a2: AutConstraints) -> bool:
    """!
    Compare languages of aut constraints. We dont need to keep equal aut
    constraints.
    """
    if a1.keys() != a2.keys():
        return False

    for k1, v1 in a1.items():
        if not mata.Nfa.equivalence_check(v1, a2[k1], alphabet=None):
            return False
    return True


def compare_aut_constraints_str(a1, a2) -> bool:
    """!
    Compare string representatives of aut constraints.
    """
    if a1.keys() != a2.keys():
        return False

    for k1, v1 in a1.items():
        if v1 != a2[k1]:
            return False
    return True

def mata_allchar(alphabet: str) -> RE:
    """
    Create awalipy RE for Σ given as a string of characters.

    Parameters
    ----------
    alphabet: str

    Returns
    -------
    RE for a+b+c+...
    """
    return "[{0}]".format(alphabet)
    #return awalipy.RatExp(all_str, alphabet=alphabet)



class SingleSEQuery:
    """
    Abstract class for string equation with constraints.

    The query is specified by a string equation and
    some (regular) constraints (typically on variables).

    Public functions
    ----------------
    automata_for_side : "left"/"right" → list of auts
    seg_aut : "left"/"right" → SegAut
        return segment automaton representing one side of ``eq``
    proper_aut : "left"/"right" → Aut
        return proper (without ε-trans.) automaton representing
        one side of ``eq``
    show_constraints
        Show constraints in Jupyter

    Attributes
    ----------
    eq : StringEquation
    constraints
    """

    def __init__(self, equation: StringEquation,
                 constraints: Constraints):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        self.eq = equation
        self.constraints = constraints

    def automata_for_side(self, side: str,
                          make_copies: bool = False) -> Sequence[Aut]:
        """
        Return list of automata for left/right side of equation.

        Parameters
        ----------
        side : "left" or "right"
        make_copies : Bool, default False
            Create copies of constraints automata if True
        Returns
        -------
        Sequence[Aut]
        """
        raise NotImplementedError
        

    def proper_aut(self, side: str,
                   minimize: bool = True) -> Aut:
        """
        Returns automaton without ε-transitions for left/right side
        of equation.

        Parameters
        ----------
        side : "left" or "right"
        minimize : bool
            return the minimal aut if True

        Returns
        -------
        Aut
            Represents the language of one side of equation.
        """
        res = multiop(self.automata_for_side(side), lambda x,y: mata.Nfa.concatenate(x, y))

        if minimize:
            return mata.Nfa.reduce(res)[0]

        return res

    def show_constraints(self):
        print(f"{self.constraints}")

    def switched(self) -> 'SingleSEQuery':
        """
        Create query with the same constraints for a switched equation
        """
        return self.__class__(self.eq.switched, self.constraints)


class AutSingleSEQuery(SingleSEQuery):
    """
    String equation with automata constraints.

    The query is specified by a string equation and regular
    constraints on variables defined by automata.

    Functions
    ---------
    automata_for_side : "left"/"right" → list of auts
    is_balanced : bool
    show_constraints
        In Jupyter, display automaton for each variable
    """

    def __init__(self, equation: StringEquation,
                 constraints: AutConstraints):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        super().__init__(equation, constraints)

    def automata_for_side(self, side: str,
                          make_copies: bool = False) -> Sequence[Aut]:
        """
        Return list of automata for left/right side of equation.

        Parameters
        ----------
        side : "left" or "right"
        make_copies : Bool, default False
            Create copies of constraints automata if True
        Returns
        -------
        list of auts
        """
        var_sequence = self.eq.get_side(side)
        automata = []

        for var in var_sequence:
            if make_copies:
                aut = self.constraints[var].copy()
            else:
                aut = self.constraints[var]
            automata.append(aut)

        return automata


    def is_sub_balanced(self) -> bool:
        """!
        Check if the query is one side balanced.
        query is balanced if the shortest strings of the first-side automaton
        belong to the language of the second-side automaton.

        @return Balanced?
        """

        auts_l = self.automata_for_side("left")
        auts_r = self.automata_for_side("right")

        aut_l = multiop(auts_l, lambda x,y: mata.Nfa.concatenate(x,y))
        aut_r = multiop(auts_r, lambda x,y: mata.Nfa.concatenate(x,y))
        short = aut_l.get_shortest_words()

        for w in short:
            if not mata.Nfa.is_in_lang(aut_r, w):
                return False
        return True


    def has_empty_product(self) -> bool:
        """
        Have the automata corresponding to each side empty language?
        """
        auts_l = self.automata_for_side("left")
        auts_r = self.automata_for_side("right")

        aut_l = multiop(auts_l, mata.Nfa.concatenate(x,y))
        aut_r = multiop(auts_r, mata.Nfa.concatenate(x,y))


        prod, _ = mata.Nfa.intersection(aut_l, aut_r)
        return mata.Nfa.is_lang_empty_word_counterexample(prod)[0]

        #return len(awalipy.product(tmp_l, tmp_r).trim().final_states()) == 0


    def automaton_for_side(self, side: str) -> Aut:
        """!
        Get an automaton for a given side.

        @param side: Side (left, right)
        @return Concatenation of automata for a given side
        """
        auts_l = self.automata_for_side(side)
        return multiop(auts_l, lambda x,y: mata.Nfa.concatenate(x,y))


    def automaton_for_side_minimal(self, side: str) -> Aut:
        """!
        Get an automaton for a given side (apply intermediate minimization).

        @param side: Side (left, right)
        @return Concatenation of automata for a given side
        """
        auts_l = self.automata_for_side(side)
        return multiop(auts_l, lambda x,y: mata.Nfa.minimize(mata.Nfa.concatenate(x, y)))


    def is_balanced(self) -> bool:
        """
        Check if query is balanced.

        query is balanced if automata representing both
        sides recognize equivalent shortest languages.

        Returns
        -------
        True if query is balanced
        """
        auts_l = self.automata_for_side("left")
        auts_r = self.automata_for_side("right")

        aut_l = multiop(auts_l, lambda x,y: mata.Nfa.concatenate(x,y))
        aut_r = multiop(auts_r, lambda x,y: mata.Nfa.concatenate(x,y))

        tmp_l = mata.Nfa.minimize(aut_l)
        tmp_r = mata.Nfa.minimize(aut_r)


        return set(tmp_l.get_shortest_words()) == set(tmp_r.get_shortest_words())

        #return awalipy.are_equivalent(aut_l, aut_r)

    def show_constraints(self):
        show_automata(self.constraints)


    def unsat_check(self):

        left = self.automaton_for_side("left")
        right = self.automaton_for_side("right")
        prod, _ = mata.Nfa.intersection(left, right) #.proper().trim()
        res, _ = mata.Nfa.is_lang_empty_word_counterexample(prod)
        return res


    def get_word(self, var):
        aut = self.constraints[var]
        return list(aut.shortest(len(aut.useful_states())).keys())[0]


    def unsat_pattern(self, literals: Set[str]):

        left = self.eq.get_side("left")
        right = self.eq.get_side("right")
        if len(left) != len(right) or len(left) != 2:
            return False

        if left[0] == right[1] and left[1] in literals and right[0] in literals:
            word1 = self.get_word(left[1])
            if not self.get_word(right[0]) in get_word_cycles(word1):
                return True

        if left[1] == right[0] and left[0] in literals and right[1] in literals:
            word1 = self.get_word(left[0])
            if not self.get_word(right[1]) in get_word_cycles(word1):
                return True

        return False


class RESingleSEQuery(SingleSEQuery):
    """
    String equation with regular expression constraints for variables.

    The query is specified by a string equation and constraints on
    variables defined by regular expressions.

    Functions
    ---------
    automata_for_side : "left"/"right" → list of auts
    is_balanced : bool
    show_constraints
        In Jupyter, display automaton for each variable
    """

    def __init__(self, equation: StringEquation,
                 constraints: Dict[str, str]):
        """
        Parameters
        ----------
        equation : StringEquation
        constraints : dict (equation.vars → aut)
        """
        res = {
            var: mata.Nfa.from_regex(c) for var, c in constraints.items()
        }
        super().__init__(equation, res)

    def automata_for_side(self, side: str,
                          make_copies: bool = False) -> Sequence[Aut]:
        """
        Return list of automata for left/right side of equation.

        Parameters
        ----------
        side : "left" or "right"
        make_copies : Bool, default False
            Create copies of constraints automata if True
        Returns
        -------
        list of auts
        """
        var_sequence = self.eq.get_side(side)
        aut_const = self._get_automata_constraints()
        automata = []

        for var in var_sequence:
            if make_copies:
                aut = aut_const[var].copy()
            else:
                aut = aut_const[var]
            automata.append(aut)

        return automata

    def _get_automata_constraints(self) -> AutConstraints:
        """
        Return dictionary with constraints as automata.
        """
        return {var: c.exp_to_aut() for var, c in self.constraints.items()}

    def aut_query(self) -> AutSingleSEQuery:
        """
        Convert into query with automata constraints.

        Returns
        -------
        AutSingleSEQuery
        """
        aut_const = self._get_automata_constraints()
        return AutSingleSEQuery(self.eq, aut_const)


class MultiSEQuery:
    """
    Represents query with system of String Equations

    The query consists of a sequence of equations
    and constraints for variables.

    Attributes
    ----------
    equations : Sequence[StringEquation]
    aut_constraints : AutConstraints
    """

    def __init__(self, equations: Sequence[StringEquation],
                 constraints: AutConstraints):
        """
        Create MultiSEQuery.

        Parameters
        ----------
        equations: Sequence[StringEquation]
        constraints: Automata Constraints
        """
        # TODO allow list of strings
        self.equations = equations

        self.aut_constraints = constraints


    def __str__(self) -> str:
        """!
        String representation of the MultiSEQuery
        """
        return str(self.equations) + str(self.aut_constraints)


    def __repr__(self) -> str:
        return str(self)



class StringConstraintQuery:

    def __init__(self, constr: StringConstraint, alphabet_str: str):
        """!
        Create a query from a given string constraint

        @param constr: A string constraint
        @param alphabet_str: Alphabet in the form of sequence of chars
        """
        self.alphabet = alphabet_str
        if len(self.alphabet) == 0:
            self.alphabet = DEFAULTALPHABET
        self.constraint = constr


    @staticmethod
    def _merge_constraints(cnstr: Sequence[AutConstraints]) -> AutConstraints:
        """!
        Merge constraints over the same variable (using automata intersection)

        @param cnstr: A list of AutConstraints
        @return Merged AutConstraint
        """
        if len(cnstr) == 0:
            return dict()

        res = cnstr[0]
        for c in cnstr:
            for k, v in c.items():
                if k in res:
                    res[k], _ = mata.Nfa.intersection(v, res[k]) #.proper().minimal_automaton().trim()
                else:
                    res[k] = v
        return res


    def sigma_star_aut(self):
        sigma_star: RE = "{0}*".format(mata_allchar(self.alphabet))
        return mata.Nfa.from_regex(sigma_star)


    def _gather_aut_constraints(self) -> AutConstraints:
        constr = [create_automata_constraints(c.left) for c in self.constraint.gather_leafs(ConstraintType.RE)]
        constr_dict = StringConstraintQuery._merge_constraints(constr)
        vars = self.constraint.get_vars()

        for var in vars:
            constr_dict.setdefault(var, self.sigma_star_aut())
        return constr_dict


    def get_queries_cnf(self):
        return self.constraint.get_cnf_list(), self._gather_aut_constraints()


    def get_sequeries_dnf(self) -> Sequence[MultiSEQuery]:
        """!
        Get subqueries for solving of the string constraint.

        @return A list of MultiSEQuery
        """
        queries = []
        dnf = self.constraint.to_dnf()

        ors = dnf.gather_op(ConstraintType.OR)
        for c_and in ors:
            constr = [create_automata_constraints(c.left) for c in c_and.gather_leafs(ConstraintType.RE)]
            constr_dict = StringConstraintQuery._merge_constraints(constr)
            eqs = [c.left for c in c_and.gather_leafs(ConstraintType.EQ)]
            c_vars = c_and.get_vars()

            for var in c_vars:
                constr_dict.setdefault(var, self.sigma_star_aut())
            queries.append(MultiSEQuery(eqs, constr_dict))
        return queries
