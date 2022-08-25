"""
Classes
-------
SimpleNoodler
    Creates unified noodles for AutSingleSEQuery instances. This is
    enough for simple equations (all variables that occur the
    right-hand side of the equation are unique).
QueueNoodler
    Seek solutions using noodlification for non-simple equations.

StraightlineNoodleMachine
    Solves Straight-line MiultiSEQueries with proved termination.
"""
import awalipy
import itertools
import mata

from collections import deque
from typing import Sequence, Optional, List

# Classes
from .core import StringEquation
from .sequery import AutSingleSEQuery, SingleSEQuery, MultiSEQuery
# Types
from .core import Aut, AutConstraints, SegAut

from .algos import eps_preserving_product, eps_segmentation, multiop, single_final_init, split_segment_aut


def noodlify(aut: SegAut,
             include_empty: bool = False) -> Sequence[SegAut]:
    """
    Create noodles from segment automaton.

    Segment automaton is a chain of automata connected
    via ε-transitions. A noodle is a copy of the segment
    automaton with exactly 1 ε-transition between each
    two consecutive segments. Noodlify return the list of
    all (non-empty) noodles.

    Parameters
    ----------
    aut : aut
        Segment automaton to noodlify.
    include_empty : Bool (default False)
        Include also empty noodles if True.
    """
    # Stores the noodles
    noodles = []

    # We need to make a copy of the automaton before running
    # segmentation to remove non-existent transitions.
    aut = aut.copy()
    # depth → list of ε-trans
    segments = eps_segmentation(aut)

    # For each combination of ε-transitions, create the automaton.
    for noodle_trans in itertools.product(*segments.values()):
        noodle = aut.copy()
        for i in reversed(range(len(noodle_trans))):
            # Remove all ε-tr. of depth i but noodle_trans[i]
            for tr in segments[i]:
                assert noodle.label_of(tr) == "\\e"
                if tr != noodle_trans[i]:
                    noodle.del_transition(tr)

        noodle = noodle.trim()
        if include_empty or noodle.num_states() > 0:
            noodles.append(noodle)

    return noodles


def noodlify_query(query: SingleSEQuery) -> Sequence[SegAut]:
    """
    Make left-noodles from query.

    The noodles (result) are not necessary unified.

    Parameters
    ----------
    query : sequery.AutSingleSEQuery
        query to be noodlified

    Returns
    -------
    noodles : Sequence[Aut]
        left-noodles for ``query``
    """

    lefts: SegAut = query.automata_for_side("left")
    right: Aut = query.proper_aut("right")
    return mata.Nfa.noodlify_for_equation(lefts, right)


    # left: SegAut = query.seg_aut("left")
    # right: Aut = query.proper_aut("right")
    # assert left.alphabet() == right.alphabet()
    # product: SegAut = eps_preserving_product(left, right, history=True)
    # return noodlify(product)


def create_unified_query(equation: StringEquation,
                         left_auts: Sequence[Aut],
                         right_auts: Sequence[Aut]) -> \
                                    Optional[AutSingleSEQuery]:
    """
    Create unified query from equation and automata.

    Unify automata given by left_auts and right_auts
    with respect to equation. That is, for each variable v
    present in the equation, make a product of automata
    that correspond to a occurrence of `v`. The product
    automaton is a constraint for `v` in the resulting
    query.

    If the language (of the product) for some variable is
    empty, the query can't be unified.

    Parameters
    ----------
    equation: StringEquation
    left_auts, right_auts: list of auts
        list of automata of the same length as ``equation.left``
        resp. ``equation.right``.
    Returns
    -------
    AutSingleSEQuery
        Unified query for ``equation`` and None if the query cannot
        be unified.
    """
    if len(left_auts) != len(equation.left):
        raise ValueError(f"""
        The length of `left_auts` must agree with length of `equation.left`.
        Given len(left_auts) = {len(left_auts)} and
              len(equation.left) = {len(equation.left)}.""")
    if len(right_auts) != len(equation.right):
        raise ValueError(f"""
        The length of `right_auts` must agree with length of `equation.right`.
        Given len(right_auts) = {len(right_auts)} and
              len(equation.right) = {len(equation.right)}.""")

    const: AutConstraints = {}

    for var in equation.vars:
        aut_l = {left_auts[i] for i in equation.indices_l[var]}
        aut_r = {right_auts[i] for i in equation.indices_r[var]}
        var_auts = aut_l.union(aut_r)
        product: Aut = multiop(list(var_auts), lambda x,y: mata.intersection(x,y)[0])
        product.trim()
        const[var] = product
        if const[var].get_num_of_states() == 0:
            return None

    return AutSingleSEQuery(equation, const)


def is_unified(equation, auts_l, auts_r):
    """
    Check if query is unified.

    Check for each variable of equation whether
    all corresponding automata in auts_l and auts_r
    recognize the same language.

    The lengths of auts must correspond to lengths
    of equation sides.

    Parameters
    ----------
    equation : StringEquation
    auts_l, auts_r : list of auts
        Automata representing eq_l

    Returns
    -------
        False if two automata for the same variable recognize
        different languages. True otherwise.
    """
    pass


class SimpleNoodler:
    """
    Makes unified automata noodles for easy equations.

    This class is intended to work for one simple
    SingleSEquery. It creates segment automaton for the
    left-hand side, intersects it with the automaton for
    the right-hand side and creates all possible unified
    noodles.

    Restrictions on equation
    ------------------------
    All variables that appear on the right-hand side of
    the equation must have only one occurrence in the
    equation.

    Attributes
    ---------
    query : SingleSEQuery
    noodles : Sequence[SingleSEQuery]
        unified noodles for ``query``
    """

    def __init__(self, query: SingleSEQuery):
        self.query = query
        self.noodles = None

    def noodlify(self) -> Sequence[SingleSEQuery]:
        """
        Create all possible non-empty unified noodles for
        self.query.

        Returns
        -------
        self.noodles:
        """
        self.noodles = []

        noodles: Sequence[SegAut] = noodlify_query(self.query)
        for auts_l in noodles:
            #auts_l = split_segment_aut(noodle)
            auts_r = self.query.automata_for_side("right")
            unified = create_unified_query(self.query.eq,
                                           auts_l,
                                           auts_r)

            # Noodle cannot be unified
            if unified is not None:
                self.noodles.append(unified)

        return self.noodles


class QueueNoodler:
    """
    QueueNoodler makes and unifies automata noodles.

    Attributes
    ----------
    Q : deque
        Keep querys to be processed.
    """

    def __init__(self, query):
        """
        Create a noodler with an initialized queue.

        Parameters
        ----------
        query: AutSingleSEQuery
            query to start with
        """
        self.Q = deque([query])
        self.solutions = []

    def one_solution(self):
        """
        Attempts to find a solution.

        Take one query out of queue, noodlify it and then
        unify each noodle with the right-hand side automata.
        If this unified query is balanced, store it into
        self.solutions and return it. Otherwise, add it to
        queue and continue.

        No guarantees on termination.

        Returns
        -------
        Balanced and unified query or None
        """
        query = self.Q.popleft()
        if query.is_balanced():
            self.solutions.append(query)
            return query

        while query:
            noodles = noodlify_query(query)
            for noodle in noodles:
                auts_l = split_segment_aut(noodle)
                auts_r = query.automata_for_side("right")
                noodle_sys = create_unified_query(query.eq,
                                                  auts_l,
                                                  auts_r)
                # Noodle cannot be unified
                if noodle_sys is None:
                    continue

                if noodle_sys.is_balanced():
                    self.solutions.append(noodle_sys)
                    return noodle_sys
                else:
                    self.Q.append(noodle_sys.switched())

            query = self.Q.popleft()

        # Nothing was found
        return None

    def process_one(self, verbose=False):
        query = self.Q.popleft()

        if verbose:
            print(f"""
================================
Processing the following query:
{query.eq}
Constraints:
{query.constraints}
--------------------------------""")

        noodles: Sequence[SegAut] = noodlify_query(query)
        for noodle in noodles:
            auts_l = split_segment_aut(noodle)
            auts_r = query.automata_for_side("right")
            noodle_sys = create_unified_query(query.eq,
                                              auts_l,
                                              auts_r)

            noodle_sys.eq = noodle_sys.eq.switched
            self.Q.append(noodle_sys)

        if verbose:
            print(f"""Found {len(noodles)} non-empty noodles.
================================""")


class StraightlineNoodleMachine:
    """
    Noodle machine that solves Straightline queries.

    Solves the SSA-like equation system using noodles.
    The system consists of k+1 equations (eq_0 ... eq_k).
    Each equation is a level. The machine starts at the
    last level (equation) with the initial constraints
    given by the query. When solving a level, it creates
    SimpleNoodler that noodlifies the level with the current
    constraints. Each noodle for level `i` is a witness for a
    solution for the system eq_i, eq_{i+1}, ..., eq_k.

    We then propagate the learned constraints for for eq_i
    cumulatively back to eq_{i+1} ... eq_k

    `propagate_constraints` can be used to restrict the languages
    of the constraints simply based on equations eq_0 ... eq_k.
    if eq_0 is `x_0 = y_1 y_2 y_3`, and the constraints are stored
    in `C` then we update the constraint of `x_0` to
      ``C[x_0] ∩ (C[y_1].C[y_2].C[y_3])``.

    Attributes
    ----------
    query: MultiSEQuery
    noodlers: Sequence[Optional[SimpleNoodler]]
        Simple noodlers for each level/equation

    Methods
    ---------
    is_sat: -> Bool
        Return True if `query` is SAT
    solve: -> AutConstraints
        If `query` is SAT, return Automata constraints that can be used
        to find a concrete solution.
    """

    def __init__(self, query: MultiSEQuery):
        self.query = query
        self.noodlers: List[Optional[SimpleNoodler]] = [None] * len(query.equations)

    def propagate_constraints(self, constraints: Optional[AutConstraints] = None) -> None:
        # TODO check empty!
        """
        Propagate constraints directly from equations.

        Update constraints for the left sides of equations 0 ... k
        to intersection of the current constraints and the automaton
        for the right-hand side of the equation.

        Parameters
        ----------
        constraints: AutConstraints, optional
            Dictionary with constraints to use (and update)
        """
        if constraints is None:
            constraints = self.query.aut_constraints
        for eq in self.query.equations:
            query = AutSingleSEQuery(eq, constraints)
            left_var = eq.left[0]
            current_constr = constraints[left_var]
            new_constr = awalipy.product(current_constr,
                                         query.proper_aut("right", minimize=False))
            constraints[left_var] = new_constr.trim()

    def is_sat(self, bidirectional: bool = False, verbose = False) -> bool:
        """
        Decide satisfiability of the `query`.

        This is only correct if `query` belongs to the straight-line fragment.

        Parameters
        ----------
        bidirectional: bool, default False
            Restricts constraints in both directions (independently) and check
            their intersection at each level. The main direction is from the end
            of the chain to the beginning (equations k → 0). The addition is the
            other direction (0 → k) with constraints build for x_i directly from
            the equation x_i = y₀y₁… with the y-vars having index lower then i.
        verbose: bool, default False
            Prints info about the computation status.

        Returns
        -------
        True if query is satisfiable, False otherwise.
        """
        def _is_sat_rec(level: int, constraints: AutConstraints,
                        fwd_constraints: AutConstraints = None):

            if verbose:
                print([len(n.noodles) for n in self.noodlers if n is not None])
            if level < 0:
                return True
            # We use switched equations. We need the form:
            # y₁y₂y₃ = x
            cur_query = AutSingleSEQuery(self.query.equations[level].switched,
                                         constraints)

            if verbose:
                print(level, cur_query.eq)

            # For bidirectional mode check whether x_i (left side of eq) has a
            # solution in both directions.
            if fwd_constraints is not None:
                assert len(cur_query.eq.right) == 1
                var = cur_query.eq.right[0]
                product: Aut = awalipy.product(constraints[var], fwd_constraints[var])
                if product.num_useful_states() == 0:
                    return False

            noodler = SimpleNoodler(cur_query)
            self.noodlers[level] = noodler
            noodles: Sequence[SingleSEQuery] = noodler.noodlify()

            if verbose:
                noodle_c = 0

            for noodle in noodles:
                # In bidirectional mode check that the unified constraints for each
                # variable from right-hand side of the original equation (left in switched)
                # is in agreement with the forward constraints.
                if fwd_constraints is not None:
                    for var in cur_query.eq.left:
                        product: Aut = awalipy.product(noodle.constraints[var], fwd_constraints[var])
                        if product.num_useful_states() == 0:
                            continue

                if verbose:
                    noodle_c += 1
                    global counter
                    counter += 1
                    print(f"{counter} noodles explored; lvl {level}; noodle: {noodle_c}/{len(noodles)}")
                    # from .utils import show_automata
                    # show_automata(noodle.constraints)
                cur_constraints: AutConstraints = constraints.copy()
                cur_constraints.update(noodle.constraints)

                if _is_sat_rec(level - 1, cur_constraints):
                    return True

            return False

        if verbose:
            global counter
            counter = 0
            print(f"====EQUATIONS====")
            for i, eq in enumerate(self.query.equations):
                print(f"{i}: {eq}")
            print("====Constraints` sizes====")
            for var, aut in self.query.aut_constraints.items():
                print(f"{var}: {aut.num_useful_states()} states, {aut.num_finals()} final")
            print("====RUN====")

        for c in self.query.aut_constraints.values():
            if c.num_useful_states() == 0:
                return False

        if bidirectional:
            fwd_constr = self.query.aut_constraints.copy()
            self.propagate_constraints(fwd_constr)
            for c in fwd_constr.values():
                if c.num_useful_states() == 0:
                    return False

        lvl = len(self.query.equations) - 1
        constr = self.query.aut_constraints.copy()
        return _is_sat_rec(lvl, constr)

    def solve(self) -> AutConstraints:
        """
        Find constraints representing a solution of `query`.

        This is only correct if `query` belongs to the straight-line fragment.

        Returns
        -------
        AutConstraints
            Constraints representing a solution of ``self.query``.
        """
        level = len(self.query.equations) - 1
        constraints = self.query.aut_constraints.copy()
        return self._solve_rec(level, constraints)

    def _solve_rec(self, level: int,
                   constraints: AutConstraints) -> Optional[AutConstraints]:
        """
        Function to compute a solution recursively.

        Parameters
        ----------
        level: int
        constraints:

        Returns
        -------
        AutConstraints
            Constraints representing one solution, or None if no solution
            exists.

        Notes
        -----
        We could store pointers to each level to see what is the current
        noodle under investigation in order to generate more solutions.
        """
        # print([len(n.noodles) for n in self.noodlers if n is not None])
        if level < 0:
            return constraints
        # We use switched equations. We need the form:
        # y₁y₂y₃ = x
        cur_query = AutSingleSEQuery(self.query.equations[level].switched,
                                     constraints)
        noodler = SimpleNoodler(cur_query)
        self.noodlers[level] = noodler
        noodles: Sequence[SingleSEQuery] = noodler.noodlify()

        # c = 0

        for noodle in noodles:
            # c += 1
            # print(f"{level}: {c}/{len(noodles)}")
            cur_constraints: AutConstraints = constraints.copy()
            cur_constraints.update(noodle.constraints)

            lower_constraints = self._solve_rec(level - 1,
                                                cur_constraints)

            if lower_constraints is not None:
                # There is a solution and we have constraints ∀x_i. i<level
                # Now we create constraints for x_{level}
                cur_query.constraints.update(lower_constraints)
                cur_var = cur_query.eq.right[0]
                lower_constraints[cur_var] = cur_query.proper_aut("left")

                return lower_constraints

        return None
