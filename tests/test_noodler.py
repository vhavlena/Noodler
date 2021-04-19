import awalipy
import pytest

from noodler import StringEquation, AutSingleSEQuery, SimpleNoodler, multiop


class TestSimpleNoodler:

    @pytest.fixture
    def acb0_constraints(self):
        alph = "abc"
        Σ = f"({'+'.join(alph)})"
        re_constraints = {
            "u": f"a{Σ}*",
            "v": f"{Σ}*c{Σ}*",
            "w": f"{Σ}{Σ}*b",
            "z": f"{Σ}*"
        }
        aut_constr = {}
        for var, re_str in re_constraints.items():
            re = awalipy.RatExp(re_str, alphabet=alph)
            aut_constr[var] = re.exp_to_aut()

        return aut_constr

    @pytest.fixture
    def simple_eq(self):
        return StringEquation("uvw","z")

    @pytest.fixture
    def repet_left_eq(self):
        return StringEquation("uzu","w")

    @pytest.fixture
    def simple_sys(self, simple_eq, acb0_constraints):
        return AutSingleSEQuery(simple_eq, acb0_constraints)

    @pytest.fixture
    def repet_left_sys(self, repet_left_eq, acb0_constraints):
        return AutSingleSEQuery(repet_left_eq, acb0_constraints)

    def test_noodles_cover_product_on_simple(self, simple_sys):
        """
        With no repetition of variables (and thus unification with
        no effect), noodles should cover the product of left and right
        side of equation precisely.
        """
        left_aut: awalipy.Automaton = simple_sys.proper_aut("left")
        right_aut: awalipy.Automaton = simple_sys.proper_aut("right")
        product: awalipy.Automaton = awalipy.product(left_aut, right_aut)
        n = SimpleNoodler(simple_sys)
        noodles = n.noodlify()
        noodles_auts = [noodle.proper_aut("left") for noodle in noodles]
        noodles_union = multiop(noodles_auts, awalipy.union)
        assert awalipy.are_equivalent(noodles_union, product)

    def test_noodles_subset_of_product(self, repet_left_sys):
        """
        Due to unification, noodles might be smaller then product. But
        can't represent bigger language.
        """
        left_aut: awalipy.Automaton = repet_left_sys.proper_aut("left")
        right_aut: awalipy.Automaton = repet_left_sys.proper_aut("right")
        product: awalipy.Automaton = awalipy.product(left_aut, right_aut)
        complement = product.minimal_automaton().complement()
        n = SimpleNoodler(repet_left_sys)
        noodles = n.noodlify()
        noodles_auts = [noodle.proper_aut("left") for noodle in noodles]
        noodles_union = multiop(noodles_auts, awalipy.union)
        assert awalipy.product(complement, noodles_union).num_useful_states() == 0