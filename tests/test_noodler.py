import awalipy
import pytest
import subprocess

# Imports from Noodler
from noodler import StringEquation, AutSingleSEQuery, SimpleNoodler, is_straightline, multiop, StraightlineNoodleMachine
from noodler import SmtlibParserHackAbc
from noodler.algos import single_final_init

# Import test cases
from generate_parsers import pytest_generate_tests, long


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
        return StringEquation("uvw", "z")

    @pytest.fixture
    def repet_left_eq(self):
        return StringEquation("uzu", "w")

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


def run_z3(filename, timeout=10):
    z3_res = subprocess.run(["z3", filename, f"-T:{timeout}"], capture_output=True, text=True)
    return z3_res.stdout.strip()


class TestStraightlineNoodlerMachine:
    def test_sat(self, noreplace_parsers: SmtlibParserHackAbc):
        """
        Tests equivalence of results given by noodler and z3.

        This runs several minutes. By default, Z3 runs with TO
        of 10s. We don't restrict noodler on time.
        """
        query = noreplace_parsers.parse_query()
        assert is_straightline(query.equations)
        nm = StraightlineNoodleMachine(query)
        res = nm.is_sat(bidirectional=False)
        print(res)

        z3_res = run_z3(noreplace_parsers.filename)
        print(z3_res)
        if z3_res != "timeout":
            assert (z3_res == "sat") == res

    def test_long_run(self, long):
        query = long.parse_query()
        assert is_straightline(query.equations)
        nm = StraightlineNoodleMachine(query)
        res = nm.is_sat(bidirectional=False)

