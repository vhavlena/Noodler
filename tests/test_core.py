import awalipy
import pytest
from noodler.core import create_automata_constraints, is_straightline, StringEquation


def test_create_automata_constraints():
    re_x = "a(a+b+c)*"
    re_y = "(a+b+c)*b"

    str_based = {
        "x": re_x,
        "y": re_y
    }
    res = create_automata_constraints(str_based)

    expected = {
        "x": awalipy.load("a-abcstar.json"),
        "y": awalipy.load("abcstar-b.json")
    }

    for var in expected:
        assert awalipy.are_equivalent(res[var], expected[var])


def convert_equations(eq_strings):
    return [
        StringEquation(*e.split("="))
        for e in eq_strings
    ]


class TestIsStraightline:
    @pytest.fixture
    def straightline_equations(self):
        return convert_equations([
            "m=klk",
            "n=mk",
            "o=nn"
        ])

    def test_valid(self, straightline_equations):
        assert is_straightline(straightline_equations)

    def test_double_assignement(self, straightline_equations):
        new_eq = StringEquation("n", "lk")
        straightline_equations.append(new_eq)
        assert not is_straightline(straightline_equations)

    def test_on_left_on_right(self, straightline_equations):
        straightline_equations[1].right += straightline_equations[1].left
        assert not is_straightline(straightline_equations)

    def test_two_on_left(self, straightline_equations):
        straightline_equations[0].left = "mx"
        assert not is_straightline(straightline_equations)
