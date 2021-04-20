import awalipy
from noodler.core import create_automata_constraints

def test_create_automata_constraints():
    re_x = "a(a+b+c)*"
    re_y = "(a+b+c)*b"

    str_based = {
        "x" : re_x,
        "y" : re_y
    }
    res = create_automata_constraints(str_based)

    expected = {
        "x" : awalipy.load("a-abcstar.json"),
        "y" : awalipy.load("abcstar-b.json")
    }

    for var in expected:
        assert awalipy.are_equivalent(res[var],expected[var])
