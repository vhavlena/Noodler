import os
from typing import Set

import pytest

import awalipy
import z3

# Noodler imports
from noodler.core import RE, is_straightline
from noodler.parser import SmtlibParserHackAbc, translate_for_awali

# Import test cases
from generate_parsers import pytest_generate_tests, f1001, p1001, p1013


def are_re_equivalent(re1: RE, re2: RE):
    return awalipy.are_equivalent(re1.exp_to_aut(),
                                  re2.exp_to_aut())


@pytest.fixture
def simple_re():
    return z3.Concat(z3.Re("a"), z3.Re("b"))


def variables_from_smt(filename) -> Set[str]:
    """
    Extract variables declared in smt2 format as uninterpreted functions

    Parameters
    ----------
    filename: str

    Returns
    -------
    Set[str] set of variable names.

    Notes
    -----
    Not all variables declared must be used in queries.
    """
    with open(filename) as f:
        lines = f.readlines()

    return {l.split()[1] for l in lines if "declare-fun" in l}


class TestParser:

    def test_alphabet_1001(self, p1001):
        # From equation
        res = {'<', 'b', 'r', ' ', '/', '>'}
        # From RE
        res.update({'\\', '<', 'S', 'C', 'R', 'I', 'P', 'T'})
        res = {translate_for_awali(c) for c in res}
        assert p1001.alphabet == res

    def test_variables_1001(self, p1001):
        assert p1001.variables == {"literal_1"}

    def test_parse_query_1001(self, p1001):
        p1001.parse_query()
        assert 'literal_1' in p1001.constraints

    def test_re_to_awali_1001(self, p1001):
        """
        Test if the conversion is successful.

        Problems might arise through unimplemented operators or
        non-valid characters.
        """
        re1 = p1001.assertions[1].children()[1]
        p1001.z3_re_to_awali(re1)

    def test_process_re_constraint_1001(self, p1001):
        constr = p1001.parse_re_constraint(p1001.assertions[1])
        re = constr['literal_1']
        assert re.is_valid()

        res_str_1 = "(S+\\+\x19+r+T+\x17+b+R+I+C+\x18+P+/+\x1a)*"
        res_str_2 = "(\\\x18SCRIPT(S+\\+\x19+r+T+\x17+b+R+I+C+\x18+P+/+\x1a)*"
        res_re = awalipy.RatExp(res_str_1).mult(awalipy.RatExp(res_str_2))
        assert are_re_equivalent(res_re, re)

    def test_variables(self, p1013: SmtlibParserHackAbc):
        """
        All variables declared in this file are used in assertions.
        """
        assert p1013.variables == variables_from_smt(p1013.filename)

    def test_all_noreplace_files_straightline(self, noreplace_parsers: SmtlibParserHackAbc):
        """
        Test that all benchmarks passed by noreplace_parsers are from the straightline fragment.
        """
        query = noreplace_parsers.parse_query()
        assert is_straightline(query.equations)