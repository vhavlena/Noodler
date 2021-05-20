import os
import pytest

import awalipy
import z3

from noodler.core import RE, is_straightline
from noodler.parser import smt2_to_query, SmtlibParserHackAbc, translate_for_awali
from generate_parsers import pytest_generate_tests, f1001, p1001


def are_re_equivalent(re1: RE, re2: RE):
    return awalipy.are_equivalent(re1.exp_to_aut(),
                                  re2.exp_to_aut())


@pytest.fixture
def simple_re():
    return z3.Concat(z3.Re("a"), z3.Re("b"))


def test_smt2_to_query(f1001):
    smt2_to_query(f1001)


class TestParser:
    # @pytest.fixture(scope="session")
    # def filenames_file_h(self):
    #     f_h = open("../benchmarks/slog/noreplace_noor.files", "w")
    #     yield f_h
    #     f_h.close()

    def test_alphabet_1001(self, p1001):
        # From equation
        res = {'<', 'b', 'r', ' ', '/', '>'}
        # From RE
        res.update({'\\', '<', 'S', 'C', 'R', 'I', 'P', 'T'})
        res = {translate_for_awali(c) for c in res}
        assert p1001.alphabet == res

    def test_variables_1001(self, p1001):
        assert p1001.variables == {"literal_1"}

    def test_re_to_awali_1001(self, p1001):
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

    def test_parse_query_1001(self, p1001):
        p1001.parse_query()
        assert 'literal_1' in p1001.constraints
        # assert 'literal_1' in p1001.parse_query().aut_constraints

    def test_all_noreplace_files_straightline(self, noreplace_parsers: SmtlibParserHackAbc):
        query = noreplace_parsers.parse_query()
        # filenames_file_h.write(os.path.basename(noreplace_parsers.filename)+"\n")
        assert is_straightline(query.equations)