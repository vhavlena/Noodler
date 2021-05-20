import os
import pytest

import awalipy
import z3

from noodler.core import RE, is_straightline
from noodler.parser import smt2_to_query, SmtlibParserHackAbc, translate_for_awali

SLOG_PREFIX = "slog_stranger"
SLOG_SUFFIX = "sink.smt2"
SLOG_DIR = "../benchmarks/slog"
NOREPLACE_LIST = "noreplace_noor.files"


def pytest_generate_tests(metafunc):
    if "noreplace_parsers" in metafunc.fixturenames:
        with open(os.path.join(SLOG_DIR, NOREPLACE_LIST)) as f:
            files = f.read().splitlines()
        paths = [os.path.join(SLOG_DIR, file) for file in files]
        parsers = [SmtlibParserHackAbc(file) for file in paths]
        metafunc.parametrize("noreplace_parsers",
                             parsers,
                             ids=files)


def are_re_equivalent(re1: RE, re2: RE):
    return awalipy.are_equivalent(re1.exp_to_aut(),
                                  re2.exp_to_aut())


def get_bench_file(n):
    if isinstance(n, str):
        n = n.strip()
    return os.path.join(SLOG_DIR,
                        f"{SLOG_PREFIX}_{n}_{SLOG_SUFFIX}")


@pytest.fixture
def f1001():
    return get_bench_file(1001)


@pytest.fixture
def p1001(f1001):
    return SmtlibParserHackAbc(f1001)


def get_parser(filename):
    return SmtlibParserHackAbc(filename)


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
