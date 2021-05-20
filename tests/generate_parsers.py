import os
import pytest

from noodler.parser import SmtlibParserHackAbc

NOREPLACE_LIST = "noreplace_noor.files"
SLOG_PREFIX = "slog_stranger"
SLOG_SUFFIX = "sink.smt2"
SLOG_DIR = "../benchmarks/slog"


def pytest_generate_tests(metafunc):
    if "noreplace_parsers" in metafunc.fixturenames:
        with open(os.path.join(SLOG_DIR, NOREPLACE_LIST)) as f:
            files = f.read().splitlines()
        paths = [os.path.join(SLOG_DIR, file) for file in files]
        # files=[1001]
        # paths = [get_bench_file(1001)]
        parsers = [SmtlibParserHackAbc(file) for file in paths]
        metafunc.parametrize("noreplace_parsers",
                             parsers,
                             ids=files)


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


@pytest.fixture
def p1013():
    return SmtlibParserHackAbc(get_bench_file(1013))
