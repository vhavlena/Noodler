"""
Generate parsers of smt2 files for test cases.

The function ``pytest_generate_tests`` can be imported in a test file
to provide a parametrized fixture `noreplace_parsers` that allows to execute
a test on each filename stored in ``NOREPLACE_LIST`` in the ``SLOG_DIR``.
The intended use is as follows:

>>> from generate_parsers import pytest_generate_tests
>>>
>>> def test_func_on_parsed_smt(noreplace_parsers):
>>>   func(noreplace_parsers)

The test-case above (function `func`) will be executed as a seperate
test for each benchmark from the ``NOREPLACE_LIST`` file.

Fixtures ``p1001`` and ``p1013`` contain 2 concrete instances of parsers
for benchmarks with ids `1001` and `1013`.
"""

import os
import pytest

from noodler import SmtlibParserHackAbc

# Directory with straight-line fragment benchmarks (SLOG)
SLOG_DIR = "../benchmarks/slog"

# File with all slog-benchmarks without `replace` and `or` operators.
NOREPLACE_LIST = "noreplace_noor.files"

# Parts of SLOG-benchmarks names
SLOG_PREFIX = "slog_stranger"
SLOG_SUFFIX = "sink.smt2"


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

@pytest.fixture
def p164():
    """Runs long with propagate constraints"""
    return SmtlibParserHackAbc(get_bench_file(164))

@pytest.fixture
def long():
    return SmtlibParserHackAbc(get_bench_file(2959))
