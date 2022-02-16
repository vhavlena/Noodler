#!/usr/bin/env python3

import argparse
import sys
import z3

from noodler.core import is_straightline
from noodler.parser import SmtlibParserHackAbc
from noodler.noodler import StraightlineNoodleMachine, QueueNoodler
from noodler.sequery import StringConstraintQuery, AutSingleSEQuery
from noodler.graph_noodler import GraphNoodler
from noodler.graph_formula import StringEqGraph


def main(args: argparse.Namespace):
    filename = args.filename
    bidi = args.bidi

    try:
        smt_parser = SmtlibParserHackAbc(filename)

        q: StringConstraint = smt_parser.parse_query()
        if not q.is_cnf():
            raise Exception("Constraint must be in CNF")

        scq = StringConstraintQuery(q, smt_parser.alphabet_str)
        cnf, aut = scq.get_queries_cnf()
        cnf = StringEqGraph.reduce_regular_eqs(cnf, aut)

        graph = StringEqGraph.get_eqs_graph(cnf)

        sl = graph.straight_line()
        if sl is not None:
            graph = sl

    except NotImplementedError:
        sys.stderr.write("unknown\n")
        exit(5)
    except z3.z3types.Z3Exception:
        sys.stderr.write("Error during reading the file\n")
        exit(4)

    gn: GraphNoodler = GraphNoodler(graph, aut)
    sat = gn.is_sat(sl is not None)

    if sat:
        print("sat")
    else:
        print("unsat")


if __name__ == "__main__":
    description = """Solves SAT problem for string constraints."""

    # TODO add helper texts.
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--parse_only", action="store_true")
    parser.add_argument("--propagate-vars", action="store_true")
    parser.add_argument("--bidi", action="store_true")
    parser.add_argument("filename", type=str)

    args = parser.parse_args()
    main(args)
