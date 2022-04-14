#!/usr/bin/env python3

import argparse
import sys
import z3

from functools import reduce
from git import Repo

from noodler.core import is_straightline
from noodler.parser import SmtlibParserHackAbc
from noodler.noodler import StraightlineNoodleMachine, QueueNoodler
from noodler.sequery import StringConstraintQuery, AutSingleSEQuery
from noodler.graph_noodler import *
from noodler.graph_formula import StringEqGraph


def main(args: argparse.Namespace):
    filename = args.filename
    bidi = args.bidi

    if args.version:
        repo = Repo("./")
        commit_hash = repo.git.rev_parse("HEAD")
        print(commit_hash[0:8])
        exit(0)


    try:
        smt_parser = SmtlibParserHackAbc(filename)

        q: StringConstraint = smt_parser.parse_query()
        if not q.is_cnf():
            raise Exception("Constraint must be in CNF")

        scq = StringConstraintQuery(q, smt_parser.alphabet_str)
        cnf, aut = scq.get_queries_cnf()

        if not StringEqGraph.check_length_compatible(cnf, aut):
            print("unsat")
            exit(0)

        is_disj: bool = reduce(lambda x,y: x or y, [len(l) > 1 for l in cnf], False)

        if not is_disj:
            cnf, aut = StringEqGraph.reduce_common_sub(cnf, aut)

        cnf = StringEqGraph.reduce_regular_eqs(cnf, aut)
        graph = StringEqGraph.get_eqs_graph(cnf)

        sl = graph.straight_line()
        if sl is not None:
            graph = sl
        elif not is_disj:
            graph = StringEqGraph.get_eqs_graph_quick_sat(cnf)
            if graph is not None:
                graph.linearize()
                gn: GraphNoodler = GraphNoodler(graph, aut)
                sett: GraphNoodlerSettings = GraphNoodlerSettings(True, StrategyType.BFS, False, True)
                sat = gn.is_sat(sett)
                if sat:
                    print("sat")
                    exit(0)
            graph = StringEqGraph.get_eqs_graph_ring(cnf)

    except NotImplementedError:
        sys.stdout.write("unknown\n")
        exit(0)
    except z3.z3types.Z3Exception:
        sys.stderr.write("Error during reading the file\n")
        exit(4)

    gn: GraphNoodler = GraphNoodler(graph, aut)
    sett: GraphNoodlerSettings = GraphNoodlerSettings()
    sett.balance_check = sl is None
    sett.strategy = StrategyType.BFS if sl is None else StrategyType.DFS
    sett.use_cache = False
    sett.both_side = False

    sat = gn.is_sat(sett)

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
    parser.add_argument("--version", action="store_true")
    parser.add_argument("filename", type=str, nargs="?")

    args = parser.parse_args()
    main(args)
