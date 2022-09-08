#!/usr/bin/env python3

import argparse
import sys
import z3
import time

from functools import reduce
from git import Repo

from noodler.core import is_straightline
from noodler.parser import SmtlibParserHackAbc, EmptyFileException
from noodler.sequery import StringConstraintQuery, AutSingleSEQuery
from noodler.graph_noodler import *
from noodler.graph_formula import StringEqGraph
from noodler.nielsen import Nielsen

from noodler.formula_preprocess import *

def print_result(sat:str, start, args):
    if sat is None:
        if args.csv:
            end = time.time()
            print("time: {0}".format(round(end-start, 2)))
        return

    sat_str = sat
    if args.csv:
        end = time.time()
        print("result: {0}".format(sat_str))
        print("time: {0}".format(round(end-start, 2)))
    else:
        print(sat_str)


def preprocess_conj(cnf, aut, scq, use_min):
    cnf = StringEqGraph.propagate_variables(cnf, aut, scq)
    cnf = StringEqGraph.propagate_eps(cnf, aut, scq)
    cnf, aut = StringEqGraph.reduce_common_sub(cnf, aut)

    cnf = StringEqGraph.reduce_regular_eqs(cnf, aut, use_min)
    cnf = StringEqGraph.reduce_regular_eqs(cnf, aut, use_min)
    cnf, aut = StringEqGraph.reduce_common_sub(cnf, aut)

    cnf = StringEqGraph.propagate_variables(cnf, aut, scq)
    cnf = StringEqGraph.remove_extension(cnf, aut, scq)
    cnf = StringEqGraph.generate_identities(cnf, aut, scq)
    cnf = StringEqGraph.propagate_variables(cnf, aut, scq)
    cnf = StringEqGraph.remove_extension(cnf, aut, scq)
    return cnf, aut


def preprocess_conj_light_ref(pr, scq, use_min):
    pr.propagate_variables()
    pr.propagate_eps()
    pr.reduce_regular_eqs()
    pr.reduce_common_sub()
    pr.reduce_regular_eqs()
    pr.generate_identities()
    pr.propagate_variables()


def preprocess_conj_ref(pr, scq, use_min):
    pr.propagate_variables()
    pr.propagate_eps()
    pr.reduce_regular_eqs()
    pr.reduce_common_sub()
    pr.reduce_regular_eqs()
    pr.reduce_common_sub()
    pr.propagate_variables()
    pr.remove_extension(scq)
    pr.generate_identities()
    pr.propagate_variables()
    pr.remove_extension(scq)
    pr.propagate_variables()

    pr.reduce_common_sub_unique()
    pr.remove_extension(scq)
    pr.generate_identities()
    pr.propagate_variables()
    

    # pr.reduce_common_sub(1)
    # pr.propagate_variables()


def main(args: argparse.Namespace):
    filename = args.filename
    bidi = args.bidi

    if args.version:
        repo = Repo("./")
        commit_hash = repo.git.rev_parse("HEAD")
        print(commit_hash[0:8])
        exit(0)

    start = time.time()

    try:
        smt_parser = SmtlibParserHackAbc(filename)

        q: StringConstraint = smt_parser.parse_query()
        if not q.is_cnf():
            raise Exception("Constraint must be in CNF")

        scq = StringConstraintQuery(q, smt_parser.alphabet_str)
        cnf, aut = scq.get_queries_cnf()

        if not StringEqGraph.check_length_compatible(cnf, aut):
            print_result("unsat", start, args)
            exit(0)

        is_disj: bool = reduce(lambda x,y: x or y, [len(l) > 1 for l in cnf], False)
        is_single_eq: bool = len(cnf) == 1

        pr = FormulaPreprocess(cnf, aut, args.min)
        if not is_disj:
            #cnf, aut = preprocess_conj(cnf, aut, scq, args.min)
            if is_single_eq:
                pr.separate_eqs()
            if args.light:
                preprocess_conj_light_ref(pr, scq, args.min)
            elif not is_single_eq:
                preprocess_conj_ref(pr, scq, args.min)
            
        else:
            pr.propagate_variables()
            pr.reduce_regular_eqs()

        literals = pr.get_literals()
        unique_vars = pr.get_unique_vars()
        cnf, aut = pr.get_cnf(), pr.get_aut_constraint()

        if StringEqGraph.quick_unsat_check(cnf, aut, literals):
            print_result("unsat", start, args)
            exit(0)

        graph = StringEqGraph.get_eqs_graph(cnf)
        graphs = [graph]
        sl = graph.straight_line()
        if sl is not None:
            graphs = [sl]

        if not is_disj:
            graph = StringEqGraph.get_inclusion_graph(cnf)
        if graph.is_acyclic():
            sl = True
            graphs = [graph]
        elif not is_disj and is_single_eq:
            graphs = StringEqGraph.get_conj_graphs_succ(cnf)
        elif not is_disj:
            graph = StringEqGraph.get_eqs_graph_quick_sat(cnf)
            if graph is not None:
                graph.linearize()
                gn: GraphNoodler = GraphNoodler(graph, aut, literals, unique_vars)
                sett: GraphNoodlerSettings = GraphNoodlerSettings(True, StrategyType.DFS, False, False, True, False)
                sat = gn.is_sat(sett)
                if sat:
                    print_result("sat", start, args)
                    exit(0)
            graphs = StringEqGraph.get_conj_graphs_succ(cnf)

    except NotImplementedError:
        print_result("unknown", start, args)
        exit(0)
    except z3.z3types.Z3Exception as e:
        sys.stderr.write("Error during reading the file: {0}\n".format(e))
        exit(4)
    except UnicodeEncodeError:
        sys.stderr.write("Unsupported non-ASCII characters\n")
        exit(4)
    except EmptyFileException:
        print_result(None, start, args)
        exit(0)

    sett: GraphNoodlerSettings = GraphNoodlerSettings()
    sett.balance_check = sl is None
    sett.strategy = StrategyType.BFS if sl is None else StrategyType.DFS
    sett.use_cache = False
    sett.both_side = False
    sett.use_retrieval = False
    sett.prod_pruning = pr.contains_shared_eq()

    for graph in graphs:
        gn: GraphNoodler = GraphNoodler(graph, aut, literals, unique_vars)

        if is_single_eq and len(graph.vertices) == 2 and graph.vertices[0].eq.switched == graph.vertices[1].eq:
            nielsen = Nielsen(graph.vertices[0].eq, aut, literals)
            if nielsen.is_quadratic(scq):
                sat = nielsen.is_sat()
        else:
            sat = gn.is_sat(sett)
        if sat:
            continue
        print_result("unsat", start, args)
        exit(0)

    print_result("sat", start, args)

if __name__ == "__main__":
    description = """Solves SAT problem for string constraints."""

    # TODO add helper texts.
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--parse_only", action="store_true")
    parser.add_argument("--propagate-vars", action="store_true")
    parser.add_argument("--bidi", action="store_true")
    parser.add_argument("--version", action="store_true")
    parser.add_argument("filename", type=str, nargs="?")
    parser.add_argument("--csv", action="store_true")
    parser.add_argument("--min", action="store_true")
    parser.add_argument("--light", action="store_true")

    args = parser.parse_args()
    main(args)
