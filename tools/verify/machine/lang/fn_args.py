#!/usr/bin/env python3
"""What the tools that follow the compiler are told about a function's calls, from the source.

    fn_args.py lift SOURCE NAME     the lifter's `--call SYMBOL=ADDRESS` for each function called by contract
    fn_args.py code SOURCE NAME     gen_code.py's `--with OTHER[+k]` for each callee whose instructions are in
                                    the program (the kernels' first), and `--ext` if a callee is assumed
    fn_args.py standins SOURCE NAME the Code modules of the functions that stand in for assumed kernels when
                                    the examples run
(prove_fn.sh and mutants_code.py both ask here, so that they cannot differ.)"""
import os, sys
import odec


def calls_of(source, name):
    text = open(source).read()
    clauses = odec.contracts_of(text)[0]
    return clauses, list(dict.fromkeys(x["callee"] for x in clauses[name].get("calls", [])))


def lift_args(source, name):
    clauses, ns = calls_of(source, name)
    P = odec.Parser(odec.tokens(odec.kernels(odec.contracts_of(open(source).read())[2])[0])); P.top()
    sym = lambda n: P.externs[n][0] if n in P.externs else f"b3l_{n}"
    return [x for n in ns for x in ("--call", f"{sym(n)}={hex(odec.own[n]['at'])}")]


def code_args(source, name, where="."):
    clauses, ns = calls_of(source, name)
    codes = list(dict.fromkeys(odec.own[n]["code"] for n in ns if odec.own[n]["code"]))
    has_k = lambda n: "import KCode" in open(os.path.join(where, f"Code_{n}.lean")).read()
    codes.sort(key=lambda n: not has_k(n))
    return [x for n in codes for x in ("--with", n + ("+k" if has_k(n) else ""))] + (["--ext"] if any(odec.own[n]["theorem"] is None for n in ns) else [])


def standins(source, name):
    """The functions of ours that stand in, when examples run, for the assumed kernels `name` reaches."""
    clauses, _ = calls_of(source, name)
    return [odec.own[c]["standin"] for c in odec.assumed_of(clauses, name) if odec.own[c].get("standin")]


if __name__ == "__main__":
    what, source, name = sys.argv[1:4]
    print(" ".join(lift_args(source, name) if what == "lift" else [f"Code_{s}" for s in standins(source, name)] if what == "standins" else code_args(source, name)))
