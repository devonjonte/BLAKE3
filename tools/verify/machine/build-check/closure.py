#!/usr/bin/env python3
"""Everything a theorem's statement rests on, from Lean's export (a prototype of what the build does).

    closure.py EXPORT.ndjson THEOREM > names.txt

From the theorem's type: every constant it names, and in turn every constant those rest on: a
definition's type and body, an axiom's or theorem's or opaque constant's type, and an inductive type
whole (its types, constructors, recursors and their rules). No proof is followed.
"""
import json, sys

names, kids, consts, decl, block = {0: ""}, {}, {}, {}, {}
with open(sys.argv[1]) as f:
    for line in f:
        o = json.loads(line)
        if "in" in o:
            if "str" in o: pre, s = o["str"]["pre"], o["str"]["str"]
            else: pre, s = o["num"]["pre"], str(o["num"]["i"])
            names[o["in"]] = (names[pre] + "." if names[pre] else "") + s
        elif "ie" in o:
            i = o["ie"]; k, c = [], []
            if "app" in o: k = [o["app"]["fn"], o["app"]["arg"]]
            elif "lam" in o: k = [o["lam"]["type"], o["lam"]["body"]]
            elif "forallE" in o: k = [o["forallE"]["type"], o["forallE"]["body"]]
            elif "letE" in o: k = [o["letE"]["type"], o["letE"]["value"], o["letE"]["body"]]
            elif "proj" in o: k = [o["proj"]["struct"]]; c = [o["proj"]["typeName"]]
            elif "mdata" in o: k = [o["mdata"]["expr"]]
            elif "const" in o: c = [o["const"]["name"]]
            kids[i], consts[i] = k, c
        elif "axiom" in o: decl[o["axiom"]["name"]] = ([o["axiom"]["type"]], [])
        elif "def" in o: decl[o["def"]["name"]] = ([o["def"]["type"], o["def"]["value"]], [])
        elif "opaque" in o: decl[o["opaque"]["name"]] = ([o["opaque"]["type"]], [])
        elif "thm" in o: decl[o["thm"]["name"]] = ([o["thm"]["type"]], [])
        elif "quot" in o: decl[o["quot"]["name"]] = ([o["quot"]["type"]], [])
        elif "inductive" in o:
            b = o["inductive"]
            members = [t["name"] for t in b["types"]] + [c["name"] for c in b["ctors"]] + [r["name"] for r in b["recs"]]
            exprs = [t["type"] for t in b["types"]] + [c["type"] for c in b["ctors"]] + [r["type"] for r in b["recs"]] + \
                    [rule["rhs"] for r in b["recs"] for rule in r["rules"]]
            for m in members: decl[m] = (exprs, members)

def of_expr(root, seen_e, out):
    stack = [root]
    while stack:
        e = stack.pop()
        if e in seen_e: continue
        seen_e.add(e)
        out.extend(consts[e]); stack.extend(kids[e])

theorem = next(i for i, n in names.items() if n == sys.argv[2])
seen_e, seen, todo = set(), set(), []
of_expr(decl[theorem][0][0], seen_e, todo)
while todo:
    c = todo.pop()
    if c in seen: continue
    seen.add(c)
    exprs, members = decl[c]
    todo.extend(members)
    for e in exprs: of_expr(e, seen_e, todo)
for n in sorted(names[c] for c in seen): print(n)
