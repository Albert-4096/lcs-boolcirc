#!/usr/bin/env python3
"""
boolcirc.py - Homework 4, exercises 6 and 7 (Logic for Computer Science).

  Exercise 6:  truth function  ->  propositional formula
               (the construction from Theorem 4.1 in the lecture notes:
                one conjunction per row where the function returns T,
                then the disjunction of these conjunctions)

  Exercise 7:  propositional formula  ->  logically equivalent, cheaper formula
               by replacing subformulas with logically equivalent ones
               (absorption, complement, double negation, adjacency,
                factoring by distributivity, De Morgan, ...).
               Every rewrite step is printed with the name of the rule.
               At the end the program checks with a truth table that the
               result is logically equivalent to the input.

Usage
  python3 boolcirc.py tt   --vars A,B,C --ones 2,3,5,7     # rows given as numbers
  python3 boolcirc.py tt   --vars A,B,C --column 00110101  # output column, row 000 first
  python3 boolcirc.py simp "(~A & B & ~C) | (~A & B & C) | (A & ~B & C) | (A & B & C)"
  python3 boolcirc.py tt   --vars A,B,C --ones 2,3,5,7 --simplify

Formula syntax (Unicode or ASCII):
  ¬ ~ !        negation          ∧ & *        conjunction
  ∨ | +        disjunction       ⇒ -> =>      implication
  ⇔ <-> <=>    equivalence       ⊤ 1 / ⊥ 0    constants
  Variables: a letter followed by letters or digits (A, B, Cin, P1).
  Precedence (strongest first): ¬, ∧, ∨, ⇒, ⇔.

Only the Python standard library is used (Python 3.8+).
"""

import argparse
import heapq
import itertools
import re
import sys

# ---------------------------------------------------------------- formulas --
# A formula is a tuple:
#   ("var", name)  ("const", True|False)  ("not", F)
#   ("and", (F1, ..., Fk))  ("or", (F1, ..., Fk))      k >= 2
# Conjunctions and disjunctions are kept flat, without duplicates and with
# the arguments sorted.  This builds in associativity, commutativity and
# idempotence, so two formulas that differ only by these rules are equal.

TOP = ("const", True)
BOT = ("const", False)


def var(name):
    return ("var", name)


def neg(f):
    return ("not", f)


def _nary(op, args):
    unit, zero = (TOP, BOT) if op == "and" else (BOT, TOP)
    flat = []
    for a in args:
        if a[0] == op:
            flat.extend(a[1])
        else:
            flat.append(a)
    if zero in flat:
        return zero                       # F ∧ ⊥ ∼ ⊥,  F ∨ ⊤ ∼ ⊤
    flat = sorted(set(a for a in flat if a != unit), key=sort_key)  # F ∧ ⊤ ∼ F
    if not flat:
        return unit
    if len(flat) == 1:
        return flat[0]
    return (op, tuple(flat))


def conj(*args):
    return _nary("and", args)


def disj(*args):
    return _nary("or", args)


def sort_key(f):
    return (variables_key(f), show(f))


def variables_key(f):
    return sorted(variables(f))


def variables(f):
    if f[0] == "var":
        return {f[1]}
    if f[0] == "const":
        return set()
    if f[0] == "not":
        return variables(f[1])
    return set().union(*(variables(a) for a in f[1]))


def evaluate(f, env):
    tag = f[0]
    if tag == "var":
        return env[f[1]]
    if tag == "const":
        return f[1]
    if tag == "not":
        return not evaluate(f[1], env)
    if tag == "and":
        return all(evaluate(a, env) for a in f[1])
    return any(evaluate(a, env) for a in f[1])


# ----------------------------------------------------------------- printing --

SYMBOLS = {
    "unicode": {"not": "¬", "and": " ∧ ", "or": " ∨ ", True: "⊤", False: "⊥"},
    "ascii": {"not": "~", "and": " & ", "or": " | ", True: "1", False: "0"},
}
STYLE = "unicode"
PREC = {"or": 1, "and": 2, "not": 3, "var": 4, "const": 4}


def show(f, parent=0):
    s = SYMBOLS[STYLE]
    tag = f[0]
    if tag == "var":
        return f[1]
    if tag == "const":
        return s[f[1]]
    if tag == "not":
        return s["not"] + show(f[1], PREC["not"])
    text = s[tag].join(show(a, PREC[tag]) for a in f[1])
    # an AND/OR inside another AND/OR always gets parentheses (easier to read)
    return "(" + text + ")" if parent in (PREC["or"], PREC["and"], PREC["not"]) else text


# ------------------------------------------------------------------ parsing --

TOKEN = re.compile(r"\s*(<->|<=>|->|=>|[A-Za-z][A-Za-z0-9_]*|[01()¬~!∧&*∨|+⇒⇔⊤⊥])")


def tokenize(text):
    pos, out = 0, []
    text = text.strip()
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise SyntaxError(f"unexpected symbol at position {pos}: {text[pos:]!r}")
        out.append(m.group(1))
        pos = m.end()
        while pos < len(text) and text[pos].isspace():
            pos += 1
    return out


def parse(text):
    tokens = tokenize(text)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def take():
        nonlocal pos
        pos += 1
        return tokens[pos - 1]

    def p_iff():
        left = p_imp()
        while peek() in ("⇔", "<->", "<=>"):
            take()
            right = p_imp()
            # F ⇔ G  ∼  (¬F ∨ G) ∧ (F ∨ ¬G)
            left = conj(disj(neg(left), right), disj(left, neg(right)))
        return left

    def p_imp():
        left = p_or()
        if peek() in ("⇒", "->", "=>"):
            take()
            right = p_imp()                      # right associative
            left = disj(neg(left), right)        # F ⇒ G  ∼  ¬F ∨ G
        return left

    def p_or():
        args = [p_and()]
        while peek() in ("∨", "|", "+"):
            take()
            args.append(p_and())
        return disj(*args) if len(args) > 1 else args[0]

    def p_and():
        args = [p_not()]
        while peek() in ("∧", "&", "*"):
            take()
            args.append(p_not())
        return conj(*args) if len(args) > 1 else args[0]

    def p_not():
        if peek() in ("¬", "~", "!"):
            take()
            return neg(p_not())
        return p_atom()

    def p_atom():
        t = take() if peek() is not None else None
        if t == "(":
            f = p_iff()
            if peek() != ")":
                raise SyntaxError("missing ')'")
            take()
            return f
        if t in ("⊤", "1"):
            return TOP
        if t in ("⊥", "0"):
            return BOT
        if t and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", t):
            return var(t)
        raise SyntaxError(f"unexpected token {t!r}")

    f = p_iff()
    if pos != len(tokens):
        raise SyntaxError(f"unexpected token {tokens[pos]!r}")
    return f


# ------------------------------------------------- exercise 6: truth function --

def rows(names):
    """All interpretations, in the order 0...0, 0...01, ..., 1...1 (first variable = MSB)."""
    for bits in itertools.product([False, True], repeat=len(names)):
        yield dict(zip(names, bits))


def formula_of_truth_function(names, ones):
    """Theorem 4.1: disjunction of one conjunction C_{a1..an} per row with value T."""
    terms = []
    for number in sorted(ones):
        bits = [(number >> (len(names) - 1 - i)) & 1 for i in range(len(names))]
        literals = [var(n) if b else neg(var(n)) for n, b in zip(names, bits)]
        terms.append(conj(*literals))
    return disj(*terms) if terms else BOT


def truth_table_text(names, values, label="f"):
    head = " ".join(names) + " | " + label
    lines = [head, "-" * len(head)]
    for number, env in enumerate(rows(names)):
        bits = " ".join(("T" if env[n] else "F").center(len(n)) for n in names)
        lines.append(f"{bits} | {'T' if values[number] else 'F'}   (row {number})")
    return "\n".join(lines)


# ------------------------------------------------------ exercise 7: rewriting --

def literals_of(term):
    return list(term[1]) if term[0] == "and" else [term]


def disjuncts_of(term):
    return list(term[1]) if term[0] == "or" else [term]


def complement(lit):
    return lit[1] if lit[0] == "not" else neg(lit)


def rules_at(f):
    """All one-step rewrites of the root of f: list of (rule name, new formula)."""
    out = []
    tag = f[0]

    if tag == "not":
        g = f[1]
        if g[0] == "not":
            out.append(("double negation  ¬¬F ∼ F", g[1]))
        if g[0] == "const":
            out.append(("¬⊤ ∼ ⊥, ¬⊥ ∼ ⊤", ("const", not g[1])))
        if g[0] == "and":
            out.append(("De Morgan  ¬(F ∧ G) ∼ ¬F ∨ ¬G", disj(*(neg(a) for a in g[1]))))
        if g[0] == "or":
            out.append(("De Morgan  ¬(F ∨ G) ∼ ¬F ∧ ¬G", conj(*(neg(a) for a in g[1]))))
        return out

    if tag not in ("and", "or"):
        return out

    args = list(f[1])
    other = "or" if tag == "and" else "and"
    sym = "∧" if tag == "and" else "∨"
    osym = "∨" if tag == "and" else "∧"
    unit_name = "⊥" if tag == "and" else "⊤"
    pieces = literals_of if tag == "or" else disjuncts_of     # parts of an argument
    join_inner = conj if tag == "or" else disj
    join_outer = disj if tag == "or" else conj

    # complement:  F ∧ ¬F ∼ ⊥,  F ∨ ¬F ∼ ⊤
    for a in args:
        if neg(a) in args:
            out.append((f"complement  F {sym} ¬F ∼ {unit_name}",
                        BOT if tag == "and" else TOP))
            break

    # absorption:  F ∨ (F ∧ G) ∼ F,   F ∧ (F ∨ G) ∼ F
    for i, a in enumerate(args):
        pa = set(pieces(a))
        for j, b in enumerate(args):
            if i != j and pa < set(pieces(b)):
                rest = [x for k, x in enumerate(args) if k != j]
                out.append((f"absorption  F {sym} (F {osym} G) ∼ F", join_outer(*rest)))

    # adjacency:  (F ∧ L) ∨ (F ∧ ¬L) ∼ F  (and the dual)
    # "keep" variant: add the merged term and keep both, so a term can be
    # used in two merges; absorption removes the covered terms afterwards.
    for i, j in itertools.combinations(range(len(args)), 2):
        pa, pb = set(pieces(args[i])), set(pieces(args[j]))
        diff_a, diff_b = pa - pb, pb - pa
        if len(diff_a) == 1 and len(diff_b) == 1:
            (la,), (lb,) = diff_a, diff_b
            if complement(la) == lb:
                merged = join_inner(*(pa & pb))
                rest = [x for k, x in enumerate(args) if k not in (i, j)]
                out.append((f"adjacency  (F {osym} L) {sym} (F {osym} ¬L) ∼ F",
                            join_outer(merged, *rest)))
                out.append((f"adjacency, keeping both terms  (idempotence + adjacency)",
                            join_outer(merged, *args)))

    # simplification:  F ∨ (¬F ∧ G) ∼ F ∨ G   (and the dual)
    for i, a in enumerate(args):
        for j, b in enumerate(args):
            if i != j and complement(a) in pieces(b):
                reduced = join_inner(*(p for p in pieces(b) if p != complement(a)))
                rest = [x for k, x in enumerate(args) if k != j]
                out.append((f"F {sym} (¬F {osym} G) ∼ F {sym} G", join_outer(reduced, *rest)))

    # factoring (distributivity read from right to left):
    #   (F ∧ G) ∨ (F ∧ H) ∼ F ∧ (G ∨ H)     and the dual
    common_candidates = set()
    for a in args:
        common_candidates.update(pieces(a))
    for c in common_candidates:
        having = [a for a in args if c in pieces(a)]
        if len(having) < 2:
            continue
        rest = [a for a in args if c not in pieces(a)]
        inner = join_outer(*(join_inner(*(p for p in pieces(a) if p != c)) for a in having))
        factored = join_inner(c, inner)
        out.append((f"distributivity  (F {osym} G) {sym} (F {osym} H) ∼ F {osym} (G {sym} H)",
                    join_outer(factored, *rest)))

    # De Morgan read from right to left: pull a negation out of several negated arguments
    negated = [a for a in args if a[0] == "not"]
    if len(negated) >= 2:
        rest = [a for a in args if a[0] != "not"]
        pulled = neg(_nary(other, [a[1] for a in negated]))
        name = ("De Morgan  ¬F ∨ ¬G ∼ ¬(F ∧ G)" if tag == "or"
                else "De Morgan  ¬F ∧ ¬G ∼ ¬(F ∨ G)")
        out.append((name, join_outer(pulled, *rest)))

    return out


def rewrites(f):
    """All formulas obtained by one rewrite at any position of f."""
    for name, g in rules_at(f):
        yield name, g
    if f[0] == "not":
        for name, g in rewrites(f[1]):
            yield name, neg(g)
    elif f[0] in ("and", "or"):
        args = list(f[1])
        for i, a in enumerate(args):
            for name, g in rewrites(a):
                yield name, _nary(f[0], args[:i] + [g] + args[i + 1:])


def gates(f):
    """Number of NOT and binary AND/OR gates; equal subformulas are built once."""
    seen = set()

    def walk(g):
        if g in seen or g[0] in ("var", "const"):
            return 0
        seen.add(g)
        if g[0] == "not":
            return 1 + walk(g[1])
        return (len(g[1]) - 1) + sum(walk(a) for a in g[1])

    return walk(f)


def size(f):
    if f[0] in ("var", "const"):
        return 1
    if f[0] == "not":
        return 1 + size(f[1])
    return 1 + sum(size(a) for a in f[1])


def simplify(f, budget=20000):
    """Best-first search over rewrites; returns the cheapest formula and its steps."""
    start = f
    best = start
    parent = {start: None}
    frontier = [(gates(start), size(start), 0, start)]
    counter = itertools.count(1)
    expanded = 0
    while frontier and expanded < budget:
        _, _, _, g = heapq.heappop(frontier)
        expanded += 1
        if (gates(g), size(g)) < (gates(best), size(best)):
            best = g
        for name, h in rewrites(g):
            if h not in parent and size(h) <= 2 * size(start) + 4:
                parent[h] = (g, name)
                heapq.heappush(frontier, (gates(h), size(h), next(counter), h))
    steps = []
    g = best
    while parent[g] is not None:
        prev, name = parent[g]
        steps.append((name, g))
        g = prev
    return best, list(reversed(steps))


def equivalent(f, g):
    names = sorted(variables(f) | variables(g))
    return all(evaluate(f, env) == evaluate(g, env) for env in rows(names))


def report_simplification(f):
    print(f"Input:   {show(f)}")
    print(f"         {gates(f)} gates (NOT and binary AND/OR)\n")
    best, steps = simplify(f)
    for k, (name, g) in enumerate(steps, 1):
        print(f"  ({k}) ∼ {show(g)}")
        print(f"        by {name};  {gates(g)} gates")
    print(f"\nResult:  {show(best)}")
    print(f"         {gates(best)} gates")
    print("Check:   the result is logically equivalent to the input "
          f"(truth table): {'yes' if equivalent(f, best) else 'NO'}")
    return best


# --------------------------------------------------------------------- main --

def main(argv=None):
    global STYLE
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ascii", action="store_true", help="print ~ & | instead of ¬ ∧ ∨")
    sub = ap.add_subparsers(dest="cmd", required=True)

    tt = sub.add_parser("tt", help="exercise 6: truth function -> formula")
    tt.add_argument("--vars", required=True, help="variable names, first = most significant bit")
    group = tt.add_mutually_exclusive_group(required=True)
    group.add_argument("--ones", help="row numbers where the function is T, e.g. 2,3,5,7")
    group.add_argument("--column", help="output column as 0/1 (or F/T), row 0...0 first")
    tt.add_argument("--simplify", action="store_true", help="also run exercise 7 on the result")

    sp = sub.add_parser("simp", help="exercise 7: simplify a formula")
    sp.add_argument("formula")

    args = ap.parse_args(argv)
    if args.ascii:
        STYLE = "ascii"

    if args.cmd == "tt":
        names = [n.strip() for n in args.vars.split(",") if n.strip()]
        n_rows = 2 ** len(names)
        if args.ones is not None:
            ones = {int(x) for x in args.ones.split(",") if x.strip()}
        else:
            col = args.column.upper().replace("T", "1").replace("F", "0")
            if len(col) != n_rows or set(col) - {"0", "1"}:
                ap.error(f"--column needs exactly {n_rows} symbols 0/1")
            ones = {i for i, c in enumerate(col) if c == "1"}
        if any(not 0 <= o < n_rows for o in ones):
            ap.error(f"row numbers must be between 0 and {n_rows - 1}")
        values = [i in ones for i in range(n_rows)]
        print(truth_table_text(names, values))
        f = formula_of_truth_function(names, ones)
        print(f"\nRows with value T: {sorted(ones)}")
        print(f"Formula (Theorem 4.1): {show(f)}")
        ok = all(evaluate(f, env) == values[i] for i, env in enumerate(rows(names)))
        print(f"Check: the formula describes the truth function: {'yes' if ok else 'NO'}")
        if args.simplify:
            print("\nSimplification (exercise 7)\n")
            report_simplification(f)
    else:
        report_simplification(parse(args.formula))


if __name__ == "__main__":
    sys.exit(main())
