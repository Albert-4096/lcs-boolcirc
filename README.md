# boolcirc

Logic for Computer Science, Homework 4, exercises 6 and 7.

- **Exercise 6:** truth function → propositional formula (Theorem 4.1 of the
  lecture notes: one conjunction per row where the function returns T, then the
  disjunction of these conjunctions).
- **Exercise 7:** formula → logically equivalent formula with fewer gates, by
  replacing subformulas with logically equivalent ones. Each step is printed with
  the name of the rule. At the end, a truth table checks that the result is
  equivalent to the input.

## Install

You need Python 3.8 or newer. There are no other dependencies.

```sh
git clone https://github.com/Albert-4096/lcs-boolcirc.git
cd lcs-boolcirc
python3 boolcirc.py --help
```

## Use

### Exercise 6: truth function → formula

Give the variable names (the first one is the most significant bit) and the
function, as the rows where it is T or as its output column (row `0…0` first):

```sh
python3 boolcirc.py tt --vars A,B,C --ones 2,3,5,7      # "prime" on 3 bits
python3 boolcirc.py tt --vars A,B,Cin --column 00010111 # carry of a full adder
```

The program prints the truth table, the formula, and a check that the formula
describes the function. Add `--simplify` to also run exercise 7 on the formula.

### Exercise 7: simplify a formula

```sh
python3 boolcirc.py simp "(~A & B & ~C) | (~A & B & C) | (A & ~B & C) | (A & B & C)"
python3 boolcirc.py simp "(P => Q) & (Q <-> ~P)"
```

Example output:

```
Input:   (A ∧ B ∧ C) ∨ (A ∧ ¬B ∧ C) ∨ (¬A ∧ B ∧ C) ∨ (¬A ∧ B ∧ ¬C)
         14 gates (NOT and binary AND/OR)

  (1) ∼ (¬A ∧ B) ∨ (A ∧ B ∧ C) ∨ (A ∧ ¬B ∧ C)
        by adjacency  (F ∧ L) ∨ (F ∧ ¬L) ∼ F;  9 gates
  (2) ∼ (¬A ∧ B) ∨ (A ∧ C)
        by adjacency  (F ∧ L) ∨ (F ∧ ¬L) ∼ F;  4 gates

Result:  (¬A ∧ B) ∨ (A ∧ C)
         4 gates
Check:   the result is logically equivalent to the input (truth table): yes
```

Use `--ascii` before the command (`python3 boolcirc.py --ascii simp ...`) to
print `~ & |` instead of `¬ ∧ ∨`.

### Formula syntax

| Connective  | You can type      |
|-------------|-------------------|
| ¬           | `¬` `~` `!`       |
| ∧           | `∧` `&` `*`       |
| ∨           | `∨` `\|` `+`      |
| ⇒           | `⇒` `->` `=>`     |
| ⇔           | `⇔` `<->` `<=>`   |
| ⊤, ⊥        | `⊤` `1`, `⊥` `0`  |

Variables are a letter followed by letters or digits (`A`, `Cin`, `P1`).
Precedence, strongest first: ¬, ∧, ∨, ⇒, ⇔. `⇒` and `⇔` are replaced on input by
`F ⇒ G ∼ ¬F ∨ G` and `F ⇔ G ∼ (¬F ∨ G) ∧ (F ∨ ¬G)`.

## How exercise 7 works

- A formula is a tree. Conjunctions and disjunctions are flat, sorted and without
  duplicates, so commutativity, associativity and idempotence are built in.
- Rules (each also in its dual form): double negation, complement
  (`F ∧ ¬F ∼ ⊥`, `F ∨ ¬F ∼ ⊤`), absorption (`F ∨ (F ∧ G) ∼ F`), adjacency
  (`(F ∧ L) ∨ (F ∧ ¬L) ∼ F`, also a variant that keeps both terms so that one
  term can be used in two merges), `F ∨ (¬F ∧ G) ∼ F ∨ G`, distributivity
  (factoring a common part out), De Morgan in both directions.
- Cost: the number of NOT gates plus binary AND/OR gates. Equal subformulas are
  counted once.
- A best-first search applies the rules at every position and keeps the cheapest
  formula it finds.

Limit: the program works with formulas (trees). It does not find circuits that
share an inner subcircuit between outputs, such as the 9-gate full adder.
