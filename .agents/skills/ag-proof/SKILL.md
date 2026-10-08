---
name: ag-proof
description: Write, revise, or review proofs in books/alg-geo using Hartshorne's definitions, the repository's Typst notation and locality lemmas, and Lean companions for verification. Use only for proof work in the algebraic-geometry textbook.
---

# Algebraic geometry proofs

Write readable textbook proofs. State each reduction explicitly and
independently check critical claims in Lean. Use Lean and mathlib to verify
the proofs; keep them out of the textbook exposition.

## Editorial scope

- Apply this skill to proofs in `books/alg-geo/`, including exercises and
  theorem, proposition, and lemma proofs in the main text.
- Do not proactively rewrite existing proofs. Edit a proof only when the user
  explicitly asks to add, rewrite, improve, or otherwise modify it.
- Treat a request to review or explain a proof as read-only unless the user
  also asks for edits.
- Keep edits within the user-named scope. If a reusable textbook lemma would
  belong elsewhere, first propose its exact statement, intended location, and
  use, and wait for the user's approval before adding it.
- If a useful new notation is missing, propose it and ask the user before
  changing any notation file.

## Sources and priorities

1. Use Hartshorne's definitions and conventions for the mathematical content.
   Read the surrounding textbook material and relevant source in
   `books/alg-geo/src/classicthesis-book.tex` when needed to identify them.
2. Give existing notation from `books/alg-geo/src/defs.typ` highest priority.
   It imports the notation dictionaries in `cat.typ`, `sym.typ`, and `ops.typ`;
   inspect those files rather than inventing parallel syntax.
3. Before devising a new reduction, search
   `books/alg-geo/src/sup/local-props.typ` and the rest of the existing
   textbook for an applicable locality or reduction lemma. Cite the relevant
   textbook result when it already exists.
4. Inspect the corresponding Lean companion and mathlib source for useful
   proof ideas. Do not assume a mathlib definition with the same name agrees
   with Hartshorne's definition; compare hypotheses and definitions explicitly.

If these sources differ, use Hartshorne's formulation for the textbook
statement. Add the necessary comparison lemma or bridge only in Lean.

## Textbook proof standard

Write all textbook mathematics in formal mathematical English, regardless of
the language used in the request. Chinese may be used in discussion and work
reports, but not in inserted textbook prose.

Never mention Lean, mathlib, formalization, kernel checking, theorem identifiers,
or implementation limitations in the textbook. Keep those details in `.lean`
comments and the work report.

For each proof:

1. State the construction or canonical morphism being studied.
2. Give the reduction as an explicit chain. Name every restriction,
   localization, cover refinement, stalk computation, affine chart, or
   equivalence used along the way.
3. Explain why each reduction is valid. Never write merely
   "the question is local" or "we may assume affine". Specify whether locality
   is on the source or target. Name the restriction and gluing principles
   used, and explain why their hypotheses hold. Prefer an existing result from
   `local-props.typ` or elsewhere in the textbook.
4. After passing to affine charts, identify the rings, modules, and ring maps,
   and state how every relevant sheaf or morphism translates under the affine
   correspondence.
5. End at a precise purely commutative-algebraic, topological, categorical, or
   affine assertion. This terminal assertion may be left to the reader once
   the reduction and its hypotheses are fully stated. Elementary intermediate
   checks may also be left to the reader when doing so does not hide the
   main geometric argument.
6. When the proof passes from local data to a global statement, verify that
   the local constructions agree on overlaps or are canonical or natural
   enough to glue.

A proof inspired by mathlib must still explain the mathematical steps and the
reason for each step. Do not replace exposition by a theorem name or reproduce
mathlib's implementation vocabulary.

## Map definitions

When defining a map explicitly, prefer centered display math showing its
source, target, and rule on elements. Choose arrows that fit the context.
The examples below use `to` from `defs.typ`.

```typst
$
f: A to B, a mapsto b
$
```

If the definition is too long for one line, use `&` and `\` to align it across
two lines:

```typst
$
f: A & to B,\ a & mapsto b
$
```

## Proof dependencies

- Do not use a statement B to prove A if B's proof depends on A, directly or
  through other results. Trace the dependencies of cited results far enough
  to rule out such a cycle.
- If A's proof uses B and B is stated later in the same section, identify
  both statements and request a change. Propose moving B before A or revising
  the proof to avoid the forward dependency. Obtain the user's approval for
  that change before making it. Do not treat B as already established while
  the change is pending.

## Reusable textbook lemmas

When several proofs share a mathematical reduction, prefer a reusable
lemma to repeating an unexplained shortcut. First search the existing textbook.
If no suitable result exists, add a lemma only within the authorized editing
scope; otherwise obtain the user's approval as required above. State its exact
hypotheses, direction of locality, affine translation, and gluing conclusion.

## Lean verification

Every added or revised textbook proof must have a corresponding Lean companion
created or updated under the relevant section's `lean/` directory.

- Prefer a Lean theorem that verifies the complete textbook claim.
- If current interfaces cannot express the complete claim, verify every key
  reduction and the terminal algebraic, topological, categorical, or affine
  assertion. Record the remaining interface gap precisely in `.lean` comments
  and in the work report, never in the textbook.
- You may add Lean definitions and lemmas in the repository to relate
  Hartshorne's formulation to mathlib. Keep them within the user's authorized
  scope.
- Do not silently substitute a stronger, weaker, or differently defined
  mathlib statement. Document the comparison in Lean and ensure the textbook
  proof still proves Hartshorne's statement.
- Keep Lean declarations aligned with the reductions used in the prose.
  A theorem that checks only an unrelated affine fact is insufficient.

Run the relevant file from the repository root, for example:

```bash
lake env lean books/alg-geo/src/sup/lean/ii-5-exe.lean
```

## Verification and handoff

Before reporting completion:

- compile the affected Typst entry point, normally
  `books/alg-geo/src/main.typ`;
- kernel-check every affected Lean companion;
- run `git diff --check` on touched files;
- inspect the diff for unauthorized edits, notation inconsistent with
  `defs.typ`, unexplained locality or affine reductions, and textbook mentions
  of Lean or mathlib;
- check proof dependencies for cycles and unresolved uses of later statements
  in the same section;
- report what the Lean companion verifies and any remaining verification gap.

Do not claim the proof is complete or verified when a required check failed.
