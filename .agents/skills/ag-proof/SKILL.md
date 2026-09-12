---
name: ag-proof
description: Write, revise, or review proofs in books/alg-geo using Hartshorne's definitions, the repository's Typst notation and locality lemmas, and Lean companions for verification. Use only for proof work in the algebraic-geometry textbook.
---

# Algebraic Geometry Proofs

Produce readable textbook proofs whose reductions are explicit and whose
critical claims are independently checked in Lean. Lean and mathlib are
verification tools, not part of the textbook exposition.

## Editorial Scope

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

## Sources and Priorities

1. Use Hartshorne's definitions and conventions for the mathematical content.
   Read the surrounding textbook material and relevant source in
   `books/alg-geo/src/classicthesis-book.tex` when needed to identify them.
2. Use existing notation from `books/alg-geo/src/defs.typ` at highest priority.
   It imports the notation dictionaries in `cat.typ`, `sym.typ`, and `ops.typ`;
   inspect those files rather than inventing parallel syntax.
3. Before devising a new reduction, search
   `books/alg-geo/src/sec-2-3/local-props.typ` and the rest of the existing
   textbook for an applicable locality or reduction lemma. Cite the relevant
   textbook result when it already exists.
4. Inspect the corresponding Lean companion and mathlib source for useful
   proof ideas. Do not assume a same-named mathlib definition agrees with
   Hartshorne's definition; compare hypotheses and definitions explicitly.

If these sources differ, Hartshorne governs the textbook statement. Add the
necessary comparison lemma or bridge only in the Lean verification layer.

## Textbook Proof Standard

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
3. Explain why each reduction is valid. In particular, never write merely
   "the question is local" or "we may assume affine": specify whether locality
   is on the source or target, the restriction and gluing principles being
   used, and why their hypotheses hold. Prefer an existing result from
   `local-props.typ` or elsewhere in the textbook.
4. After passing to affine charts, identify the rings, modules, and ring maps,
   and state how every relevant sheaf or morphism translates under the affine
   correspondence.
5. End at a precise purely commutative-algebraic, topological, categorical, or
   affine assertion. Such a terminal assertion may be left to the reader once
   the reduction and its hypotheses are fully stated. Elementary intermediate
   checks may likewise be left to the reader when doing so does not hide the
   main geometric argument.
6. Verify that local constructions agree on overlaps or are canonical/natural
   enough to glue whenever the proof returns from local data to a global
   statement.

A proof inspired by mathlib must still expose the mathematical steps and the
reason for each step. Do not replace exposition by a theorem name or reproduce
mathlib's implementation vocabulary.

## Reusable Textbook Lemmas

When several proofs share a genuine mathematical reduction, prefer a reusable
lemma over repeating an opaque shortcut. First search the existing textbook.
If no suitable result exists, add a lemma only within the authorized editing
scope; otherwise obtain the user's approval as required above. State its exact
hypotheses, direction of locality, affine translation, and gluing conclusion.

## Lean Verification

Every added or revised textbook proof must have a corresponding Lean companion
created or updated under the relevant section's `lean/` directory.

- Prefer a Lean theorem that verifies the complete textbook claim.
- If current interfaces cannot express the complete claim, verify every key
  reduction and the terminal algebraic, topological, categorical, or affine
  assertion. Record the remaining interface gap precisely in `.lean` comments
  and in the work report, never in the textbook.
- It is acceptable to add repo-local Lean definitions and lemmas needed to
  bridge Hartshorne's formulation to mathlib, provided they remain within the
  user's authorized scope.
- Do not silently substitute a stronger, weaker, or differently defined
  mathlib statement. Document the comparison in Lean and ensure the textbook
  proof still proves Hartshorne's statement.
- Keep Lean declarations aligned with the actual reductions in the prose; a
  theorem that checks only an unrelated affine fact is insufficient.

Run the relevant file from the repository root, for example:

```bash
lake env lean books/alg-geo/src/sec-2-5/lean/exe.lean
```

## Verification and Handoff

Before reporting completion:

- compile the affected Typst entry point, normally
  `books/alg-geo/src/main.typ`;
- kernel-check every affected Lean companion;
- run `git diff --check` on touched files;
- inspect the diff for unauthorized edits, notation inconsistent with
  `defs.typ`, unexplained locality or affine reductions, and textbook mentions
  of Lean or mathlib;
- report what the Lean companion verifies and any remaining verification gap.

Do not claim the proof is complete or verified when a required check failed.
