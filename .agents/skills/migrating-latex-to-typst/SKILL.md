---
name: migrating-latex-to-typst
description: Use when migrating LaTeX math notes, classicthesis-book.tex sections, theorem/proof blocks, TikZ diagrams, or algebraic-geometry notation into Typst files using defs.typ and existing section examples.
---

# Migrating LaTeX to Typst

## Overview

Migrate one contiguous source block at a time. First establish the LaTeX source span, the last live Typst block, and the next unmigrated block; then transfer syntax while preserving mathematical content, ordering, labels, numbering, and local Typst style.

## Required First Step

Run the briefing tool before editing:

```bash
rg -n -F -e '\chapter{' -e '\section{' alg-geo/classicthesis-book.tex

python3 .agents/skills/migrating-latex-to-typst/scripts/migration_brief.py \
  --source alg-geo/classicthesis-book.tex \
  --target alg-geo/sec-2-5.typ \
  --start "\\chapter{Sheaves of Modules}" \
  --end "\\section{Weil Divisors}"
```

Use `rg` to choose the real source markers for the section being migrated; the `sec-2-5` command is only an example. Use the report to choose the next small block. Commented LaTeX-like backlog in the target is not finished Typst migration.

## Quick Reference

| LaTeX | Typst pattern in this project |
|---|---|
| `\chapter{Title}` / `\section{Title}` | `== Title` inside section files; `main.typ` owns top-level includes |
| `\begin{definition}{...}` | `#definition(title: "...")[ ... ]` or `#definition(number: none, title: "...")[ ... ]` |
| `\begin{proposition}{5.4}` | `#proposition(number: 5.4)[ ... ]` |
| `\begin{proof}` | `#proof[ ... ]` |
| `\begin{itemize}` with `(a)` labels | `#set enum(numbering: "a)", spacing: 1em)` then `+ ...` |
| `\textit{(5.1b)}` | `_(5.1b)_` |
| `\begin{align*} A & B \\ & C \end{align*}` | Display math: `$ A & B \ & C $`; LaTeX `\\` becomes Typst `\`, and `&` stays `&` |
| `\Longleftrightarrow` | `arrow.l.r.double.long`, not `<=>` |
| `\Spec`, `\Proj`, `\OO`, `\FF`, `\qcoh` | Prefer symbols already in `defs.typ` |
| `\xrightarrow[\Sch]{f}` | Prefer helpers such as `morph(f, Sch)` or local arrow style |
| `\begin{fact}{3.A}` | `#lemma-box(title: "Fact 3.A")[ ... ]` |
| `tikzcd` | Use Fletcher `diagram`, `node`, `edge` as in `sec-2-5.typ` |

## Workflow

1. Read the brief, `alg-geo/defs.typ`, and a nearby migrated example.
2. Select one source environment or proof subsection, not an arbitrary line count.
3. Convert only that block in the target `.typ`, after the last live Typst content.
4. Reuse existing definitions before inventing notation. Add to `defs.typ` only when a symbol recurs and the local pattern supports it.
5. Re-run the briefing tool. Its `Live LaTeX residue` section ignores commented backlog; raw grep does not.
6. Compile `alg-geo/main.typ` when `typst` is available; otherwise report that compiler verification was unavailable and include static checks run.

## Regression Check

Use the completed `Morphisms` section as a golden outline test:

```bash
python3 .agents/skills/migrating-latex-to-typst/scripts/migration_brief.py \
  --source alg-geo/classicthesis-book.tex \
  --target alg-geo/sec-1-3.typ \
  --start "\\chapter{Morphisms}" \
  --end "\\chapter{Sheaves of Modules}" \
  --expect-complete
```

Expected: `PASS`, matching `Fact 3.A`, its proof, and `Fact 3.B` with no live LaTeX residue.

## Example

LaTeX:

```tex
\begin{proposition}{5.4}
  Let $(X,\OO_X)$ be a scheme.
  \begin{itemize}
    \item[(i)] $\FF\in\MOD_{\OO_X}$ is quasi-coherent ...
  \end{itemize}
\end{proposition}
```

Typst:

```typst
#proposition(number: 5.4)[
  Let $(X,OO_X)$ be a scheme. Then

  #set enum(numbering: "a)", spacing: 1em)

  + $FF in MOD(OO_X)$ is quasi-coherent ...
]
```

## Common Mistakes

- Continuing from commented backlog instead of the last live Typst block.
- Migrating past the next environment boundary.
- Leaving raw LaTeX commands in live Typst.
- Treating raw grep hits inside commented backlog as live Typst residue.
- Recreating symbols already present in `defs.typ`.
- Flattening proofs, lists, or displayed equations in a way that changes structure.
- Translating `align*` line breaks or alignment points incorrectly: use Typst `\` for LaTeX `\\`, keep `&`, and translate `\Longleftrightarrow` as `arrow.l.r.double.long`.
- Treating a successful grep as equivalent to a Typst compile.
