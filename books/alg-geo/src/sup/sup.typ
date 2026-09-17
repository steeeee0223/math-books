#import "../defs.typ": book-link

#pagebreak(weak: true)
== Supplements <supplements>

These supplements collect tools for II.1-II.5. Statements without an
accompanying proof are recorded for reference. Proofs transferred from the
exercises retain their original part numbering. Each application reproduces
the complete exercise statement before its proof.

#metadata(none) <sup-roadmap>
*Reading roadmap*

Read each tree from its root toward its leaves. Blue boxes are main-text
entry points; pale boxes are supplements. Branches give the main reading
path. The prerequisite table records inputs from other branches and later
returns. Elementary commutative algebra and topology are assumed.

#let roadmap-node(title, main: false) = block(
  width: 100%,
  inset: (x: 7pt, y: 5pt),
  radius: 3pt,
  fill: if main { rgb("#dceaf3") } else { rgb("#f3f6f8") },
  stroke: 0.5pt + rgb("#a9bdca"),
)[
  #set par(justify: false)
  #text(size: 10pt, weight: "semibold", title)
]
#let roadmap-branches(..children) = block(
  inset: (left: 8pt),
  above: 3pt,
  below: 3pt,
)[
  #block(stroke: (left: 0.6pt + rgb("#a9bdca")))[
    #stack(dir: ttb, spacing: 4pt, ..children
      .pos()
      .map(child => grid(
        columns: (12pt, 1fr),
        align: left + top,
        line(start: (0pt, 10pt), end: (12pt, 10pt), stroke: 0.6pt + rgb("#a9bdca")), child,
      )))
  ]
]

#block(breakable: false)[
  *1. Foundations and locality — before II.3*
  #roadmap-node([#book-link(<sup-cat>)[CAT — Categorical language]])
  #v(5pt)
  #roadmap-node([#book-link(<text-ii-1>)[II.1 — Sheaves]], main: true)
  #roadmap-branches([
    #roadmap-node([#book-link(<sup-sl>)[SL — Sheaf locality and gluing]])
    #roadmap-branches([
      #roadmap-node([#book-link(<sup-sc>)[SC — Groups and rings]])
    ])
  ])
  #roadmap-node([#book-link(<text-ii-2>)[II.2 — Schemes, Spec and Proj]], main: true)
  #roadmap-branches(
    [
      #roadmap-node([#book-link(<sup-xl>)[XL-1-7 — Scheme gluing and principal opens]])
      #roadmap-branches(
        [
          #roadmap-node([#book-link(<sup-lp>)[LP-1-15 — Locality core]])
        ],
        [
          #roadmap-node([#book-link(<sup-pj>)[PJ-1-3 — Basic Proj geometry]])
        ],
      )
    ],
    [
      #roadmap-node([#book-link(<sup-xp-1>)[XP-1a-c — Generic points and specialization]])
    ],
  )
]

#block(breakable: false)[
  *2. Properties, fiber products and diagonals — II.3-II.4*
  #roadmap-node([#book-link(<text-ii-3>)[II.3 — First properties of schemes]], main: true)
  #roadmap-branches(
    [
      #roadmap-node([#book-link(<sup-xp>)[XP — Intrinsic properties, except XP-5]])
    ],
    [
      #roadmap-node([#book-link(<sup-lp>)[LP — Finite type, finite, quasi-compact and affine]])
    ],
    [
      #roadmap-node([#book-link(<text-ii-3>)[II.3.3 — Fiber products]], main: true)
      #roadmap-branches(
        [
          #roadmap-node([#book-link(<sup-mg>)[MG-1-2,7 — Affine products, fibers and field-valued points]])
        ],
        [
          #roadmap-node([#book-link(<sup-lp>)[LP — Base change, finite presentation and flatness]])
        ],
      )
    ],
    [
      #roadmap-node([#book-link(<sup-lp-33>)[LP-30-33 — Surjections and closed immersions]])
    ],
  )
  #roadmap-node([#book-link(<text-ii-4>)[II.4 — Separated and proper morphisms]], main: true)
  #roadmap-branches(
    [
      #roadmap-node([#book-link(<sup-xp-5>)[XP-5 — Quasi-separatedness]])
    ],
    [
      #roadmap-node([#book-link(<sup-lp>)[LP-50-57 — Separated and universally closed morphisms]])
    ],
    [
      #roadmap-node([#book-link(<sup-lp-27>)[LP-26-29 — Integral morphisms]])
    ],
    [
      #roadmap-node([#book-link(<sup-vs>)[VS — Varieties and schemes]])
    ],
  )
]

#block(breakable: false)[
  *3. Modules, closed subschemes and projective constructions — II.5*
  #roadmap-node([#book-link(<text-ii-5>)[II.5 — Sheaves of modules]], main: true)
  #roadmap-branches(
    [
      #roadmap-node([#book-link(<sup-al>)[AL — Algebraic tools for modules]])
    ],
    [
      #roadmap-node([#book-link(<sup-sc>)[SC — Module statements]])
    ],
    [
      #roadmap-node([#book-link(<text-ii-5>)[II.5.1-5.8 — The affine module dictionary]], main: true)
      #roadmap-branches(
        [
          #roadmap-node([#book-link(<sup-qc>)[QC — Quasi-coherent and coherent operations]])
          #roadmap-branches(
            [
              #roadmap-node([#book-link(<sup-se>)[SE — Support, extension and local freeness]])
            ],
            [
              #roadmap-node([#book-link(<sup-rv>)[RV — Relative Spec and vector bundles]])
            ],
          )
        ],
        [
          #roadmap-node([#book-link(<sup-xl-8>)[XL-8 — Affine ring-map dictionary]])
        ],
      )
    ],
    [
      #roadmap-node([#book-link(<text-ii-5>)[II.5.9-5.10 — Ideal sheaves and closed subschemes]], main: true)
      #roadmap-branches([
        #roadmap-node([#book-link(<sup-cs>)[CS — Closed subschemes and ideal sheaves]])
        #roadmap-branches(
          [
            #roadmap-node([#book-link(<sup-lp-33>)[LP-33 — Affine closed-immersion criterion]])
          ],
          [
            #roadmap-node([#book-link(<sup-mg>)[MG-3-6,8-10 — Graphs, stability and images]])
          ],
        )
      ])
    ],
    [
      #roadmap-node([#book-link(<text-ii-5>)[II.5.11-5.20 — Graded sheaves, twists and projective results]], main: true)
      #roadmap-branches([
        #roadmap-node([#book-link(<sup-pj>)[PJ-4-10 — Quotients, graded modules and embeddings]])
      ])
    ],
  )
]

#block(breakable: false)[
  *Supplement index*

  - #book-link(<sup-cat>)[CAT — Categorical language]
  - #book-link(<sup-sl>)[SL — Sheaf locality and gluing]
  - #book-link(<sup-sc>)[SC — Sheaf constructions and exactness]
  - #book-link(<sup-al>)[AL — Algebraic tools for modules]
  - #book-link(<sup-xl>)[XL — Scheme locality and gluing]
  - #book-link(<sup-lp>)[LP — A Locality Calculus for Morphisms]
  - #book-link(<sup-xp>)[XP — Topology and intrinsic properties of schemes]
  - #book-link(<sup-mg>)[MG — Morphisms, diagonals and graphs]
  - #book-link(<sup-qc>)[QC — Quasi-coherent and coherent operations]
  - #book-link(<sup-se>)[SE — Support, extension and local freeness]
  - #book-link(<sup-rv>)[RV — Relative Spec and vector bundles]
  - #book-link(<sup-pj>)[PJ — Proj and graded modules]
  - #book-link(<sup-cs>)[CS — Closed subschemes and ideal sheaves]
  - #book-link(<sup-vs>)[VS — Varieties and schemes]
]

#include "categorical-language.typ"
#include "sheaf-locality.typ"
#include "sheaf-constructions.typ"
#include "module-algebra.typ"
#include "scheme-locality.typ"
#include "local-props.typ"
#include "scheme-properties.typ"
#include "morphisms.typ"
#include "quasi-coherent.typ"
#include "support-extension.typ"
#include "relative-spec.typ"
#include "proj.typ"
#include "closed-subschemes.typ"
#include "varieties-schemes.typ"
