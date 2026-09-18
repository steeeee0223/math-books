#import "../defs.typ": book-link
#import "@preview/cetz:0.3.4"

#pagebreak(weak: true)
= Supplements <supplements>

These supplements collect tools for II.1–II.8. Each reusable result is
stated as a proposition, lemma, or corollary, followed by its proof and a
link to the original exercise when applicable. Worked counterexamples
appear with the property they illustrate. Original exercise anchors lead
to the corresponding result.

Within each supplement, definitions, results, remarks, and examples share
one consecutive sequence, such as SL-1, SL-2, and SL-3. Hartshorne's
chapter, proposition, and exercise numbers retain their original form.

In proofs, “Check!” explicitly assigns the indicated purely algebraic or
topological fact to the reader; a longer reader proof may include a hint.
The geometric argument still specifies its canonical maps, hypotheses,
affine or stalk reductions, and compatibility on overlaps.

#metadata(none) <sup-roadmap>
*Reading roadmap*

Read each diagram from top to bottom, following the connecting lines.
Blue cards are main-text entry points; pale cards are supplements.
Separate roots give independent starting points. II.5 continues across
two diagrams, with its entry point repeated. Elementary commutative
algebra and topology are assumed.

// Columns set horizontal positions; each row grows to fit its longest card.
#let roadmap-node(id, column, row, target, title, main: false, span: 1) = (
  id: id,
  column: column,
  row: row,
  target: target,
  title: title,
  main: main,
  span: span,
)

#let roadmap(title, nodes, edges, columns: 3, row-gap: 22) = block(breakable: false, above: 12pt)[
  #text(size: 11pt, weight: "semibold", title)
  #v(7pt)
  #layout(size => {
    let width = size.width / 1pt
    let margin = 10
    let gap = 20
    let padding = 10
    let column-width = (width - 2 * margin - (columns - 1) * gap) / columns
    let line-color = rgb("#9bafbd")
    let nodes = nodes.map(n => {
      let card-width = column-width * n.span + gap * (n.span - 1)
      let parts = n.title.split(" — ")
      let label = text(size: 10pt, weight: "semibold", parts.first().split(", ").map(part => box(part)).join([, ]))
      let body = block(width: (card-width - 16) * 1pt)[
        #set text(font: "Helvetica Neue", size: 9.5pt, fill: rgb("#273b49"))
        #set par(justify: false, leading: 2.5pt, spacing: 0pt)
        #align(center)[
          #book-link(n.target)[
            #if n.span > 1 {
              label
              h(10pt)
              parts.last()
            } else {
              label
              linebreak()
              v(2.5pt)
              parts.last()
            }
          ]
        ]
      ]
      let min-height = if n.span > 1 { 34 } else { 44 }
      let card-height = calc.max(min-height, measure(body).height / 1pt + 16)
      (..n, width: card-width, body: body, height: card-height)
    })
    let rows = range(calc.max(..nodes.map(n => n.row)) + 1).map(row => calc.max(
      ..nodes.filter(n => n.row == row).map(n => n.height),
    ))
    let height = rows.sum() + (rows.len() - 1) * row-gap + 2 * padding
    let position(n) = (
      margin + column-width / 2 + n.column * (column-width + gap),
      -padding - rows.slice(0, n.row).sum(default: 0) - n.row * row-gap - rows.at(n.row) / 2,
    )
    let lookup(id) = nodes.find(n => n.id == id)
    let port(n, bottom: false) = {
      let (x, y) = position(n)
      (x, y + rows.at(n.row) / 2 * if bottom { -1 } else { 1 })
    }
    let ports = ()
    cetz.canvas(length: 1pt, {
      import cetz.draw: bezier, circle, content, rect
      rect((0, 0), (width, -height), fill: rgb("#fafcfd"), stroke: none, radius: 8)
      // Shared endpoints keep forks and merges on the same visual axis.
      for (source, target) in edges {
        let start = port(lookup(source), bottom: true)
        let end = port(lookup(target))
        let middle = (start.at(1) + end.at(1)) / 2
        ports.push(start)
        ports.push(end)
        bezier(start, end, (start.at(0), middle), (end.at(0), middle), stroke: .8pt + line-color)
      }
      for n in nodes {
        content(position(n), block(
          width: n.width * 1pt,
          height: rows.at(n.row) * 1pt,
          inset: 8pt,
          radius: 6pt,
          fill: if n.main { rgb("#dceaf3") } else { rgb("#f1f5f7") },
          stroke: .8pt + line-color,
        )[
          #align(center + horizon, n.body)
        ])
      }
      for point in ports.dedup() {
        circle(point, radius: 2.4, fill: rgb("#fafcfd"), stroke: .9pt + line-color)
      }
    })
  })
]

#roadmap(
  "1. Foundations and locality — before II.3",
  (
    roadmap-node("n0", 1, 0, <sup-cat>, "CAT — Categorical language", span: 3),
    roadmap-node("n1", 0, 1, <text-ii-1>, "II.1 — Sheaves", main: true),
    roadmap-node("n2", 0, 2, <sup-sl>, "SL — Sheaf locality and gluing"),
    roadmap-node("n3", 0, 3, <sup-sc>, "SC — Groups and rings"),
    roadmap-node("n4", 1.5, 1, <text-ii-2>, "II.2 — Schemes, Spec and Proj", main: true),
    roadmap-node("n5", 1, 2, <sup-xl>, "XL — Scheme gluing and principal opens"),
    roadmap-node("n6", 1, 3, <sup-lp>, "LP — Locality core"),
    roadmap-node("n7", 2, 3, <sup-pj>, "PJ — Basic Proj geometry"),
    roadmap-node("n8", 2, 2, <sup-xp-generic-points>, "XP — Generic points and specialization"),
  ),
  (
    ("n1", "n2"),
    ("n2", "n3"),
    ("n4", "n5"),
    ("n4", "n8"),
    ("n5", "n6"),
    ("n5", "n7"),
  ),
)

#pagebreak(weak: true)
#roadmap(
  "2. Properties, fiber products and diagonals — II.3~II.4",
  (
    roadmap-node("n9", 1, 0, <text-ii-3>, "II.3 — First properties of schemes", main: true),
    roadmap-node("n10", 0, 1, <sup-xp>, "XP — Intrinsic properties, except XP-11"),
    roadmap-node("n11", 2, 1, <sup-lp>, "LP — Locality checking"),
    roadmap-node("n12", 1, 2, <text-ii-3>, "II.3.3 — Fiber products", main: true),
    roadmap-node("n13", 1, 3, <sup-mg>, "MG — Affine products, fibers and field-valued points"),
    roadmap-node("n16", 1, 4, <text-ii-4>, "II.4 — Separated and proper morphisms", main: true),
    roadmap-node("n17", 0, 5, <sup-xp-11>, "XP-11 — Quasi-separatedness"),
    roadmap-node("n18", 1, 5, <sup-lp>, "LP-48~LP-53 — Separated, universally closed, integral morphisms"),
    roadmap-node("n20", 2, 5, <sup-vs>, "VS — Varieties and schemes"),
  ),
  (
    ("n9", "n10"),
    ("n9", "n11"),
    ("n9", "n12"),
    ("n11", "n12"),
    ("n12", "n13"),
    ("n16", "n17"),
    ("n16", "n18"),
    ("n16", "n20"),
  ),
)

#pagebreak(weak: true)
#roadmap(
  "3. Modules and the affine dictionary — II.5",
  (
    roadmap-node("n21", 1, 0, <text-ii-5>, "II.5 — Sheaves of modules", main: true),
    roadmap-node("n22", 0, 1, <sup-al>, "AL — Algebraic tools for modules"),
    roadmap-node("n23", 2, 1, <sup-sc>, "SC — Module statements"),
    roadmap-node("n24", 1, 2, <text-ii-5>, "II.5.1-5.8 — The affine module dictionary", main: true),
    roadmap-node("n25", 0.5, 3, <sup-qc>, "QC — Quasi-coherent and coherent operations"),
    roadmap-node("n28", 2, 3, <sup-xl-8>, "XL-8 — Affine ring-map dictionary"),
    roadmap-node("n26", 0, 4, <sup-se>, "SE — Support, extension and local freeness"),
    roadmap-node("n27", 1, 4, <sup-rv>, "RV — Relative Spec and vector bundles"),
  ),
  (
    ("n21", "n22"),
    ("n21", "n23"),
    ("n21", "n24"),
    ("n24", "n25"),
    ("n24", "n28"),
    ("n25", "n26"),
    ("n25", "n27"),
  ),
  row-gap: 18,
)

#roadmap(
  "3. Closed subschemes and projective constructions — II.5 (continued)",
  (
    roadmap-node("n21", 0.5, 0, <text-ii-5>, "II.5 — Sheaves of modules", main: true),
    roadmap-node("n29", 0, 1, <text-ii-5>, "II.5.9-5.10 — Ideal sheaves and closed subschemes", main: true),
    roadmap-node("n33", 1, 1, <text-ii-5>, "II.5.11-5.20 — Graded sheaves, twists and projective results", main: true),
    roadmap-node("n30", 0, 2, <sup-cs>, "CS — Closed subschemes and ideal sheaves"),
    roadmap-node("n34", 1, 2, <sup-pj>, "PJ — Quotients, graded modules and embeddings"),
    roadmap-node("n32", 0, 3, <sup-mg>, "MG — Graphs, stability and images"),
  ),
  (
    ("n21", "n29"),
    ("n21", "n33"),
    ("n29", "n30"),
    ("n33", "n34"),
    ("n30", "n32"),
  ),
  columns: 2,
  row-gap: 18,
)

#pagebreak(weak: true)
#roadmap(
  "4. Divisors and projective geometry — II.6~II.7",
  (
    roadmap-node("n35", 0, 0, <text-ii-6>, "II.6 — Divisors", main: true),
    roadmap-node("n36", 0, 1, <sup-al2>, "AL2 — Associated points and total quotients"),
    roadmap-node("n37", 0, 2, <sup-lp-62>, "LP-62~LP-64 — Dense opens and extension"),
    roadmap-node("n38", 0, 3, <sup-dv>, "DV — Divisors and line bundles"),
    roadmap-node("n39", 1.5, 0, <text-ii-7>, "II.7 — Projective morphisms", main: true),
    roadmap-node("n40", 1, 1, <sup-pj2>, "PJ2 — Relative Proj and projectivization"),
    roadmap-node("n42", 1.5, 3, <sup-lp-54>, "LP-54~LP-58 — Projectivity and its locality failures"),
    roadmap-node("n43", 2, 1, <sup-rm>, "RM — Rational maps, function fields and graphs"),
    roadmap-node("n41", 1, 2, <sup-pm>, "PM — Global embeddings and positivity"),
    roadmap-node("n44", 2, 2, <sup-bu>, "BU — Blowup charts and base points"),
  ),
  (
    ("n35", "n36"),
    ("n36", "n37"),
    ("n37", "n38"),
    ("n39", "n40"),
    ("n39", "n42"),
    ("n39", "n43"),
    ("n40", "n41"),
    ("n43", "n44"),
  ),
)

#roadmap(
  "5. Differential and tangent geometry — II.8",
  (
    roadmap-node("n45", 1, 0, <text-ii-8>, "II.8 — Differentials", main: true),
    roadmap-node("n46", 0, 1, <sup-df-1>, "DF — Differentials, tangent spaces and fibers"),
    roadmap-node("n48", 1.5, 1, <sup-al2-6>, "AL2 — Regular sequences and local algebra"),
    roadmap-node("n47", 0, 2, <sup-lp2-1>, "LP2 — Smooth, étale and unramified morphisms"),
    roadmap-node("n49", 1.5, 2, <sup-lp2-7>, "LP2 — Cartier and regular immersions"),
    roadmap-node("n50", 1, 3, <sup-df-10>, "DF — Normal and canonical bundles"),
    roadmap-node("n51", 2, 3, <sup-bu-8>, "BU-8 — Regular centers and exceptional geometry"),
    roadmap-node("n52", 1, 4, <sup-vs2>, "VS2 — Ten calculations, ending with a conic family", span: 3),
  ),
  (
    ("n45", "n46"),
    ("n45", "n48"),
    ("n46", "n47"),
    ("n48", "n49"),
    ("n49", "n50"),
    ("n49", "n51"),
  ),
)

#pagebreak(weak: true)
#block(breakable: true)[
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
  - #book-link(<sup-al2>)[AL2 — Associated points and regular sequences]
  - #book-link(<sup-dv>)[DV — Divisors and line bundles]
  - #book-link(<sup-pj2>)[PJ2 — Relative Proj and projectivization]
  - #book-link(<sup-pm>)[PM — Projective morphisms and positivity]
  - #book-link(<sup-rm>)[RM — Rational maps of schemes]
  - #book-link(<sup-bu>)[BU — Blowups and birational constructions]
  - #book-link(<sup-df>)[DF — Differentials and tangent geometry]
  - #book-link(<sup-lp2>)[LP2 — Further locality criteria]
  - #book-link(<sup-vs2>)[VS2 — Calculations on varieties]
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
#include "module-algebra-2.typ"
#include "divisors-line-bundles.typ"
#include "proj-2.typ"
#include "projective-morphisms.typ"
#include "rational-maps.typ"
#include "blowups.typ"
#include "differentials-tangent-spaces.typ"
#include "local-props-2.typ"
#include "varieties-schemes-2.typ"
