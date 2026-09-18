#import "@preview/ilm:1.4.1": *

#set text(lang: "en")

#show: ilm.with(
  title: [Algebraic Geometry],
  author: "Shih-Wen Yu",
  date: datetime.today(),
  abstract: [
    This is a set of notes on Hartshorne's Algebraic Geometry.
  ],
  preface: [
    #align(center + horizon)[
      To all who study Hartshorne's Algebraic Geometry #emoji.heart,\ I hope you like it #emoji.face.smile
    ]
  ],
  bibliography: bibliography("refs.bib"),
  figure-index: (enabled: true),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)

#set list(indent: 1em)
#set enum(numbering: "(a)", indent: 1em)

= Variaties

#include "sec-1-1/sec-1-1.typ"
#include "sec-1-2/sec-1-2.typ"
#include "sec-1-3/sec-1-3.typ"
#include "sec-1-4/sec-1-4.typ"
#include "sec-1-5/sec-1-5.typ"
#include "sec-1-6/sec-1-6.typ"
#include "sec-1-7/sec-1-7.typ"
#include "sec-1-8/sec-1-8.typ"

= Schemes

#include "sec-2-1/sec-2-1.typ"
#include "sec-2-2/sec-2-2.typ"
#include "sec-2-3/sec-2-3.typ"
#include "sec-2-4/sec-2-4.typ"
#include "sec-2-5/sec-2-5.typ"
#include "sec-2-6/sec-2-6.typ"
#include "sec-2-7/sec-2-7.typ"
#include "sec-2-8/sec-2-8.typ"
#include "sec-2-9/sec-2-9.typ"

= Cohomology

#include "sec-3-1/sec-3-1.typ"

// Supplement codes identify each article; nested headings use indentation
// instead of the book's numeric prefixes in both the text and the outline.
#set heading(numbering: none)

#include "sup/sup.typ"

= Appendices
