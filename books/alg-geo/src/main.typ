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

= Variaties

#include "sec-1-1.typ"
#include "sec-1-2.typ"
#include "sec-1-3.typ"

= Schemes

#include "sec-2-5.typ"
#include "sec-2-6-1.typ"
#include "sec-2-6-2.typ"
#include "sec-2-6-3.typ"
#include "sec-2-7-1.typ"
#include "sec-2-7-2.typ"
#include "sec-2-7-3.typ"
#include "sec-2-7-4.typ"
#include "sec-2-8-1.typ"
#include "sec-2-8-2.typ"
#include "sec-2-8-3.typ"
#include "sec-2-8-4.typ"

= Cohomology

#include "sec-3-1.typ"

= Appendices
