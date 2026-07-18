#import "@preview/ilm:1.4.1": *

#set text(lang: "en")

#show: ilm.with(
  title: [Arithmetic Curves & Algebraic Number Theory],
  author: "Shih-Wen Yu",
  date: datetime.today(),
  abstract: [
    As a general rule in algebraic geometry and number theory you never know enough algebra. For this lecture course knowledge of basic ring theory and rudiments of field theory as taught in the Algebra course of your syllabus is indispensable. A good reference for this material is *S. Bosch, Algebra, Springer*. This introductory chapter summarizes some algebraic background material.\
    Moreover, we often have to appeal to the theory of modules and algebras which are direct generalisations of vector spaces and polynomial rings. Most of this is covered in the course GAGA A. Here a good standard reference is *M. Atiyah* and *I. McDonald, Introduction to Commutative Algebra, Addison-Wesley*. You can first safely admit these results and approach this course as a concrete and preliminary motivation for the abstract foundations of (commutative algebra).
  ],
  figure-index: (enabled: true),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)

= Review of Basic Notions

#include "sec-0-1.typ"
#include "sec-0-2.typ"
#include "sec-0-3.typ"
#include "sec-0-4.typ"
#include "sec-0-5.typ"
#include "sec-0-6.typ"

= Integral Ring Extensions & Rings of Integers

#include "sec-1-1.typ"
#include "sec-1-2.typ"
#include "sec-1-3.typ"
#include "sec-1-4.typ"
#include "sec-1-5.typ"

= Dedekind Domains

#include "sec-2-1.typ"
#include "sec-2-2.typ"
#include "sec-2-3.typ"
#include "sec-2-4.typ"
#include "sec-2-5.typ"

= Affine Schemes

#include "sec-3-1.typ"
#include "sec-3-2.typ"
#include "sec-3-3.typ"
#include "sec-3-4.typ"
#include "sec-3-5.typ"

= Completions & Local-Global Principles

#include "ch-4-intro.typ"
#include "sec-4-1.typ"
#include "sec-4-2.typ"
#include "sec-4-3.typ"
#include "sec-4-4.typ"
#include "sec-4-5.typ"

= Appendix: Completions

#include "ch-a-intro.typ"

= Appendix: Sheaves & Schemes

#include "sec-b-1.typ"
