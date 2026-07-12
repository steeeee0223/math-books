#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Morphisms

#lemma-box(title: "Fact 3.A")[
  Let $A$ be an integral domain with $K = Frac A$.
  Then, for any prime ideal $pp lt.closed A$, $A_pp$ can be viewed as a subring of $K$, and
  $ A = { A_pp : pp lt.closed A text("prime ideal") } = { A_mm : mm lt.closed A text("maximal ideal") }. $
]

#proof[ (Matsumura, Lemma 2, p.8).
  The containment $subset$ is clear, as $A$ is an integral domain. ]

#lemma-box(title: "Fact 3.B")[
  Fix a graded ring $S$. Recall that for any homogeneous prime ideal $pp lt.closed S$,
  the localization $S_pp$ is a graded $S$-module, which is also a local ring with maximal ideal $pp S_pp$.

  - Show that its degree-$0$ part $S_((pp))$ is also a local ring with maximal ideal
    $(pp S_pp) inter S_((pp))$.
  - In particular, if $S$ is an integral domain and $pp = ideal(0)$, the zero ideal,
    show that $S_(((0))) = (Frac S)_0$ is a field.
]
