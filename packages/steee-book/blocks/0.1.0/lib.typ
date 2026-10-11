// One block API for main text and supplement articles.
#import "@preview/theorion:0.6.0" as _theorion
#import "boxes.typ" as _boxes
#import "supplements.typ" as _supplements
#import "proof-layout.typ" as _proof-layout
#import "links.typ": *

#let _clouds = _theorion.cosmos.clouds
#let _in-supplement() = _supplements.supplement-prefix.get() != ""

#let show-blocks(body) = {
  // Each included article starts in main-text mode until it sets a supplement prefix.
  _supplements.supplement-prefix.update("")
  _clouds.show-theorion(body)
}

#let supplement-numbering(prefix) = _supplements.supplement-numbering(prefix)
#let main-numbering() = _supplements.supplement-prefix.update("")

#let theorem(..args) = context {
  if _in-supplement() { _supplements.theorem(..args) } else { _clouds.theorem(..args) }
}
#let lemma(..args) = context {
  if _in-supplement() { _supplements.lemma(..args) } else { _clouds.lemma(..args) }
}
#let corollary(..args) = context {
  if _in-supplement() { _supplements.corollary(..args) } else { _clouds.corollary(..args) }
}
#let definition(..args) = context {
  if _in-supplement() { _supplements.definition(..args) } else { _clouds.definition(..args) }
}
#let proposition(..args) = context {
  if _in-supplement() { _supplements.proposition(..args) } else { _clouds.proposition(..args) }
}
#let example(..args) = context {
  if _in-supplement() { _supplements.example(..args) } else { _boxes.example(..args) }
}
#let remark(..args) = context {
  if _in-supplement() { _supplements.remark(..args) } else { _boxes.remark(..args) }
}

// Explicitly unnumbered practice boxes can also occur inside a supplement.
#let exercise(numbered: auto, ..args) = context {
  let numbered = if numbered == auto { _in-supplement() } else { numbered }
  if numbered { _supplements.supplement-exercise(..args) } else { _boxes.exercise(..args) }
}

#let proof(..args) = context {
  if _in-supplement() { _proof-layout.proof(..args) } else { _theorion.proof(..args) }
}
#let notation(..args) = _boxes.notation(..args)
#let axiom(..args) = _clouds.axiom(..args)
#let postulate(..args) = _clouds.postulate(..args)
#let assumption(..args) = _clouds.assumption(..args)
#let property(..args) = _clouds.property(..args)
#let conjecture(..args) = _clouds.conjecture(..args)
#let note(..args) = _clouds.note(..args)
#let problem(..args) = _clouds.problem(..args)
#let theorem-box(..args) = _clouds.theorem-box(..args)
#let lemma-box(..args) = _clouds.lemma-box(..args)
#let solution(..args) = _theorion.solution(..args)
#let conclusion(..args) = _theorion.conclusion(..args)
#let emph-block(..args) = _theorion.emph-block(..args)
#let quote-block(..args) = _theorion.quote-block(..args)
#let note-block(..args) = _theorion.note-block(..args)
#let tip-block(..args) = _theorion.tip-block(..args)
#let important-block(..args) = _theorion.important-block(..args)
#let warning-block(..args) = _theorion.warning-block(..args)
#let caution-block(..args) = _theorion.caution-block(..args)
#let remark-block(..args) = _theorion.remark-block(..args)
#let qedhere = _theorion.qedhere
#let set-result = _theorion.set-result
#let set-qed-symbol = _theorion.set-qed-symbol
