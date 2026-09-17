#import "@preview/theorion:0.4.0": proof as theorion-proof

#let paragraph-text(it) = {
  if it.has("text") { it.text }
  else if it.has("children") { it.children.map(paragraph-text).join() }
  else if it.has("child") { paragraph-text(it.child) }
  else if it.has("body") { paragraph-text(it.body) }
  else { "" }
}

// A list puts theorion's inline proof heading in its own paragraph. Keep
// that heading with the first step; leave ordinary paragraph proofs alone.
#let proof(..args) = {
  show par: it => {
    if paragraph-text(it.body).trim() == "Proof." {
      block(sticky: true, it)
    } else { it }
  }
  theorion-proof(..args)
}
