#import "@preview/theorion:0.6.0" as theorion: *

#let paragraph-text(it) = {
  if it.has("text") { it.text }
  else if it.has("children") { it.children.map(paragraph-text).join() }
  else if it.has("child") { paragraph-text(it.child) }
  else if it.has("body") { paragraph-text(it.body) }
  else { "" }
}

// Lists put proof and stage headings in separate paragraphs. Keep each
// heading with the following step; leave ordinary proof paragraphs alone.
#let proof(..args) = {
  show par: it => {
    let heading = paragraph-text(it.body).trim()
    let proof-heading = heading.replace(regex("\\s+"), "") in ("Proof.", "Proof.Sketch.")
    let stage-heading = heading.contains(regex("^\\([IVXLCDM]+\\)\\."))
    if proof-heading or stage-heading {
      block(sticky: true, it)
    } else { it }
  }
  theorion.proof(..args)
}
