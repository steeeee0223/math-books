#import "@preview/theorion:0.6.0" as _theorion

// Keep cross-references clickable when their targets are included.
// Standalone previews display the text when the target is absent.
#let book-link(target, body) = context {
  if query(target).len() > 0 {
    link(target, body)
  } else {
    body
  }
}

// Link to a numbered supplement item using its live Theorion number.
// The fallback keeps standalone article previews readable when the target
// belongs to a different included file.
#let supplement-link(target, body) = context {
  let targets = query(target)
  if targets.len() == 0 {
    body
  } else {
    let target-element = targets.first()
    let frame = if target-element.func() == figure {
      target-element
    } else {
      query(selector(figure).after(target-element.location())).first(default: none)
    }
    if frame == none {
      body
    } else {
      link(target, _theorion.theorion-display-number(frame))
    }
  }
}
