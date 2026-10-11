#import "@preview/theorion:0.6.0": *

// block
#let notation(body) = note-block(title: "Notation", body)
#let exercise(title: "Exercise", body) = block(
  width: 100%,
  inset: 1em,
  radius: .4em,
  fill: rgb("#f7eed8"),
)[
  #strong(title) #body
]
#let example(number: none, title: "", body) = block(
  width: 100%,
  inset: 1em,
  radius: .4em,
  fill: rgb("#b5e7f4"),
)[
  #let t = {
    let heading = "Example" + if number == none { "" } else { " " + str(number) }
    if title != "" {
      heading + " (" + title + ")."
    } else { heading + "." }
  }
  #strong(t) #body
]

// Preserve the remark styling while allowing an explicit reference number.
#let remark(number: none, title: "", body) = {
  let heading = if number == none {
    if title == "" { "Remark" } else { title }
  } else {
    "Remark " + str(number) + if title == "" { "" } else { " (" + title + ")" }
  }
  note-block(fill: rgb("#118D8D"), title: heading, icon-name: "comment", body)
}
