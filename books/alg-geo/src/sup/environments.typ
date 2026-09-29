#import "@preview/theorion:0.6.0": *
#import cosmos.clouds: render-fn

#let supplement-prefix = state("supplement-prefix", "")
#let supplement-counter = richer-counter(
  identifier: "supplement",
  inherited-levels: 0,
)

#let _supplement-numbering-pattern(loc) = {
  let prefix = supplement-prefix.at(loc)
  (..numbers) => prefix + "-" + numbers.pos().map(str).join(".")
}

#let supplement-numbering(prefix) = {
  supplement-prefix.update(prefix)
  (supplement-counter.update)((0,))
}

#let supplement-frame(identifier, supplement, render) = {
  let (_, _, base-frame, _) = make-frame(
    identifier,
    supplement,
    counter: supplement-counter,
    numbering: _supplement-numbering-pattern,
    render: render,
  )
  let frame(key: none, ..args, body) = [
    #base-frame(..args, body)
    #if key != none {
      label(key)
    }
  ]
  frame
}

#let theorem = supplement-frame(
  "theorem",
  theorion-i18n-map.at("theorem"),
  render-fn.with(fill: red.lighten(85%)),
)

#let lemma = supplement-frame(
  "lemma",
  theorion-i18n-map.at("lemma"),
  render-fn.with(fill: teal.lighten(85%)),
)

#let corollary = supplement-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  render-fn.with(fill: navy.lighten(90%)),
)

#let definition = supplement-frame(
  "definition",
  theorion-i18n-map.at("definition"),
  render-fn.with(fill: olive.lighten(85%)),
)

#let proposition = supplement-frame(
  "proposition",
  theorion-i18n-map.at("proposition"),
  render-fn.with(fill: blue.lighten(85%)),
)

#let render-example(prefix: none, title: "", full-title: "", body) = block(
  width: 100%,
  inset: 1em,
  radius: .4em,
  fill: rgb("#b5e7f4"),
)[
  #strong[#full-title.] #body
]

#let example = supplement-frame(
  "example",
  theorion-i18n-map.at("example"),
  render-example,
)

#let render-remark(prefix: none, title: "", full-title: "", body) = note-block(
  fill: rgb("#118D8D"),
  title: full-title,
  icon-name: "comment",
  body,
)

#let remark = supplement-frame(
  "remark",
  theorion-i18n-map.at("remark"),
  render-remark,
)

#let render-exercise(prefix: none, title: "", full-title: "", body) = block(
  width: 100%,
  inset: 1em,
  radius: .4em,
  fill: rgb("#f7eed8"),
)[
  #strong[#full-title] #body
]

#let supplement-exercise = supplement-frame(
  "exercise",
  theorion-i18n-map.at("exercise"),
  render-exercise,
)
