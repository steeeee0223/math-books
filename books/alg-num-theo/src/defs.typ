// Shared math definitions for Arithmetic Curves & Algebraic Number Theory.

#import "@preview/theorion:0.4.0": note-box
#import "@preview/theorion:0.4.0" as theorion

#let environment-title(kind, number: none, title: none) = {
  if title != none and number != none {
    [#kind #number. (#title)]
  } else if title != none {
    [#kind. #title]
  } else if number != none {
    [#kind #number.]
  } else {
    kind
  }
}

#let example(body, number: none, title: none) = theorion.example(
  title: environment-title([Example], number: number, title: title),
  body,
)

#let exercise(body, number: none, title: none) = theorion.exercise(
  title: environment-title([Exercise], number: number, title: title),
  body,
)

#let remark(body, number: none, title: none) = theorion.remark(
  title: environment-title([Remark], number: number, title: title),
  body,
)

#let notation(body, number: none, title: none) = {
  let label = if title != none { title } else if number != none { [Notation #number] } else { [Notation] }
  note-box(title: label, body)
}

#let note(body, number: none, title: none) = {
  let label = if title != none { title } else if number != none { [Note #number] } else { [Note] }
  note-box(title: label, body)
}

#let motivation(body, number: none, title: none) = {
  note-box(title: environment-title([Motivation], number: number, title: title), body)
}

#let proofthm(body, number: none, title: none) = {
  note-box(title: environment-title([Proof], number: number, title: title), body)
}

#let summary-box(body, title: none) = {
  note-box(title: if title == none { [Summary] } else { title }, body)
}

#let ideal(x) = $lr(chevron.l #x chevron.r)$
#let tildeOf(x) = $accent(#x, tilde.op)$
#let tensor(x, y, base) = $#x times.o_#base #y$
#let morph(top, bottom) = $stretch(->, size: #150%)_#bottom^#top$
#let inclusion(top, bottom) = $stretch(arrow.r.hook, size: #150%)_#bottom^#top$
#let bigOPlus(val, bottom, top: none) = $attach(plus.o.big, tr: #top, br: #bottom) #val$
#let coprod(val, bottom, top: none) = $attach(product.co, tr: #top, br: #bottom) #val$

#let simeq = $tilde.equiv$
#let eqBy(x) = $attach(=, b: #x)$
#let isoBy(x) = $attach(tilde.equiv, b: #x)$
#let to = $arrow.r.long$
#let Leftarrow = $arrow.l.double$
#let Rightarrow = $arrow.r.double$

#let E = $op("E")$
#let Ann = $op("Ann")$
#let Aut = $op("Aut")$
#let Char = $op("char")$
#let Cl = $op("Cl")$
#let Coker = $op("coker")$
#let Der = $op("Der")$
#let End = $op("End")$
#let Frac = $op("Frac")$
#let Gal = $op("Gal")$
#let GL = $op("GL")$
#let Hom(from, to, over: none) = $op("Hom")_#over paren.l #from, #to paren.r$
#let Ht = $op("ht")$
#let Im = $op("Im")$
#let Ker = $op("Ker")$
#let LCM = $op("LCM")$
#let maxSpec = $op("mSpec")$
#let nil = $op("nil")$
#let Norm = $op("N")$
#let ord = $op("ord")$
#let Proj = $op("Proj")$
#let rank = $op("rank")$
#let sgn = $op("sgn")$
#let Spec = $op("Spec")$
#let tr = $op("tr")$
#let trdeg = $op("trdeg")$
#let val = $op("val")$

#let scr(it) = text(features: ("ss01",), box($cal(it)$))

#let AA = $bb("A")$
#let EE = $scr("E")$
#let FF = $scr("F")$
#let GG = $scr("G")$
#let HH = $scr("H")$
#let II = $scr("I")$
#let JJ = $scr("J")$
#let KK = $scr("K")$
#let LL = $scr("L")$
#let MM = $scr("M")$
#let NN = $cal("N")$
#let OO = $cal("O")$
#let PP = $bb("P")$
#let Ss = $scr("S")$
#let TT = $cal("T")$

#let aa = $frak("a")$
#let bfrak = $frak("b")$
#let dd = $frak("d")$
#let mm = $frak("m")$
#let nn = $frak("n")$
#let pp = $frak("p")$
#let qq = $frak("q")$

#let Ab = $frak("Ab")$
#let ALG = $frak("Alg")$
#let GR = $frak("Gr")$
#let MOD(x) = {
  if x == "" [
    $frak("Mod")$
  ] else [
    $frak("Mod")_#x$
  ]
}
#let Ring = $frak("Ring")$
#let Sch = $frak("Sch")$
#let Shf = $frak("Shf")$
#let Top = $frak("Top")$
