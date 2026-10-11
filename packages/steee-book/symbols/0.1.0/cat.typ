#let ab = $frak("Ab")$
#let ring = $frak("Ring")$
#let top = $frak("Top")$
#let alg = $frak("Alg")$
#let gr = $frak("Gr")$
#let qcoh = $frak("Qch")$
#let coh = $frak("Coh")$
#let mod(x) = {
  if x == "" [
    $frak("Mod")$
  ] else [
    $frak("Mod")(#x)$
  ]
}
#let shf = $frak("Shf")$
#let psh = $frak("Psh")$
#let lrs = $frak("LRS")$
#let sch = $frak("Sch")$
#let var = $frak("Var")$
