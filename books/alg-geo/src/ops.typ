#let one = $bb("1")$
#let ann = $op("Ann")$
#let supp = $op("Supp")$
#let sing = $op("Sing")$

#let im = $op("Im")$
#let spec = $op("Spec")$
#let sp = $op("sp")$
#let max-spec = $op("mSpec")$
#let soc = $op("Soc")$
#let ht = $op("ht")$
#let aut = $op("Aut")$
#let char = $op("char")$
#let frac = $op("Frac")$
#let proj = $op("Proj")$
#let ker = $op("Ker")$
#let coker = $op("coker")$
#let cdiv = $op("CDiv")$
#let div = $op("Div")$
#let pic = $op("Pic")$
#let id = $op("id")$
#let cl = $op("Cl")$
#let cacl = $op("CaCl")$
#let dv = $op("div")$
#let der = $op("Der")$
#let nil = $op("nil")$
#let trdeg = $op("trdeg")$
#let ob = $op("Ob")$

#let colim = $op("colim")$

#let hom(from, to, over: "") = $op("Hom")_#over paren.l #from, #to paren.r$
#let ass(body, over: "") = $op("Ass")_#over paren.l #body paren.r$
#let dim(body, over: "") = $op("dim")_#over #body$
#let rank(body, over: "") = $op("rank")_#over #body$
#let codim(body, ambient) = $op("codim") paren.l #body, #ambient paren.r$
