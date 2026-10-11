#import "@preview/fletcher:0.5.8" as fletcher: *
#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

// Keep diagram labels compact and leave a little clearance at arrow tips.
#let diagram = fletcher.diagram.with(
  label-size: 0.85em,
  label-sep: 0.15em,
  node-outset: 1pt,
)

// Hartshorne II.4, Definition D1
#definition(number: none, title: "Diagonal and Separated Morphisms")[

  For a morphism $f:X->Y$,

  - the *diagonal morphism* is the unique map $Delta:X->X times_Y X$ whose composite with either projection $p_1, p_2: fiber(X, X, base: Y)->X$ is $ops.id_X$.
  - The morphism $f$ is *separated* if $Delta$ is a closed immersion; in this case, we also say $X$ is separated over $Y$.
  - A scheme is separated if it is separated over $ops.spec ZZ$.
]

#example(title: "Non-separated scheme")[
  Let $k$ be a field, and let $X$ be the affine line $sym.sch.a_k^1$ with doubled origin $O$ and $O'$. Then, $X$ is not separated over $k$.
]
#proof[
  We could see that
  - $fiber(X, X, base: k)$ is the affine plane $sym.sch.a_k^2$ with 4 origins $(O,O), (O,O'), (O',O), (O',O')$.
  - The image $Delta(X)$ is the union of the diagonal line $x=y$ and the two points $(O,O), (O',O')$.
  But, $Delta(X)$ is not closed in $fiber(X, X, base: k)$, since the 4 origins are all in $Delta(X)^-$
]

// Hartshorne II.4, Proposition 4.1
#proposition(number: "4.1")[
  Every morphism of affine schemes is separated.
]
#proof[
  Suppose $f:X->Y$ is the morphism of affine schemes induced by the ring homomorphism $B->A$. Then, $A$ is a $B$-algebra and $fiber(X, X, base: Y)=ops.spec(tensor(A, A, over: B))$.

  Now, the diagonal morphism $Delta$ comes from the ring homomorphism
  $
    delta: tensor(A, A, over: B)to A,quad tensor(a, a')mapsto a a'.
  $
  (Note that $a mapsto tensor(a, 1) mapsto a dot 1=a$). Thus, $delta$ is surjective, and $Delta$ is a closed immersion (#book-link(<sup-cs-1>)[CS-1]).
]


// Hartshorne II.4, Corollary 4.2
#corollary(number: "4.2")[
  A morphism $f:X->Y$ is separated if and only if the image of its diagonal
  is closed in $X times_Y X$.
]
#proof[
  ($Rightarrow$) Comes from definition. ($Leftarrow$) Conversely, let $X'$ denote $fiber(X, X, base: Y)$. I claim the following:

  #set enum(numbering: "(i)")
  + _Claim: The map $Delta: X -> Delta(X)$ is a homeomorphism._
  + _Claim: $Delta^sharp: shf.o_(X')->Delta_ast shf.o_X$ is surjective._
]


#lemma(number: "4.A")[
  #set math.equation(numbering: none)
  If $Z$ is an integral scheme with (unique) generic point $z_1 in Z$.
  For any $z_0 in Z$,
  #set enum(numbering: "(i)")
  + the natural map $shf.o_(Z,z_0) to shf.o_(Z,z_1)$ is injective.
  + $ops.frac shf.o_(Z,z_0) = k(z_1)$.
]
#proof[
  #set math.equation(numbering: none)
  (i) Let $U in cal(N)_(z_0)(Z)$: open affine, $U:=ops.spec A$. Since $Z$: integral, we have $A simeq shf.o_(Z)(U)$: integral.

  - Since $z_0 in Z = {z_1}^-$, by definition of “closure”, $U in.rev z_1$. Say $z_0:=frak(p) in ops.spec A$. Since $U=ops.spec A$: integral, $z_1=(0) in ops.spec A$ (generic point).
  - Now, the map becomes
    $
      #diagram(cell-size: (35mm, 15mm), $ shf.o_(Z,z_0)=shf.o_(U,z_0) edge("r", simeq, "-") edge("d", ->) & A_frak(p) edge("d", arrow.hook) \
                    shf.o_(Z,z_1)=shf.o_(U,z_1) edge("r", simeq, "-") & A_((0)) edge("r", #[(A: integral)], "=") & ops.frac A $)
    $

  (ii) $A arrow.r.hook A_frak(p) arrow.r.hook ops.frac A$ since $A$: integral. Thus,
  $ k(z_1)=shf.o_(Z,z_1)=ops.frac A=ops.frac A_frak(p)=ops.frac shf.o_(Z,z_0). $
]
#remark(number: "4.B")[
  #set math.equation(numbering: none)
  Suppose $ops.spec R=T morph(h, cat.sch) X$ is a morphism with $R$: valuation.
  Let $t_0,t_1 in T$ be the unique closed, generic point, respectively, and $t_i mapsto x_i$ ($i=0,1$).
  Then, we have $x_1 arrow.r.squiggly x_0$. (This is proved in (4.4 ii)($Rightarrow$).)
]

#lemma(number: "4.C")[
  #set math.equation(numbering: none)
  The morphism $X=ops.spec A morph(f, cat.sch) ops.spec B=Y$ is dominant. $arrow.l.r.double ops.ker(B morph(phi, cat.ring) A) subset ops.nil B$.
  In particular, if $Y$ (or $B$) is reduced, then $phi$: injective.
]
#proof[
  #set math.equation(numbering: none)
  - Recall. For any $frak(a) ◁ A$, $V(phi^(-1)(frak(a)))=f(V(frak(a)))^-$. In particular, taking $frak(a)=(0)$, then
    $
      f:"dominant". & arrow.l.r.double f(X)^-=Y. arrow.l.r.double V(ops.ker phi)=Y. \
                    & arrow.l.r.double frak(q) supset ops.ker phi "for every" frak(q) in ops.spec B. \
                    & arrow.l.r.double ops.ker phi subset inter_(frak(q) in Y) frak(q)=ops.nil B.
    $
  - If $B$: reduced, $ops.ker phi subset ops.nil B=(0)$. $=> phi$ is injective.
]

#lemma(number: "4.D", supplement: "Fact")[
  #set math.equation(numbering: none)
  If $frak(p) ◁ A$ is a minimal prime ideal, then the maximal ideal of $A_frak(p)$, $frak(p) A_frak(p) subset ops.nil A_frak(p)$.
  In particular, if $A$ is reduced, then $A_frak(p)$ is a field.
]
#proof[
  #set math.equation(numbering: none)
  - Recall. [AM, 1.17(ii)], $f$: nilpotent $arrow.l.r.double D(f)=emptyset$.

  (i) Let $a':=a/f in frak(p) A_frak(p)$ ($a in frak(p)$, $f in.not frak(p)$). If $a' in.not ops.nil A_frak(p)$, then $D(a') != emptyset$.
  $=> exists frak(q) A_frak(p) in ops.spec A_frak(p)$, where $frak(q) in ops.spec A$ with $frak(q) subset frak(p)$, such that $frak(q) A_frak(p) in.rev.not a'=a/f$.
  $=> a in.not frak(q)$. $=> frak(q) subset.neq frak(p)$. ($↯$).
  Contradict to the minimality of $frak(p)$. Thus, $a' in ops.nil A_frak(p)$.

  (ii) $A$: reduced. $arrow.r.double^((3.B)) A_frak(p)$: reduced. $=> 0=ops.nil A_frak(p) supset.eq^(("i")) frak(p) A_frak(p)$: maximal ideal. $=> A_frak(p)$: field.
]

#definition(number: none, supplement: "Criterion", title: "*")[
  Given a morphism $X morph(f, cat.sch) Y$.
  For any $K$: field, and $R$: valuation with $ops.frac R=K$.
  Set $i:U morph("", cat.sch) T$ induced by $R inclusion("", cat.ring) K$.
  Given any morphisms $U morph(alpha, cat.sch) X$, $T morph(beta, cat.sch) Y$ such that $f alpha=beta i$.
  Then $exists!$ morphism $T morph(h, cat.sch) X$ satisfying $alpha=h i$ and $beta=f h$.
  $
    #diagram(cell-size: 20mm, $ ops.spec K=U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
                      ops.spec R=T edge("r", beta, ->) & Y $)
  $
]

// Hartshorne II.4, Theorem 4.3
#theorem(number: "4.3", title: "Valuative Criterion for Separatedness")[
  Let $f:X morph("", cat.sch) Y$ be a morphism with $X$ Noetherian.
  Then, $f$ is separated. $arrow.l.r.double$ The “uniqueness” part of (\*) holds.
]
#proof[
  #set math.equation(numbering: none)
  ($Rightarrow$). Suppose $f$: separated. Given the commutative diagram (i) and suppose $exists h,h'$ making the whole diagram (i) commute.
  - Consider diagram (ii). Since $T$ is such that $f h=beta=f h'$, by Universal Property of $X times_Y X$, $exists T morph(h'', cat.sch) X times_Y X$ such that $h=pi_1 h''$, $h'=pi_2 h''$.
  - Since $h i=alpha=h' i$, again $exists! g:U morph("", cat.sch) X times_Y X$ such that $alpha=pi_j g$ ($j=1,2$).
  - Note. $pi_(j)(Delta h i)=ops.one_X alpha=alpha$ ($j=1,2$). By “uniqueness” of $g$, we have $g=Delta h i$.
    Similarly, for $pi_(j)(h'' i)=alpha$ ($j=1,2$), we have $g=h'' i$, whence $Delta h i=h'' i$.
  - $R$: valuation. $=> exists! t_1 in T$: generic point. ($U inclusion(i, "") T$, $(0) mapsto (0)=t_1$).
    $=> h''(t_1)=Delta h(t_1) in Delta(X)$. Write $x_1:=h(t_1) in X$.
  - Note. $h''(T)=h''({t_1}^-) subset.eq^(h'':"conti.") {h''(t_1)}^-={Delta h(t_1)}^- subset Delta(X)^-=Delta(X)$ (closed, (4.2)).
    $=> h(t_0) in Delta(X)$, say $h(t_0):=Delta(x_0)$, where $x_0 in X$, and $t_0 in T$: unique closed point.
  - Now, $h(t_k)=pi_1 h''(t_k)=pi_1 Delta(x_k)=x_k=pi_2 Delta(x_k)=pi_2 h''(t_k)=h'(t_k)$ ($k=0,1$).
    $=> h^sharp_(t_k)=(h')^sharp_(t_k):shf.o_(X,x_k) to shf.o_(T,t_k)$ ($k=0,1$).
    Thus, $k(x_1) arrow.r.hook^((k=1)) K$ and $shf.o arrow.r.hook^((k=0)) R$ induced by $h,h'$ are the same (see (4.4 ii)).
    Further, $x_1 arrow.r.squiggly x_0$ by (4.B). $arrow.r.double^((4.4"ii")) h=h'$.

  #grid(
    columns: (1fr,),
    row-gutter: 1em,
    [
      #figure(
        $
          #diagram(cell-size: 19mm, $ ops.spec K=U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
          ops.spec R=T edge("r", beta, ->) edge("ur", h, ->, shift: #2pt, label-side: #left) edge("ur", h', ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Y $)
        $,
        kind: "diagram",
        caption: [(i)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #figure(
        $
          #diagram(cell-size: (24mm, 22mm), $ U edge("d", i, ->) edge("dr", g, "-->") edge("drr", alpha=h'i, ->, bend: #40deg, label-pos: #65%) edge("ddr", alpha=h i, ->, bend: #(-55deg), label-pos: #65%) & & \
          T edge("r", h'', "-->") edge("rr", h', ->, bend: #30deg) edge("dr", h, ->) & X times_Y X edge("r", pi_2, ->) edge("d", pi_1, ->) & X edge("d", f, ->, label-side: #left) \
          & X edge("r", f, ->) & Y $, node((1.5, 1.5), $square$))
        $,
        kind: "diagram",
        caption: [(ii)],
        numbering: none,
        supplement: none,
      )
    ],
  )

  ($Leftarrow$). Suppose the “uniqueness” part of (\*) is satisfied. Claim. $f$: separated.
  - By (4.2), it suffices to show $Delta(X) subset X times_Y X$: closed.
  - $X$: Noetherian. $=> X$: quasi-compact. $=> Delta$: quasi-compact morphism.
    By (4.5), it suffices to show that $Delta(X)$ is stable under specialization, i.e. for given $xi_1 in Delta(X)$ and $xi_0 in X times_Y X$ with $xi_1 arrow.r.squiggly xi_0$, we show that $xi_0 in Delta(X)$.
  - Let $Z={xi_1}^-$ with its reduced induced structure, and let $K:=k(xi_1)=shf.o_(Z,xi_1)$, and $shf.o=shf.o_(Z,xi_0)$ (i.e. $xi_1$ is the unique generic point of $Z$ as $Z={xi_1}^-$: irreducible).
    Since $xi_1 arrow.r.squiggly xi_0$, $exists$ natural map $shf.o=shf.o_(Z,xi_0) to shf.o_(Z,xi_1)=K$, which is injective by (4.A).
    Further, $shf.o$: local ring. $arrow.r.double^(["I.6.1"]) exists R subset K$: valuation such that $R$ dominates $shf.o$.
    Now, by (4.4 ii), $exists h:T=ops.spec R morph("", cat.sch) X times_Y X$ sending $t_0=idl.m_R mapsto xi_1$, $t_1=(0) mapsto xi_1$, where $t_0,t_1$ are the unique closed, generic points of $T$, respectively.
  - Consider $pi_j h:T to X times_Y X to X$ ($j=1,2$). Since $xi_1 in Delta(X)$, say $xi_1=Delta(x_1)$ ($x_1 in X$).
    Consider diagram (iii). From the product $X times_Y X$, we have $f pi_1=f pi_2$, so $beta$ is defined and $△$ commutes.
    Further, $U={t_1}$, so $x_1=pi_j Delta(x_1)=pi_(j)(xi_1)=pi_j h i(t_1)$, i.e. $alpha$ is defined and $▽$ commutes.
    By assumption of (\*), we have $pi_1 h=pi_2 h=:tilde(h)$.
  - Further, since $Delta tilde(h)(t_1)=Delta(x_1)=xi_1=h(t_1)$ and ${t_1} subset T$: dense, we have $h=Delta tilde(h)$.
    Thus, $xi_0=h(t_0)=Delta(tilde(h)(t_0)) in Delta(X)$, done.
  #figure(
    $
      #diagram(cell-size: 22mm, $ ops.spec K=U edge("r", alpha=pi_j h i, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
      ops.spec R=T edge("r", beta=f pi_j h, ->, label-side: #right) edge("ur", pi_1 h, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", pi_2 h, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Y $)
    $,
    kind: "diagram",
    caption: [(iii)],
    numbering: none,
    supplement: none,
  )
]

// Hartshorne II.4, Lemma 4.4
#lemma(number: "4.4")[
  Let $R$: valuation ring with $K=ops.frac R$. Consider
  $
    #diagram(cell-size: 20mm, $  ops.spec K=U edge("r", ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #right) \
    ops.spec R=T edge("r", ->) edge("ur", "-->") & Y $)
  $
  #set enum(numbering: "(i)")
  + To give a morphism $U morph("", cat.sch) X$ is equivalent to give $x_1 in X$ and $k(x_1) inclusion("", cat.ring) K$.
  + To give $T morph("", cat.sch) X$ is equivalent to give $x_0,x_1 in X$ with $x_1 arrow.r.squiggly x_0$ and $k(x_1) arrow.r.hook K$ such that $R$ dominates $shf.o=shf.o_(Z,x_0)$ on $Z:={x_1}^- subset X$, the subscheme with its reduced induced structure.
]
#proof[
  #set math.equation(numbering: none)
  (i)
  - To give $U morph(g, cat.top) X arrow.l.r.double$ To give $x_1 in X$ with $(0) mapsto x_1$.
  - To give $shf.o_X morph(g^sharp, cat.shf) g_(ast)(shf.o_U) arrow.l.r.double$ To give $(shf.o_(X,x_1), idl.m_(x_1)) morph("", cat.ring) (shf.o_(U,(0)),(0))=K$.
    $ arrow.l.r.double^("Isom. Thm.") "To give" shf.o_(X,x_1)\/idl.m_(x_1)=k(x_1) arrow.r.hook K. $

  (ii)
  - Note. $R$: valuation. $arrow.r.double^("Def.") R$: integral domain. $arrow.r.double^((3.C)) T=ops.spec R$: integral.
    #text(size: .9em)[
      $
        cases(
          "(AM)." R:"local ring". => exists! t_0=idl.m_R in T:"closed point".,
          "(3.1)." T:"irreducible". arrow.r.double^([2.9]) T "has a unique generic point" t_1=(0) in T.,
        ) => t_1 arrow.r.squiggly t_0.
      $
    ]
    [3.6]. $shf.o_(T,t_1)="function field of" T simeq ops.frac R=K$.

  ($Rightarrow$).
  - Given $T morph(h, cat.sch) X$. Let $x_i:=h(t_i)$ ($i=0,1$). Then
    $ x_0=h(t_0) in h(T)=h({t_1}^-) subset.eq^(h:"conti.") {h(t_1)}^-={x_1}^-, $
    so $x_1 arrow.r.squiggly x_0$.
  - $T$: integral. $arrow.r.double^((3.1)) T$: reduced. $arrow.r.double^([3.11d]) exists! T' morph("", cat.sch) X$: closed subscheme such that $T'$ is the reduced induced structure on $h(T)^-={x_1}^-=Z$, so $h$ factors through $Z$, i.e. $h:T morph(overline(h), exists) T'=Z arrow.r.hook X$.
  - Note. $Z={x_1}^- subset X$: irreducible closed. $=> x_1$: the unique generic point of $Z$.
    - $Z$: irreducible. If not, say $Z=Z_1 union Z_2$ where $Z_i subset.neq Z$: closed in $X$. Say $x_1 in Z_i$, then $Z={x_1}^- subset Z_i subset.neq Z$. ($↯$).
    - $Z=T'$: reduced. $arrow.r.double^((3.1)) Z$: integral. $arrow.r.double^((4.A)) shf.o_(Z,x_0) arrow.r.hook shf.o_(Z,x_1)$: injective.
    - $t_1 arrow.r.squiggly t_0$, i.e. $t_0 in {t_1}^-$. $=>$ Every neighborhood of $t_0$ contains $t_1$.
      $=> exists$ natural map $shf.o_(T,t_0) to shf.o_(T,t_1)$. For $x_1 arrow.r.squiggly x_0$, similarly, $exists shf.o_(Z,x_0) to shf.o_(Z,x_1)$.

  Now, we have
  $
    #diagram(cell-size: (40mm, 18mm), $ shf.o=shf.o_(Z,x_0) edge("r", overline(h)^sharp_(t_0), ->) edge("d", arrow.hook) & shf.o_(T,t_0)=R edge("d", ->) \
                 shf.o_(Z,x_1) edge("r", overline(h)^sharp_(t_1), ->) edge("d", "=") & shf.o_(T,t_1) edge("d", "=") \
    k(x_1) edge("r", #text(size: 9pt)[field homomorphism\ is injective], arrow.hook) & K $)
  $
  ($R$: local.) By commutativity, $overline(h)^sharp_(t_0):shf.o arrow.r.hook R$: injective. $=> R$ dominates $shf.o$.

  ($Leftarrow$). Suppose $x_0,x_1 in X$ with $x_1 arrow.r.squiggly x_0$, $k(x_1) arrow.r.hook K$ such that $R$ dominates $shf.o$.
  Then $shf.o inclusion("", cat.ring) R$ induces $T=ops.spec R morph("", cat.sch) ops.spec shf.o$. Consider an open affine $U:=ops.spec A$ of $Z$.
  Then $shf.o=shf.o_(Z,x_0)=A_frak(p)$ ($x_0=frak(p) in U$). $=>$ The natural map $A arrow.r.hook A_frak(p)$ induces $ops.spec A_frak(p) to U arrow.r.hook_("open") Z$.
  Thus, we obtain $T to ops.spec shf.o=ops.spec A_frak(p) to Z$.
]

// Hartshorne II.4, Lemma 4.5
#lemma(number: "4.5")[
  Let $f:X morph("", cat.sch) Y$ be quasi-compact. Then $f(X) subset Y$ is closed.
  $arrow.l.r.double f(X)$ is stable under specialization, i.e. if $y in Y$ and $y' in f(X)$ satisfy $y' arrow.r.squiggly y$, then $y in f(X)$.
]
#proof[
  #set math.equation(numbering: none)
  ($Rightarrow$) Clear from [3.17e(iii)].

  ($Leftarrow$).
  - Note that this lemma is just a “topological fact”, we may assume both $X,Y$: reduced.
    Further, may assume $f(X)^-=Y$ by replacing $Y$ by the reduced induced structure on $f(X)^-$.
  - Fix $y in Y$. (Claim. $y in f(X)$). Replace $Y$ by an open affine neighborhood of $y$, we may assume $Y$ is affine.
  - $f$: quasi-compact. $=> X$ has a finite open affine cover ${X_i}_(i=1)^r$. Note that
    $ y in Y=f(X)^-=(union_(i=1)^r f(X_i))^-=union_(i=1)^r f(X_i)^-, $
    say $y in f(X_i)^-$. Let $Y_i:=f(X_i)^-$ with the reduced induced structure, then $Y_i$: affine.
  - Consider the dominant morphism $X_i morph(f, cat.sch) Y_i$ of reduced affine schemes.
    Write $X_i:=ops.spec A$, $Y_i:=ops.spec B$. $arrow.r.double^((4.C)) B inclusion(phi, cat.ring) A$ is injective.
  - Let $y:=frak(p) in ops.spec B$ and $frak(p)' ◁ B$: minimal prime ideal contained in $frak(p)$.
    (Existence of $frak(p)'$: By Zorn's Lemma, since $inter {frak(q) in ops.spec B:frak(q) subset frak(p)} in ops.spec B$.)
  - Say $y'=frak(p)' in Y_i$. Check $y' arrow.r.squiggly y$, i.e. $y in {y'}^-$.
    For any $V in cal(N)_(y)(Y_i)$, take $g in B$ with $y in D(g) subset V$.
    $=> g in.not frak(p) => g in.not frak(p)' => y' in D(g) subset V$.
    $=> V inter {y'} != emptyset$. Thus, $y in {y'}^-$.
  - Claim. $y' in f(X_i)$. Localize $A,B$ at $frak(p)'$. Then $B inclusion(phi, cat.ring) A$ implies $B_(frak(p)') inclusion(phi_(frak(p)'), "") A_(frak(p)')=tensor(A, B_(frak(p)'), over: B)$.
    - $Y_i=ops.spec B$: reduced. $=> B$: reduced. $arrow.r.double^((4.D)) B_(frak(p)')$: field.
    - Let $frak(q)_0' ◁ tensor(A, B_(frak(p)'), over: B)$: prime. Since $B_(frak(p)')$: field, $frak(q)_0' inter B_(frak(p)')=(0)$.
    - Consider $A morph(psi, "") A_(frak(p)')=tensor(A, B_(frak(p)'), over: B)$ and let $frak(q)':=psi^(-1)(frak(q)_0') subset A$.
      By commutativity, $frak(q)' inter B=frak(p)'$. $=> x':=frak(q)' ◁ A$: prime, and $f(x')=phi^(-1)(frak(q)')=frak(p)'=y'$, i.e. $y' in f(X_i)$.
  $
    #diagram(cell-size: (27mm, 17mm), $ frak(p)' & frak(p)' B_(frak(p)')=(0) edge("l", "|->") \
    B edge("u", ->) edge("r", arrow.hook) edge("d", phi, arrow.hook) & B_(frak(p)') edge("u", #[(field)], ->) edge("d", phi_(frak(p)'), arrow.hook) \
    A edge("r", psi, ->) & tensor(A, B_(frak(p)'), over: B) \
    frak(q)' edge("uuu", "-->", bend: #30deg) & frak(q)_0' edge("l", "|->") edge("u", "hook->") $)
  $
  - Now, $y' in f(X) arrow.r.squiggly y in Y$, by assumption, $y in f(X)$.
    Thus, $f(X)=Y=f(X)^-$, i.e. $f(X)$: closed.
]

// Hartshorne II.4, Corollary 4.6
#corollary(number: "4.6")[
  Assume that all schemes are Noetherian.
  #set enum(numbering: "(a)")
  + Open and closed immersions are separated.
  + Composition of separated morphisms is separated.
  + Separated morphisms are stable under base change.
  + If $f:X morph("", cat.sch) Y$ and $f':X' morph("", cat.sch) Y'$ are separated $S$-morphisms, then $f times f':X times_S X' morph("", cat.sch) Y times_S Y'$ is separated.
  + If $X morph(f, cat.sch) Y morph(g, cat.sch) Z$ is separated, so is $f$.
  + $f:X morph(f, cat.sch) Y$ is separated $arrow.l.r.double Y$ can be covered by open sets $V_i$ such that $f^(-1)(V_i) to V_i$ is separated for every $i$, i.e. “Separatedness” is local on the base.
]
#proof[
  #set math.equation(numbering: none)
  (a) Suppose $i:X morph("", cat.sch) Y$ is an open/closed immersion.
  Then, we have $Delta_(X\/Y):X isoto X times_X X isoto X times_Y X$.
  Thus, $Delta_(X\/Y)(X)=X times_Y X$: closed. $arrow.r.double^((4.2)) i$: separated.
  $
    #diagram(cell-size: 20mm, $ X times_Y X edge("r", ->) edge("d", ->) & X edge("d", i simeq, ->) \
                   X edge("r", i simeq, ->) & i(X) subset Y $, node((0.5, 0.5), $square$))
  $

  (b)
  - Consider the diagram (i) with $T attach(⇉, t: h_1, b: h_2) X$ such that (i) commutes.
  - We have the commutative diagram (ii). Since $g$: separated, by (4.3), $f h_1=f h_2$.
  - Now, the diagram (iii) commutes since $f h_1=f h_2$. Further, $f$: separated.
    $arrow.r.double^((4.3)) h_1=h_2$. Thus, $g f$: separated.
  #grid(
    columns: (1fr, 1fr, 1fr),
    gutter: 1em,
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 13mm, $ U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", g f, ->, label-side: #left) edge("dr", f, ->) & \
          T edge("r", beta, ->) edge("ur", h_1, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", h_2, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Z & Y edge("l", g, ->) $)
        $,
        kind: "diagram",
        caption: [(i) (Given $alpha,beta$)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 17mm, $ U edge("r", f alpha, ->) edge("d", i, ->) & X edge("d", g "(sep)", ->, label-side: #left) \
          T edge("r", beta, ->) edge("ur", f h_1, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", f h_2, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Z $)
        $,
        kind: "diagram",
        caption: [(ii)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 17mm, $ U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", f "(sep)", ->, label-side: #left) \
          T edge("r", f h_1=f h_2, ->, label-side: #right) edge("ur", h_1, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", h_2, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Y $)
        $,
        kind: "diagram",
        caption: [(iii)],
        numbering: none,
        supplement: none,
      )
    ],
  )

  (c)
  - Suppose $exists T attach(⇉, t: h_1, b: h_2) X'=X times_Y Y'$ such the small square of diagram (iv) commutes, where $X' morph(f', cat.sch) Y'$ is a base change of the separated morphism $X morph(f, cat.sch) Y$.
  #grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 18mm, $ U edge("rr", alpha' alpha, ->) edge("d", "=") & & X edge("dd", f "(sep)", ->, label-side: #left) \
          U edge("r", alpha, ->) edge("d", i, ->) & X' edge("ur", alpha', ->) edge("d", f', ->, label-side: #left) & \
          T edge("r", beta, ->) edge("ur", h_1, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", h_2, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Y' edge("r", beta', ->) & Y $, node((1.5, 1.5), $square$))
        $,
        kind: "diagram",
        caption: [(iv)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 20mm, $ T edge("r", h_1, ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("r", h_2, ->, shift: #(-2pt), label-side: #right, label-pos: #40%) edge("rr", alpha' h_1=alpha' h_2, ->, bend: #35deg) edge("dr", beta, ->, bend: #(-25deg)) & X' edge("r", alpha', ->) edge("d", f', ->, label-side: #left) & X edge("d", f, ->, label-side: #left) \
          & Y' edge("r", beta', ->) & Y $, node((1.5, 0.5), $square$))
        $,
        kind: "diagram",
        caption: [(v)],
        numbering: none,
        supplement: none,
      )
    ],
  )
  - Composing with $alpha'$, we have $T attach(⇉, t: alpha' h_1, b: alpha' h_2) X$ such that $f(alpha' alpha)=(beta' f') alpha=(beta' beta)i$, $alpha' alpha=alpha'(h_j i)=(alpha' h_j)i$ and $beta' beta=beta'(f' h_j)=f(alpha' h_j)$ for $j=1,2$.
    By (4.3), the separatedness of $f$ implies $alpha' h_1=alpha' h_2$.
  - Consider (v), by the fiber product $X'=X times_Y Y'$, we have $h_1=h_2$. $arrow.r.double^((4.3)) f'$ separated.

  (d)(e). These follow from [4.8].

  (f). ($Rightarrow$) Suppose ${V_i}$: open cover for $Y$. For each $i$, denote $U_i:=f^(-1)(V_i)$, $f_i:=f|_(U_i)$.
  Then, we have the diagram (vi) since $U_i=u_(U_i)^(-1)(U_i) isoBy([3.3]) U_i times_Y V_i=X times_Y V_i$.
  $=> f_i$ is the base change of $f$ through $u_(V_i)$. Now, $f$: separated. $arrow.r.double^(("c")) f_i$: separated.

  ($Leftarrow$). Suppose $exists {V_i}$: open cover for $Y$ such that $f_i:U_i=f^(-1)(V_i) morph(f, "") V_i$ is separated.
  - Consider diagram (vii) where $T attach(⇉, t: h, b: h') X$ making (i) commutative.
  - Suppose $t_1 in T$: (unique) generic point. $=> U={t_1}$. Write $x_1:=alpha(t_1)$ ($=h i(t_1)=h' i(t_1)$), and $y_1=f(x_1) in Y$. Say $y_1 in V_i$ for some $i$, so $x_1 in U_i$.
  - Choose a basic open set for which $t_1 in ops.spec R_f simeq D(f) subset beta^(-1)(V_i)$.
    Now, $f h(D(f)) eqBy(("vii")) beta(D(f)) subset V_i$. $=> h(D(f)) subset f^(-1)(V_i)=U_i$.
  #grid(
    columns: (1fr, 1fr, 1fr),
    gutter: 1em,
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 17mm, $ U_i edge("r", u_(U_i), ->) edge("d", f_i, ->, label-side: #left) & X edge("d", f, ->, label-side: #left) \
                                                V_i edge("r", u_(V_i), ->) & Y $, node((0.5, 0.5), $square$))
        $,
        kind: "diagram",
        caption: [(vi)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 17mm, $ ops.spec K=U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
          ops.spec R=T edge("r", beta, ->) edge("ur", h, ->, shift: #2pt, label-side: #left) edge("ur", h', ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & Y $)
        $,
        kind: "diagram",
        caption: [(vii) (Given $alpha,beta$)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #set text(size: 9pt)
      #figure(
        $
          #diagram(cell-size: 17mm, $ ops.spec K edge("r", alpha, ->) edge("d", i, ->) & U_i edge("d", f_i, ->, label-side: #left) \
          D(f) edge("r", beta|_(D(f)), ->, label-side: #right) edge("ur", h|_(D(f)), ->, shift: #2pt, label-side: #left, label-pos: #60%) edge("ur", h'|_(D(f)), ->, shift: #(-2pt), label-side: #right, label-pos: #40%) & V_i $)
        $,
        kind: "diagram",
        caption: [(viii)],
        numbering: none,
        supplement: none,
      )
    ],
  )
  - Similarly, $h'(D(f)) subset U_i$. Note, $ops.frac R_f=(R_f)_((0))=R_((0))=K$, so $D(f) attach(⇉, t: h|_(D(f)), b: h'|_(D(f))) U_i$ make (viii) commutative.
    By “separatedness” of $f_i$, $h|_(D(f))=h'|_(D(f))$.
    But $D(f) subset T$: nonempty open subset containing the generic point $t_1$. $=> h=h'$.
    Thus, $f$: separated by (4.3).
]

// Hartshorne II.4, Definition D2
#definition(number: none, title: "Proper Morphism")[
  Fix a scheme morphism $f:X morph("", cat.sch) Y$.
  - $f$ is *universally closed* if $f$ is closed and any base extension $f':X'=X times_Y Y' to Y'$ through $Y' to Y$ is closed.
  - $f$ is *proper* if $f$ is separated, of finite type, and universally closed.
]

// Hartshorne II.4, Theorem 4.7
#theorem(number: "4.7", title: "Valuative Theorem for Properness")[
  Suppose $f:X morph("", cat.sch) Y$ is of finite type with $X$ Noetherian.
  Then $f$ is proper $arrow.l.r.double$ (\*) holds, i.e. the “existence” and “uniqueness” parts follow.
]
#proof[
  #set math.equation(numbering: none)
  ($Rightarrow$).
  - $f$: proper. $arrow.r.double^("Def.") f$: separated. $arrow.r.double^((4.3))$ The “uniqueness” part of (\*) follows.
    It suffices to prove the “existence” part of (\*).
  - Given diagram (i) and consider the base extension (ii) where $X_T:=X times_Y T$.
    Since $f alpha=beta i$, by the product $X_T$, $exists U morph(theta, cat.sch) X_T$ for which $i=f' theta$, $beta' theta=alpha$.
  - Write $t_1:=(0) in U$ and set $xi_1:=theta(t_1) in X_T$. Take $Z:={xi_1}^- subset X_T$: closed.
    Since $f$: universally closed, $f'$: closed. $=> f'(Z) subset T$: closed.
  #grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    [
      #figure(
        $
          #diagram(cell-size: 21mm, $ ops.spec K=U edge("r", alpha, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
          ops.spec R=T edge("r", beta, ->) edge("ur", "-->") & Y $)
        $,
        kind: "diagram",
        caption: [(i) (Given $alpha,beta$)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #figure(
        $
          #diagram(cell-size: 20mm, $ U edge("r", theta, "-->") edge("rr", alpha, ->, bend: #30deg) edge("dr", i, ->, bend: #(-30deg)) & X_T edge("r", beta', ->) edge("d", f', ->, label-side: #left) & X edge("d", f, ->, label-side: #left) \
          & T edge("r", beta, ->) & Y $, node((1.5, 0.5), $square$))
        $,
        kind: "diagram",
        caption: [(ii)],
        numbering: none,
        supplement: none,
      )
    ],
  )
  But, $f'(xi_1)=f' theta(t_1)=i(t_1)=t_1$.
  $=> T={t_1}^-=(f'{xi_1})^- subset f'(Z)^-=f'(Z) subset T$, i.e. $f'(Z)=T$.
  $=> exists xi_0 in Z$ such that $f'(xi_0)=t_0$, the unique closed point of $T$.
  - We obtain a local homomorphism
    $
      #diagram(cell-size: (35mm, 17mm), $ shf.o_(T,t_0) edge("r", (f')^sharp_(xi_0), ->) edge("d", "=") & shf.o_(X_T,xi_0) edge("d", "=") \
                                        R_(idl.m_R)=R edge("r", ->) & shf.o_(Z,xi_0) $)
    $
    ($R$: local, $f'(Z)=T$.)
    of local rings, which is injective by the proof of (4.4 ii) and (4.A) by viewing $(f')^sharp_(xi_1)$.
  - Note. $xi_1 in Z$: generic point. $=> shf.o_(Z,xi_1)=k(xi_1)$, the function field of $Z$.
    Consider $theta^sharp:shf.o_(X_T) to theta_ast shf.o_U$, we have $theta^sharp_(t_1):k(xi_1)=shf.o_(X_T,xi_1) to shf.o_(U,t_1)=K$, which is a homomorphism of fields, thus injective, i.e. $k(xi_1) arrow.r.hook K$.
    $=> shf.o_(Z,xi_0)$ dominates $R$ in $K$. $arrow.r.double^(["I.6.1"]) R simeq shf.o_(Z,xi_0)$, i.e. $R$ dominates $shf.o_(Z,xi_0)$.
  - To conclude, we have $xi_0,xi_1 in Z subset X_T$ with $xi_1 arrow.r.squiggly xi_0$, $k(xi_1) subset K$, and $R$ dominates $shf.o_(Z,xi_0)$.
    By (4.4 ii), $exists$ morphism $T morph(Phi, cat.sch) X_T$ such that $t_k mapsto xi_k$ for $k=0,1$.
    Thus, we obtain $h:T morph(Phi, "") X_T morph(beta', "") X$.
  - Note. $h i(t_1)=beta' Phi i(t_1)=beta'(xi_1)=beta' theta(t_1) eqBy(("ii")) alpha(t_1)$, i.e. $h i=alpha$.
  - Further, $f h(t_1)=f beta' Phi(t_1) eqBy(("ii")) beta f' Phi(t_1)=beta f'(xi_1)=beta(t_1)$.
    As ${t_1} subset T$: dense, we have $f h=beta$.

  ($Leftarrow$).
  - Suppose (\*) holds. Then $f$: separated (4.3), of finite type (assumption).
    $=>$ It suffices to show $f$: universally closed.
  - Given any base change $f':X'=X times_Y Y' to Y'$ of $f$ through $alpha:Y' to Y$.
    Let $Z subset X'$: closed, and give it the reduced induced structure. Claim: $f'(Z) subset Y'$: closed.
  - $f$: finite type. $arrow.r.double^([3.13"d"]) f'$: finite type. $arrow.r.double^([3.13"b"]) f'|_Z$: finite type. $arrow.r.double^([3.3"a"]) f'|_Z$: quasi-compact.
    $arrow.r.double^((4.5))$ It suffices to show: $f'(Z)$ is stable under specialization.
  - Given $y_1=f'(z_1) in f'(Z)$, $y_0 in Y'$ with $y_1 arrow.r.squiggly y_0$. Claim. $y_0 in f'(Z)$.
  - Let $W:={y_1}^- subset Y'$: closed, with its reduced induced structure, $shf.o:=shf.o_(W,y_0)$.
  #grid(
    columns: (1fr,),
    row-gutter: 1.5em,
    [
      #figure(
        $
          #diagram(cell-size: 19mm, $ U edge("r", g, ->) edge("d", i, ->) & Z edge("r", j, arrow.hook) edge("d", f'|_Z, ->, label-side: #left) & X' edge("r", beta, ->) edge("d", f', ->, label-side: #left) & X edge("d", f, ->, label-side: #left) \
          T edge("r", h, ->) & Y' edge("r", "=") & Y' edge("r", alpha, ->) & Y $, node((2.5, 0.5), $square$))
        $,
        kind: "diagram",
        caption: [(iii)],
        numbering: none,
        supplement: none,
      )
    ],
    [
      #figure(
        $
          #diagram(cell-size: 20mm, $        U edge("r", beta j g, ->) edge("d", i, ->) & X edge("d", f, ->, label-side: #left) \
          T edge("r", alpha h, ->) edge("ur", theta, "-->") & Y $)
        $,
        kind: "diagram",
        caption: [(iv)],
        numbering: none,
        supplement: none,
      )
    ],
  )
  #figure(
    $
      #diagram(cell-size: 21mm, $ U edge("d", i, ->) edge("drr", beta j g, ->, bend: #40deg) & & \
      T edge("r", theta', "-->") edge("rr", theta, ->, bend: #30deg) edge("dr", h, ->, bend: #(-25deg)) & X' edge("r", beta, ->) edge("d", f', ->, label-side: #left) & X edge("d", f, ->, label-side: #left) \
      & Y' edge("r", alpha, ->) & Y $, node((1.5, 1.5), $square$))
    $,
    kind: "diagram",
    caption: [(v)],
    numbering: none,
    supplement: none,
  )
  Then, $exists$ natural map $shf.o_(W,y_0) arrow.r.hook shf.o_(W,y_1)=k(y_1)$ (field).
  $arrow.r.double^((4.A)) ops.frac shf.o=k(y_1)$ since our $W$ here is an integral scheme.
  Further, consider
  $ k(y_1)=shf.o_(W,y_1) morph((f')^sharp_(z_1), "") shf.o_(Z,z_1) to shf.o_(Z,z_1)\/idl.m_(z_1)=k(z_1), $
  which is a homomorphism between fields, thus injective. $=> k(y_1) subset k(z_1)$: subfield.
  - Take $K:=k(z_1)$. Note that $shf.o subset ops.frac shf.o=k(y_1) subset K$.
    $arrow.r.double^(["I.6.1"]) exists R subset K$: valuation such that $R$ dominates $shf.o$. Now, we have
    $
      cases(
        z_1 in Z "and" K=k(z_1). arrow.r.double^((4.4"i")) exists ops.spec K=U morph(g, cat.sch) Z, (0) mapsto z_1.,
        y_1 arrow.r.squiggly y_0 "in" Y', k(y_1) subset K "and" R "dominates" shf.o arrow.r.double^((4.4"ii")) exists ops.spec R=T morph(h, cat.sch) Y'
      )
    $
    with $t_k mapsto y_k$ where $t_0,t_1 in T$: unique closed, generic point, respectively.
  - Now, we have the commutative diagram (iii), (since $U={t_1}$ and that $h i(t_1)=y_1=f'(z_1)=f'|_Z dot g(t_1)$), which makes diagram (iv) commutative.
    By (\*), $exists T morph(theta, cat.sch) X$ such that $theta i=beta j g$ and $f theta=alpha h$.
  - Consider (v), since $alpha h eqBy(("iv")) f theta$, by the product $X'=X times_Y Y'$, $exists! T morph(theta', cat.sch) X'$ such that $h=f' theta'$ and $theta=beta theta'$.
  - Again, restricting $theta'$ to $U$, we have $alpha(h i) eqBy(("iv")) f(beta j g)$, so $exists! U morph(theta'', cat.sch) X'$ such that $f' theta''=h i$ and $beta theta''=theta i$.
    By “uniqueness” of $theta''$, we have $theta' i=theta''$.
    Further, $f'(j g) eqBy(("iii")) h i$ and $beta(j g) eqBy(("iv")) theta i$.
    By “uniqueness”, we have $j g=theta''=theta' i$.
  - Note. $U={t_1} => theta' i(t_1)=theta'(t_1)=j g(t_1)=g(t_1) in Z$.
    $=> theta'(T)=theta'({t_1}^-) subset.eq^("conti.") {theta'(t_1)}^- subset Z^-=Z$ (closed).
    $=> theta'$ factors as $theta':T morph(theta', "") Z inclusion(j, "") X'$.
  - Take $z_0:=theta'(t_0) in Z$, then $y_0=h(t_0) eqBy(("v")) f' theta'(t_0)=f'(z_0) in f'(Z)$. Done!
]

// Hartshorne II.4, Corollary 4.8
#remark(number: "4.E")[
  #set math.equation(numbering: none)
  From the proof of (4.7), one can see that: If $f:X morph("", cat.sch) Y$ is of finite type with $X$ Noetherian.
  Then $f$ is universally closed. $arrow.l.r.double$ The “existence” part of (\*) follows.
]

#corollary(number: "4.8")[
  #set math.equation(numbering: none)
  Assume all the schemes are Noetherian.
  #set enum(numbering: "(a)")
  + Closed immersions are proper.
  + Compositions of proper morphisms are proper.
  + Proper morphisms are stable under base extension.
  + Products of morphisms are proper.
  + If $X morph(f, cat.sch) Y morph(g, cat.sch) Z$ is proper with $g$ separated, then $f$ is proper.
  + “Properness” is local on the base.
]
#proof[
  #set math.equation(numbering: none)
  (a)–(e).
  - Note: “Finite type [3.13]” and “Separatedness (4.6)” are the properties $P$ (as in [4.8]).
    It suffices to show “Universal Closedness” is also a property $P$.

  (a). [3.11(a)]: Closed immersions are universally closed.

  (b). Clearly, given $X morph(f, "") Y morph(g, "") Z$ with $f,g$: universally closed.
  Consider any $Z' morph("", cat.sch) Z$, and the base extension $X':=X times_Z Z' morph((g f)', "") Z'$.
  Let $Y':=Y times_Z Z'$, then $(g f)':X' morph(f', "") Y' morph(g', "") Z'$ is closed since $f',g'$: closed.

  (c). Clearly, take $X'':=X' times_(Y') Y''=(X times_Y Y') times_(Y') Y''=X times_Y Y''$.
  - Now, “Properness” is also a property $P$, so (a)–(e) hold.

  (f).
  - “Finite type [3.3]” and “Separatedness (4.6f)” are local on the base.
    So it suffices to show that “Universal Closedness” is local on the base.
    But ($Rightarrow$) is clear, it remains to show ($Leftarrow$).

  ($Leftarrow$). Suppose ${V_i}$: open cover of $Y$ such that each $f_i=f|_(U_i):U_i:=f^(-1)(V_i) to V_i$ is universally closed.
  Claim. $f$: universally closed.
  - Given $Z subset X$: closed. Claim. $f(Z) subset Y$: closed.
    Note that $f(Z)=f(union_(i)(Z inter U_i))=union_i f(Z inter U_i)=union_i f_(i)(Z inter U_i)$.
    Since $f_i$: universally closed, and each $Z inter U_i subset U_i$: closed, $f_(i)(Z inter U_i) subset V_i$: closed.
    By (4.F), $f(Z)=union_i f_(i)(Z inter U_i)$: closed in $union_i V_i=Y$.
  - Given any base extension $f':X'=X times_Y Y' to Y'$ through $Y' morph(g, cat.sch) Y$.
    For each $i$, set $V_i':=g^(-1)(V_i)$, $U_i':=(f')^(-1)(V_i')$. Given $Z' subset X'$: closed.
    Note that $f_i':U_i' isoBy([3.3]) X times_Y V_i'=U_i times_(V_i) V_i' to V_i'$ is a base extension of $f_i$ through $V_i' morph(g, "") V_i$.
    By universal closedness of $f_i$, $f_i'$: closed mapping.
    $=> f_(i')(Z' inter U_i') subset V_i'$: closed.
    $arrow.r.double^((4.F)) f'(Z')=union_i f_(i')(Z' inter U_i')$: closed in $union_i V_i'=Y'$.
    Thus, $f'$: closed mapping. $=> f$: universally closed.
]

#lemma(number: "4.F", supplement: "Fact")[
  #set math.equation(numbering: none)
  Let $X in cat.top$ and ${U_i}$ be an open cover for $X$. Then
  #set enum(numbering: "(i)")
  + A subset $U subset X$ is open. $arrow.l.r.double$ Each $U inter U_i$ is open in $U_i$.
  + A subset $V subset X$ is closed. $arrow.l.r.double$ Each $V inter U_i$ is closed in $U_i$.
]
#proof[
  #set math.equation(numbering: none)
  (i) Clear. (ii) ($Rightarrow$) is clear. We prove ($Leftarrow$).

  ($Leftarrow$). Suppose $V inter U_i subset U_i$: closed for all $i$.
  $=> U_i without V$: open for all $i$.
  $arrow.r.double^(("i")) X without V subset X$: open. $=> V subset X$: closed.
]

// Hartshorne II.4, Definition D3
#definition(number: none, title: "Projective Spaces & Projective Morphisms")[
  - For $A$: ring, define $sch.p_A^n:=ops.proj A[x_0,dots,x_n] =$ the projective $n$-space over $A$.
  - For $Y$: scheme, define $sch.p_Y^n:=sch.p_ZZ^n times_(ops.spec ZZ) Y =$ the projective $n$-space over $Y$.
  - (Projective Morphism). $f:X morph("", cat.sch) Y$ is *projective* if $f$ can be factored as $f:X inclusion(i, "") sch.p_Y^n to Y$ for some $n >= 0$, where $i$: closed immersion.
  - (Quasi-Projective Morphism). $f:X morph("", cat.sch) Y$ is *quasi-projective* if $f$ can be factored as $f:X inclusion(j, "") X' morph(g, "") Y$, where $j$: open immersion, $g$: projective morphism.
]

// Hartshorne II.4, Theorem 4.9
#theorem(number: "4.9")[
  #set enum(numbering: "(i)")
  + Projective morphisms are proper.
  + Quasi-projective (quasi-compact) morphisms are separated of finite type.
]
#proof[
  #set math.equation(numbering: none)
  First, we prove the “properness of $sch.p_ZZ^n morph(g, cat.sch) ops.spec ZZ$”.
  Note that $g$ is clearly of finite type.

  (I). (Separatedness). Cover $sch.p_ZZ^n times_(ops.spec ZZ) sch.p_ZZ^n$ by ${pi_1^(-1)(D_+(x_i)) inter pi_2^(-1)(D_+(x_j))}_(0 <= i,j <= n)$.
  - Consider the diagonal morphism $Delta:sch.p_ZZ^n to sch.p_ZZ^n times_(ops.spec ZZ) sch.p_ZZ^n$, then
    $
      Delta^(-1)(pi_1^(-1)(D_+(x_i)) inter pi_2^(-1)(D_+(x_j)))
      & =(pi_1 Delta)^(-1)(D_+(x_i)) inter (pi_2 Delta)^(-1)(D_+(x_j)) \
      & =D_+(x_i) inter D_+(x_j)=D_+(x_i x_j) \
      & simeq ops.spec(S_((x_i x_j))),
    $
    where $S=ZZ[x_0,dots,x_n]$.
    So, $pi_1^(-1)(D_+(x_i)) inter pi_2^(-1)(D_+(x_j))=D_+(x_i) times_(ops.spec ZZ) D_+(x_j) simeq ops.spec(tensor(S_((x_i)), S_((x_j)), over: ZZ))$.
  - Clearly, $tensor(S_((x_i)), S_((x_j)), over: ZZ) morph("", cat.ring) S_((x_i x_j))$, $tensor(x_k/x_i, x_l/x_j) mapsto (x_k x_l)/(x_i x_j)$, is surjective.
    By [2.18c],
    $
      #diagram(cell-size: (65mm, 17mm), $ ops.spec(S_((x_i x_j))) edge("r", ->) edge("d", "=") & ops.spec(tensor(S_((x_i)), S_((x_j)), over: ZZ)) edge("d", "=") \
      Delta^(-1)(pi_1^(-1)(D_+(x_i)) inter pi_2^(-1)(D_+(x_j))) edge("r", Delta, ->) & pi_1^(-1)(D_+(x_i)) inter pi_2^(-1)(D_+(x_j)) $)
    $
    is a closed immersion for every $i,j$. But, “closed immersions are local on the base”, so $Delta$: closed immersion. $=> g$: separated.

  (II). (Universal Closedness).
  - Consider any base extension $g'$ of $g$ via $X' morph("", cat.sch) ops.spec ZZ$.
    Cover $X'$ by open affine subsets, by (4.F), it suffices to show that $sch.p_A^n=sch.p_ZZ^n times_(ops.spec ZZ) ops.spec A morph(g', "") ops.spec A$ is a closed map, for all $A$: ring.
    $
      #diagram(cell-size: 22mm, $ sch.p_(X')^n edge("r", g', ->) edge("d", ->) & X' edge("d", ->) \
                       sch.p_ZZ^n edge("r", g, ->) & ops.spec ZZ $, node((0.5, 0.5), $square$))
    $
  - Given $frak(a) ◁ A[x_0,dots,x_n]$: homogeneous. To show that $g'(V_+(frak(a))) subset ops.spec A$: closed, it suffices to show that $ops.im(ops.proj B morph(h, "") ops.spec A) subset ops.spec A$: closed, where $B=A[x_0,dots,x_n]\/frak(a)$, since $ops.proj B to sch.p_A^n$ is a closed immersion by [3.14].
    Now, set each $overline(x_i):=x_i+frak(a) in B$.
  - If $frak(p) in ops.spec A$ but $frak(p) in.not ops.im h$, then $h^(-1)(frak(p)) inter D_+(overline(x_i))=emptyset$ for each $i$ (as ${D_+(overline(x_i))}_(i=0)^n$ covers $ops.proj B$).
    Note that $h^(-1)(frak(p)) isoBy([3.10"a"]) ops.proj B times_(ops.spec A) ops.spec k(frak(p))$ (homeom.), we have
    $
      h^(-1)(frak(p)) inter D_+(overline(x_i))
      & =h^(-1)(frak(p)) times_(ops.spec A) D_+(overline(x_i)) \
      & simeq (ops.proj B times_(ops.spec A) ops.spec k(frak(p))) times_(ops.spec A) ops.spec B_((overline(x_i))) \
      & =ops.spec k(frak(p)) times_(ops.spec A) ops.spec B_((overline(x_i))) \
      & isoBy((3.3)) ops.spec(tensor(k(frak(p)), B_((overline(x_i))), over: A)).
    $
    - Recall. $ops.spec R=emptyset arrow.l.r.double 1_R=0_R$. Thus, $tensor(k(frak(p)), B_((overline(x_i))), over: A)=0$.
      $=> tensor(1, overline(x_i)) in ops.nil(tensor(k(frak(p)), B, over: A))$.
      Indeed $exists$ natural surjective homomorphism $B morph("", cat.ring) B_((overline(x_i)))$, $overline(b) in B_n mapsto overline(b)/overline(x_i)^n$.
      But, $tensor(k(frak(p)), dash, over: A)$: right exact, so $tensor(k(frak(p)), B, over: A) epi() tensor(k(frak(p)), B_((overline(x_i))), over: A)=0$, $tensor(1, overline(x_i)) mapsto tensor(1, overline(x_i)/overline(x_i))=1=0$.
      We may regard $tensor(1, overline(x_i)/overline(x_i)) in tensor(k(frak(p)), B_(overline(x_i)), over: A) simeq (tensor(k(frak(p)), B, over: A))_(overline(x_i))$ (since $k(frak(p))$: field, and $B_(x_i) simeq_(cat.mod_A) B_((overline(x_i)))$).
      By definition of “localization”, $exists n_i>0:(tensor(1, overline(x_i)))^(n_i)=0$, i.e. $tensor(1, overline(x_i)) in ops.nil(tensor(k(frak(p)), B, over: A))$.
    - Take $N >= max {n_i}_(i=0)^n$, i.e. $(tensor(1, overline(x_i)))^N=0$ for all $i$.
      $=> tensor(k(frak(p)), B_d, over: A)=0$ for every $d >= N$.
      Since $B$ is finitely generated by ${overline(x_0)^(d_0) dots overline(x_n)^(d_n):sum_(i=0)^n d_i=d}$ over $A$, and that
      $
        tensor(A_frak(p), B_d, over: A) / tensor(frak(p) A_frak(p), B_d, over: A) simeq tensor(k(frak(p)), B_d, over: A)=0,
      $
      by (Nakayama), $(B_d)_frak(p) simeq tensor(A_frak(p), B_d, over: A)=0$ for all $d >= N$.
      ($k(frak(p))$: flat over $A_frak(p) =>$ flat over $A$.)
    - As $B_d in fg(cat.mod_A)$, by [AM, 3.19(iv)], $V(ops.ann_(A)(B_d))={frak(q) in ops.spec A:(B_d)_frak(q) != 0}$ in $ops.spec A$.
      $=> ops.ann_(A)(B_d) subset.not frak(p)$ for all $d >= N$.
  - Claim. If $exists N>0$ with $ops.ann_(A)(B_d) subset.not frak(p)$ for all $d >= N$, then $frak(p) in.not ops.im h$.
    - If $exists$ such $N>0$, then $tensor(A_frak(p), B_d, over: A) simeq (B_d)_frak(p) eqBy(["AM"]) 0$ for all $d >= N$.
      $=> tensor(k(frak(p)), B_d, over: A)=0$ for all $d >= N$.
      $=> tensor(1, overline(x_i))^N=0$ for all $i$.
      $=> tensor(k(frak(p)), B_((overline(x_i))), over: A)=0$ for all $i$.
      $=> h^(-1)(frak(p)) inter D_+(overline(x_i)) simeq ops.spec(tensor(k(frak(p)), B_((overline(x_i))), over: A))=0$ for all $i$.
      But ${D_+(overline(x_i))}_(i=0)^n$ covers $ops.proj B$, so $h^(-1)(frak(p))=emptyset$, i.e. $frak(p) in.not ops.im h$.
  - Hence,
    $
      frak(p) in ops.im h & arrow.l.r.double "For all" N>0, exists d >= N:ops.ann_(A)(B_d) subset frak(p). \
                          & arrow.l.r.double "For all" d >= 0, ops.ann_(A)(B_d) subset frak(p) \
                          & quad ("since" ops.ann_(A)(B_d) subset ops.ann_(A)(B_(d+1))). \
                          & arrow.l.r.double union_(d >= 0) ops.ann_(A)(B_d) subset frak(p). \
                          & arrow.l.r.double frak(p) in V(union_(d >= 0) ops.ann_(A)(B_d)) quad ("closed in" ops.spec A).
    $
  Thus, $g:sch.p_ZZ^n to ops.spec ZZ$ is proper.

  (III). Now, given any projective morphism $X morph(f, cat.sch) Y$, we can factor $f$ into $f:X inclusion(i, "") sch.p_Y^n morph(p, "") Y$ with $i$: closed immersion.
  - Note. $p$ is a base extension of $g$ via $Y to ops.spec ZZ$.
    $arrow.r.double^((4.8"c")) p$: proper. By (4.8a), $i$: proper. $arrow.r.double^((4.8"b")) f=p i$: proper.
    $
      #diagram(cell-size: 22mm, $ sch.p_Y^n edge("r", p, ->) edge("d", ->) & Y edge("d", ->) \
                   sch.p_ZZ^n edge("r", g, ->) & ops.spec ZZ $, node((0.5, 0.5), $square$))
    $

  (IV). If $X morph(f, cat.sch) Y$ is quasi-projective, we factor $f$ into $f:X inclusion(j, "") X' morph(p, "") Y$ where $j$: open immersion and $p$: projective.
  $=> p$: proper by (III), and $j$: separated (4.6a) of finite type [3.13b].
  $=> f=p j$: separated (4.6b) of finite type [3.13c].
]

// Hartshorne II.4, Proposition 4.10
#proposition(number: "4.10")[
  Consider the functor $t:cat.var(k) to ops.sch(k)$ in (2.6). Then,
  #set enum(numbering: "(i)")
  + $ops.im t={"quasi-projective integral schemes over" k}$.
  + If $V in cat.var(k)$, then $V$: projective $arrow.l.r.double t(V) in ops.sch(k)$: projective integral.
  + For any $V in cat.var(k)$, $t(V) in ops.sch(k)$: integral separated scheme of finite type.
]
#proof[
  #set math.equation(numbering: none)
  (iii) This follows from (i) and (4.9 ii).

  (i) Note that every variety is a quasi-projective variety, i.e. a locally closed subset of $sch.p^n$, so it suffices to show (ii).

  (ii) ($Rightarrow$) Clearly from (3.2.1) and the explanation above.

  ($Leftarrow$). Suppose $Y$ is any such scheme, i.e. $Y morph("", cat.sch) ops.spec k$ is integral and projective.
  Then, $Y$ is a closed subscheme of $sch.p_k^n$ for some $n>0$.
  - Consider the set $V:={P in Y:"closed points"}$, which is closed in $sch.p_k^n eqBy([2.14d]) t(sch.p^n)$.
    $arrow.r.double^([3.14]) V$ is dense in $Y$.
    But, $Y$: integral. $arrow.r.double^((3.1)) Y$: irreducible. $=> V$: irreducible.
    Thus, $V$ defines a projective variety in $sch.p^n$.
  - Note that $ops.sp(V) isoBy((2.6)) ops.sp(Y)$ (homeom.), but they are both reduced closed subschemes of $sch.p_k^n$ (since $Y$: integral).
    $arrow.r.double^([3.11]) t(V) simeq Y$.
]

// Hartshorne II.4, Definition D4
#definition(number: none, title: "Abstract Variety")[
  An *abstract variety* over an algebraically closed field is an integral
  separated scheme of finite type. It is *complete* if it is proper over the
  field.
]

// Hartshorne II.4, Remark 4.10.1
#remark(title: "4.10.1")[
  From here on, “variety” means abstract variety. Chapter I varieties are
  identified with their associated quasi-projective schemes; curve, surface,
  and three-fold mean abstract varieties of dimensions $1,2,3$.
]

// Hartshorne II.4, Remark 4.10.2
#remark(title: "4.10.2")[
  Weil introduced abstract varieties to construct Jacobians algebraically.
  Complete varieties need not be projective: complete curves and smooth
  complete surfaces are projective, but singular complete surfaces and
  smooth complete three-folds may fail to be. Every variety nevertheless
  embeds as a dense open in a complete variety.
]

// Hartshorne II.4, Theorem 4.11A
#theorem(number: "4.11A")[
  If $A$ is a subring of a field $K$, its integral closure in $K$ is the
  intersection of all valuation rings of $K$ containing $A$.
]
