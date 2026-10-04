#import "@preview/theorion:0.6.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

#definition(title: "Abelian Category")[

  An _abelian category_ is a category $Af$ such that: for any objects $A,B in ops.ob Af$,

  - $ops.hom(A, B, over: Af)$ has a structure of ablian group.
  - The composition law is linear.
  - Finite direct sums exist.
  - Every morphism has a kernel and a cokernel.
  - Every monomorphism is the kernel of its cokernel; every epimorphism is the cokernel of its kernel.
  - Every morphism can be factored into an epimorphism followed by a monomorphism.
]

#remark[
  In an abelian category, a morphism is mono [resp. epi, isomorphism] $arrow.l.r.double.long$ it is injective [resp. surjective, bijective].
]

#definition(title: "Cochain Complex & Cohomology")[
  - A _complex_ $sym.cplx(A)$ in an abelian category $Af$ is a collection of objects $sym.coll(A^i, i in ZZ)$ together with morphisms $A^i arrow.r.long A^(i+1)$ such that $d^(i+1) compose d^i=0$ for all $i$.
  - A _morphism of complexes_ $(sym.cplx(A),d_A)$ and $(sym.cplx(B),d_B)$ in $Af$, denoted by $f:sym.cplx(A) to sym.cplx(B)$, is a set of morphisms $f^i:A^i to B^i$ for each $i$, which commute with the coboundary maps, i.e. $ f^(i+1)d_A^i=d_B^i f^i "for all" i. $
  - The _$i$th cohomology object_ $sym.coho(sym.cplx(A), i)$ of the complex $(sym.cplx(A),d)$ is defined to be $ops.ker d^i\/ ops.im d^(i-1)$.
  - If $f:sym.cplx(A) to sym.cplx(B)$ is a morphism of complexes, then $f$ indeces a natural map $h^i (f):sym.coho(sym.cplx(A), i) to sym.coho(sym.cplx(B), i)$ for every $i$.
  - If $0 to sym.cplx(A) to sym.cplx(B) to sym.cplx(C) to 0$ is a short exact sequence of complexes, then there are natural maps $delta^i:sym.coho(sym.cplx(C), i) to sym.coho(sym.cplx(A), i+1)$ giving rise to a long exact sequence
  $
    dots.c to sym.coho(sym.cplx(A), i) to sym.coho(sym.cplx(B), i) to sym.coho(sym.cplx(C), i) morph(delta^i, "") sym.coho(sym.cplx(A), i+1) to dots.c
  $
]

#definition(title: "Homotopy")[

  Let $f,g:sym.cplx(A) to sym.cplx(B)$ be two morphisms of complexes.

  - We say $f$ and $g$ are _homotopic_, written $f tilde.op g$, if there is a collection of morphisms $k^i:A^i to B^(i-1)$ for each $i$ (which need not commute with the $d^i$) such that $f-g=d k-k d$, precisely,
  $
    f^i-g^i=d_B^(i-1)k^i+k^(i+1)d_A^i "for every" i.
  $
  - The collection of morphisms $k=sym.coll(k^i, i in ZZ)$ is called a _homotopy operator_.
  - If $f tilde.op g$, then $f$ and $g$ induce the same morphism $sym.coho(f, i)=sym.coho(g, i)$ for every $i$.
]

#remark(title: "Covariant & Contravariant Functors")[
  - *(Additive Functor).* A covariant [resp. contravariant] functor $F: Af to Bf$ between two abelian categories is _additive_ if for any objects $A,A' in ops.ob Af$, the induced map $ops.hom(A, A', over: Af) to ops.hom(F A, F A', over: Bf)$ [resp. $ops.hom(A, A', over: Af) to ops.hom(F A', F A, over: Bf)$] is a homomorphism of abelian groups.
  - From now on, we only consider abelian categories and the exact [resp. left exact, right exact] covariant [resp. contravariant] functors between abelian categories are assumed to be additive.
]

#definition(title: "Resolutions")[

  A $(ast)$-_resolution_ of an object $A in ops.ob Af$ is a complex $sym.cplx(C)$ together with a morphism $epsilon:A to C^0$ such that every $C^i in ops.ob Af$ has property $(ast)$, and that the sequence
  $
    0 to A morph(epsilon, "") C^0 to C^1 to C^2 to dots.c
  $
  is exact.
]

#definition(title: "Injective Objects")[
  - An object $I in ops.ob Af$ is _injective_ if the functor $ops.hom(-, I, over: Af)$ is exact.
  - If every object of $Af$ is isomorphic to a subobject of an injective object of $Af$, we say that $Af$ has _enough injectives_.
]

#lemma(number: "1.A")[
  + If $Af$ has enough injectives, then every object has an injective resolution.
  + If $A to B$ is a morphism and both $A$ and $B$ admit injective resolutions $sym.cplx(I)$ and $sym.cplx(J)$, respectively. Then there exists a morphism $sym.cplx(f):sym.cplx(I) to sym.cplx(J)$ of complexes such that the diagram
    #remark[Diagram.] // TODO: recover the diagram in the remark
    commutes.
  + Any two injective resolutions of the same object are homotopy equivalent.
]
#proof[
  First, we show the existence of the cochain map $sym.cplx(f):sym.cplx(I) to sym.cplx(J)$.
  - Note that $J^0 in ops.ob Af$ is injective, the contravariant functor $ops.hom(-, J^0, over: Af)$ is exact. Apply to the exact sequence $0 to A arrow.r.tail I^0$, we have
    $ ops.hom(I^0, J^0, over: Af) epi(t: - compose epsilon_A) ops.hom(A, J^0, over: Af) to 0, $ i.e. $- compose epsilon_B$ is epi. Thus, $exists f^0 in ops.hom(I^0, J^0, over: Af) mapsto epsilon_B f$, i.e. $f^0epsilon_A=epsilon_B f$.
  - Suppose the $(n-1)$th step holds, i.e. such $f^(n-1)$ exists such that $f^(i+1)d_I^i=d_J^i f^i$ for every $0 <= i <= n-2$. Note that the object $J^n in ops.ob Af$ is injective, so $ops.hom(-, J^n, over: Af)$ is an exact functor, which gives the following exact sequence $ ops.hom(I^n, J^n, over: Af) morph(- compose d_I^(n-1), "") ops.hom(I^(n-1), J^n, over: Af) & morph(- compose d_I^(n-2), "") ops.hom(I^(n-2), J^n, over: Af),\
    d_J^(n-1)f^(n-1) & mapsto d_J^(n-1)f^(n-1)d_I^(n-2)=d_J^(n-1)d_J^(n-2)f^(n-2)=0. $ By exactness, $exists f^n in ops.hom(I^n, J^n, over: Af) mapsto d_J^(n-1)f^(n-1)$, i.e. $f^n d_I^(n-1)= d_J^(n-1)f^(n-1)$.

  Now, we show that such cochain map $sym.cplx(f)$ exists up to homotopy. Suppose $sym.cplx(g):sym.cplx(I) to sym.cplx(J)$ is another such cochain map. We construct the homotopy operater $sym.cplx(h):sym.cplx(I) to J^(circle.filled.tiny-1)$.
  - Define $h^i=0$ for every $i <= 0$.
  - For $i=1$, we shall find an $h^1:I^1 to J^0$ satisfying $h^1d_I^0=f^0-g^0$. First, since $d_I^0epsilon_A=0$, we may factor
    $
      d_I^0:I^0 epi(t: p^0) ops.coker epsilon mono(t: i^0)I^1.
    $
    Further, note that $(f^0-g^0)epsilon_A=epsilon_B (f-f)=0$, factor
    $
      f^0-g^0:I^0 epi(t: p^0) ops.coker epsilon mono(t: "j^0")J^0.
    $
    Apply the exact functor $ops.hom(-, J^0, over: Af)$ to $0 to ops.coker epsilon mono(t: i^0)I^0$, we have
    $
      ops.hom(I^1, J^0, over: Af) epi(t: - compose i^0) ops.hom(ops.coker epsilon_A, J^0, over: Af) to 0.
    $
    So, $exists h^1 in ops.hom(I^1, J^0, over: Af) mapsto j^0$. Finally,
    $
      f^0-g^0=j^0p^0=h^1i^0p^0=h^1d_I^0.
    $
  - Suppose the $n$th step holds, i.e. we have such $h^i$ for all $i <= n$ such that $f^i-g^i=h^(i+1)d_I^i+d_J^(i-1)h^i$ for all $i <= n-1$. First, factor $d_I^n:I^n epi(t: p^n) ops.coker d_I^(n-1) mono(t: i^n)I^(n+1)$ as $d_I^n d_I^(n-1)=0$. Note that
    $
      (f^n-g^n-d_J^(n-1)h^n)d_I^(n-1) & =d_J^(n-1) (f^(n-1)-g^(n-1))-d_J^(n-1)h^n d_I^(n-1) \
                                      & =d_J^(n-1) (h^n d_I^(n-1)+d_J^(n-2)h^(n-1))-d_J^(n-1)h^n d_I^(n-1) \
                                      & =0.
    $
    Factor
    $
      f^n-g^n-d_J^(n-1)h^n:I^n epi(t: p^n) ops.coker d_I^(n-1) mono(t: j^n)J^n.
    $
    Apply the exact functor $ops.hom(-, J^n)$ to $0 to ops.coker d_I^(n-1) mono(t: i^n) I^(n+1)$, we have
    $
      ops.hom(I^(n+1), J^n, over: Af) epi(t: - compose i^n)ops.hom(ops.coker d_I^(n-1), J^n) to 0.
    $
    So, $exists h^(n+1) in ops.hom(I^(n+1), J^n) mapsto j^n$. Finally,
    $
      f^n-g^n-d_J^(n-1)h^n=j^n p^n=h^(n+1)i^n p^n=h^(n+1)d_I^n.
    $
]
#definition(title: "Derived Functor")[
  Let $Af$ be an abelian category with enough injectives, and let $F: Af to Bf$ be a covariant left exact functor. We construct the _right derived functors_ $R^i F, i>=0$,  of $F$ as follows. For each $A in ops.ob Af$, choose once and for all an injective resolution $sym.cplx(I)$ of $A$. Then we define $R^i F(A) := sym.coho(F(sym.cplx(I)), i)$.
]

#theorem(number: "1.1")[

  Let $Af$ be an abelian category with enough injectives, and let $F: Af to Bf$ be a covariant left exact functor. Then

  + For each $i>=0$, $R^i F$ is an aditive functor from $Af$ to $Bf$. Futhermore, it is independent (up to isomorphism of functors) of the choice of injective resolutions.
  + There is a natural isomorphism $F simeq R^0 F$.
  + For each short exact sequence $0 -> A' -> A -> A'' -> 0$ and for each $i>=0$, there is a natural morphism $delta^i: R^i F(A'') -> R^(i+1) F(A')$, such that we obtain a long exact sequence
    $
      dots.c -> R^i F(A') -> R^i F(A) -> R^i F(A'') morph(delta^i, "") R^(i+1) F(A') -> dots.c.
    $
  + Given a morphism of the exact sequence of (c) to another short exact sequence $0 -> B' -> B -> B'' -> 0$, the $delta$'s give a commutative diagram
    $
      #diagram(
        cell-size: 15mm,
        $ R^i F(A'') edge("r", delta^i, ->) edge("d", ->) & R^(i+1) F(A') edge("d", ->) \
                      R^i F(B'') edge("r", delta^i, ->) & R^(i+1) F(B') $,
      ).
    $

  + For each injective $I in ops.ob Af$, and for each $i>0$, we have $R^i F(I)=0$.
]

#definition(title: "Acyclic Object")[

  Let $F:Af->Bf$ as in the theorem, ($F$ being a covariant left exact functor and $Af$ having enough injectives). An object $J in ops.ob Af$ is called _$F$-acyclic_ if $R^i F(J)=0$ for all $i>0$.
]

#proposition(number: "1.2")[
  With $F:Af->Bf$ as in _(1.1)_, suppose $sym.cplx(J)$ is an $F$-acyclic resolution of $A$. Then for each $i>=0$, there is a natural isomorphism $R^i F(A) simeq sym.coho(F(sym.cplx(J)), i)$.
]

=== Universal Property of Derived Functors


#definition(title: $delta$ + "-Functor")[

  Let $Af$ and $Bf$ be ablian categories. A (covariant) _$delta$-functor_ $T: Af to Bf$ is a collection of functors $(T^i)_(i>=0)$, together with a morphism $delta^i:T^i(A'') -> T^(i+1)(A')$ for each short exact sequence $0 -> A' -> A -> A'' -> 0$, such that the following conditions hold:

  + For each short exact sequence above, there is a long exact sequence
    $
      dots.c -> T^0(A') -> T^0(A) -> T^0(A'') morph(delta^0, "") T^1(A') -> dots.c\
      dots.c -> T^i(A) -> T^i(A'') morph(delta^i, "") T^(i+1)(A') -> T^(i+1)(A) -> dots.c;
    $

  + for each morphism of one short exact sequence (as above) into another $0 -> B' -> B -> B'' -> 0$, the $delta$'s give a commutative diagram
    $
      #diagram(
        cell-size: 15mm,
        $ T^(i)(A'') edge("r", delta^i, ->) edge("d", ->) & T^(i+1)(A') edge("d", ->) \
                      T^(i)(B'') edge("r", delta^i, ->) & T^(i+1)(B') $,
      ).
    $

]

#definition(title: "Universal Property")[

  The $delta$-functor $T=(T^i): Af -> Bf$ is _universal_ if, given any other $delta$-functor $S=(S^i): Af -> Bf$, and given any morphism of functors $f^0: T^0 -> S^0$, there exists a unique sequence of morphisms $f^i: T^i -> S^i$ for each $i>=0$, starting with the given $f^0$, which commute with the $delta^i$ for each short exact sequence.
]

#definition(title: "Effaceable Functor")[

  Let $F: Af->Bf$ be an additive functor.

  - $F$ is _effaceable_ if for each object $A in ops.ob Af$, there exists a monomorphism $u:A mono() M$, for some $M$, such that $F(u)=0$.
  - $F$ is _coeffaceable_ if for each object $A in ops.ob Af$, there exists an epimorphism $u:P epi() A$, for some $P$, such that $F(u)=0$.
]

#theorem(number: "1.3")[

  Let $T=(T^i)_(i>=0): Af->Bf$ be a covariant $delta$-functor. If $T^i$ is effaceable for each $i>0$, then $T$ is universal.
]
#proof[
  Grothendiect [1, II, 2.2.1]
]

#corollary(number: "1.4")[

  Assume that $Af$ has enough injectives. Then for any left exact functor $F: Af->Bf$, the derived functors $(R^(i)F)_(i>=0)$ form a universal $delta$-functor with $F simeq R^(0)F$. Conversely, if $T=(T^i)_(i>=0)$ is any universal $delta$-functor, then $T^0$ is left exact, and the $T^i$ are isomorphic to $R^(i)T^(0)$ for each $i>=0$.
]
