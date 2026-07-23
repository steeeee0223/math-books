#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

#definition(title: "Abelian Category")[
  An _abelian category_ is a category $Af$ such that: for any objects $A,B in ops.ob Af$,
  - $op("Hom")_Af (A,B)$ has a structure of ablian group.
  - The composition law is linear.
  - Finite direct sums exist.
  - Every morphism has a kernel and a cokernel.
  - Every monomorphism is the kernel of its cokernel; every epimorphism is the cokernel of its kernel.
  - Every morphism can be factored into an epimorphism followed by a monomorphism.
]
#remark[
  - In an abelian category, a morphism is mono [resp. epi, isomorphism] $arrow.l.r.double.long$ it is injective [resp. surjective, bijective].
]
#definition(title: "Cochain Complex & Cohomology")[
  - A _complex_ $A^op("bullet")$ in an abelian category $Af$ is a collection of objects $A^i_i in ZZ$ together with morphisms $A^i arrow.r.long A^(i+1)$ such that $d^(i+1) compose d^i=0$ for all $i$.
  - A _morphism of complexes_ $(A^op("bullet"),d_A)$ and $(B^op("bullet"),d_B)$ in $Af$, denoted by $f:A^op("bullet") to B^op("bullet")$, is a set of morphisms $f^i:A^i to B^i$ for each $i$, which commute with the coboundary maps, i.e. $f^(i+1)d_A^i=d_B^op("if")^i$ for all $i$.
  - The _$i$th cohomology object_ $h^i (A^op("bullet"))$ of the complex $(A^op("bullet"),d)$ is defined to be $ops.ker d^i\/ ops.im d^(i-1)$.
  - If $f:A^op("bullet") to B^op("bullet")$ is a morphism of complexes, then $f$ indeces a natural map $h^i (f):h^i (A^op("bullet")) to h^i (B^op("bullet"))$ for every $i$.
  - If $0 to A^op("bullet") to B^op("bullet") to C^op("bullet") to 0$ is a short exact sequence of complexes, then there are natural maps $op("delta")^i:h^i (C^op("bullet")) to h^(i+1) (A^op("bullet"))$ giving rise to a long exact sequence
  $
    dots.c to h^i (A^op("bullet")) to h^i (B^op("bullet")) to h^i (C^op("bullet")) arrow.r.long h^(i+1) (A^op("bullet")) to dots.c
  $
]
#definition(title: "Homotopy")[
  Let $f,g:A^op("bullet") to B^op("bullet")$ be two morphisms of complexes.
  - We say $f$ and $g$ are _homotopic_, written $op("fop")("sim") g$, if there is a collection of morphisms $k^i:A^i to B^(i-1)$ for each $i$ (which need not commute with the $d^i$) such that $f-g=op("dk")-op("kd")$, (precisely,  $f^i-g^i=d_B^(i-1)k^i+k^(i+1)d_A^i$ for every $i$).
  - The collection of morphisms $k=k^i_i in ZZ$ is called a _homotopy operator_.
  - If $op("fop")("sim") g$, then $f$ and $g$ induce the same morphism $h^i (f)=h^i (g)$ for every $i$.
]
#remark(title: "Covariant & Contravariant Functors")[
  - *(Additive Functor).* A covariant [resp. contravariant] functor $F: Af to Bf$ between two abelian categories is _additive_ if for any objects $A,A' in ops.ob Af$, the induced map $op("Hom")_Af (A,A') to op("Hom")_Bf (op("FA"),op("FA")')$ [resp. $op("Hom")_Af (A,A') to op("Hom")_Bf (op("FA")',op("FA"))$] is a homomorphism of abelian groups.
  - From now on, we only consider abelian categories and the exact [resp. left exact, right exact] covariant [resp. contravariant] functors between abelian categories are assumed to be additive.
]
#definition(title: "Resolutions")[
  A $( ast )$-_resolution_ of an object $A in ops.ob Af$ is a complex $C^op("bullet")$ together with a morphism $op("epsilon"):A to C^0$ such that every $C^i in ops.ob Af$ has property $( ast )$, and that the sequence
  $
    0 to A arrow.r.long C^0 to C^1 to C^2 to dots.c
  $
  is exact.
]
#definition(title: "Injective Objects")[
  - An object $I in ops.ob Af$ is _injective_ if the functor $op("Hom")_Af (-,I)$ is exact.
  - If every object of $Af$ is isomorphic to a subobject of an injective object of $Af$, we say that $Af$ has _enough injectives_.
]
#lemma(number: "1.A")[
  + *(i).* If $Af$ has enough injectives, then every object has an injective resolution.
  + *(ii).* If $A arrow.r.long B$ is a morphism and both $A$ and $B$ admit injective resolutions $I^op("bullet")$ and $J^op("bullet")$, respectively. Then there exists a morphism $f^op("bullet"):I^op("bullet") to J^op("bullet")$ of complexes such that the diagram
  #remark[Diagram.]
  commutes.
  + *(iii).* Any two injective resolutions of the same object are homotopy equivalent.
]
#proof[
  First, we show the existence of the cochain map $f^op("bullet"):I^op("bullet") to J^op("bullet")$.
  - Note that $J^0 in ops.ob Af$ is injective, the contravariant functor $op("Hom")_Af (-,J^0)$ is exact. Apply to the exact sequence $0 to A arrow.r.tail I^0$, we have $op("Hom")_Af (I^0,J^0)attach(arrow.r.twohead, t: "- compose op(\"epsilon\")_A")op("Hom")_Af (A,J^0) to 0$, i.e. $- compose op("epsilon")_B$ is epi. Thus, $exists \ f^0 in op("Hom")_Af (I^0,J^0) mapsto op("epsilon")_Bf$, i.e. $f^0op("epsilon")_A=op("epsilon")_Bf$.
  - Suppose the $(n-1)$th step holds, i.e. such $f^(n-1)$ exists such that $f^(i+1)d_I^i=d_J^op("if")^i$ for every $0 <= i <= n-2$. Note that the object $J^n in ops.ob Af$ is injective, so $op("Hom")_Af (-,J^n)$ is an exact functor, which gives the following exact sequence
  $
    op("Hom")_Af (I^n,J^n) arrow.r.long - compose d_I^(n-1) op("Hom")_Af (I^(n-1),J^n) & arrow.r.long - compose d_I^(n-2) op("Hom")_Af (I^(n-2),J^n),\
    d_J^(n-1)f^(n-1) & mapsto d_J^(n-1)f^(n-1)d_I^(n-2)=d_J^(n-1)d_J^(n-2)f^(n-2)=0.
  $
  By exactness, $exists \ f^n in op("Hom")_Af (I^n,J^n) mapsto d_J^(n-1)f^(n-1)$, i.e. $f^op("nd")_I^(n-1)= d_J^(n-1)f^(n-1)$.
  Now, we show that such cochain map $f^op("bullet")$ exists up to homotopy. Suppose $g^op("bullet"):I^op("bullet") to J^op("bullet")$ is another such cochain map. We construct the homotopy operater $h^op("bullet"):I^op("bullet") to J^(op("bullet")-1)$.
  - Define $h^i=0$ for every $i <= 0$.
  - For $i=1$, we shall find an $h^1:I^1 to J^0$ satisfying $h^1d_I^0=f^0-g^0$. First, since $d_I^0op("epsilon")_A=0$, we may factor  $d_I^0:I^0attach(arrow.r.twohead, t: "p^0") ops.coker op("epsilon")_op("Aattach") (arrow.r.tail, t: "i^0")I^1$. Further, note that $(f^0-g^0)op("epsilon")_A=op("epsilon")_B (f-f)=0$, factor $f^0-g^0:I^0attach(arrow.r.twohead, t: "p^0") ops.coker op("epsilon")_op("Aattach") (arrow.r.tail, t: "j^0")J^0$. Apply the exact functor $op("Hom")_Af (-,J^0)$ to $0 to ops.coker op("epsilon")_op("Aattach") (arrow.r.tail, t: "i^0")I^0$, we have $op("Hom")_Af (I^1,J^0)attach(arrow.r.twohead, t: "- compose i^0")op("Hom")_Af ( ops.coker op("epsilon")_A,J^0) to 0$. So, $exists \ h^1 in op("Hom")_Af (I^1,J^0) mapsto j^0$. Finally,
  $
    f^0-g^0=j^0p^0=h^1i^0p^0=h^1d_I^0.
  $
  - Suppose the $n$th step holds, i.e. we have such $h^i$ for all $i <= n$ such that $f^i-g^i=h^(i+1)d_I^i+d_J^(i-1)h^i$ for all $i <= n-1$. First, factor $d_I^n:I^op("nattach") (arrow.r.twohead, t: "p^n") ops.coker d_I^(n-1)attach(arrow.r.tail, t: "i^n")I^(n+1)$ as $d_I^op("nd")_I^(n-1)=0$. Note that
  $
    (f^n-g^n-d_J^(n-1)h^n)d_I^(n-1) & =d_J^(n-1) (f^(n-1)-g^(n-1))-d_J^(n-1)h^op("nd")_I^(n-1) \
                                    & =d_J^(n-1) (h^op("nd")_I^(n-1)+d_J^(n-2)h^(n-1))-d_J^(n-1)h^op("nd")_I^(n-1)=0.
  $
  Factor $f^n-g^n-d_J^(n-1)h^n:I^op("nattach") (arrow.r.twohead, t: "p^n") ops.coker d_I^(n-1)attach(arrow.r.tail, t: "j^n")J^n$. Apply the exact functor $op("Hom")_Af (-,J^n)$ to $0 to ops.coker d_I^(n-1)attach(arrow.r.tail, t: "i^n")I^(n+1)$, we have $op("Hom")_Af (I^(n+1),J^n)attach(arrow.r.twohead, t: "- compose i^n")op("Hom")_Af ( ops.coker d_I^(n-1),J^n) to 0$. So, $exists \ h^(n+1) in op("Hom")_Af (I^(n+1),J^n) mapsto j^n$. Finally,
  $
    f^n-g^n-d_J^(n-1)h^n=j^op("np")^n=h^(n+1)i^op("np")^n=h^(n+1)d_I^n.
  $
]
#definition(title: "Derived Functor")[
  Let $Af$ be an abelian category with enough injectives, and let $F: Af to Bf$ be a covariant left exact functor. We construct the _right derived functors_ $R^op("iF")_i >= 0$ of $F$ as follows. For each $A in ops.ob Af$, choose once and for all an injective resolution $I^op("bullet")$ of $A$. Then we define $R^op("iF") (A) := h^i (F(I^op("bullet")))$.
]
