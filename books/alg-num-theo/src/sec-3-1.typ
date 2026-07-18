#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge

== Spectra of Rings

#motivation(number: "166")[
  Consider $A=bb("C")[x]$ as a ring of functions $bb("C") -> bb("C")$. Given a point $P in bb("C")$ we take the associate valuation on $op("ord")_P:bb("C")(x)^times -> bb("Z")$, (cf. *Example 150*). The induced valuation ring is $bb("C")[x]_((x-P))$. One should therefore think of a point $P$ in terms of the prime ideal $(x-P)$ it defines.
]


#definition(number: "167", title: [Spectra])[
  The *(prime) spectrum* of a ring $A$ is defined by
  $
    op("Spec")A := {frak("p") lt.closed A: text("prime ideal")}.
  $

  For each ideal $frak("a") lt.closed A$, we define
  $
    cal("V")(frak("a")) := {frak("p") in op("Spec")A:frak("a") subset frak("p")} equiv op("Spec")(A/frak("a")).
  $

  Then
  - $cal("V")(0)=op("Spec")A$ and $cal("V")(A)= nothing$.
  - If ${frak("a")_i }_(i in I)$ is any family of ideals of $A$, then
  $
    cal("V")( sum_(i in I) frak("a")_i)= inter.big_(i in I) frak("a")_i.
  $

  - For any two ideals $frak("a"), frak("b") lt.closed A$, we have
  $
    cal("V")(frak("a") inter frak("b"))=cal("V")(frak("a") dot frak("b"))=cal("V")(frak("a")) union cal("V")(frak("b")).
  $


  In particular, the sets $cal("V")(frak("a"))$ define the closed sets of the so-called *Zariski topology* of $op("Spec")A$.
]


As usual in this course, we assume that $A$ is an integral domain with quotient field $K$, though everything remains true for arbitrary rings using a suitable notion of localisation.
#example(number: 168)[
  - _(a)_ $op("Spec") bb("C")[x]={(0)} union {(x-P):P in bb("C")}$ for the nontrivial prime ideals are maximal, (note: $bb("C")[x]$ is a UFD). They correspond to the points in $bb("C")$ and are called *closed points* since their closure is $overline({(x-P)})={(x-P)}$.\
    Moreover, $(0)$ is called the *generic point* -- its closure is all of $op("Spec") bb("C")[x]$, i.e. $(0)$ is dense in $op("Spec") bb("C")[x]$.\
    The nonempty open sets of $op("Spec") bb("C")[x]$ can be identified with the subsets of $bb("C")$ having finite complement. In particular, the Zariski topology is co-finite and much coarser than the Euclidean topology.
  - _(b)_ Similarly, $op("Spec") bb("Z")$ consists of the generic point $(0)$ and the closed points $(p)$, where $p in bb("Z")$ prime. As in the previous discussion, the nontrivial open sets are the subsets of $bb("Z")$ with finite complement.

]


#remark(number: 169)[
  We have $overline({frak("p")})=cal("V")(frak("p"))$ for all $frak("p") in op("Spec")A$. In particular, $frak("p")$ is a closed point iff $frak("p")$ is maximal. [Exercise]
]


#proposition(number: "170", title: [Radical Ideals])[
  For an ideal $frak("a") lt.closed A$, we define its *radical* by
  $
    sqrt(frak("a")) := {a in A:a^n in frak("a") text("for some") n in bb("N")_( >= 1)}.
  $

  This is an ideal which contains $frak("a")$. Let $X subset op("Spec") A$. If we define $cal("I")(X) := inter.big_(frak("p") in X) frak("p")$, then
  $
    cal("V(I")(X))=overline(X) quad text("and") quad cal("I(V")(frak("a")))=sqrt(frak("a")).
  $

]

#proof[
  We proof the second part. Note that $cal("I(V")(frak("a")))= inter.big_(frak("p") in cal("V")(frak("a"))) frak("p")$.
  \ "$supset$"\ Let $a in sqrt(frak("a"))$, then $a^n in frak("a")$ for some $n in bb("N")$. For any $frak("p") in cal("V")(frak("a")), because a^n in frak("a") subset frak("p"). therefore$ Either $a in frak("p")$ or $a^(n-1) in frak("p")$, it follows that $a in frak("p")$. Hence, $a in cal("I(V")(frak("a")))$.\
  "$supset$"\ Assume $a in cal("I(V")(frak("a")))$ but $a in.not sqrt(frak("a"))$. Indeed, if $a^n in.not frak("a"), forall n in bb("N")$, then $S := {f^i:i in bb("N")}$ is a multiplicative system disjoint from $frak("a"). because op("Spec") S^(-1)A equiv {frak("p") in op("Spec")A:frak("p") inter S= nothing }. therefore exists frak("p") in op("Spec")A$ such that $frak("p") supset frak("a")$ and $frak("p") inter S= nothing$. Thus, $a in.not inter.big_(frak("p") supset frak("a")) frak("p"). ( -> arrow.l )$
]


#definition(number: "171", title: [Structure Sheaf & Affine Scheme])[
  - For any open set $nothing eq.not U subset op("Spec")A$, we let $cal("O")_X(U) := inter.big_(frak("p") in U)A_frak("p") subset K$ and $cal("O")_X( nothing ) := {0}$.
  - Further, for open sets $V subset U$, the inclusion $rho_(U V):cal("O")(U) -> cal("O")(V)$ defines the so-called *restriction morphism* satisfying $rho_(U U)=1_(cal("O")(U))$ and $rho_(V W) compose rho_(U V)= rho_(U W)$. We write $s|_V := rho_(U V)(s)$.
  - A *presheaf of rings* is an assignment $U mapsto cal("O") (U)$ together with restriction morphisms. The elements $s in cal("O")_X(U)$ are called *sections*.
  - In fact, $cal("O")$ defines a *sheaf*, which is called the *structure sheaf*; the pair $(op("Spec")A,cal("O"))$ is called an *affine scheme*.
  - Given $s in cal("O")_X(U)$ and a point $frak("p") in U subset X$, we define the "value" of $s(frak("p"))$ by
  $
    s(frak("p")) := overline(s) in A_frak("p")/frak("p")A_frak("p")=k(A_frak("p")).
  $

  Of course there values $s(frak("p"))$ live a priori in different (residue) fields which is why we call $s$ a section, not a function.
  For instance, the value of $f in bb("C")[x]$ at the generic point $(0)$ is $f$ "evaluated" at the unknown $x$. Namely, $f((0))=overline(f)=f(x) in op("Quot")(bb("C")[x]/(0))$. Since $frak("p")={a in A:a(frak("p"))=0}$, we can recover any point from the ideal of "functions" vanishing at it.

]


#remark(number: 172)[
  - _(a)_ The construction above makes sense for any ring. If $A$ is not an ID, this requires a more general localisation procedure, cf. [G, Ch6]. However, IDs are sufficient for our purposes.
  - _(b)_ We have $cal("O")(op("Spec")A)=A$. [Exercise]
  - _(c)_ For $s in cal("O")_X(U) subset K$, we consider its *zero locus* $cal("V")(s)={frak("p") in op("Spec")A:s(frak("p"))=0}$. If $s in A$, then $cal("V")(s)=cal("V")((s)))={frak("p") in op("Spec")A: frak("p") supset (s)}$. For example, $cal("V")((s))=s^(-1)(0)$ in $op("Spec") bb("C")[x]$ for $s in bb("C")[x]$.

]


#definition(number: "173", title: [Scheme Morphism])[
  \ Let $X=op("Spec")A$ and $Y=op("Spec")B$. A *scheme morphism* $F:(Y,cal("O")_Y) -> (X,cal("O")_X)$ consists of a continuous map $f:op("Spec")B -> op("Spec")A$ and a family of ring homomorphisms $f_U^ast :cal("O")_X(U) -> cal("O")_Y(f^(-1)(U))$, where $U subset X$ open, such that
  - For any open sets $V subset U$, we have $rho_{f^(-1)(U)f^(-1)(V)} compose f_U^ast =f_V^ast compose rho_(U V)$.
  #align(center)[
    #diagram(
      cell-size: 18mm,
      $
        cal("O")_X(U) edge("r", f_U^ast, ->) edge("d", rho_(U V), ->)
        & cal("O")_Y(f^(-1)(U)) edge("d", rho_(f^(-1)(U) f^(-1)(V)), ->) \
        cal("O")_X(V) edge("r", f_V^ast, ->)
        & cal("O")_Y(f^(-1)(U))
      $,
    )
  ]
  - For any $frak("q") in f^(-1)(U)$ and $s in cal("O")(U)$, we have
  $
    s(f(frak("q")))=0 quad arrow.r.double.long quad f_U^ast (s)(frak("q"))=0,
  $

  that is, $f^(-1)(cal("V")(s)) subset cal("V")(f^ast_U(s))$.

  We often simply write $F:op("Spec")B -> op("Spec")A$.\ In particular, a *scheme isomorphism* is a scheme morphism with a two-sided inverse.
]


#example(number: 174)[
  A ring homomorphism $phi:A -> B$ induces a scheme morphism\ $F:(op("Spec")B, cal("O")_Y) -> (op("Spec")A, cal("O")_X)$ via
  $
    f(frak("q")) := phi^(-1)(frak("q")) quad text("and") quad f_U^ast (s)(frak("q")) := phi_(frak("q")) compose s(phi^(-1) (frak("q"))).
  $

  Here, $phi_(frak("q"))$ is the naturally induced map $phi_frak("q"):A_{phi^(-1) (frak("q"))} -> B_frak("q"), frac(a, b) mapsto frac(phi(a), phi(b))$.
]


#example(number: "174*", title: [])[
  We obtain a scheme morphism $F=(f,f^ast ):(Y,cal("O")_Y) -> (X,cal("O")_X)$, where $X=op("Spec")A$ and $Y=op("Spec")B$, from a ring morphism $phi:A -> B$ as follows:
  - For $f:Y -> X$ we define $f(frak("q")) := phi^(-1)(frak("q"))$. It is easy to see that $f^(-1)(cal("V")(frak("a")))=cal("V")(phi(frak("a")))$, hence $f$ is continuous.
  - To define $f^ast$, we note that for every $frak("p") in X$, there is a unique map
  #align(center)[
    #diagram(
      cell-size: 17mm,
      $
                        A edge("r", phi, ->) edge("d", ->) & B edge("d", ->) \
        A_(f(frak("q"))) edge("r", hat(phi)_frak("q"), ->) & B_frak("q")
      $,
    )
  ]
  by the universal property of localisation, (cf. AM, 3.1).
  - In fact, $hat(phi)_frak("q")(frac(g, h))= frac(phi(g), phi(h))$. Then define
  $
    f(x)=cases(0 & text("if") f^(-1)(U)= nothing, hat(phi)_frak("q")|_(cal("O")_X(U)) & text("if") frak("q") in f^(-1)(U)).
  $

  This is compatible with restrictions by design.
  - Furthermore, let $s=frac(g, h) in A_(f(frak("q")))$. If $s(f(frak("q")))=0$, then $frac(g, h) in f(frak("q"))A_(f(frak("q")))$, that is, $g in f(frak("q"))=phi^(-1)(frak("q"))$. It follows that $phi(g) in frak("q")$, i.e. $f_U^ast (s)=frac(phi(g), phi(h)) in frak("q")A_frak("q")$, whence $f_U^ast (s)(frak("q"))=0$.

]


#theorem(number: 175)[
  Every scheme morphism is of the form $(op("Spec")B,cal("O")_Y) -> (op("Spec")A,cal("O")_X)$.
]

#proof[
  *Sketch*. Write $X=op("Spec")A, Y=op("Spec")B, K=op("Quot")A$ and $L=op("Quot")B$ and we denote by $op("Hom")(X,Y)$ the set of scheme morphisms $F=(f,f^ast ):Y -> X$. Now, consider the following map
  $
    Phi:op("Hom")(X,Y) arrow.r.long op("Hom")(A,B), F arrow.r.long.bar phi := f_X^ast :A -> B.
  $

  Now that:
  - $Phi$ is surjective. This follows from an example in the lecture notes where we constructed a scheme morphism $F=(f,f^ast ): op("Spec")B -> op("Spec")A$ for every $phi:A -> B$ such that $f_X^ast =phi$, (cf. *Example 174*).
  - $Phi$ is injective. This requires some sheaf theory. Namely, a sheaf morphism ${f_U^ast :cal("O")_X(U) -> cal("O")_(Y)(f^(-1)(U))}$ gives rise to a ring morphism $f_(frak("q"))^ast :A_(f(frak("q"))) -> B_(frak("q"))$ such that $f_(frak("q"))^ast (s)=f_U^ast (s)$ whenever $s in cal("O")_X(U)$ and $f(frak("q")) in U$.\
    The second condition in the definition of a scheme morphisms ensures that $f_(frak("q"))^ast$ is a local morphism, that is, if $frak("p")^e$ and $frak("q")^e$ are the maximal ideals of $A_(f(frak("q")))$ and $B_frak("q")$, respectively, then $f_frak("q")^ast (frak("p")^e) =frak("q")^e$. Indeed, if $s in frak("a") inter cal("O")_X(U)$ for some $frak("a") in U$, then $s(f(frak("q")))=0.\ arrow.r.double f_U^ast (s)(frak("q"))=f_frak("q")^ast (s)(frak("q"))=0$, i.e. $f_frak("q")^ast (s) in frak("q")$. It follows that $frak("p")^e subset (f_frak("q")^ast )^(-1)(frak("q")^e)$ and since $frak("p")$ is maximal in $A_frak("p")$, we have the equality.\ Hence we obtain the commutative diagram
  #align(center)[
    #diagram(
      cell-size: 17mm,
      $
                     A edge("r", phi, ->) edge("d", ->) & B edge("d", ->) \
        A_(f(frak("q"))) edge("r", f_frak("q")^ast, ->) & B_frak("q")
      $,
    )
  ]
  and by the universal property of  the localisation, we have $f_frak("q")^ast (frac(g, h))=hat(phi)_frak("q")(frac(g, h))=frac(phi(g), phi(h))$. This shows that $f_frak("q")^ast$ is determined by $phi$ and thus ${f_U^ast }$ is determined by $phi$ since the $f_frak("q")^ast$'s determine ${f_U^ast }$, (this is the local native of schemes). \
  Finally, consider that $f(frak("q")) in op("Spec")A$. This is determined by
  $
    f(frak("q")) ,={a in A:a(f(frak("q")))=0} ; ,={a in A:f_frak("q")^ast (a)(frak("q"))=0} ; ,={a in A:f_X^ast (a)(frak("q"))=0} quad text("since") a in cal("O")_X(X)=A ; ,={a in A:phi(a) in frak("q")=0} ; ,=phi^(-1)(frak("q")).
  $

  Hence, $phi$ also determines $f$.

]


#remark(number: 176)[
  Everything we stated so far remains true for arbitrary commutative rings. The previous theorem then states that the category of affine schemes is equivalent to the category of commutative rings generalising the equivalence of categories between affine varieties over an algebraically closed field $k$ and the category of finitely generated $k$-algebras which are integral domains.\ The additional difficulty of working with general rings which are not necessarily integral domains comes from nilpotent elements. For instance, compare $op("Spec") bb("C")[x]/(x)$ (one closed point, "functions" are $a+b overline(x), (a,b in bb("C"))$, but $overline(x)$ is a nilpotent function!) Though the geometric interpretation of nilpotent functions is difficult at first glance they prove to be extremely important from a geometric point of view as well.
]


#example(number: 177)[
  - *Fields.* For $X=op("Spec") k, (k:text("field"))$, consists of one (closed) point. Further, $cal("O")_X( nothing )=0$ and $cal("O")_X(op("Spec") k)=k$. Hence, the spectra of distinct fields are homeomorphic topological spaces, but not isomorphic as affine schemes.
  - *DVRs.* For $X=op("Spec")A, (A: text("DVR"))$, consists of two points: The generic point $(0)$ and the closed point given by its maximal ideal $frak("m")$. Further, $cal("O")((0))=op("Quot")A$ and $cal("O")(op("Spec")A)=A$. We thus think of $X$ as an infinitesimal neighbourhood of $frak("m")$.
  - *Dedekind Rings.* For $X=op("Spec") A, (A: text("Dedekind ring"))$, consists of the closed points given by the nontrivial prime ideals $frak("p")$ and the generic point $(0)$. The localisation $A_frak("p")$ gives a DVR with inclusion $A arrow.r.hook A_frak("p")$, whence
  $
    F:X_frak("p") := op("Spec")A_frak("p") -> X.
  $

  Thinking of $A_frak("p")$ as "functions", then
  $
    A_frak("p") = {frac(f, g):g(frak("p")) eq.not 0}
  $

  is the *function germ* of $op("Spec")A$ at $frak("p")$. If $(0) eq.not frak("q") in X$, then $frak("q")+frak("p")=A$, so we find $g in A$ with
  $
    g equiv 1 (op("mod") frak("p")) quad text("and") quad g equiv 0 (op("mod") frak("q"))
  $

  by *CRT*. Hence $frac(1, g) in A_frak("p")$, but $frac(1, g)$ is not defined on any open set containing $frak("q")$, thus $A_frak("p")$ is called the *local ring* of $frak("p")$.
  - *Polynomial Rings.* $X := op("Spec")A[x_1, dots.h.c ,x_n]$ is called the affine $n$-space over $A$ and denoted by $bb("A")_A^n$. A prominent example is $A=k$, ($k$: algebraically closed field). Here, maximal ideals correspond to points of $k^n$. (cf. *Cor. 196*).

]


#remark(number: 178)[
  Recall that any DVR arises as the localisation of a Dedekind ring by *(121)*.
]


#note(number: "179", title: [Geometric View on Ring Extensions])[
  We consider a Dedekind ring $A$ with quotient field $K$ and a finite separable extension $L/K$. Let $overline(A)$ be the integral closure of $A$ in $L$. The integral extension of Dedekind rings $A arrow.r.hook overline(A)$ leads to a scheme morphism
  $
    F=(f,f^ast ): X=op("Spec") overline(A) -> Y=op("Spec")A
  $

  with $f$ surjective, (cf. *Lying Over Thm. 190*).\
  If $frak("p") in op("Spec")A$, then $frak("p")^e := frak("P")_1^(e_1) dots.h.c frak("P")_r^(e_r)$ with $frak("p") := frak("P")_i inter A=f(frak("P")_i)$. If the quotient fields $A/frak("p")$ are algebraically closed, then $f_i=1$. Hence $sum e_i=[L:K]$, and $frak("p")$ ramifies iff the preimages $frak("p")^c$ under $f$ coincide. Topologically speaking, the map $f$ is a *ramified covering*.
]


#example(number: 180)[
  This requires some basic knowledge of Riemann surfaces.\
  Let $X$ and $Y$ be compact connected Riemann surfaces, and let $F:X -> Y$ be a nonconstant holomorphic mapping. Write $cal("M")(X)$ and $cal("M")(Y)$ to be the field of meromorphic functions on $X$ and $Y$, respectively. The map $f mapsto F compose f$ defines an inclusion $cal("M")(Y) arrow.r.hook cal("M")(X)$ and thus a finite extension of fields of degree $m$. The map is $m$-to-$1$ except at a finite number of branch points.\ Let $P in Y$ and $cal("O")_P$ be the set of meromorphic functions on $Y$ that are holomorphic at $P$. This is the DVR attached to the discrete valuation $op("ord")_P$, (cf. *Example 50*). Its maximal ideal $frak("q")$ is the set of meromorphic functions on $Y$ that vanish at $P$. \ Let $B$ be the integral closure of $cal("O")_P$ in $cal("M")(X), F^(-1)(P) := {Q_i:1 <= i <= g}$, and $e_i$ be the number of sheets of $X$ over $Y$ that coincide at $Q_i$. Then
  $
    frak("q")B= product_(i=1)^g frak("Q")_i^(e_i), text("where") frak("Q")_i := {f in B:f(Q_i)=0} lt.closed B text("prime ideal").
  $

]


#remark(number: 181)[
  In your Topology course you have seen unramified coverings, for instance the universal covering of a sufficiently good topological space. This has an algebraic counterpart.\
  In the situation of the previous note, we assume additionally that $L/K$ is Galois with the Galois group $op("Gal")(L/K)$. Then any $sigma in op("Gal")(L/K)$ fixes $K$ and in particular $A$, and thus maps $overline(A)$ to $overline(A)$. (Apply $sigma$ to an integral equation $f in A[x]$ satisfied by any element $x in overline(A)$. Then $sigma(f) in A[x]$ will be an integral equation for $sigma(x)$ over $A$). Hence $sigma$ induces a scheme morphism $op("Spec") overline(A) -> op("Spec") overline(A)$, also denoted by $sigma$, and we get a commutative diagram (with $F$ the scheme morphism from the previous note):
  #align(center)[
    #diagram(
      cell-size: 18mm,
      $
        op("Spec") overline(A) edge("r", sigma, ->) edge("dr", F, ->) & op("Spec") overline(A) edge("d", F, ->) \
                                                                      & op("Spec") A
      $,
    )
  ]
  The transformation $sigma$ is called a *Deck transformation* of the ramified covering $op("Spec") tilde(A) -> op("Spec")A$ corresponding to a field extension $tilde(K)/K$, (cf. *Cor. 277*). This scheme morphism is called the *universal covering*. One then defines the *fundamental group* of the scheme $op("Spec")A$ by $pi_1(Y) := op("Gal")(tilde(K)/K)$.
]
