#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== The Gaussian Integers

#motivation(number: 86)[
  Consider the basic question, "When is a prime number the sum of two squares?"\ (e.g. the sequence $2=1^2+1^2, 5=1^2+2^2, 13=2^2+3^2$, etc.)
]


#theorem(number: 87)[
  For all prime numbers $p>2$, one has
  $
    p=a^2+b^2, (a,b in bb("Z")). quad arrow.l.r.double.long quad p equiv 1 (op("mod") 4).
  $

]


To prove Thm. 87. it is beneficial, as often in mathematics, to pass to a bigger domain of definition, and to consider the *Gaussian integers* $bb("Z")[i] := { a+b i:a,b in bb("Z")}$, (cf. *Example 10*).
The *norm* is the function $op("N"):bb("Z")[i] -> bb("N"), a+b i mapsto a^2+b^2=|a+b i|^2$. It's multiplicative, i.e. $op("N")(z dot w)= op("N")(z) dot op("N")(w)$.

#proposition(number: 88)[
  The ring $bb("Z")[i]$ is Euclidean and in particular a UFD. Its group of units is given by $bb("Z")[i]^ast ={ plus.minus 1, plus.minus i}.$
]

#proof[
  We prove the following two facts:\
  claim 1.
  The restricted norm $op("N")|_(bb("Z")[i] without {0}): bb("Z")[i] without {0} -> bb("N")$ is a degree function.\ Let $alpha,beta in bb("Z")[i], (beta eq.not 0)$. If $alpha=gamma dot beta$ for some $gamma in bb("Z")[i]$, we are done. Otherwise, there are $gamma,rho in bb("Z")[i]$ with $alpha=gamma dot beta+rho, rho eq.not 0, op("N")(rho)<op("N")(beta)$. Since $bb("Z")[i]$ forms a Lattice in $bb("C")$, we can find $gamma in bb("Z")[i]$ with $|frac(alpha, beta)-gamma|<frac(sqrt(2), 2)<1$, (two points in a mesh of a lattice have a distance of at most half of diagonal). $arrow.r.double |beta| |frac(alpha, beta)-gamma|=|alpha-gamma beta|<|beta|$. Now put $rho := alpha-gamma beta$.\
  claim 2.
  $alpha in bb("Z")[i]$ is a unit $arrow.l.r.double op("N")(alpha) =1$.\ "$arrow.r.double$"\ $alpha dot beta=1. arrow.r.double op("N")(alpha) dot op("N")(beta)=1. arrow.r.double op("N")(alpha)$ is a unit in $bb("Z"). arrow.r.double op("N")(alpha)=1$. \ "$arrow.l.double$"\ Write $1 := beta dot alpha+rho$. If $rho eq.not 0$, we may assume that $op("N")(rho)<op("N")(alpha)=1. arrow.r.double rho=0$ and $alpha in bb("Z")[i]$. Hence $op("N")(alpha)=op("N")(a+b i)=a^2+b^2=1. arrow.r.double (a,b)=( plus.minus 1,0)$ or $(0, plus.minus 1)$.
]

#proof[
  (i) Wir zeigen, dass $bb("Z")[i]$ euklidisch ist bzgl. der Funktion $bb("Z")[i] -> bb("N") union {0}, alpha mapsto |alpha|^2$. Sind $alpha,beta in bb("Z")[i], beta eq.not 0$, so ist die Existenz von Gaußschen Zahlen $gamma,rho$ nachzuweisen mit\ $alpha=gamma beta+rho quad$ und $quad |rho|^2<|beta|^2$.\
  Es genügt offenbar, ein $gamma in bb("Z")[i]$ zu finden mit $|frac(alpha, beta)-gamma|<1$. Die Gaußschen Zahlen bilden nur ein *Gitter* (Lattice) in der komplexen Zahlenebene $bb("C")$ (Punkte mit ganzzahligen Koordinaten bzgl. der Basis $1$ und $i$). Die komplexe Zahl $frac(alpha, beta)$ liegt in einer Masche des Gitters und hat vom nächsten Gitterpunkt einen Abstand, der nicht größer ist, als die halbe Länge $frac(sqrt(2), 2)$ der Diagonalen der Masche. Daher gibt es ein $gamma in bb("Z")[i]$ mit $|frac(alpha, beta)-gamma|<frac(sqrt(2), 2)<1$. [N, I.1.2]
]


#proofthm(number: 87)[
  "$arrow.r.double$"\ $because 2 divides.not p. therefore p$ must be the sum of squares of an odd and an even integer. $arrow.r.double p := (2k+1)^2+(2l)^2=4k^2+4k+1+4l^2 equiv 1 (op("mod") 4)$.\
  "$arrow.l.double$"\ Suppose $p equiv 1 (op("mod") 4)$ is a prime in $bb("Z")$ but not in $bb("Z")[i]$. Write $p := 1+4n$, then\ $-1 equiv [(2n)!]^2 (op("mod") p)$. Indeed, *Wilson's Thm.* implies that $-1 equiv (p-1)! (op("mod") p)$, whence
  $
    -1 & equiv (p-1)! \
       & equiv (p-1) dot (p-2) dots.h.c (p-2n) dot (2n) dot (2n-1) dots.h.c 1 \
       & equiv (-1)^(2n) dot (2n)! dot (2n)! \
       & equiv [(2n)!]^2 quad (op("mod") p).
  $

  (Note: $(p-1)(p-2) dots.h.c (p-2n)= sum_(i=1)^(2n)a_i p^i+(-1)^(2n)(2n)!$, for coefficients $a_i in bb("Z")$). \ Setting $X := [(2n)!]^2$, it follows that $p|x^2+1=(x+i)(x-i)$. But $p divides.not x plus.minus i$ since $frac(x, p) plus.minus frac(i, p) in.not bb("Z")[i]$, hence $p$ is not prime in $bb("Z")[i]$.
  $because bb("Z")[i]$ is a UFD. $therefore p := alpha dot beta$ for some nonunits $alpha,beta in bb("Z")[i]$.\ Moreover, $op("N")(alpha),op("N")(beta)>1$. Hence, $op("N")(p)= p^2=op("N")(alpha) dot op("N")(beta)$, which implies\
  $op("N")(alpha)=op("N")(beta)=p=a^2+b^2$,\ if $alpha := a+b i$ in $bb("Z")[i]$.
]


#proposition(number: 89)[
  Up to multiplying with units, the primes $pi$ of $bb("Z")[i]$ are:
  - _(i)_ $pi=1+i$;
  - _(ii)_ $pi=a+b i$ with $a^2+b^2=p, p equiv 1 (op("mod") 4)$ and $a>|b|>0$;
  - _(iii)_ $pi=p$, where $p equiv 3 (op("mod") 4)$,

  where $p$ denotes a prime number of $bb("Z")$.
]

#proof[
  The first two cases imply $op("N")(pi)=p=op("N")(alpha) dot op("N")(beta)$ for $pi=alpha dot beta$ and $p in bb("Z")$ prime. So either $op("N")(alpha)$ or $op("N")(beta)$ is a unit, whence $pi$ is a prime. If $p equiv 3 (op("mod") 4)$ and $pi=p=alpha dot beta, (alpha, beta in bb("Z")[i]). arrow.r.double op("N")(pi)=p^2=op("N")(alpha) dot op("N")(beta)$, which gives $p equiv 1 (op("mod") 4)$, unless $op("N")(alpha)$ or $op("N")(beta)$ is a unit. \
  Conversely, suppose that $pi in bb("Z")[i]$ is prime. Then $op("N")(pi)=pi dot overline(pi)= p_1 dot dots.h.c dot p_r, (p_i in bb("Z")$: prime). Hence $pi|p$ for some $p=p_i$, and therefore $op("N")(pi)|op("N")(p)=p^2$, so either $op("N")(pi)=p$ or $op("N")(pi)=p^2$.\ If $op("N")(pi)=p$, then $pi=a+b i$ with $a^2+b^2=p$ so that $p$ is of type (i) or (ii). If $op("N")(pi)=p^2$, then writing $p := alpha dot pi (alpha in bb("Z")[i])$ gives $op("N")(alpha) dot op("N")(pi)=p^2$ and thus $alpha$ must be a unit. But then $p$ is prime in $bb("Z")[i]$  and they cannot be of the form $p=2=(1+i)(1-i)$ or $p equiv 1 (op("mod") 4)$, whence $pi$ is of type (iii).
]

#proof[
  Die Zahlen unter (i) und (ii) sind prim, weil aus einer Zerlegung $pi=alpha dot beta$ in $bb("Z")[i]$ die Gleichung \
  $p= op("N")(pi)=op("N")(alpha) dot op("N")(beta)$
  mit einer Primzahl $p$ folgt, so dass entweder $op("N")(alpha)=1$ oder $op("N")(beta)=1$, also entweder $alpha$ oder $beta$ eine Einheit (unit) ist. Die Zahlen $pi=p, (p equiv 3 op("mod") 4)$, sind prim in $bb("Z")[i]$, weil eine Zerlegung $p=alpha dot beta$ in Nicht-Einheiten $alpha,beta$ zur Folge hätte, dass $p^2=op("N")(alpha) dot op("N")(beta)$ ist, d.h. $p=op("N")(alpha)= op("N")(a+b i)=a^2+b^2$, woraus sich nach *Satz. 87* $p equiv 1 op("mod") 4$ ergäbe.\
  Nach dieser Feststellung haben wir zu zeigen, dass ein beliebiges Primelement $pi$ von $bb("Z")[i]$ assoziiert ist zu einem der Genannten. Zunächst folgt aus \ $op("N")(pi)=pi dot overline(pi)= p_1 dot dots.h.c dot p_r, quad p_i:$ Primzahl in $bb("Z")$, dass $pi|p$ für ein $p=p_i$, also $op("N")(pi)|op("N")(p)=p^2$, d.h. entweder $op("N")(pi)=p$ oder $op("N")(pi)=p^2$. Im Falle $op("N")(pi)=p$ ist $pi=a+b i$ mit $a^2+b^2=p$, d.h. $pi$ ist vom Typ (ii) oder, wenn $p=2$ ist, assoziiert zu $1+i$. Ist aber $op("N")(pi)=p^2$, so ist $pi$ zu $p$ assoziiert, weil $frac(p, pi)$ wegen $op("N")(frac(p, pi))=1$ eine Einheit ist. Es muss überdies $p equiv 3 op("mod") 4$ gelten, weil sonst $p=2$ oder $p equiv 1 op("mod") 4$ und nach Satz. 87, $p=a^2+b^2=(a+b i)(a-b i)$ nicht prim wäre. Damit ist alles gezeigt. [N, I.1.4]
]


#note(number: "89*", title: [])[
  $bb("Z")[i]=bb("Z") dot 1 plus.o bb("Z") dot i$ is a free $bb("Z")$-module in $bb("Q")(i)={ a+b i:a,b in bb("Q")}$ and plays the same role as $bb("Z")=bb("Z") dot 1$ in $bb("Q")$. For a basis independent characterisation we have the following proposition.
]


#proposition(number: 90)[
  $bb("Z")[i]$ consists precisely of those elements in $bb("Q")(i)$ which satisfy a monic polynomial equation $x^2+a x+b=0, (a,b in bb("Z"))$.
]

#proof[
  Note that $c+d i in bb("Q")(i)$ is a root of the polynomial $x^2+alpha x+beta in bb("Q")[x]$ with
  $
    alpha := -2c quad text("and") quad beta := c^2+d^2.
  $

  Hence $alpha,beta in bb("Z")$ if $c,d in bb("Z")$.\
  Conversely, if $alpha,beta in bb("Z")$, then $2c,2d in bb("Z")$. (Note: $(2d)^2=4beta-(2c)^2$ and a rational number whose square is in $bb("N")$ must be an integer). It follows that $(2c)^2+(2d)^2=4beta equiv 0 (op("mod") 4)$. Since all squares must be either $0$ or $1 (op("mod") 4)$, we must have $(2c)^2 equiv (2d)^2 equiv 0 (op("mod") 4)$, so that $c^2,d^2 in bb("Z")$, whence $c,d in bb("Z")$.
]


#remark(number: "90*", title: [])[
  This result sets out the goal of this section: Given a finite field extension $bb("Q") subset K$, try to find a natural ring extension $bb("Z") subset A$ characterised in the vein of *Prop. 81*, and analyse its $bb("Z")$-module structure.
]
