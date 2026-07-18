#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Sheaves

#definition(number: "1", title: [Presheaf])[
  Let $X$ be a topological space. A *presheaf* $cal("F")$ of abelian groups on $X$ consists of the data:
  - For every open subset $U subset X$, an abelian group $cal("F")(U)$;
  - For every inclusion of open sets $V subset U$ of $X$, a morphism of abelian groups $rho_(U V):cal("F")(U) -> cal("F")(V)$,

  subject to the conditions:
  - $cal("F")( nothing )=0$.
  - $rho_(U U)=1_(cal("F")(U))$.
  - If $W subset V subset U$ are open subsets, then $rho_(U W)=rho_(V W) compose rho_(U V)$.

]


#definition(number: "2", title: [Stalk])[
  If $cal("F")$ is a presheaf on $X$ and if $P$ is a point on $X$, we define the *stalk* $cal("F")_P$ of $cal("F")$ at $P$ to be the direct limit of the groups $cal("F")(U)$ for all open sets $P in U$, via the restriction maps $rho$.
]


#remark(number: 3)[
  From the definition, we have the following observation:
  - $cal("F")_P={(U,s):U in cal("N")_P, s in cal("F")(U)}/ tilde$.
  - $(U,s) tilde (V,t). arrow.l.r.double.long exists W in cal("N")_P$ such that $W subset U inter V$ and $s|_W=t|_W$. Thus we may speak of elements of the stalk $cal("F")_P$ as *germs* of *sections* $s$ of $cal("F")$ at the point $P$.

]


#definition(number: "4", title: [Sheaf])[
  A presheaf $cal("F")$ on a topological space $X$ is *a sheaf* if it satisfies the following supplementary conditions:
  - Let $U subset X$ be an open set and ${V_i }$ be an open covering of $U$. If $s in cal("F")(U)$ is an element such that $s|_(V_i)=0$ for all $i$, then $s=0$.
  - If we have $s_i in cal("F")(V_i)$ for each $i$, with the property that $s_i|_(V_i inter V_j)=s_j|_(V_i inter V_j)$ for each $i,j$, then there is an element $s in cal("F")(U)$ such that $s|_(V_i)=s_i$ for each $i$.

  *Note.* The first condition implies that $s$ is unique.
]
