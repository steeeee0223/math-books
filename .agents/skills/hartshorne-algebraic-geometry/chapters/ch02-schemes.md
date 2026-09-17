# Chapter II: Schemes

**Source:** Hartshorne, II.1-II.9, printed pp. 60-200. This chapter allows general schemes; apply the noetherian, integrality, finite-type, and separation hypotheses of each result individually.

## Core idea

Define geometric objects by local rings and compatible sheaves, then reduce suitable questions to algebra on affine opens. Scheme structure retains generic points, nilpotents, residue fields, and relative information that a classical point set loses.

## Section map

| Section | Begins | Consult for |
|---|---:|---|
| II.1 Sheaves | 60 | Stalks, sheafification, exactness, gluing |
| II.2 Schemes | 69 | Spec, Proj, locally ringed spaces |
| II.3 First Properties of Schemes | 82 | Finiteness, subschemes, fibre products |
| II.4 Separated and Proper Morphisms | 95 | Diagonal, valuative criteria, abstract varieties |
| II.5 Sheaves of Modules | 108 | Quasi-coherence, coherence, twists |
| II.6 Divisors | 129 | Weil, Cartier, Picard group |
| II.7 Projective Morphisms | 149 | Linear systems, ampleness, projective bundles, blowups |
| II.8 Differentials | 172 | Cotangent and normal sheaves, canonical sheaf, adjunction |
| II.9 Formal Schemes | 190 | Completions, inverse limits, formal neighborhoods |

## Methods

### Stalks for exactness, overlaps for construction

**Use when:** checking a sheaf morphism or defining a sheaf, section, or morphism locally.

For a proposed sheaf map, compute the map on each stalk. A sequence of sheaves of abelian groups or modules is exact exactly when the stalk sequences are exact. In particular, a sheaf epimorphism gives local lifts of sections; it need not give a lift over an entire prescribed open set. Global sections are left exact, and Chapter III measures the obstruction to right exactness.

To construct something by gluing, first specify local data, then their identifications on pairwise overlaps, and finally the cocycle compatibility on triple overlaps. Uniqueness comes from the sheaf condition or the relevant gluing theorem. Showing that local pieces are individually isomorphic is not enough without compatibility.

### Spec, Proj, and fibre products

**Use when:** replacing a scheme calculation by a ring calculation.

For `X=Spec A`, points are prime ideals, `O_{X,p}=A_p`, and `Gamma(D(f),O_X)=A_f`. The residue field at `p` is `Frac(A/p)`. A ring map `A -> B` induces `Spec B -> Spec A` by contraction of primes, with local maps on stalks (II.2.3).

For a graded ring `S`, `Proj S` uses homogeneous prime ideals not containing the irrelevant ideal `S_+`. Its chart is

\[
D_+(f)\simeq\operatorname{Spec}(S_f)_0,
\]

where the degree-zero part is essential (II.2.5). Do not use the whole graded localization as the affine coordinate ring of the chart.

For maps `Spec A -> Spec R <- Spec B`, the fibre product is `Spec(A tensor_R B)`. Compute a fibre over `y` by tensoring with `k(y)`, not just by looking at inverse images of closed points. A geometric fibre further extends to an algebraic closure of `k(y)`.

**Why it works:** the universal property of the tensor product matches the universal property of the fibre product after reversing arrows. **Failure mode:** set-theoretic products omit scheme structure and residue-field extensions.

### Locality and finiteness

- A scheme is locally noetherian if it has an affine cover by spectra of noetherian rings; II.3.2 promotes this to every affine open. A noetherian scheme is also quasi-compact.
- Reducedness and integrality can be tested through appropriate local/affine descriptions. Reducedness alone does not imply irreducibility.
- A closed subscheme is specified by a quasi-coherent ideal sheaf, not merely its support (II.5.9).
- Finite type is a property relative to a morphism. A local ring of a finite-type variety is generally essentially of finite type over the field, not necessarily finitely generated as a field-algebra.

When proving a property from one cover, name the lemma making the property independent of that cover. Do not assume an affine open subset of the source maps onto an affine open subset of the target.

### Separatedness and properness

The morphism `f:X -> Y` is separated when its diagonal `X -> X x_Y X` is a closed immersion. It is proper when it is separated, of finite type, and universally closed.

For II.4.3, assume `X` noetherian. Separatedness is equivalent to at most one lift in each valuation-ring diagram. For II.4.7, also assume `f` finite type. Properness is equivalent to a unique lift in every such diagram. Existence tests whether a limit is missing; uniqueness tests whether more than one limit is possible. These are interpretations of the criterion, not replacements for the diagram and its hypotheses.

Use the stability results in II.4 to handle compositions and base extensions. Projective morphisms of noetherian schemes are proper (II.4.9). The converse is false.

### Quasi-coherent sheaves as modules

On `Spec A`, the functors `M -> M~` and `F -> Gamma(X,F)` give an equivalence between modules and quasi-coherent sheaves (II.5.5). On a noetherian affine scheme, coherent sheaves correspond to finitely generated modules. Under `A -> B`, pullback becomes `M tensor_A B`, while pushforward from `Spec B` is restriction of scalars (II.5.2).

Use the equivalence to calculate kernels, cokernels, tensor products, or localizations. Tensor product and pullback are right exact; add flatness before claiming left exactness. On a projective scheme over a noetherian ring, sufficiently positive twists of a coherent sheaf are generated by finitely many global sections (II.5.17). Chapter III supplies the accompanying cohomological vanishing.

### Divisors, invertible sheaves, and projective maps

For Weil divisors, II.6 works with noetherian integral separated schemes regular in codimension one; normal noetherian integral separated schemes give an important sufficient setting. Codimension-one local rings are DVRs, providing orders of rational functions. A Cartier divisor instead consists of local rational equations with unit ratios on overlaps; the general definition uses the sheaf of total quotient rings.

Cartier divisor classes identify with `Pic(X)` on an integral scheme (II.6.15). On a noetherian integral separated locally factorial scheme, Weil and Cartier divisors agree and `Cl(X) ~= Pic(X)` (II.6.11, II.6.16). Normality by itself does not make every Weil divisor Cartier.

Given an invertible sheaf `L` and generating global sections `s_0,...,s_n`, construct a map to `P^n` using the ratios `s_j/s_i` where `s_i` does not vanish (II.7.1). For an embedding, verify the extra closed-immersion criterion. A very ample line bundle exhibits an embedding; an ample bundle need only have suitable positive powers with this property in the finite-type setting of II.7.6.

Hartshorne defines `P(E)=Proj Sym E` with an invertible quotient `pi^*E -> O_{P(E)}(1)`. Use quotient lines when interpreting its points and universal property (II.7.12); do not silently switch to the subspace convention. A blowup uses the graded Rees algebra of an ideal sheaf, not the symmetric algebra of an unrelated bundle.

### Differentials and adjunction

Use `Omega_{B/A}` to represent `A`-derivations. Present a ring by generators and relations, differentiate the relations, and sheafify. The conormal sequence for a closed immersion `Y -> X` over `S` is

\[
I/I^2\longrightarrow\Omega_{X/S}|_Y\longrightarrow\Omega_{Y/S}\longrightarrow0.
\]

The displayed sequence does not have a zero at its left in general. In the nonsingular closed-subvariety situation of II.8.17 it is short exact, and `I/I^2` is locally free. For a nonsingular variety of dimension `n`, `omega_X=det Omega_{X/k}`. If `Y` is a nonsingular divisor on a nonsingular variety `X`, adjunction gives

\[
\omega_Y\simeq(\omega_X\otimes O_X(Y))|_Y.
\]

For a nonsingular degree-`d` hypersurface in `P^n`, this becomes `omega_Y ~= O_Y(d-n-1)` (II.8.20). Smoothness is relative; Chapter III distinguishes it from regularity over an arbitrary field.

### Formal neighborhoods

To study a closed subscheme defined by `I`, retain the successive thickenings defined by `I^m`. Formal completion assembles these infinitesimal neighborhoods. It is not merely the reduced closed subset, nor generally the ordinary spectrum of the completed ring with its full spectrum topology. Read II.9 before interchanging inverse limits with exact sequences; Mittag-Leffler conditions supply an important exactness criterion.

## Worked example: the doubled origin

Reconstruct II.2.3.6 and II.4.0.1. Take `U=Spec k[t]` and `V=Spec k[t]`, and identify their principal opens `D(t)` by the identity. Gluing gives a scheme `X` with two distinct origins and a shared punctured affine line.

1. A global function is a pair `(a(t),b(t))` whose images agree in `k[t,t^-1]`. Injectivity of localization gives `a=b`, so `Gamma(X,O_X)=k[t]`.
2. Put `R=k[t]_(t)` and `K=k(t)`. The generic-point map `Spec K -> X` lands in the common punctured open.
3. It has two extensions `Spec R -> X`, one through `U` and one through `V`. The closed point goes to different origins, so the extensions are distinct.
4. II.4.3 therefore proves that `X -> Spec k` is not separated. Since affine schemes are separated over `k`, `X` is not affine.

This also explains why the global ring fails to recover this scheme. The canonical map `X -> Spec Gamma(X,O_X)=A^1` identifies the two origins. An affine cover and a familiar global ring do not prove affineness.

## Key concepts and anti-patterns

| Concept | Working meaning | Common failed inference |
|---|---|---|
| Scheme | Locally a spectrum as a locally ringed space | Its closed points determine it |
| Stalk | Direct limit over neighborhoods | A global section always lifts from a sheaf quotient |
| Quasi-coherent | Locally associated to a module | Every sheaf is quasi-coherent |
| Coherent | Finite module data in the noetherian setting | The same finite-generation shortcut works over every ring |
| Invertible sheaf | Locally free of rank one | Ample means already very ample |
| Weil divisor | Codimension-one cycle with the required order theory | Normal implies locally factorial |
| Cartier divisor | Local equations modulo units | Arbitrary set-theoretic hypersurface data suffice |
| Proper | Separated, finite type, universally closed | Closed image over the original base suffices |

## Mental models and takeaways

1. A scheme carries local algebra at every prime, not just values at geometric closed points.
2. Local proof steps need a named locality result; constructions need compatible overlaps.
3. Distinguish the support, ideal sheaf, and infinitesimal thickenings of a closed subscheme.
4. Treat a projective map as a line bundle plus generating sections, then check embedding conditions separately.
5. Use valuation diagrams to diagnose missing or nonunique limits.

## Connects to

- [Chapter I](ch01-varieties.md): the classical geometric examples motivating these constructions.
- [Chapter III](ch03-cohomology.md): derived functors repair global exactness; flatness controls tensor operations in families.
- [Chapter IV](ch04-curves.md): divisors and invertible sheaves become concrete Riemann-Roch data.
- [Chapter V](ch05-surfaces.md): blowups and adjunction govern surface calculations.
