# Chapter III: Cohomology

**Source:** Hartshorne, III.1-III.12, printed pp. 201-292. Retain the hypotheses on the scheme, morphism, and sheaf separately. Several results are stated for projective morphisms even where stronger generalizations are known elsewhere.

## Core idea

Use cohomology to measure the failure of global sections to be exact, and turn geometry into calculations through exact sequences, affine vanishing, twists, and duality. In families, replace unsupported specialization arguments with flatness, semicontinuity, and base-change theorems.

## Section map

| Section | Begins | Consult for |
|---|---:|---|
| III.1 Derived Functors | 202 | Resolutions, long exact sequences, universal delta functors |
| III.2 Cohomology of Sheaves | 206 | Derived global sections, flasque resolutions |
| III.3 Cohomology of a Noetherian Affine Scheme | 213 | Vanishing and Serre's affineness criterion |
| III.4 Cech Cohomology | 218 | Explicit complexes and comparison |
| III.5 The Cohomology of Projective Space | 225 | Twists, finiteness, Serre vanishing |
| III.6 Ext Groups and Sheaves | 233 | Global Ext, sheaf Ext, local resolutions |
| III.7 The Serre Duality Theorem | 239 | Dualizing sheaves, Cohen-Macaulay hypotheses |
| III.8 Higher Direct Images of Sheaves | 250 | Relative coherent cohomology |
| III.9 Flat Morphisms | 253 | Tensor exactness, flat families, Hilbert polynomials |
| III.10 Smooth Morphisms | 268 | Relative differentials and geometric regularity |
| III.11 The Theorem on Formal Functions | 276 | Completed direct images and infinitesimal fibres |
| III.12 The Semicontinuity Theorem | 281 | Fibre dimensions and cohomology/base change |

## Methods

### Derived functors as controlled obstructions

**Use when:** applying a left exact functor to an exact sequence.

Start with a short exact sequence of sheaves, apply global sections, and retain the connecting homomorphism:

\[
0\to H^0(F')\to H^0(F)\to H^0(F'')
\xrightarrow{\delta}H^1(F')\to\cdots.
\]

A section of `F''` lifts globally exactly when its image under `delta` vanishes. Define the cohomology through an injective resolution; use an acyclic resolution or a Cech complex only after justifying that it computes the same derived functor. Universal delta-functor arguments compare constructions by their degree-zero functor and suitable effaceability, rather than by a superficial resemblance between complexes.

### Affine vanishing and Cech computation

For a quasi-coherent sheaf on a noetherian affine scheme, `H^i(X,F)=0` for `i>0` (III.3.5). Serre's criterion (III.3.7) says that for a noetherian scheme, affineness is equivalent to vanishing of all positive cohomology for all quasi-coherent sheaves, and also to vanishing of `H^1` for all coherent ideal sheaves. Testing only `O_X` is insufficient.

For a noetherian separated scheme, a quasi-coherent sheaf, and an affine open cover, Cech cohomology computes sheaf cohomology (III.4.5). Separatedness ensures the needed affine intersection behavior. Build the alternating restriction differential explicitly. Do not use the theorem for an arbitrary nonaffine cover or an arbitrary sheaf without checking acyclicity.

**Why it works:** cohomology on the affine pieces and their intersections vanishes in positive degrees, leaving the gluing complex to record the global obstruction. **Failure mode:** a convenient-looking cover can carry its own higher cohomology.

### Projective calculations by twists and resolutions

For a coherent sheaf `F` on a projective scheme over a noetherian ring `A`, III.5.2 gives finite `A`-modules `H^i(X,F)` and vanishing `H^i(X,F(n))=0` for `i>0` and all sufficiently large `n`. Combine this with II.5.17 to obtain surjections from finite sums of twists and then calculate using kernels and long exact sequences.

Useful starting sequences include

\[
0\to I_Y(n)\to O_X(n)\to O_Y(n)\to0
\]

and, for an effective Cartier divisor `D`,

\[
0\to O_X(-D)\to O_X\to O_D\to0.
\]

The second sequence depends on the Cartier condition. Euler characteristic is additive, but `h^0` alone generally is not. A Hilbert polynomial agrees with the corresponding section count only after the required higher-cohomology vanishing and large-degree conditions are satisfied.

### Ext and Serre duality

Keep global `Ext^i_X(F,G)` separate from the sheaf `mathcal Ext^i_X(F,G)`. A locally free resolution computes the sheaf Ext after applying sheaf Hom. For a locally free finite-rank `E`, global Ext against `E` is computed by cohomology of `E^vee tensor G`; it does not vanish merely because local sheaf Ext does.

On a projective Cohen-Macaulay scheme of pure dimension `n` over the algebraically closed field, III.7.6 gives

\[
\operatorname{Ext}^{n-i}_X(F,\omega_X^\circ)
\simeq H^i(X,F)^\vee
\]

for coherent `F`. If `F` is locally free, this becomes

\[
H^i(X,F)^\vee\simeq
H^{n-i}(X,F^\vee\otimes\omega_X^\circ).
\]

For nonsingular `X`, the dualizing sheaf is the canonical bundle `det Omega_{X/k}`. For general singular projective schemes, III.7.6 initially gives natural maps; it does not assert all are isomorphisms without the Cohen-Macaulay and equidimensional conditions. A dualizing sheaf need not be invertible. Do not replace a coherent sheaf by its naive dual in the locally free formula unless local freeness has been established.

### Higher direct images and flatness

For a projective morphism of noetherian schemes and a coherent sheaf, higher direct images are coherent (III.8.8). They organize relative cohomology over the base. Flatness of `F` over the base means the appropriate stalks of `F` are flat modules over the base local rings; flatness of `f` means this for `O_X`.

Before tensoring an exact sequence with a residue field, identify the relevant flat module or calculate the Tor term. Over a DVR, torsion-free modules are flat. For `X` a closed subscheme of projective space over an integral noetherian base `T`, III.9.9 characterizes flatness by constancy of the fibre Hilbert polynomial. Constancy of just fibre dimension or degree is weaker and is not this criterion.

### Smoothness

In the finite-type-over-a-field setting of III.10.2, smoothness of relative dimension `n` is equivalent to flatness together with geometrically regular fibres of pure dimension `n`. Check geometric fibres after extending residue fields; regularity over the original field can be insufficient over an imperfect field. Local freeness of the sheaf of differentials alone is not the whole smoothness criterion.

### Formal functions and base change

For a projective morphism of noetherian schemes and a coherent sheaf, III.11.1 identifies the completed stalk of `R^if_*F` at `y` with the inverse limit of `H^i(X_m,F_m)` on the infinitesimal neighborhoods of that fibre. This is an assertion about completion and inverse limits, not an unconditional identification with the cohomology of the reduced fibre.

For III.12.8 and III.12.11, assume `f:X -> Y` projective, both schemes noetherian, and `F` coherent and flat over `Y`.

- The function `y -> dim_{k(y)} H^i(X_y,F_y)` is upper semicontinuous. Values may increase on special fibres.
- Form the actual map `phi^i(y):(R^if_*F) tensor k(y) -> H^i(X_y,F_y)`.
- If `phi^i(y)` is surjective, it is an isomorphism, and remains so on a neighborhood (III.12.11(a)).
- Under that surjectivity assumption, `phi^{i-1}(y)` is surjective exactly when `R^if_*F` is locally free near `y` (III.12.11(b)).
- In III.12.9, constancy of `h^i` on an integral base gives local freeness and the fibre comparison isomorphisms under the stated projective and flat-sheaf hypotheses.

Do not interchange the hypotheses or infer all base-change maps are isomorphisms solely from upper semicontinuity.

## Worked example: all twists on the projective line

Reconstruct the calculation underlying III.4-III.5. Cover `P^1` by `U_0={x_0!=0}` and `U_1={x_1!=0}`. Put `t=x_1/x_0`; the intersection has ring `k[t,t^-1]`.

For `O(d)`, use local frames `e_0=x_0^d` and `e_1=x_1^d`. On the overlap, `e_1=t^d e_0`; this identity also specifies the frames when `d` is negative. In the frame `e_0`, the degree-one Cech group is `k[t,t^-1]` and the coboundaries form

\[
k[t]+t^d k[t^{-1}].
\]

Thus

\[
H^1(\mathbb P^1,O(d))
\simeq k[t,t^{-1}]/(k[t]+t^d k[t^{-1}]).
\]

The first summand removes all exponents at least zero; the second removes all exponents at most `d`. If `d<=-2`, a basis of the quotient is `t^{d+1},...,t^{-1}`, with `-d-1` elements. Otherwise the quotient is zero.

A global section lies in the intersection `k[t] intersect t^d k[t^-1]`. It has basis `1,t,...,t^d` if `d>=0`, and is zero if `d<0`. Therefore

\[
h^0(O(d))=\max(d+1,0),\qquad
h^1(O(d))=\max(-d-1,0),\qquad
\chi(O(d))=d+1.
\]

Check the transition sign with `d=-2`: the only surviving class is `t^-1`, so `h^1(O(-2))=1`. This also agrees with duality because `omega_{P^1}=O(-2)`. A wrong transition convention reverses the range and fails this test.

## Reference table: twists on projective space

For `P^n_k` with `n>=1`, III.5.1 yields:

| Group | Dimension |
|---|---|
| `H^0(O(d))`, `d>=0` | `binomial(d+n,n)` |
| `H^0(O(d))`, `d<0` | `0` |
| `H^i(O(d))`, `0<i<n` | `0` for every `d` |
| `H^n(O(d))`, `d<=-n-1` | `binomial(-d-1,n)` |
| `H^n(O(d))`, `d>=-n` | `0` |

## Key concepts

- **Acyclic sheaf:** one on which the positive derived functors in question vanish.
- **Flasque sheaf:** a sheaf with surjective restriction maps; such sheaves are acyclic for global sections.
- **Euler characteristic:** the alternating sum of cohomology dimensions, when finite.
- **Dualizing sheaf:** the sheaf with trace representing the top-degree duality functor in III.7.
- **Flatness:** preservation of exact sequences by tensoring with the module in question.
- **Geometric fibre:** a fibre after extension to an algebraic closure of the residue field.
- **Upper semicontinuity:** the loci where a fibre dimension is at least a given integer are closed.
- **Base-change map:** the natural comparison between pulled-back higher direct image and cohomology after changing the base.

## Anti-patterns and takeaways

1. Write the connecting map before assuming global lifts or adding section dimensions.
2. Attach a vanishing theorem to every deleted term in a long exact sequence.
3. Distinguish local sheaf Ext from global Ext.
4. Treat Euler characteristic, individual cohomology dimensions, and Hilbert polynomials as related but distinct invariants.
5. In families, check sheaf flatness and the comparison map before identifying fibre cohomology.
6. Keep regularity, geometric regularity, and smoothness separate until the field and morphism hypotheses connect them.

## Connects to

- [Chapter II](ch02-schemes.md): sheaves, twists, modules, differentials, and formal completion.
- [Chapter IV](ch04-curves.md): duality turns the curve Euler characteristic into Riemann-Roch.
- [Chapter V](ch05-surfaces.md): Euler characteristic and duality feed surface Riemann-Roch.
- [Appendix B](ch07-transcendental-methods.md): GAGA compares coherent cohomology with its analytic counterpart.
