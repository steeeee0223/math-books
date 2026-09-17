# Chapter IV: Curves

**Source:** Hartshorne, IV.1-IV.6, printed pp. 293-355. An unqualified curve in this chapter is a nonsingular projective curve over an algebraically closed field `k`; an unqualified point is closed. Singular or nonproper curves need separate wording and hypotheses.

## Core idea

Use divisors, their spaces of sections, and the canonical divisor to turn curve geometry into numerical questions. Riemann-Roch controls the dimensions, while base-point and separation conditions determine the geometry of the associated maps.

## Section map

| Section | Begins | Consult for |
|---|---:|---|
| IV.1 Riemann-Roch Theorem | 294 | Genus, special divisors, dimensions of linear systems |
| IV.2 Hurwitz's Theorem | 299 | Finite maps, separability, ramification, Frobenius |
| IV.3 Embeddings in Projective Space | 307 | Base points, very ampleness, degree bounds |
| IV.4 Elliptic Curves | 316 | Group law, j-invariant, Jacobian, complex uniformization |
| IV.5 The Canonical Embedding | 340 | Hyperelliptic curves, Clifford's theorem, canonical models |
| IV.6 Classification of Curves in Projective Space | 349 | Degree-genus constraints and special linear systems |

## Methods

### Riemann-Roch with a controlled special term

Write `ell(D)=h^0(X,O_X(D))`, and let `K` be a canonical divisor. Theorem IV.1.3 states

\[
\ell(D)-\ell(K-D)=\deg D+1-g,
\qquad g=h^1(X,O_X)=h^0(X,\omega_X).
\]

**Use when:** calculating sections, proving existence of effective divisors, or constructing a map.

1. Compute `deg D` and recall `deg K=2g-2`.
2. If `deg D<0`, conclude `ell(D)=0`.
3. If `deg D=0`, a nonzero section exists exactly when `D~0`.
4. If `deg D>2g-2`, then `deg(K-D)<0`, so `ell(D)=deg D+1-g`.
5. Otherwise, keep the special term `ell(K-D)=h^1(O_X(D))`; bound or calculate it using the geometry of the curve.
6. Convert to the dimension of the complete linear system by `dim |D|=ell(D)-1`, using dimension `-1` for the empty system.

**Why it works:** duality identifies the obstruction term with a second space of sections, whose degree is often negative. **Failure mode:** dropping it merely because `D` is effective gives wrong answers in small degree.

### Constructing morphisms and embeddings

The complete system `|D|` is base-point-free exactly when `ell(D-P)=ell(D)-1` for every point `P`. It is very ample exactly when

\[
\ell(D-P-Q)=\ell(D)-2
\]

for every pair `P,Q`, including `P=Q` (IV.3.1). The repeated-point case tests tangent directions. These conditions concern the complete system; for a chosen subspace of sections, test its evaluation maps instead.

Riemann-Roch gives convenient sufficient bounds (IV.3.2):

| Degree condition | Conclusion |
|---|---|
| `deg D>2g-2` | `h^1(O(D))=0` |
| `deg D>=2g` | `|D|` is base-point-free |
| `deg D>=2g+1` | `D` is very ample |
| `deg D>0` | `D` is ample (IV.3.3) |

To derive the embedding bound, apply vanishing not just to `D`, but to `D-P-Q`, whose degree is still greater than `2g-2`. These are sufficient bounds, not necessary characterizations of all very ample divisors.

### Finite maps and Hurwitz

A nonconstant morphism of these curves is finite. For a finite **separable** morphism `f:X -> Y`, define

\[
R=\sum_P\operatorname{length}_{O_{X,P}}(\Omega_{X/Y,P})P.
\]

Then `K_X ~ f^*K_Y+R` (IV.2.3), hence

\[
2g_X-2=\deg(f)(2g_Y-2)+\deg R
\]

by IV.2.4. At a tame ramification point, the coefficient is `e_P-1`; at a wild point it is larger. In local parameters `u` upstairs and `t` downstairs, compute the coefficient from the order of `dt/du`.

**Procedure:** check separability of the function-field extension, determine the degree, identify ramification points including infinity, check whether ramification is tame, then take degrees. A purely inseparable Frobenius map does not meet the hypotheses. Differentiate only after fixing the field characteristic.

### Genus one and the role of a chosen origin

Hartshorne calls a genus-one curve elliptic; choose `P_0` to equip it with a group structure. The map

\[
P\longmapsto[O_X(P-P_0)]\in\operatorname{Pic}^0(X)
\]

identifies points with degree-zero divisor classes. Use this to define the group law intrinsically before relying on a plane chord-and-tangent picture. Under the embedding by `|3P_0|`, a line section is linearly equivalent to `3P_0`, so three collinear intersection points sum to zero, with tangencies interpreted using multiplicity.

The normal forms and j-invariant statements in IV.4 have characteristic assumptions. In particular, IV.4.6 uses `char k!=2` for the Legendre form `y^2=x(x-1)(x-lambda)` with distinct branch points. Over an algebraically closed field in the setting of IV.4.1, the j-invariant classifies elliptic curves up to isomorphism. Over a nonclosed field, equal j-invariants do not by themselves rule out twists. The complex uniformization discussion uses a lattice in `C`; it does not apply in positive characteristic.

### Canonical maps and special divisors

For `g>=2`, the canonical system is base-point-free. It is very ample exactly when the curve is not hyperelliptic (IV.5.2). A hyperelliptic curve has a degree-two map to `P^1`; its canonical map factors through that map and the `(g-1)`-uple embedding of `P^1` (IV.5.3).

Use the canonical system to distinguish a canonical embedding from a double cover of a rational normal curve. For an effective special divisor, Clifford's theorem (IV.5.4) gives

\[
\ell(D)\le 1+\frac{\deg D}{2}.
\]

The words effective and special matter. For equality classifications, consult the complete theorem and its hyperelliptic cases rather than extrapolating from the inequality.

### Embedded classification

Record both intrinsic invariants and embedding data: `g`, degree `d`, projective dimension, nondegeneracy, completeness of the system, and whether the hyperplane divisor is special. IV.6 uses these distinctions to constrain possible curves; degree and genus alone do not describe every embedding.

For a nondegenerate nonsingular curve of degree `d` in `P^3`, IV.6.4 gives the bound

\[
g\le\left\lfloor\frac{(d-2)^2}{4}\right\rfloor.
\]

It is a space-curve statement; a plane curve is excluded. Curves attaining the bound lie on a quadric. Use a quadric's two ruling classes to reconstruct such examples, rather than applying the smooth plane-curve genus formula to every embedded curve.

## Worked example: the genus of a smooth plane curve

Combine the hypersurface calculation in II.8.20.3 with IV.1. Let `C subset P^2` be a nonsingular plane curve of degree `d`.

1. The canonical bundle of `P^2` is `O(-3)`, and `O_{P^2}(C)=O(d)`.
2. Adjunction gives `omega_C ~= O_C(d-3)`.
3. A hyperplane divisor on `C` has degree `d`, so `deg omega_C=d(d-3)`.
4. Since `deg K_C=2g-2`, solve

   \[
   2g-2=d(d-3),\qquad g=\frac{(d-1)(d-2)}2.
   \]

For `d=3`, `g=1` and `omega_C` is trivial. For `d=4`, `g=3` and `omega_C=O_C(1)`; the plane embedding is its canonical embedding. This connects a local differential calculation, a global line bundle, and an intrinsic invariant.

If the plane curve is singular, the same expression is its arithmetic genus, not automatically the genus of its nonsingular model. The cuspidal cubic from Chapter I has arithmetic genus one but normalization `P^1`, of genus zero. The nonsingularity assumption is doing real work.

### A second check: why degree two does not embed an elliptic curve

Fix an origin `P_0` on a genus-one curve. Since `K~0`, Riemann-Roch gives `ell(mP_0)=m` for every `m>0`. Thus `|2P_0|` has projective dimension one and is base-point-free, giving a degree-two map to `P^1`. It cannot embed a genus-one curve as `P^1`. The divisor `3P_0`, however, satisfies the very-ampleness bound and embeds the curve into `P^2` as a cubic.

## Key concepts

- **Genus:** `h^1(O_X)`, equal to `h^0(omega_X)` in this chapter's setting.
- **Special divisor:** a divisor `D` with `h^1(O_X(D))>0`.
- **Complete linear system:** all effective divisors linearly equivalent to `D`.
- **Linear series `g_d^r`:** a projective `r`-dimensional linear system of degree `d`, which need not be complete.
- **Base point:** a point where every section in the selected system vanishes.
- **Hyperelliptic curve:** a curve of genus at least two admitting a degree-two morphism to `P^1`.
- **Ramification divisor:** the divisor measured by lengths of relative differentials for a finite separable map.
- **Jacobian:** the abelian variety organizing degree-zero line bundles, with the universal-property formulation in IV.4.

## Anti-patterns and takeaways

1. Do not use a degree inequality without checking whether it is strict.
2. Distinguish sections from projective dimension: `ell(D)` and `dim |D|` differ by one.
3. Separating distinct points alone does not establish very ampleness; test tangent directions.
4. Hurwitz needs separability; the expression `sum(e_P-1)` additionally needs tameness.
5. A singular plane model and its normalization can have different arithmetic genera.
6. Fix an origin before discussing an elliptic curve as a group.
7. Distinguish intrinsic genus from the degree of a chosen projective embedding.

## Connects to

- [Chapter I](ch01-varieties.md): function fields and the nonsingular projective model.
- [Chapter II](ch02-schemes.md): divisors, line bundles, differentials, adjunction.
- [Chapter III](ch03-cohomology.md): duality and exact sequences behind Riemann-Roch.
- [Chapter V](ch05-surfaces.md): intersections on surfaces compute the genera of embedded curves.
- [Appendix C](ch08-weil-conjectures.md): Frobenius and point counts require a different cohomology theory.
