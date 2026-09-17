# Appendix C: The Weil Conjectures

**Source:** Hartshorne, Appendix C.1-C.4, printed pp. 449-458. `ch08` is the skill identifier for Appendix C. This file gives the book's conceptual and computational route; it does not supply the foundations of etale cohomology or Deligne's proof.

## Core idea

Package counts over all finite extensions into a zeta function, identify those counts with fixed points of Frobenius, and convert traces on cohomology into determinants. Duality controls the functional equation, while the eigenvalue bounds require the deeper theorem quoted in the appendix.

## Section map

| Section | Begins | Consult for |
|---|---:|---|
| C.1 The Zeta Function and the Weil Conjectures | 449 | Point counts and the four assertions |
| C.2 History of Work on the Weil Conjectures | 451 | Historical motivation and references |
| C.3 The l-adic Cohomology | 453 | Coefficients, duality, cycle classes, fixed-point formula |
| C.4 Cohomological Interpretation of the Weil Conjectures | 454 | Trace-determinant formula and Frobenius |

## Methods

### Package all extension-field counts

For a finite-type scheme `X` over `F_q`, let `N_r=#X(F_{q^r})`. Define the zeta function as a formal power series

\[
Z(X,t)=\exp\left(\sum_{r\ge1}N_r\frac{t^r}{r}\right).
\]

**Use when:** comparing arithmetic point counts or translating them into cohomological invariants.

1. Fix the base field and count points over its specified extensions.
2. Keep `r` as the extension degree, distinct from the dimension of `X`.
3. Form the logarithmic generating series; the factor `1/r` is essential.
4. If working from a proposed zeta function, recover counts with

   \[
   t\frac{d}{dt}\log Z(X,t)=\sum_{r\ge1}N_rt^r.
   \]

These are formal identities; no analytic convergence assumption is needed. A few small-field counts can check a candidate formula but do not by themselves identify all cohomology or determine an arbitrary zeta function.

### Choose l-adic rather than coherent cohomology

Let `ell` be a prime different from `char F_q`, and put `Xbar=X x_{F_q} F_qbar`. The cohomology in the determinant formula is `H^i_et(Xbar,Q_ell)`. Its coefficient field has characteristic zero, allowing traces that retain ordinary integer counting information.

Coherent groups such as `H^i(X,O_X)` live over the ground field and have a different purpose. They do not serve as a substitute for this Weil cohomology theory. The comparison with complex Betti numbers uses the appropriate smooth proper comparison and specialization setup; one cannot simply regard a finite-field variety as the same space over `C`.

For smooth projective geometrically connected `X` of dimension `n`, use the cohomological range `0<=i<=2n`, Poincare duality, cup products, and cycle classes described in C.3. In particular, `H^0` and `H^{2n}` are one-dimensional. Connectedness over the algebraic closure matters to these endpoint statements.

### Fix the Frobenius convention

Use the endomorphism `F` obtained by base-changing the `q`-power Frobenius of the scheme over `F_q` to `F_qbar`, as in C.4. In affine or projective coordinates defined over `F_q`, its effect on geometric points is `a -> a^q`. The fixed points of `F^r` are the `F_{q^r}`-points.

Keep the action in the formula as the pullback `F^*` on cohomology. This geometric endomorphism and the Galois actions sometimes called arithmetic or geometric Frobenius must not be interchanged without reconciling conventions. A useful normalization check is that `F^*` acts by `q` on `H^2(P^1,Q_ell)`, giving the factor `1-qt`.

### From fixed points to a rational function

In this smooth projective setting the Lefschetz formula gives

\[
N_r=\sum_{i=0}^{2n}(-1)^i
\operatorname{Tr}((F^*)^r\mid H^i_{et}(\bar X,\mathbb Q_\ell)).
\]

Use the finite-dimensional linear algebra identity of C.4.1:

\[
\exp\left(\sum_{r\ge1}\operatorname{Tr}(A^r)\frac{t^r}{r}\right)
=\det(1-tA)^{-1}.
\]

Then C.4.2 gives

\[
Z(X,t)=\prod_{i=0}^{2n}P_i(t)^{(-1)^{i+1}},
\qquad
P_i(t)=\det(1-tF^*\mid H^i_{et}(\bar X,\mathbb Q_\ell)).
\]

Odd-degree factors go in the numerator and even-degree factors in the denominator. This sign can be checked immediately on projective space.

**Why it works:** exponentiation converts the sum of traces into the product of characteristic factors. **Failure mode:** using the determinant of `t-F^*` instead of `1-tF^*` changes the normalization and reciprocal-root convention.

### Separate the four assertions and their inputs

| Assertion | Tool or content |
|---|---|
| Rationality of `Z` | Finite-dimensional cohomology, trace formula, determinant identity |
| Functional equation | Poincare duality and Frobenius compatibility |
| Analogue of the Riemann hypothesis | Eigenvalues in degree `i` have complex absolute value `q^(i/2)` |
| Betti-number interpretation | Degrees of the factors and the stated comparison/specialization results |

For geometrically connected `X`, `P_0(t)=1-t` and `P_{2n}(t)=1-q^n t`. Let `E=sum_i (-1)^i dim H^i`; the functional equation in C.1.2 is

\[
Z\left(X,\frac1{q^nt}\right)
=\pm q^{nE/2}t^E Z(X,t).
\]

Deligne's theorem as stated in C.4.5 supplies integral coefficients, independence of `ell`, and the absolute values of the algebraic eigenvalues in the factors `P_i(t)=product_j(1-alpha_{ij}t)`. Distinguish the eigenvalues `alpha_{ij}`, with absolute value `q^(i/2)`, from the roots in the variable `t`, whose absolute value is reciprocal.

The determinant identity alone does not prove those absolute-value assertions. The book explicitly treats the final theorem as deeper than the formal cohomological argument.

## Worked example: the projective line

Reconstruct C.1 and C.4. Over `F_{q^r}`, the affine line has `q^r` points and `P^1` has one additional point. Thus `N_r=q^r+1`, and

\[
\begin{aligned}
\log Z(\mathbb P^1,t)
&=\sum_{r\ge1}\frac{(qt)^r}{r}
+\sum_{r\ge1}\frac{t^r}{r}\\
&=-\log(1-qt)-\log(1-t).
\end{aligned}
\]

Exponentiating gives

\[
Z(\mathbb P^1,t)=\frac1{(1-t)(1-qt)}.
\]

Now match cohomology: degree zero contributes eigenvalue `1`, degree two contributes `q`, and degree one is zero. Both nontrivial groups have even degree, so both factors belong in the denominator.

The Euler characteristic is `E=2` and `n=1`. Direct substitution verifies

\[
Z\left(\mathbb P^1,\frac1{qt}\right)=qt^2 Z(\mathbb P^1,t).
\]

Finally, logarithmic differentiation recovers `q^r+1` for every `r`. These three checks test the counting, sign convention, and functional equation independently.

### A derived check for a curve

For a smooth projective geometrically connected curve of genus `g`, the formula has the form

\[
Z(X,t)=\frac{P_1(t)}{(1-t)(1-qt)},
\quad \deg P_1=2g,
\quad N_1=q+1-\sum_{j=1}^{2g}\alpha_j.
\]

The degree-one weight bound gives `|N_1-(q+1)|<=2g sqrt(q)`. This is a consequence of the theorem, not a proof of it. For genus zero the numerator is one, agreeing with the projective-line calculation in this setting. The similarity to the analytic Riemann hypothesis concerns the eigenvalue/root bounds; it is not a claim about zeros of the classical Riemann zeta function.

## Key concepts

- **Zeta function:** the exponential generating function of all extension-field point counts.
- **Frobenius endomorphism:** the finite-field power map in the explicitly chosen convention.
- **l-adic cohomology:** etale cohomology with the characteristic-zero coefficient field `Q_ell`, for `ell` different from the field characteristic.
- **Trace formula:** a fixed-point count expressed as an alternating sum of cohomological traces.
- **Betti number:** the dimension of a cohomology group in the relevant theory.
- **Weight bound:** the specified absolute value `q^(i/2)` for degree-`i` Frobenius eigenvalues.
- **Cycle class:** the image of an algebraic cycle in even-degree cohomology, with the appropriate coefficient and twist conventions.

## Anti-patterns and takeaways

1. Use all extension degrees in the definition of the zeta function.
2. Distinguish coherent cohomology from l-adic cohomology.
3. Fix Frobenius conventions before writing eigenvalues or determinants.
4. Keep odd-degree determinants in the numerator.
5. Geometric connectedness is needed for the simple endpoint factors.
6. Duality and formal linear algebra do not prove the weight bounds on their own.
7. Read the historical discussion as history; do not repeat its publication-era open-status claims as current facts.

## Connects to

- [Chapter IV](ch04-curves.md): finite maps, Frobenius, genus, and ramification.
- [Appendix A](ch06-intersection-theory.md): cycle classes and intersection numbers.
- [Appendix B](ch07-transcendental-methods.md): complex topology explains the comparison with Betti numbers.
- [Chapter III](ch03-cohomology.md): derived-functor ideas provide background, but the coefficient objects and topology differ here.
