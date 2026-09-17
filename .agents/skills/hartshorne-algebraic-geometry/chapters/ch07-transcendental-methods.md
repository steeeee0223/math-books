# Appendix B: Transcendental Methods

**Source:** Hartshorne, Appendix B.1-B.5, printed pp. 438-448. `ch07` is the skill identifier for Appendix B. The base field in this file is `C`; the comparison results do not transfer unchanged to other fields.

## Core idea

Translate an algebraic problem into complex analytic geometry only after establishing a comparison theorem strong enough to bring the answer back. Analytification preserves much geometric structure, but arbitrary holomorphic data need not be algebraic.

## Section map

| Section | Begins | Consult for |
|---|---:|---|
| B.1 The Associated Complex Analytic Space | 438 | Analytification of schemes and coherent sheaves |
| B.2 Comparison of the Algebraic and Analytic Categories | 440 | GAGA and Chow's theorem |
| B.3 When Is a Compact Complex Manifold Algebraic? | 441 | Riemann existence, Moishezon manifolds, counterexamples |
| B.4 Kahler Manifolds | 445 | Hodge metrics and projectivity |
| B.5 The Exponential Sequence | 446 | Picard groups, Chern classes, Jacobians |

## Methods

### Analytification as a change of local functions

For a finite-type scheme over `C`, use affine presentations by polynomial equations, regard those equations as holomorphic functions, and glue the resulting analytic spaces. Analytification of a coherent sheaf can be constructed from a local presentation by a matrix of regular functions, now viewed as holomorphic functions.

The associated space has the classical complex topology and a sheaf of holomorphic functions. It is not the same ringed space as the algebraic variety. Its points correspond to the algebraic scheme's closed points; its topology is different, and its local rings generally have more functions.

B.1 provides the following useful comparisons in the finite-type complex setting:

| Algebraic condition | Analytic counterpart |
|---|---|
| Separated | Hausdorff |
| Proper over `C` | Compact associated analytic space |
| Smooth over `C` | Complex manifold |
| Reduced | Reduced analytic structure |

Use these as comparison statements for an algebraic input. Compactness of an arbitrary complex manifold does not assert that an algebraic input exists.

### GAGA for coherent sheaves and cohomology

For a projective scheme `X` over `C`, B.2.1 identifies the category of coherent algebraic sheaves on `X` with that of coherent analytic sheaves on `X^an`, and gives

\[
H^i(X,F)\simeq H^i(X^{an},F^{an})
\]

for coherent `F` and every `i`.

**Use when:** an analytic calculation concerns a coherent sheaf on a projective complex scheme.

1. Identify the algebraic scheme and prove the projective hypothesis.
2. Identify the coherent sheaf or algebraic line bundle corresponding to the analytic object.
3. Perform the calculation in the category where the available tools are simpler.
4. Apply the comparison isomorphism or categorical equivalence to transfer the conclusion.

For morphisms of projective complex schemes, the graph and coherent-sheaf methods recover algebraicity; B, Exercise 6.6 also gives a line-bundle approach. The appendix notes the proper generalization of GAGA, but its principal stated theorem is projective. Cite the generalization explicitly if using it.

**Why it works:** projectivity supplies enough finite algebraic structure for coherent analytic data to algebraize. **Failure mode:** applying the comparison to an arbitrary open complex manifold or to noncoherent analytic data.

### Chow's theorem and algebraicity of analytic subspaces

If an analytic space is already realized as a compact analytic subspace of complex projective space, Chow's theorem (B.2.2) provides an algebraic closed subscheme with that analytification. The projective embedding is essential evidence. Compactness without an embedding is a different problem.

For a holomorphic map between projective varieties, an appropriate graph argument packages the map as a closed analytic subspace of a projective product, where Chow's theorem applies. Explain why the graph is closed and how its projection recovers the map, rather than simply declaring every holomorphic map algebraic.

### Riemann existence and the dimension-one exception

Every compact Riemann surface is projective algebraic (B.3.1). The proof route needs a nonconstant global meromorphic function, then a finite map to `P^1`; the existence of that function is not a consequence of local coordinates alone.

The generalized Riemann existence theorem (B.3.2) algebraizes a finite morphism from a normal analytic space to the analytification of a normal finite-type complex scheme. It connects finite unramified topological covers with finite etale covers. The resulting algebraic fundamental group is a profinite completion, not the uncompleted topological fundamental group.

Use the curve theorem when dimension is one. Higher-dimensional compact complex manifolds can fail to be algebraic, and the appendix supplies examples and criteria rather than a blanket replacement theorem.

### Projectivity, Kahler metrics, and meromorphic functions

A Moishezon manifold is a compact complex manifold whose field of meromorphic functions has transcendence degree equal to its complex dimension. This is a birational condition; it does not by itself imply projectivity or representability by a scheme in dimensions at least three.

A Kahler manifold has a Hermitian metric whose associated real `(1,1)` form is closed. A Hodge manifold, in the appendix's terminology, is compact Kahler with an integral Kahler class. Kodaira's embedding theorem (B.4.1) makes a Hodge manifold projective algebraic. The second useful criterion is that a compact Moishezon manifold which is Kahler is projective (B.4.2).

| Evidence available | What to do next |
|---|---|
| Compact analytic curve | Apply the dimension-one algebraicity theorem |
| Compact analytic subspace of `P^n(C)` | Apply Chow's theorem |
| Integral Kahler class | Apply the Hodge/Kodaira criterion |
| Moishezon and Kahler | Apply B.4.2 |
| Compact only, dimension greater than one | Seek stronger hypotheses or a counterexample |
| Kahler only | Do not conclude projectivity |
| Moishezon only | Check the distinction among projective, proper algebraic, and analytic models |

The Hironaka examples in B.3.4 distinguish complete nonprojective algebraic varieties from nonalgebraic Moishezon manifolds. Use them to prevent the implications from being silently reversed. Their discussion of algebraic spaces enlarges the category again; it is not a statement that every such manifold is an algebraic scheme.

### The exponential sequence

On a reduced complex analytic space, local logarithms give the exact sequence of sheaves

\[
0\to\mathbb Z\to O_{X^{an}}
\xrightarrow{f\mapsto\exp(2\pi i f)}O_{X^{an}}^*\to1.
\]

The final group is multiplicative, which explains writing `1` rather than `0`. Sheaf surjectivity follows locally from logarithms; there need not be a global logarithm for every invertible function.

For a nonsingular projective complex variety, identify `H^1(O^*)` with the analytic Picard group, then use GAGA to identify it with `Pic(X)`. The connecting map to `H^2(X^an,Z)` is the first Chern class. The exact sequence separates continuous line-bundle parameters from discrete topological information.

Do not confuse `H^1(X,O_X)` with singular cohomology `H^1(X^an,Z)`: they have different coefficient objects, and the exponential sequence is the bridge between them.

## Worked example: the Picard group of a complex curve

Reconstruct B.5. Let `X` be a nonsingular projective complex curve of genus `g`. Topology gives

\[
H^1(X^{an},\mathbb Z)\simeq\mathbb Z^{2g},
\qquad H^2(X^{an},\mathbb Z)\simeq\mathbb Z.
\]

Coherent cohomology gives `H^1(X,O_X) ~= C^g` and `H^2(X,O_X)=0`. Compactness implies that the global holomorphic functions are constant; the exponential map `C -> C^*` is surjective. Thus the relevant long exact sequence becomes

\[
0\to H^1(X^{an},\mathbb Z)\to H^1(X,O_X)
\to\operatorname{Pic}(X)\xrightarrow{c_1}\mathbb Z\to0.
\]

On a curve, the integer is the degree. The image of `H^1(X^an,Z)` in `C^g` is a lattice `Lambda` of rank `2g`, so

\[
\operatorname{Pic}^0(X)\simeq\mathbb C^g/\Lambda.
\]

This is the Jacobian, an abelian variety of dimension `g`. The lattice's embedding, not merely its rank, records the complex structure. The expression does not say that all genus-`g` Jacobians are the same torus. The quotient of the Picard group by its degree-zero subgroup is `Z`, so the Neron-Severi group of the curve is `Z`.

For `g=0`, the torus vanishes and degree gives `Pic(P^1) ~= Z`, recovering the algebraic calculation. For `g=1`, choosing a base point identifies the curve with its Jacobian, linking the analytic quotient with the group law of IV.4.

## Key concepts

- **Analytification:** the analytic space or coherent analytic sheaf obtained from algebraic data over `C`.
- **GAGA:** the coherent algebraic-analytic equivalence and cohomology comparison in the stated proper/projective setting.
- **Moishezon:** maximal transcendence degree of global meromorphic functions on a compact complex manifold.
- **Hodge manifold:** a compact Kahler manifold admitting the integral Kahler class in B.4.
- **First Chern class:** the connecting class of a line bundle in integral degree-two cohomology.
- **Picard variety:** the abelian variety of algebraically trivial line bundles in the nonsingular projective setting.
- **Neron-Severi group:** line bundles modulo algebraic equivalence.

## Takeaways

1. Name the comparison theorem before transferring an analytic result back to algebraic geometry.
2. Local holomorphic coordinates do not themselves produce global meromorphic functions.
3. Keep compact, projective, Kahler, and Moishezon hypotheses distinct.
4. Local logarithms prove sheaf exactness, not global surjectivity in every situation.
5. A lattice quotient needs the actual lattice embedding to determine its complex structure.
6. Treat the appendix as a guide to methods and references, not a proof of the analytic theorems it cites.

## Connects to

- [Chapter II](ch02-schemes.md): sheaves, line bundles, and the Picard group.
- [Chapter III](ch03-cohomology.md): long exact sequences and coherent cohomology.
- [Chapter IV](ch04-curves.md): elliptic curves and Jacobians.
- [Appendix C](ch08-weil-conjectures.md): comparison with topological Betti numbers motivates a different cohomology theory in finite characteristic.
