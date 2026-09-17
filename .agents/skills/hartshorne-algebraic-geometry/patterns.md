# Proof and Calculation Patterns

These are synthesized procedures drawn from the book's arguments. Names below are navigation labels, not claims that Hartshorne named a formal framework this way. Read the cited chapter file for hypotheses.

## 1. Reduce a geometric assertion to the right local algebra

**When to use:** a property is local, or the objects are affine.

**How:** Identify the locality statement. Choose compatible affine charts, write the ring map in the reverse direction, localize as needed, and prove the corresponding ring or module assertion. Return to geometry and explain the gluing or locality step. For Proj charts use degree-zero localization.

**Trade-offs:** The calculation becomes explicit, but source-local and target-local properties are different. A global conclusion needs the missing local-to-global argument. See [II](chapters/ch02-schemes.md).

## 2. Test a stronger conclusion at the exceptional locus

**When to use:** an argument claims isomorphism from bijectivity, or extends a birational map everywhere.

**How:** Find the dense open where the inverse is defined. Examine omitted points, their local rings, and functions required by the inverse. The cusp normalization tests bijective birational maps; the doubled origin tests uniqueness of extensions.

**Trade-offs:** One counterexample diagnoses the bad inference, but does not replace the positive theorem needed in the actual setting. See [I](chapters/ch01-varieties.md), [II](chapters/ch02-schemes.md).

## 3. Construct a map from sections

**When to use:** building a projective morphism or interpreting a linear system.

**How:** Specify the invertible sheaf and selected sections. Determine where they generate it. On each nonvanishing chart take section ratios and check agreement. For an embedding, additionally verify the closed-immersion criterion; on smooth projective curves test length-two divisors, including repeated points.

**Trade-offs:** Global generation gives a morphism, not automatically an embedding. A subsystem can behave differently from the complete system. See [II](chapters/ch02-schemes.md), [IV](chapters/ch04-curves.md).

## 4. Compute through an exact sequence

**When to use:** sections or cohomology of a subvariety, divisor, or coherent sheaf are unknown.

**How:** Choose an ideal, divisor, or resolution sequence. Verify exactness and any Cartier or flatness assumption. Write the relevant long exact cohomology sequence. Mark terms vanishing by a specific theorem, then calculate kernels, cokernels, or dimensions. Use additivity of Euler characteristic when individual groups are harder.

**Trade-offs:** A known middle term does not automatically determine all maps or groups. Avoid replacing a long exact sequence by an unjustified subtraction of dimensions. See [III](chapters/ch03-cohomology.md).

## 5. Use an acyclic affine cover

**When to use:** a quasi-coherent sheaf admits concrete descriptions on affine charts and overlaps.

**How:** Check the noetherian separated setting of III.4.5, or prove cover acyclicity directly. Write intersections, transition functions, and the alternating restriction differential. Compute its kernels and quotients; test signs on a known twist of `O_{P^1}`.

**Trade-offs:** A cover with nonacyclic intersections can omit essential higher cohomology. Coordinate transition conventions change the apparent exponents. See [III](chapters/ch03-cohomology.md).

## 6. Twist, vanish, and descend through a resolution

**When to use:** proving finiteness or computing a coherent sheaf on a projective scheme over a noetherian ring.

**How:** Use II.5.17 for global generation after twisting. Obtain a surjection from a finite sum of suitable twists, identify the coherent kernel, and apply the cohomology sequence. Use III.5.2 only in sufficiently large degrees, with a threshold depending on the sheaf.

**Trade-offs:** This proves eventual statements, not arbitrary small-degree vanishing. Positive twisting can change the geometric problem unless the desired conclusion is transferred back carefully. See [II](chapters/ch02-schemes.md), [III](chapters/ch03-cohomology.md).

## 7. Apply curve Riemann-Roch before an embedding test

**When to use:** counting sections or proving base-point-freeness or very ampleness.

**How:** Fix genus and degree. Compute or bound the complementary term `ell(K-D)`. Repeat for `D-P` and `D-P-Q`. The drops by one and two prove the relevant separation properties; include `P=Q`.

**Trade-offs:** Degree bounds are sufficient, not necessary. A special divisor requires additional geometry. See [IV](chapters/ch04-curves.md).

## 8. Compute ramification through differentials

**When to use:** applying Hurwitz to a finite map of smooth projective curves.

**How:** Check separability, then use local parameters to calculate the order of `dt/du`. Include points at infinity. Use `e_P-1` only after checking tameness. Sum the resulting lengths and apply the canonical-divisor or genus formula.

**Trade-offs:** Inseparable maps require a different analysis; wild ramification makes naive branch counts wrong. See [IV](chapters/ch04-curves.md).

## 9. Keep a divisor ledger through blowups

**When to use:** resolving a curve, computing genus or self-intersection, or studying a rational surface.

**How:** Record pullback basis classes, exceptional classes, the intersection matrix, and the canonical class. For each center subtract its multiplicity from the strict transform and add the new exceptional divisor to the pulled-back canonical class. Check adjunction against a known curve.

**Trade-offs:** Infinitely near centers require care: old exceptional curves can change under further strict transform. Do not reuse the intersection matrix for total transforms as if it described all strict transforms. See [V](chapters/ch05-surfaces.md).

## 10. Audit a claim about specialization

**When to use:** comparing cohomology on different fibres of a family.

**How:** State projectivity/noetherianity and flatness of the sheaf. Calculate the fibre invariant. Use semicontinuity for inequalities, or form the base-change map and verify the criterion in III.12.11 for isomorphism/local freeness. Use the full Hilbert polynomial in III.9.9, not only its degree or leading coefficient.

**Trade-offs:** Flatness controls families without making every individual cohomology dimension constant. See [III](chapters/ch03-cohomology.md).

## 11. Truncate characteristic classes by dimension

**When to use:** calculating an Euler characteristic by Riemann-Roch.

**How:** Fix the Chow-ring grading, expand `ch(E)` and `td(T_X)`, discard degrees above `dim X`, multiply, and take the degree of the top component. Use `c_1(T_X)=-K_X`. Apply separate vanishing results if a section count is needed.

**Trade-offs:** Numerical output loses some geometric information, and singular inputs need a different theorem. See [A](chapters/ch06-intersection-theory.md).

## 12. Transfer to a second mathematical language

**When to use:** analytic geometry or finite-field cohomology offers a simpler calculation.

**How:** For a complex projective coherent-sheaf problem, identify the GAGA comparison before computing analytically. For finite-field counts, fix Frobenius and the l-adic coefficient theory, then pass from fixed points to traces to determinants. Bring the result back through the stated comparison.

**Trade-offs:** Similar notation does not identify cohomology theories. Formal determinant identities do not prove the Weil eigenvalue bounds. See [B](chapters/ch07-transcendental-methods.md), [C](chapters/ch08-weil-conjectures.md).
