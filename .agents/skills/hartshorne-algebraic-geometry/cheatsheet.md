# Decision Cheatsheet

Use the referenced chapter for full assumptions. All curve shortcuts below use Chapter IV's nonsingular projective algebraically closed setting; surface shortcuts use Chapter V's setting.

| Situation | Decision and reason | Read |
|---|---|---|
| Same closed points or bijective map | Inspect rings and stalks; points can miss nilpotents and failure of a regular inverse. | I-II |
| Property proved on an affine cover | Name the locality theorem before concluding globally. | II |
| Surjective sheaf map | Expect local lifts; the connecting cohomology class obstructs a global lift. | II-III |
| Proj chart | Take the degree-zero part of the graded localization. | II.2 |
| Need a map to projective space | Choose a line bundle and generating sections; then separately test embedding. | II.7 |
| Need `Cl(X)=Pic(X)` | Use the noetherian integral separated locally factorial setting; normality alone is insufficient. | II.6 |
| Missing versus nonunique limit | In the applicable valuation criterion, test existence for properness and uniqueness for separatedness; retain finite type. | II.4 |
| Quasi-coherent sheaf on noetherian affine | Higher cohomology vanishes. A test on `O_X` alone does not characterize affineness. | III.3 |
| Explicit affine cover available | Check Cech comparison hypotheses, then calculate transition maps. | III.4 |
| Coherent projective calculation | Try an exact sequence, then sufficiently positive twists; justify each vanished term. | III.5 |
| Singular scheme in a duality argument | Check Cohen-Macaulayness and pure dimension; keep Ext unless local freeness allows simplification. | III.7 |
| Family cohomology jumps | Upper semicontinuity permits larger special-fibre dimensions; test the actual base-change map. | III.12 |
| Regular fibres proposed as smoothness proof | Check flatness and geometric regularity, especially over imperfect fields. | III.10 |
| Riemann-Roch gives a number | It computes `chi`; remove higher cohomology only with a reason. | III-V, A |
| Negative curve proposed for contraction | Castelnuovo's smooth contraction requires `P^1` with square `-1`. | V.5 |
| Analytic computation available | Use GAGA in its coherent projective setting over `C`. | B.2 |
| Point counts over finite fields | Use l-adic cohomology and a fixed Frobenius convention, not `H^i(O_X)`. | C |

## Curve degree decisions

| Given `D` on a genus-`g` curve | Conclusion |
|---|---|
| `deg D<0` | `h^0(O(D))=0` |
| `deg D=0` | Nonzero section exactly when `D~0` |
| `deg D>2g-2` | `h^1(O(D))=0`; `h^0=deg D+1-g` |
| `deg D>=2g` | Complete system is base-point-free |
| `deg D>=2g+1` | `D` is very ample |
| `deg D>0` | `D` is ample |
| Finite map, characteristic positive | Check separability, then tameness before using `e_P-1` |
| Canonical map, `g>=2` | Embedding exactly in the nonhyperelliptic case |

## Surface calculation decisions

- Blow up a point of multiplicity `m`: use `C'=pi^*C-mE`, not the total transform.
- Update intersections: `E^2=-1`, `pi^*D.E=0`, `(C')^2=C^2-m^2`.
- Update canonical class: `K'=pi^*K+E`, so `(K')^2=K^2-1`.
- Need ampleness: test `D^2>0` and `D.C>0` for every irreducible curve; justify any reduction to generators.
- Need genus: for a smooth curve use `2g-2=C.(C+K)`; for singular curves distinguish arithmetic genus and normalization genus.
- Need a unique minimal model: retain the rational and ruled exceptions.

## Fast error detectors

- A curve argument ignores `ell(K-D)` at small degree: a special divisor may be missing.
- A blowup calculation leaves `K^2` unchanged: the exceptional contribution was lost.
- A Cech calculation gives `h^1(P^1,O(-2))=0`: check transition signs.
- A Weil formula puts `1-qt` in the numerator for `P^1`: reverse the parity placement.
- An intersection uses only quotient length in higher dimension: inspect higher Tor terms.
- A compact complex manifold is declared projective: identify an embedding or the missing Hodge/Moishezon-Kahler hypothesis.
- A paper's “lines in E” convention is mixed with Hartshorne: check the quotient convention for `P(E)`.

Detailed routes: [patterns](patterns.md) and the [chapter index](SKILL.md).
