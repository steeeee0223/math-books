import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Companion to DF. Hartshorne's universal-derivation definition agrees with
`KaehlerDifferential.linearMapEquivDerivation`; conormal modules here are
`Ideal.Cotangent`, i.e. I/I², not the derived cotangent complex.

Verified reductions: DF-1 square-zero lifts/derivations; DF-2 and DF-3 the
actual conormal exact sequence for a surjection and its surjective final map;
DF-4 the canonical base-change isomorphism and its value on db; the source
localization comparison needed to identify stalks; DF-5 functoriality on db;
DF-6 normalization substitutions, relation compatibility and torsion
annihilation; DF-7 cone relation; DF-8 power derivative and characteristic-p
vanishing; DF-10 injectivity of the conormal map for standard smooth
presentations; DF-12 Euler chart kernel; DF-14 equality of canonical forms
where the two denominators are units. These declarations check the maps
used in the prose, not merely dimension identities.

Precise remaining gaps: the dual-number specialization has not been assembled
as an equivalence of scheme-valued points; finite-separable residue-field
injectivity in DF-3 is not formalized. The Jacobian cokernel follows from the
verified conormal sequence and polynomial basis, but the finite list of
relations is not packaged as a single presented-module equivalence. No sheaf
of differentials/stalk API is installed here; restriction and gluing of the
verified affine maps remain prose. For DF-6 the entire torsion-kernel quotient
is not proved, only the exact polynomial identities, so its claimed length
and exhaustive generation remain unverified. The tangent cones, normalization
universal property, geometric regularity of the examples, conormal bundle
identifications, exterior determinant sheaf isomorphisms, and projective
canonical-form transition are not fully formalized. These are material gaps;
this file is partial verification and must not be reported as full coverage.
-/

open TensorProduct

noncomputable section

namespace SupplementDF

section Universal
variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- DF-1: the algebraic lift/derivation equivalence, with fixed reduction. -/
def squareZeroLifts (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Derivation R A I ≃
      { f : A →ₐ[R] B //
        (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } :=
  derivationToSquareZeroEquivLift I hI

/-- DF-1: the exact universal property used to dualize cotangents. -/
def derivationsAsLinearMaps (M : Type*) [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] :
    (Ω[A⁄R] →ₗ[A] M) ≃ₗ[A] Derivation R A M :=
  KaehlerDifferential.linearMapEquivDerivation R A (M := M)

/-- DF-2/3: conormal exactness for the actual quotient map, including residue maps. -/
theorem quotient_conormal_exact (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

/-- DF-2/3: the rightmost zero in that exact sequence. -/
theorem quotient_differentials_surjective (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

/-- DF-3: the first map sends the class of a relation to its differential. -/
theorem conormal_formula (x : RingHom.ker (algebraMap A B)) :
    KaehlerDifferential.kerCotangentToTensor R A B (Ideal.toCotangent _ x) =
      (1 : B) ⊗ₜ[A] KaehlerDifferential.D R A x.1 := rfl

/-- DF-5: the differential of a coordinate map on generators. -/
theorem tangent_map_formula (a : A) :
    KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a) =
      KaehlerDifferential.D R B (algebraMap A B a) :=
  KaehlerDifferential.map_D R R A B a

/-- DF-7: the actual Kähler relation of the quadric hypersurface. -/
theorem cone_differential_relation (x y z : A) (h : x * y = z ^ 2) :
    x • KaehlerDifferential.D R A y + y • KaehlerDifferential.D R A x =
      (2 : ℕ) • (z • KaehlerDifferential.D R A z) := by
  have hd := congrArg (KaehlerDifferential.D R A) h
  simpa only [Derivation.leibniz, Derivation.leibniz_pow, Nat.reduceSub, pow_one] using hd

/-- DF-6: the cusp relation in the Kähler module itself, before normalization. -/
theorem cusp_differential_relation (x y : A) (h : y ^ 2 = x ^ 3) :
    (2 : ℕ) • (y • KaehlerDifferential.D R A y) =
      (3 : ℕ) • (x ^ 2 • KaehlerDifferential.D R A x) := by
  have hd := congrArg (KaehlerDifferential.D R A) h
  simpa only [Derivation.leibniz_pow, Nat.reduceSub, pow_one] using hd

/-- DF-3/4: localization is the required source-restriction comparison. -/
def differentialsLocalize (S : Submonoid A) [IsLocalization S B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄R] := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) S
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
end Universal

section BaseChange
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
variable [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]

/-- DF-4: not just existence, but the canonical isomorphism. -/
def differentialsBaseChange : B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] :=
  KaehlerDifferential.tensorKaehlerEquiv R S A B

theorem differentialsBaseChange_formula (b : B) (a : A) :
    differentialsBaseChange R S A B (b ⊗ₜ[A] KaehlerDifferential.D R A a) =
      b • KaehlerDifferential.D S B (algebraMap A B a) :=
  KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B b a
end BaseChange

section PolynomialCharts
variable (R : Type*) [CommRing R]

/-- DF-2: the polynomial differential basis from which the Jacobian starts. -/
def polynomialDifferentialBasis (n : ℕ) :
    Module.Basis (Fin n) (MvPolynomial (Fin n) R) Ω[MvPolynomial (Fin n) R⁄R] :=
  KaehlerDifferential.mvPolynomialBasis R (Fin n)

/-- DF-8: the derivative giving the relation mt^(m-1)dt. -/
theorem power_derivative (m : ℕ) :
    Polynomial.derivative ((Polynomial.X : Polynomial R) ^ m) =
      (m : Polynomial R) * Polynomial.X ^ (m - 1) := by
  simp [Polynomial.derivative_X_pow]

/-- DF-8/9: characteristic-p powers have zero differential polynomial. -/
theorem frobenius_derivative (p : ℕ) [CharP R p] :
    Polynomial.derivative ((Polynomial.X : Polynomial R) ^ p) = 0 := by
  rw [power_derivative]
  simp
end PolynomialCharts

section ExplicitRelations
variable {K : Type*} [CommRing K]

/-- DF-6: the normalization equations themselves. -/
theorem cusp_equation (t : K) : (t ^ 3) ^ 2 = (t ^ 2) ^ 3 := by ring

theorem node_equation (t : K) :
    (t * (t ^ 2 - 1)) ^ 2 = (t ^ 2 - 1) ^ 2 * ((t ^ 2 - 1) + 1) := by ring

/-- DF-6: the cusp Jacobian relation pulls back to zero. -/
theorem cusp_relation_pullback (t : K) :
    2 * t ^ 3 * (3 * t ^ 2) - 3 * (t ^ 2) ^ 2 * (2 * t) = 0 := by ring

/-- DF-6: the proposed torsion generator pulls back to zero. -/
theorem cusp_torsion_pullback (t : K) :
    2 * t ^ 2 * (3 * t ^ 2) - 3 * t ^ 3 * (2 * t) = 0 := by ring

/-- DF-6: y times the torsion vector is x times the relation vector modulo F. -/
theorem cusp_torsion_y (x y : K) (h : y ^ 2 = x ^ 3) :
    (y * (-3 * y), y * (2 * x)) = (x * (-3 * x ^ 2), x * (2 * y)) := by
  apply Prod.ext
  · calc
      _ = -3 * y ^ 2 := by ring
      _ = _ := by rw [h]; ring
  · ring

/-- DF-6: x² also annihilates the proposed class modulo the Jacobian relation. -/
theorem cusp_torsion_xsq (x y : K) (h : y ^ 2 = x ^ 3) :
    (x ^ 2 * (-3 * y), x ^ 2 * (2 * x)) = (y * (-3 * x ^ 2), y * (2 * y)) := by
  apply Prod.ext
  · ring
  · calc
      _ = 2 * x ^ 3 := by ring
      _ = _ := by rw [← h]; ring

theorem node_relation_pullback (t : K) :
    2 * (t * (t ^ 2 - 1)) * (3 * t ^ 2 - 1) -
      (t ^ 2 - 1) * (3 * (t ^ 2 - 1) + 2) * (2 * t) = 0 := by ring

theorem node_torsion_pullback (t : K) :
    (t * (t ^ 2 - 1)) * (3 * (t ^ 2 - 1) + 2) * (2 * t) -
      2 * (t ^ 2 - 1) * ((t ^ 2 - 1) + 1) * (3 * t ^ 2 - 1) = 0 := by ring

/-- DF-6: both generators of the nodal maximal ideal annihilate sigma. -/
theorem node_torsion_x (x y : K) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (x * (y * (3 * x + 2)), x * (-2 * x * (x + 1))) =
      (y * (x * (3 * x + 2)), y * (-2 * y)) := by
  apply Prod.ext
  · ring
  · calc
      _ = -2 * (x ^ 2 * (x + 1)) := by ring
      _ = _ := by rw [← h]; ring

theorem node_torsion_y (x y : K) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (y * (y * (3 * x + 2)), y * (-2 * x * (x + 1))) =
      (x * (x + 1) * (x * (3 * x + 2)), x * (x + 1) * (-2 * y)) := by
  apply Prod.ext
  · calc
      _ = y ^ 2 * (3 * x + 2) := by ring
      _ = _ := by rw [h]; ring
  · ring

/-- DF-7: the cone's gradient vanishes at the vertex. -/
theorem cone_gradient_vertex :
    ((0 : K), (0 : K), -2 * (0 : K)) = (0, 0, 0) := by simp

/-- DF-12: the Euler kernel is precisely the graph of this linear expression. -/
theorem euler_kernel_coordinates (n : ℕ) (u b : Fin n → K) (a : K) :
    a + ∑ j, u j * b j = 0 ↔ a = -∑ j, u j * b j :=
  add_eq_zero_iff_eq_neg

/-- DF-12: the stated kernel coordinates always produce an element of the kernel. -/
theorem euler_kernel_reconstruction (n : ℕ) (u b : Fin n → K) :
    (-∑ j, u j * b j) + ∑ j, u j * b j = 0 := by ring

end ExplicitRelations

section CanonicalForm
variable {K : Type*} [Field K]

/-- DF-14: local expressions agree, with both denominators explicitly nonzero. -/
theorem plane_form_agreement (fx fy dx dy : K) (hx : fx ≠ 0) (hy : fy ≠ 0)
    (h : fx * dx + fy * dy = 0) : dx / fy = -dy / fx := by
  apply (div_eq_div_iff hy hx).mpr
  linear_combination h

/-- DF-14: the projective overlap computation before collecting integer powers. -/
theorem plane_chart_transition (x a fy dx : K) (hx : x ≠ 0)
    (ha : a ≠ 0) (hy : fy ≠ 0) :
    -(-dx / x ^ 2) / (a * fy) = (1 / (x ^ 2 * a)) * (dx / fy) := by
  field_simp
end CanonicalForm

section SmoothConormal
variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite σ]

/-- DF-10: injectivity for the precise standard-smooth conormal map. -/
theorem standardSmooth_conormal_injective (P : Algebra.SubmersivePresentation R S ι σ) :
    Function.Injective P.toExtension.cotangentComplex :=
  P.cotangentComplex_injective
end SmoothConormal

end SupplementDF

/- DF-10 is now the tangent/normal corollary of LP2-9, which remains the
single home of conormal injectivity. The same standard-smooth conormal
interfaces support the input. Dualizing a split finite-free sequence is the
explicit algebraic reader check; the global sheaf-dual identification remains
within the sheaf-assembly gap recorded above. -/
