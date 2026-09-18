import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring

/-!
Verification map for PM. Hartshorne projectivity means a closed immersion into
finite P^n_Y, not a projective-bundle immersion or merely local projectivity.
No mathlib class is silently used as a different definition of this property.

PM-1 is a definition, with locality delegated to LP2.
PM-2–PM-3: actual closed-immersion composition and affine quotient charts are
checked. The finite-list exponent bound and the surjectivity preserved on
adding projective coordinates are explicit theorems below. The essential
section-extension theorem, affine-section criterion for ampleness, global
sheaf quotient, and relative-Proj reconstruction remain formalization gaps.
PM-4: the ring-level graph retraction and Segre equation are checked; the
line-bundle global-generation theorem and Segre closed immersion are not
constructed as global scheme theorems here.
PM-5: the monic-at-infinity prime argument is proved for arbitrary rings;
actual finite affine morphisms are checked and finite morphisms are proper.
The homogenization closure and the global ample-base embedding remain gaps.
PM-6: the coordinate monomials' pointwise nonvanishing and Segre equation are
checked; the four-chart Laurent intersection, restriction of ample sheaves,
and the full positivity equivalence remain gaps.
PM-7: the coordinate-ring surjectivity argument is checked in a polynomial
model with all coefficient and coordinate generators, and the overlap formula
is checked. Identification of section blocks with the sheaf's complete linear
system and the resulting global closed immersion remain unassembled.
PM-8: a finite injective algebra has a finite affine spectrum map and a
surjective map of prime spectra. This verifies the exact terminal assertions
used AFTER homogeneous normalization and degree-zero finite generation. Those
two graded-algebra statements and the global Proj morphism remain gaps;
ordinary (nonhomogeneous) Noether normalization is not substituted for them.
PM-9 refers to the BU companion for the incidence chart equations.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.PM

universe u

/-- A single exponent works for a finite family, as required when extending
the finite collection of sections in PM-2. -/
theorem common_exponent {ι : Type*} (s : Finset ι) (n : ι → ℕ) :
    ∃ N, ∀ i ∈ s, n i ≤ N := by
  exact ⟨s.sup n, fun i hi => Finset.le_sup hi⟩

/-- Adding more coordinates preserves the original chart's surjectivity. -/
theorem adding_coordinates_preserves_surjective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (ι : A →+* B) (φ : B →+* C) (h : Function.Surjective (φ.comp ι)) :
    Function.Surjective φ := by
  intro c
  obtain ⟨a, ha⟩ := h c
  exact ⟨ι a, ha⟩

/-- The graph algebra admits the original coordinate algebra as a retract. -/
theorem graph_coordinate_surjective {A B : Type*} [CommRing A] [CommRing B]
    (ι : A →+* B) (π : B →+* A) (h : π.comp ι = RingHom.id A) :
    Function.Surjective π := by
  intro a
  exact ⟨ι a, DFunLike.congr_fun h a⟩

theorem closed_composition {X Y Z : Scheme} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsClosedImmersion (i ≫ j) := by
  infer_instance

theorem finite_is_proper {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] : IsProper f := by
  infer_instance

/-- The projective closure has no point at infinity: at a prime, a power
vanishes only when its base coordinate vanishes. No reducedness is needed. -/
theorem monic_at_infinity {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    {ι : Type*} (x : ι → R) (d : ι → ℕ) (h : ∀ i, x i ^ d i ∈ p) :
    ∀ i, x i ∈ p := by
  intro i
  exact (inferInstance : p.IsPrime).mem_of_pow_mem (d i) (h i)

theorem no_infinity_point {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    {ι : Type*} (x : ι → R) (d : ι → ℕ)
    (h : ∀ i, x i ^ d i ∈ p) (hproj : ∃ i, x i ∉ p) : False := by
  obtain ⟨i, hi⟩ := hproj
  exact hi (monic_at_infinity p x d h i)

theorem segre_equation {R : Type*} [CommRing R] (a b c d : R) :
    (a * c) * (b * d) = (a * d) * (b * c) := by ring

theorem product_generating_monomial {k : Type*} [Field k]
    (x y : k) (a b : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ a * y ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)

/-- If a chart map contains the scalar coefficients and every variable,
it is surjective onto the entire polynomial chart ring. This is the
coordinate separation test used for the four ruled-surface charts. -/
theorem polynomial_chart_surjective {k A : Type*} [CommRing k] [CommRing A]
    {ι : Type*} (φ : A →+* MvPolynomial ι k)
    (hC : ∀ c : k, ∃ a, φ a = MvPolynomial.C c)
    (hX : ∀ i : ι, ∃ a, φ a = MvPolynomial.X i) :
    Function.Surjective φ := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hX i
    exact ⟨a * b, by rw [map_mul, ha, hb]⟩

theorem ruled_transition {R : Type*} [CommRing R]
    (t a b : R) (n : ℕ) : a * (t ^ n * b) = t ^ n * (a * b) := by ring

/-- Actual affine finiteness, rather than an inference from properness. -/
theorem finite_affine {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact (RingHom.finite_algebraMap).mpr inferInstance

/-- The precise lying-over assertion in every chart of PM-8. -/
theorem finite_injective_surjective_spectrum {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (h : Function.Injective (algebraMap R S)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
  exact Algebra.IsIntegral.comap_surjective R S

theorem quotient_chart_closed {R : Type*} [CommRing R] (I : Ideal R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end Supplements.PM
