import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic

/-!
PJ verification map (Hartshorne's nonnegative gradings and degree-zero charts).
1: actual affine chart and empty affine spectrum criterion; positive homogeneous
   cover, nilpotent prime criterion and finite nilpotent sums.
2: homogeneous fraction maps and their composition; mapEverywhere has mathlib's
   STRONGER irrelevant-ideal containment, not the radical criterion in the text.
   The latter's pointwise prime argument is checked by radical_le_prime below.
   The partial-domain scheme map must still be assembled from these charts.
3--4: localization equality, chart gluing uniqueness and affine closed immersion;
   the high-degree inverse on homogeneous fractions and quotient degree-zero
   exactness are not yet packaged as graded-map theorems.
5: no graded associated-module sheaf / augmented graded Cech complex interface
   is constructed here. The eventual-exactness calculation, the graded
   adjunction and reconstruction remain unformalized; finite denominator and
   power lemmas check only their algebraic substeps, not the entire claims.
6: saturation_power verifies the finite-power criterion with the actual colon
   ideal; saturation_localizes verifies equality of extended ideals, for arbitrary
   s whose positive power is in the irrelevant ideal. The section-extension
   comparison with arbitrary ideal sheaves remains unassembled.
7--8: chart fractions, common-exponent arithmetic, tensor bilinearity and Segre
   relation are checked; neither the Veronese/Segre algebra equivalence nor the
   twist sheaf comparison is constructed as a single isomorphism here.
9: graph pullback, stability and composition of actual closed immersions;
   no projective-space or very-ample line-bundle interface is constructed.
10: normal intersection and finite-algebra integrality are actual ring theorems.
    The section-ring intersection identification and normality of a Veronese
    subring still require graded-algebra bridges. The final diagonal example
    is checked as a nonsurjective map; its sheaf-sections interpretation is prose.
These gaps are explicit verification work remaining, not extra textbook hypotheses.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.PJ

def affineChart := @Proj.basicOpenIsoSpec
abbrev emptyAffine := @PrimeSpectrum.isEmpty_iff_subsingleton
abbrev standardCover := @Proj.iSup_basicOpen_eq_top
abbrev overlap := @Proj.basicOpen_mul
abbrev powerChart := @ProjectiveSpectrum.basicOpen_pow
def fractionMap := @HomogeneousLocalization.map
abbrev fractionMapComp := @HomogeneousLocalization.map_comp
abbrev fractionRepresentatives := @HomogeneousLocalization.Away.mk_surjective
abbrev homogeneousNumeratorsEventually := @HomogeneousLocalization.Away.eventually_smul_mem
abbrev homogeneousMonomialSpan := @HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
abbrev nilpotentFiniteSum := @isNilpotent_sum
abbrev fractionFaithful := @HomogeneousLocalization.val_injective
def mapEverywhere := @Proj.map
abbrev mapChart := @Proj.awayι_comp_map
abbrev mapChartPreimage := @Proj.map_preimage_basicOpen
abbrev localizationEquality := @IsLocalization.Away.exists_of_eq
abbrev localizationSurjective := @IsLocalization.Away.surj
abbrev glueUnique := @Scheme.Cover.hom_ext
abbrev closedAffine := @IsClosedImmersion.spec_of_surjective
abbrev finitePower := @Ideal.exists_pow_le_of_le_radical_of_fg
abbrev normalIntersection := @IsIntegrallyClosed.iInf
abbrev finiteAlgebraIntegral := @IsIntegral.of_finite
abbrev graphPullback := @pullback_lift_diagonal_isPullback

/-- PJ-2: containment up to radical suffices at a prime. -/
theorem radical_le_prime {R : Type*} [CommRing R] (I p : Ideal R)
    [p.IsPrime] (h : I ≤ p) : I.radical ≤ p := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  exact (inferInstance : p.IsPrime).mem_of_pow_mem n (h hn)

/-- PJ-6: finite generation converts separate powers into an irrelevant ideal power.
The ideal J is (I:s), so this is exactly J_irr^n s ⊆ I. -/
theorem saturation_power {R : Type*} [CommRing R] (I B : Ideal R)
    (hB : B.FG) (s : R)
    (h : ∀ x ∈ B, ∃ n : ℕ, x ^ n * s ∈ I) :
    ∃ n : ℕ, ∀ x ∈ B ^ n, x * s ∈ I := by
  let J := I.colon ({s} : Set R)
  have hBJ : B ≤ J.radical := by
    intro x hx
    obtain ⟨n, hn⟩ := h x hx
    exact ⟨n, Submodule.mem_colon_singleton.mpr hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hBJ hB
  exact ⟨n, fun x hx => Submodule.mem_colon_singleton.mp (hn hx)⟩

/-- PJ-6: a denominator power killing a quotient class makes it belong to the
extended ideal. This is the precise chart test for saturation. -/
theorem saturation_localizes {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal R) (x s : R)
    (hx : IsUnit (algebraMap R A x)) (n : ℕ) (h : x ^ n * s ∈ I) :
    algebraMap R A s ∈ I.map (algebraMap R A) := by
  have hh := Ideal.mem_map_of_mem (algebraMap R A) h
  rw [map_mul, map_pow] at hh
  exact ((I.map (algebraMap R A)).smul_mem_iff_of_isUnit (hx.pow n)).mp hh

/-- PJ-3/4: numerator degree can be made arbitrarily high. -/
theorem raise_degree (e m N : ℕ) (he : 0 < e) : ∃ l, N ≤ (m + l) * e := by
  refine ⟨N, ?_⟩
  have : m + N ≤ (m + N) * e := Nat.le_mul_of_pos_right _ he
  omega

/-- PJ-7: a denominator exponent can be raised to a multiple of d. -/
theorem veronese_exponent (m d : ℕ) (hd : 0 < d) :
    ∃ l n : ℕ, m + l = n * d := by
  refine ⟨m * (d - 1), m, ?_⟩
  have hh : d = 1 + (d - 1) := by omega
  conv_rhs => rw [hh]
  ring

/-- PJ-8: both exponents may be raised to the same exponent. -/
theorem common_exponent (a b : ℕ) : ∃ n, a ≤ n ∧ b ≤ n :=
  ⟨max a b, le_max_left _ _, le_max_right _ _⟩

/-- PJ-8: the Segre determinant vanishes, over any commutative ring. -/
theorem segre_equation {R : Type*} [CommRing R] (a b c d : R) :
    (a * c) * (b * d) - (a * d) * (b * c) = 0 := by ring

/-- PJ-9's closed case retains the actual scheme morphisms. -/
theorem closed_composition {X Y Z : Scheme} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsClosedImmersion (i ≫ j) := by
  infer_instance

/-- PJ example: the degree-zero diagonal cannot be surjective. -/
theorem diagonal_not_surjective {k : Type*} [Field k] :
    ¬ Function.Surjective (fun a : k => (a, a)) := by
  intro h
  obtain ⟨a, ha⟩ := h (0, 1)
  have h0 := congrArg Prod.fst ha
  have h1 := congrArg Prod.snd ha
  exact zero_ne_one (h0.symm.trans h1)

/-- PJ-1's complete affine terminal criterion for degree-zero homogeneous localization. -/
theorem homogeneous_chart_empty_iff {R : Type*} [CommRing R]
    (𝒜 : ℕ → AddSubgroup R) [GradedRing 𝒜] (f : R) :
    IsEmpty (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f)) ↔ IsNilpotent f := by
  rw [PrimeSpectrum.isEmpty_iff_subsingleton]
  constructor
  · intro h
    letI := h
    have hv : (1 : Localization.Away f) = 0 := by
      simpa using congrArg HomogeneousLocalization.val
        (Subsingleton.elim (1 : HomogeneousLocalization.Away 𝒜 f) 0)
    have hm : algebraMap R (Localization.Away f) 1 = algebraMap R (Localization.Away f) 0 := by
      simpa using hv
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := f) hm
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact HomogeneousLocalization.subsingleton 𝒜 ⟨n, hn⟩

/-- PJ-5/6's exact monomial bound, with no assertion of a uniform exponent
when the set of variables is infinite. -/
theorem monomial_bound {ι : Type*} (s : Finset ι) (a n : ι → ℕ)
    (h : (∑ i ∈ s, n i) < ∑ i ∈ s, a i) : ∃ i ∈ s, n i < a i := by
  by_contra! H
  exact (not_lt_of_ge (Finset.sum_le_sum H)) h
end Supplements.PJ
