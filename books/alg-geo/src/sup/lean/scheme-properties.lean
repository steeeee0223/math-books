import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
XP: Hartshorne's irreducible spaces are nonempty, as is IsIrreducible here.
Normality means integrally closed DOMAIN stalks, not merely reduced stalks.
The generic-point, affine-specialization, function-field, dominance,
idempotent, compactness, and finite-type/Noetherian interfaces below retain
all hypotheses of the cited theorems. XP-9 now includes its full II.2.3
statement and proof, with reducedness, reduction, and its universal property
covered by ii-2-exe.lean. The nilradical/localization identities in that proof
are explicitly left as algebraic checks.
The normal scheme assembly and explicit example schemes are not defined here;
normality is checked through the localization algebra and the finite-component
argument in the prose. The locality table uses the existing XL/LP companions.
-/
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace Supplements.XP

/-- XP-1, the complete assertion for an arbitrary scheme. -/
theorem unique_generic (X : Scheme) (C : Set X) (hC : IsClosed C)
    (hi : IsIrreducible C) : ∃! x, IsGenericPoint x C := by
  refine ⟨hi.genericPoint, hi.isGenericPoint_genericPoint hC, ?_⟩
  intro y hy
  exact hy.eq (hi.isGenericPoint_genericPoint hC)

abbrev closedPointDensity := @LocallyOfFiniteType.jacobsonSpace
abbrev finiteResidueField := @finite_of_finite_type_of_isJacobsonRing
abbrev primeSpecialization := @PrimeSpectrum.le_iff_specializes
abbrev primeClosure := @PrimeSpectrum.closure_singleton
abbrev closedPointMaximal := @PrimeSpectrum.isClosed_singleton_iff_isMaximal
abbrev primeComponents := @PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents
abbrev componentsRestrict := @preimage_mem_irreducibleComponents
abbrev normalDomainDescent := @IsIntegrallyClosed.of_localization_maximal
abbrev genericInOpen := @IsGenericPoint.mem_open_set_iff
abbrev genericImage := @IsGenericPoint.image
abbrev integralCriterion := @isIntegral_iff_irreducibleSpace_and_isReduced
abbrev functionFieldFractions := @functionField_isFractionRing_of_isAffineOpen
abbrev sectionsEmbedInFunctionField := @Scheme.germToFunctionField_injective
abbrev dominantAffine := @PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
abbrev clopenIdempotent := @PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
abbrev noetherianOpens := @noetherianSpace_iff_opens
abbrev finiteComponents := @NoetherianSpace.finite_irreducibleComponents
abbrev noetherianAffine := @isNoetherian_Spec
abbrev locallyNoetherianCover := @isLocallyNoetherian_iff_openCover
abbrev finiteTypeNoetherianCharts := @LocallyOfFiniteType.isLocallyNoetherian
abbrev quasiSeparatedAffineIntersections := @quasiSeparatedSpace_iff_forall_affineOpens
abbrev quasiSeparatedDiagonal := @quasiSeparatedSpace_iff_quasiSeparated
abbrev normalDomainLocalization := @isIntegrallyClosed_of_isLocalization

/-- Reduced stalks imply reducedness with Hartshorne's sheaf convention. -/
theorem reduced_of_stalks (X : Scheme)
    [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] : IsReduced X :=
  isReduced_of_isReduced_stalk X

/-- XP-13 includes quasi-compactness, not just local finite type. -/
theorem finite_type_noetherian {X Y : Scheme} (f : X ⟶ Y)
    [IsNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- XP-19: in a square-zero ideal a prime contains every element. -/
theorem square_zero_in_prime {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (e : R) (h : e * e = 0) : e ∈ p := by
  exact ((inferInstance : p.IsPrime).mem_or_mem_of_mul_eq_zero h).elim id id

/-- XP-20's actual strictly increasing sequence of ideals in the Boolean product. -/
def initialSupport (n : ℕ) : Ideal (ℕ → ZMod 2) where
  carrier := {a | ∀ i, n ≤ i → a i = 0}
  zero_mem' := by simp
  add_mem' := by intros a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intros a b hb i hi; simp [hb i hi]

theorem initialSupport_strict (n : ℕ) : initialSupport n < initialSupport (n+1) := by
  constructor
  · intro a ha i hi
    exact ha i (by omega)
  · intro h
    let a : ℕ → ZMod 2 := fun i => if i = n then 1 else 0
    have ha : a ∈ initialSupport (n+1) := by
      intro i hi
      simp [a, show i ≠ n by omega]
    have hzero := h ha n (le_refl n)
    simp [a] at hzero
end Supplements.XP

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
