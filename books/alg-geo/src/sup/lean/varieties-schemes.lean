import Mathlib.RingTheory.Nullstellensatz
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Tactic

/-!
VS: k is algebraically closed. Hartshorne's Chapter I varieties are not silently
replaced by all finite-type schemes. The affine Nullstellensatz, closed-point
criterion, Proj chart and fraction identifications, field-valued-point naturality,
and gluing uniqueness below verify the reductions. The repo does not define the
classical variety category or Hartshorne's t functor; thus the assembled global
full-faithfulness and the identification of classical regular functions with
localized coordinate rings are not end-to-end Lean theorems here. The P¹ chart
transition is an actual field inverse identity, not a construction of P¹.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace Supplements.VS
abbrev maximalPoints := @MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
abbrev closedPoints := @PrimeSpectrum.isClosed_singleton_iff_isMaximal
abbrev finiteResidueFields := @finite_of_finite_type_of_isJacobsonRing
abbrev jacobsonCharts := @LocallyOfFiniteType.jacobsonSpace
def closedPointBijection := @pointEquivClosedPoint
def closedResidueField := @residueFieldIsoBase
def fieldPoints := @Scheme.SpecToEquivOfField
abbrev pointNaturality := @Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
def affineMaps := @Spec.homEquiv
abbrev affineMapFaithful := @Spec.map_injective
def projectiveChart := @Proj.basicOpenIsoSpec
abbrev chartRestrictions := @Proj.awayι_preimage_basicOpen
def glueMorphisms := @Scheme.Cover.glueMorphisms
abbrev glueUnique := @Scheme.Cover.hom_ext

/-- VS-1/CS-6: radical affine equations are exactly the equations on classical points. -/
theorem equations_from_points {k : Type*} [Field k] [IsAlgClosed k]
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι k)) (hI : I.IsRadical) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I := by
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

/-- VS-1: a k-algebra embedded in k equals k; this is the residue-field converse. -/
theorem algebra_map_to_base_surjective {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] (f : A →ₐ[k] k) : Function.Surjective f := by
  intro x
  exact ⟨algebraMap k A x, by simp⟩

/-- VS-2: the two P¹ coordinate transitions are mutually inverse. -/
theorem reciprocal_transition {k : Type*} [Field k] (t : k) (ht : t ≠ 0) :
    t * t⁻¹ = 1 ∧ (t⁻¹)⁻¹ = t := by
  exact ⟨mul_inv_cancel₀ ht, inv_inv t⟩
end Supplements.VS

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
