import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
MG. Fiber, diagonal, and graph use actual scheme fiber products. Mathlib's
`Hom.ker` for an arbitrary morphism is the largest quasi-coherent ideal
inside the sectionwise kernel. `kernelOnAffine` below requires QuasiCompact
and proves it is the actual kernel, so we do not silently identify these
notions without the hypothesis in MG-12. `LocallyQuasiFinite` alone is not
our finite-type/finite-fiber convention: finiteFibers and the cited criterion
retain quasi-compactness. The example rings and the reduction factor's
quotient map are checked separately below where relevant. The full named
counterexample schemes and the global reduced-morphism construction are
not assembled in this companion.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.MG

def affineFiberProduct := @pullbackSpecIso
abbrev firstProjection := @pullbackSpecIso_inv_fst
abbrev secondProjection := @pullbackSpecIso_inv_snd
def fiberTopology := @Scheme.Hom.fiberHomeo
abbrev fiberProjection := @Scheme.Hom.fiberHomeo_apply
abbrev graphCartesian := @pullback_lift_diagonal_isPullback
abbrev denseOpenUniqueness := @ext_of_isDominant_of_isSeparated
abbrev reducedClosedEqualizer := @isIso_of_isClosedImmersion_of_surjective
abbrev affineIntersectionCriterion := @diagonal_isAffine_iff_forall_isAffineOpen_inf
abbrev finiteTypeCancellation := @locallyOfFiniteType_of_comp
def fieldValuedPoints := @Scheme.SpecToEquivOfField
abbrev fieldPointNaturality := @Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
abbrev finiteFibers := @Scheme.Hom.finite_preimage_singleton
abbrev quasiFiniteConvention := @locallyQuasiFinite_iff_finite_preimage_singleton
abbrev closedMap := @Scheme.Hom.isClosedMap
abbrev kernelOnAffine := @Scheme.Hom.ker_apply
abbrev kernelRestriction := @Scheme.ker_morphismRestrict_ideal
abbrev imageClosure := @Scheme.Hom.support_ker
abbrev kernelFiniteCover := @Scheme.Hom.iInf_ker_openCover_map_comp
def imageFactor := @Scheme.Hom.toImage
abbrev imageFactorization := @Scheme.Hom.toImage_imageι
def imageUniversalProperty := @Scheme.kerAdjunction
abbrev universalClosedDescent := @UniversallyClosed.of_comp_surjective
abbrev properGraphCancellation := @IsProper.of_comp

/-- MG-11: finiteness gives the complete properness assertion. -/
theorem finite_is_proper {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] : IsProper f := by
  infer_instance

/-- MG-13's terminal descent, after constructing the proper surjection onto the image. -/
theorem proper_descends {Z W S : Scheme} (q : Z ⟶ W) (p : W ⟶ S)
    [Surjective q] [IsProper (q ≫ p)] [LocallyOfFiniteType p]
    [IsSeparated p] : IsProper p := by
  letI : UniversallyClosed p := UniversallyClosed.of_comp_surjective q p
  exact ⟨⟩

/-- MG-9: the map B/I → B/J for I ≤ J is surjective. -/
theorem quotient_factor_surjective {B : Type*} [CommRing B]
    (I J : Ideal B) (h : I ≤ J) :
    Function.Surjective (Ideal.Quotient.factor h) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk I b, rfl⟩
end Supplements.MG

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
