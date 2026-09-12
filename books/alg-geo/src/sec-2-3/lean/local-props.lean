import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Local properties of morphisms

Kernel-checked companions to the revised proofs in `../local-props.typ`.
The textbook uses Hartshorne-style definitions and spells out the geometric
reductions.  The declarations below verify the corresponding ring-locality,
affine-comparison, stalk, target-locality, and base-change claims available in
mathlib.  The negative examples, the derivation of source gluing for integral
and finite maps, and the faithful-flat gluing arguments remain mathematical
arguments in the textbook; their supporting positive equivalences are checked
below.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace HartshorneII3LocalProperties

section AbstractLocality

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

/-- The two localization fields used by a principal target refinement followed
by a principal source refinement. -/
theorem principalRefinement_fields (h : RingHom.PropertyIsLocal P) :
    RingHom.LocalizationAwayPreserves P ∧
      RingHom.StableUnderCompositionWithLocalizationAwayTarget P :=
  ⟨h.localizationAwayPreserves, h.StableUnderCompositionWithLocalizationAwayTarget⟩

/-- Target localization and target gluing make the all-affine-pairs property
local as an affine-target property.  This is the target half of strong affine
locality. -/
theorem sourceAffineLocally_isLocal
    (hIso : RingHom.RespectsIso P)
    (hT : RingHom.LocalizationAwayPreserves P)
    (hGT : RingHom.OfLocalizationSpan P) :
    (sourceAffineLocally P).IsLocal :=
  AlgebraicGeometry.sourceAffineLocally_isLocal P hIso hT hGT

/-- The whole-affine-inverse-image route uses target localization and target
gluing, and is the formal counterpart of the affineAnd proof. -/
theorem affineAnd_isLocal
    (hIso : RingHom.RespectsIso P)
    (hT : RingHom.LocalizationAwayPreserves P)
    (hGT : RingHom.OfLocalizationSpan P) :
    (affineAnd P).IsLocal :=
  AlgebraicGeometry.affineAnd_isLocal hIso hT hGT

/-- Ring-theoretic base change transports through the whole-affine-inverse-
image criterion. -/
theorem affineAnd_isStableUnderBaseChange
    (hIso : RingHom.RespectsIso P)
    (hBC : RingHom.IsStableUnderBaseChange P) :
    (affineAnd P).IsStableUnderBaseChange :=
  AlgebraicGeometry.affineAnd_isStableUnderBaseChange hIso hBC

variable (Q : MorphismProperty Scheme.{u}) [HasRingHomProperty Q P]

/-- Fixed-target affine communication from an affine source cover. -/
theorem fixedTarget_affineCommunication {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    (h : ∀ i, P ((𝒰.f i ≫ f).appTop).hom) : Q f :=
  HasRingHomProperty.of_source_openCover (P := Q) 𝒰 h

/-- The logical core of the RS/GSS and RT/GTT equivalences. -/
theorem restriction_and_gluing_iff {I : Type*} (q : Prop) (qᵢ : I → Prop) :
    ((q → ∀ i, qᵢ i) ∧ ((∀ i, qᵢ i) → q)) ↔ (q ↔ ∀ i, qᵢ i) := by
  tauto

end AbstractLocality

section RingProfiles

/-- Finite type has T, S, GS, and GT. -/
theorem finiteType_isLocal : RingHom.PropertyIsLocal @RingHom.FiniteType :=
  RingHom.finiteType_isLocal

/-- Finite type is stable under arbitrary base change. -/
theorem finiteType_baseChange :
    RingHom.IsStableUnderBaseChange @RingHom.FiniteType :=
  RingHom.finiteType_isStableUnderBaseChange

/-- Finite presentation has T, S, GS, and GT. -/
theorem finitePresentation_isLocal :
    RingHom.PropertyIsLocal @RingHom.FinitePresentation :=
  RingHom.finitePresentation_isLocal

/-- Finite presentation is stable under arbitrary base change. -/
theorem finitePresentation_baseChange :
    RingHom.IsStableUnderBaseChange @RingHom.FinitePresentation :=
  RingHom.finitePresentation_isStableUnderBaseChange

/-- Finite ring maps satisfy target gluing. -/
theorem finite_targetGluing : RingHom.OfLocalizationSpan @RingHom.Finite :=
  RingHom.finite_ofLocalizationSpan

/-- Finite ring maps are stable under arbitrary base change. -/
theorem finite_baseChange : RingHom.IsStableUnderBaseChange @RingHom.Finite :=
  RingHom.finite_isStableUnderBaseChange

/-- Integral ring maps satisfy target gluing. -/
theorem integral_targetGluing :
    RingHom.OfLocalizationSpan (RingHom.IsIntegral ·) :=
  RingHom.isIntegral_ofLocalizationSpan

/-- Integral ring maps are stable under arbitrary base change. -/
theorem integral_baseChange :
    RingHom.IsStableUnderBaseChange (RingHom.IsIntegral ·) :=
  RingHom.isIntegral_isStableUnderBaseChange

/-- Surjective ring maps satisfy target gluing. -/
theorem surjective_targetGluing :
    RingHom.OfLocalizationSpan (fun f ↦ Function.Surjective f) :=
  RingHom.surjective_ofLocalizationSpan

/-- Surjective ring maps are stable under arbitrary base change. -/
theorem surjective_baseChange :
    RingHom.IsStableUnderBaseChange (fun f ↦ Function.Surjective f) :=
  RingHom.surjective_isStableUnderBaseChange

/-- Flat ring maps have the complete four-field locality package. -/
theorem flat_isLocal : RingHom.PropertyIsLocal RingHom.Flat :=
  RingHom.Flat.propertyIsLocal

/-- Flat ring maps are stable under arbitrary base change. -/
theorem flat_baseChange : RingHom.IsStableUnderBaseChange RingHom.Flat :=
  RingHom.Flat.isStableUnderBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The algebraic equivalence used in the faithfully-flat gluing proof. -/
theorem faithfullyFlat_iff_flat_and_spec_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.comap f) :=
  RingHom.FaithfullyFlat.iff_flat_and_comap_surjective

/-- Faithful flatness is stable under arbitrary base change. -/
theorem faithfullyFlat_baseChange :
    RingHom.IsStableUnderBaseChange RingHom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.isStableUnderBaseChange

end RingProfiles

section SchemeProfiles

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Locally finite-type morphisms are local on both source and target. -/
theorem locallyOfFiniteType_locality :
    IsZariskiLocalAtSource @LocallyOfFiniteType ∧
      IsZariskiLocalAtTarget @LocallyOfFiniteType :=
  ⟨inferInstance, inferInstance⟩

/-- Locally finite-type morphisms are stable under base change. -/
theorem locallyOfFiniteType_baseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType :=
  inferInstance

/-- Locally finite-presentation morphisms are local on both sides and stable
under base change. -/
theorem locallyOfFinitePresentation_locality_and_baseChange :
    IsZariskiLocalAtSource @LocallyOfFinitePresentation ∧
      IsZariskiLocalAtTarget @LocallyOfFinitePresentation ∧
      MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The finite-morphism affine criterion. -/
theorem finite_affine_criterion [IsAffine X] [IsAffine Y] :
    IsFinite f ↔ (f.appTop).hom.Finite := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  simp only [and_iff_right_iff_imp]
  exact fun _ ↦ inferInstance

/-- Finite morphisms are target local and stable under base change. -/
theorem finite_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @IsFinite ∧
      MorphismProperty.IsStableUnderBaseChange @IsFinite :=
  ⟨inferInstance, inferInstance⟩

/-- Integral morphisms are target local and stable under base change. -/
theorem integral_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @IsIntegralHom ∧
      MorphismProperty.IsStableUnderBaseChange @IsIntegralHom :=
  ⟨inferInstance, inferInstance⟩

/-- Closed immersions are target local and stable under base change. -/
theorem closedImmersion_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @IsClosedImmersion ∧
      MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion :=
  ⟨inferInstance, inferInstance⟩

/-- Flatness agrees with the stalk-map criterion. -/
theorem flat_iff_flat_stalkMap :
    Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat :=
  Flat.iff_flat_stalkMap f

/-- Flat morphisms are local on both sides and stable under base change. -/
theorem flat_locality_and_baseChange :
    IsZariskiLocalAtSource @Flat ∧ IsZariskiLocalAtTarget @Flat ∧
      MorphismProperty.IsStableUnderBaseChange @Flat :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- On affine schemes, faithful flatness is flatness plus surjectivity. -/
theorem affine_faithfullyFlat_iff [IsAffine X] [IsAffine Y] :
    (f.appTop).hom.FaithfullyFlat ↔ Flat f ∧ Surjective f := by
  simpa [and_comm] using
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).symm

/-- The scheme property “flat and surjective,” hence faithful flatness, is
target local and stable under base change. -/
theorem faithfullyFlatMorphism_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget (@Flat ⊓ @Surjective) ∧
      MorphismProperty.IsStableUnderBaseChange (@Flat ⊓ @Surjective) :=
  ⟨inferInstance, inferInstance⟩

/-- Quasi-compact morphisms are target local and stable under base change. -/
theorem quasiCompact_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @QuasiCompact ∧
      MorphismProperty.IsStableUnderBaseChange @QuasiCompact :=
  ⟨inferInstance, inferInstance⟩

/-- Affine morphisms are target local and stable under base change. -/
theorem affine_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @IsAffineHom ∧
      MorphismProperty.IsStableUnderBaseChange @IsAffineHom :=
  ⟨inferInstance, inferInstance⟩

/-- Separatedness is target local and stable under base change. -/
theorem separated_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @IsSeparated ∧
      MorphismProperty.IsStableUnderBaseChange @IsSeparated :=
  ⟨inferInstance, inferInstance⟩

/-- Separatedness is exactly the closed-immersion condition on the diagonal. -/
theorem separated_iff_diagonal_closedImmersion :
    IsSeparated f ↔ IsClosedImmersion (pullback.diagonal f) := by
  exact ⟨fun h ↦ h.isClosedImmersion_diagonal, fun h ↦ ⟨h⟩⟩

/-- Restriction to an open source preserves separatedness. -/
theorem separated_sourceRestriction (U : X.Opens) [IsSeparated f] :
    IsSeparated (U.ι ≫ f) :=
  inferInstance

/-- Universal closedness is target local and stable under base change. -/
theorem universallyClosed_targetLocal_and_baseChange :
    IsZariskiLocalAtTarget @UniversallyClosed ∧
      MorphismProperty.IsStableUnderBaseChange @UniversallyClosed :=
  ⟨inferInstance, inferInstance⟩

end SchemeProfiles

end HartshorneII3LocalProperties
