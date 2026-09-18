import Mathlib.AlgebraicGeometry.Birational.Composition
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Tactic.Ring

/-!
RM-1–RM-10. PartialMap and RationalMap use dense open representatives
and equality on a common dense open, as in the textbook. The equivalence,
restriction, maximal representative, composition and generic-point
extension are actual scheme constructions here. Mathlib's functionField
is the generic stalk; functionField_isFractionRing_of_isAffineOpen checks
the fraction-field comparison used when clearing denominators.

The maximal-representative theorem below is complete for an absolutely
separated target. The relative overlap equality theorem is also checked,
but its gluing into a relative maximal representative over a possibly
nonseparated base is not assembled here. The generic-map equivalence is
not itself the full contravariant equivalence with field embeddings:
the dominant generic-point/field-map bridge and the passage from inverse
rational maps to a PartialIso still need assembly.

RM-5: finite/proper/graph inputs are checked; denominator clearing and
the nonempty clopen argument for the entire inverse image are not yet
packaged together. RM-6: graph cartesian identity and proper projection
are checked, not the reduced graph closure and its restriction. RM-7–RM-8:
valuative existence/uniqueness and local-stalk spreading are checked;
normal codimension-one local rings as DVRs, the affine Hartogs bridge,
and global gluing of curve extensions remain gaps. RM-9–RM-10 polynomial
identities below check the chart equations, not the projective incidence
scheme, its maximality, or the cusp's nonregular inverse.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.RM

abbrev representativeEquivalence := @Scheme.PartialMap.equivalence_rel
abbrev restrictionCompatibility := @Scheme.PartialMap.restrict_toRationalMap
abbrev relativeOverlapEquality := @Scheme.PartialMap.equiv_iff_of_isSeparated

theorem maximal_representative {X Y : Scheme} [IsReduced X] [Y.IsSeparated]
    (f : X.RationalMap Y) :
    f.toPartialMap.toRationalMap = f ∧ f.toPartialMap.domain = f.domain := by
  exact ⟨f.toRationalMap_toPartialMap, rfl⟩

abbrev representativeRestriction := @Scheme.PartialMap.toPartialMap_toRationalMap_restrict
abbrev composition := @Scheme.RationalMap.comp
abbrev compositionRepresentatives := @Scheme.RationalMap.toRationalMap_comp
abbrev compositionAssociative := @Scheme.RationalMap.comp_assoc
abbrev compositionIdentity := @Scheme.RationalMap.comp_id
abbrev dominanceIndependent := @Scheme.PartialMap.isDominant_hom_iff_of_equiv
abbrev genericMapEquivalence := @Scheme.RationalMap.equivFunctionFieldOver
abbrev finiteTypeStalkSpreading := @Scheme.PartialMap.ofFromSpecStalk
abbrev stalkSpreadingValue := @Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk
abbrev fieldOnAffine := @functionField_isFractionRing_of_isAffineOpen
abbrev rationalFunctionsInjective := @Scheme.germToFunctionField_injective
abbrev partialIsomorphismComposition := @Scheme.PartialIso.trans

theorem generic_map_determines_rational_map {X Y : Scheme} [IsIntegral X]
    (f g : X.RationalMap Y) (h : f.fromFunctionField = g.fromFunctionField) : f = g :=
  Scheme.RationalMap.eq_of_fromFunctionField_eq f g h

theorem finite_is_proper {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] : IsProper f := by
  infer_instance

abbrev properGraphCancellation := @IsProper.of_comp
abbrev graphCartesian := @pullback_lift_diagonal_isPullback
abbrev valuativeExistence := @UniversallyClosed.eq_valuativeCriterion
abbrev valuativeUniqueness := @IsSeparated.valuativeCriterion
abbrev affineTargetMaps := @ΓSpec.adjunction
abbrev denseUniqueness := @ext_of_isDominant_of_isSeparated

theorem proper_graph_projection {G X Y S : Scheme} (sX : X ⟶ S) (sY : Y ⟶ S)
    (i : G ⟶ pullback sX sY) [IsClosedImmersion i] [IsProper sY] :
    IsProper (i ≫ pullback.fst sX sY) := by infer_instance

/-- RM-9: the u-chart factors through xv-yu=0 with [u:v]=[1:a]. -/
theorem incidence_chart {R : Type*} [CommRing R] (a x : R) :
    x * a - (a * x) * 1 = 0 := by ring

/-- RM-10: the normalization parameter satisfies the cusp equation. -/
theorem cusp_parameter {R : Type*} [CommRing R] (t : R) :
    (t ^ 3) ^ 2 = (t ^ 2) ^ 3 := by ring

/-- RM-10: coordinates of the square of the Cremona map have common factor xyz. -/
theorem cremona_square {R : Type*} [CommRing R] (x y z : R) :
    ((x*z)*(x*y), (y*z)*(x*y), (y*z)*(x*z)) =
      ((x*y*z)*x, (x*y*z)*y, (x*y*z)*z) := by
  ext <;> ring

end Supplements.RM
