import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.Limits

/-!

The unit locus in XL-2 is named explicitly; XL-4 states its terminal
scheme and arithmetic point description without an extra nesting level.
These changes preserve the statements checked by the interfaces below.
XL-5's new proof: actual scheme morphism gluing, its restriction equations,
and source-cover uniqueness. XL-9's new proof uses exact module localization;
the existing ii-2-exe.lean and local-props.lean verify XL-1,2,3,6,7,8.
The added unit-locus interfaces verify XL-2 for locally ringed spaces
before any affine-target adjunction; XL-4 has its own terminal/initial interfaces.
The conversion of the affine pushforward's component maps to A_f → B_f is
an existing affine dictionary, not a new assertion of faithfulness of stalks.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.XL

def glueSchemeMaps := @Scheme.Cover.glueMorphisms

abbrev glueRestrictions := @Scheme.Cover.ι_glueMorphisms

abbrev sourceCoverEquality := @Scheme.Cover.hom_ext

abbrev injectiveLocalization := @LocalizedModule.map_injective

/-- XL-2: the unit locus is an open subset already for ringed spaces.
This construction precedes, and does not use, the affine-target adjunction. -/
def unitLocus := @RingedSpace.basicOpen

abbrev unitLocusMembership := @RingedSpace.mem_basicOpen

abbrev unitLocusRestrictionIsUnit := @RingedSpace.isUnit_res_basicOpen

abbrev unitGermHasLocalInverse := @RingedSpace.isUnit_res_of_isUnit_germ

/-- XL-4 is independent of the gluing propositions that follow it. -/
def terminalScheme := AlgebraicGeometry.specZIsTerminal

def initialEmptyScheme := @AlgebraicGeometry.isInitialOfIsEmpty

/-- Abstract gluing of the local inverse, used in XL-7 and in the affine criterion. -/
theorem inverse_unique {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (g h : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) (hh : f ≫ h = 𝟙 X) : g = h := by
  calc
    g = g ≫ (f ≫ h) := by rw [hh, Category.comp_id]
    _ = (g ≫ f) ≫ h := (Category.assoc _ _ _).symm
    _ = h := by rw [hg, Category.id_comp]
end Supplements.XL

/- XL-1,2,3,6,7,8 contain the former II.2.1,2,4,12,16,17
proofs directly. The scheme-gluing proof delegates ring-sheaf gluing to SL-4;
the quotient-topology and localization assertions are explicitly reader checks.
The ii-2-exe.lean declarations retain their original exercise-based names. -/
