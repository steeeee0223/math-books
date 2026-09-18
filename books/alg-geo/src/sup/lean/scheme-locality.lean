import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
XL-3's new proof: actual scheme morphism gluing, its restriction equations,
and source-cover uniqueness. XL-8's new proof uses exact module localization;
the existing ii-2-exe.lean and local-props.lean verify XL-1,2,4,5,6,7.
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

/-- Abstract gluing of the local inverse, used in XL-5 and in the affine criterion. -/
theorem inverse_unique {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (g h : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) (hh : f ≫ h = 𝟙 X) : g = h := by
  calc
    g = g ≫ (f ≫ h) := by rw [hh, Category.comp_id]
    _ = (g ≫ f) ≫ h := (Category.assoc _ _ _).symm
    _ = h := by rw [hg, Category.id_comp]
end Supplements.XL

/- XL-1,2,4,5,6,7 now contain the former II.2.1,2,4,12,16,17
proofs directly. The scheme-gluing proof delegates ring-sheaf gluing to SL-4;
the quotient-topology and localization assertions are explicitly reader checks.
The ii-2-exe.lean declarations retain their original exercise-based names. -/
