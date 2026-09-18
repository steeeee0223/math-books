import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
SL-1–SL-5. SL-1 combines local equality with finite common neighborhoods.
These interfaces retain the concrete-category hypotheses of
mathlib's stalk results, rather than claiming arbitrary category-valued
sheaves have underlying germs. `basisExtension` verifies morphism extension
and `basisIso` its uniqueness/isomorphism test; the compatible-family object
construction in SL-2 is verified separately below by unique gluing.
The ring/module versions use the same operations on compatible families.
SL-4 now contains the compatible-family proof formerly placed in the
II.1.22 application. It is checked by ii-1-exercise-15-22.lean, whose final
comment records the remaining fixed-base gluing interface gap.
-/
open CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace Supplements.SL

abbrev sectionEquality := @TopCat.Presheaf.section_ext

abbrev coverEquality := @TopCat.Sheaf.eq_of_locally_eq'

abbrev uniqueGluing := @TopCat.Sheaf.existsUnique_gluing'

def basisSheafEquivalence := @CategoryTheory.Functor.IsDenseSubsite.sheafEquiv

def basisExtension := @TopCat.Sheaf.restrictHomEquivHom

abbrev basisExtensionRestriction := @TopCat.Sheaf.extend_hom_app

abbrev basisEquality := @TopCat.Sheaf.hom_ext

abbrev basisIso := @TopCat.Sheaf.isIso_iff_isIso_basis

abbrev germsEquality := @TopCat.Presheaf.germ_eq

abbrev germsRepresented := @TopCat.Presheaf.exists_germ_eq

def sheafificationStalk := @TopCat.Presheaf.sheafifyStalkIso

abbrev canonicalSheafificationStalk := @TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso

abbrev homSheaf := @CategoryTheory.Presheaf.IsSheaf.hom

section EqualityCriteria
universe v u
open Opposite
variable {C : Type u} [Category.{v} C]
    {FC : C → C → Type v} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits.{v} C] [HasLimits C]
    [PreservesFilteredColimits (forget C)] [PreservesLimits (forget C)]
    [(forget C).ReflectsIsomorphisms] {X : TopCat.{v}}

/-- SL-1: both directions of the section/germ equivalence, with all points quantified. -/
theorem section_eq_iff_germs (F : TopCat.Sheaf C X) (U : Opens X)
    (s t : ToType (F.1.obj (op U))) :
    s = t ↔ ∀ (x : X) (hx : x ∈ U),
      F.presheaf.germ U x hx s = F.presheaf.germ U x hx t := by
  constructor
  · rintro rfl x hx
    rfl
  · exact TopCat.Presheaf.section_ext F U s t

omit [HasColimits C] [PreservesFilteredColimits (forget C)] in
/-- SL-1: the cover is fixed before the equivalence is asserted. -/
theorem section_eq_iff_cover (F : TopCat.Sheaf C X) {ι : Type v}
    (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V)
    (hcover : V ≤ iSup U) (s t : ToType (F.1.obj (op V))) :
    s = t ↔ ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t := by
  constructor
  · rintro rfl i
    rfl
  · exact F.eq_of_locally_eq' U V iUV hcover s t

end EqualityCriteria

section BasisRestriction

variable {ι : Type*} [Preorder ι] {F : ι → Type*}
    (res : ∀ {B C : ι}, C ≤ B → F B → F C)

/-- SL-2: `U` is the set of basis opens contained in an ambient open.
The compatibility condition uses the specified restriction maps on the basis. -/
def CompatibleBasisFamily (U : Set ι) :=
  {s : ∀ B, B ∈ U → F B //
    ∀ (B C : ι) (hB : B ∈ U) (hC : C ∈ U) (hCB : C ≤ B),
      res hCB (s B hB) = s C hC}

/-- The restriction formula in SL-2 preserves compatibility. -/
def restrictBasisFamily {U V : Set ι} (hVU : V ⊆ U)
    (s : CompatibleBasisFamily res U) : CompatibleBasisFamily res V :=
  ⟨fun B hB => s.1 B (hVU hB),
    fun B C hB hC hCB => s.2 B C (hVU hB) (hVU hC) hCB⟩

/-- Each component on a basis open contained in `V` is unchanged. -/
theorem restrictBasisFamily_apply {U V : Set ι} (hVU : V ⊆ U)
    (s : CompatibleBasisFamily res U) (B : ι) (hB : B ∈ V) :
    (restrictBasisFamily res hVU s).1 B hB = s.1 B (hVU hB) := rfl

/-- The identity law for the restriction maps of the extended presheaf. -/
theorem restrictBasisFamily_id {U : Set ι} (s : CompatibleBasisFamily res U) :
    restrictBasisFamily res (Set.Subset.refl U) s = s := rfl

/-- The composition law for the restriction maps of the extended presheaf. -/
theorem restrictBasisFamily_comp {U V W : Set ι} (hVU : V ⊆ U) (hWV : W ⊆ V)
    (s : CompatibleBasisFamily res U) :
    restrictBasisFamily res hWV (restrictBasisFamily res hVU s) =
      restrictBasisFamily res (hWV.trans hVU) s := rfl

end BasisRestriction

/-- The finite-intersection reduction in SL-1's germ criterion. -/
theorem finite_common_neighborhood {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] (U : ι → Set X) (x : X)
    (ho : ∀ i, IsOpen (U i)) (hx : ∀ i, x ∈ U i) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ i, V ⊆ U i := by
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite ho, Set.mem_iInter.mpr hx, ?_⟩
  intro i
  exact Set.iInter_subset U i
end Supplements.SL
