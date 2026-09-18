import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Localization.Basic

/-!
CAT: the universal-property arguments are checked at arbitrary categories;
localization uses the unital ring localization, not a field of fractions.
The filtered-colimit comparison below has precisely the common-object,
two-arrow formulation used in the text. No choice of a directed replacement
is implicit. The module forgetful functor's preservation theorem checks the
passage from the quotient of sets to the module colimit.
-/
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace Supplements.CAT
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The square drawn in CAT-1, in Lean's left-to-right composition convention. -/
theorem naturality_square {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := α.naturality f

/-- The two universal maps are inverse because endomorphisms are unique. -/
def initialComparison {P Q : C} (hP : IsInitial P) (hQ : IsInitial Q) : P ≅ Q where
  hom := hP.to Q
  inv := hQ.to P
  hom_inv_id := hP.hom_ext _ _
  inv_hom_id := hQ.hom_ext _ _

/-- Cone comparison is uniquely determined by its projections. -/
def limitComparison := @limMap

abbrev filteredEquality := @Types.FilteredColimit.colimit_eq_iff

abbrev leftTriangle := @Adjunction.left_triangle

abbrev rightTriangle := @Adjunction.right_triangle

abbrev unitFromIdentity := @Adjunction.homEquiv_id

abbrev counitFromIdentity := @Adjunction.homEquiv_symm_id

abbrev transposeNaturality := @Adjunction.homEquiv_naturality_right

abbrev inverseTransposeNaturality := @Adjunction.homEquiv_naturality_left_symm

abbrev preservesColimits := @Adjunction.leftAdjoint_preservesColimits

abbrev preservesLimits := @Adjunction.rightAdjoint_preservesLimits

def localizationLift := @IsLocalization.lift

abbrev localizationUnique := @IsLocalization.ringHom_ext

example (R : Type u) [Ring R] :
    PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by infer_instance

/-- The product map is exactly the coordinate tuple. -/
def productUniversal (T : Type u) {ι : Type u} (X : ι → Type u) :
    (T → ∀ i, X i) ≃ (∀ i, T → X i) where
  toFun f i t := f t i
  invFun f t i := f i t
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coproduct map is exactly restriction to the summands. -/
def coproductUniversal (T : Type u) {ι : Type u} (X : ι → Type u) :
    ((Σ i, X i) → T) ≃ (∀ i, X i → T) where
  toFun f i x := f ⟨i, x⟩
  invFun f x := f x.1 x.2
  left_inv _ := rfl
  right_inv _ := rfl
end Supplements.CAT

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
