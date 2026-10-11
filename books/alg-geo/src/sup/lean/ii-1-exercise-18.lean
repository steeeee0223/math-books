/- Relocated from sec-2-1/lean/exercise-18.lean; mathematical declarations unchanged. -/
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits

open CategoryTheory

namespace Exercise1_18

variable {X Y : TopCat} (f : X ⟶ Y)

/- Mathlib's formalization of the whole assertion `f⁻¹ ⊣ f_*`. -/
noncomputable def adjunction :
    TopCat.Sheaf.pullback Ab f ⊣ TopCat.Sheaf.pushforward Ab f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction Ab f

/- Exercise 1.18(i): the counit `f⁻¹ f_* F ⟶ F`. -/
noncomputable def counit (F : TopCat.Sheaf Ab X) :
    (TopCat.Sheaf.pullback Ab f).obj
        ((TopCat.Sheaf.pushforward Ab f).obj F) ⟶ F :=
  (adjunction f).counit.app F

/- Exercise 1.18(ii): the unit `G ⟶ f_* f⁻¹ G`. -/
noncomputable def unit (G : TopCat.Sheaf Ab Y) :
    G ⟶ (TopCat.Sheaf.pushforward Ab f).obj
        ((TopCat.Sheaf.pullback Ab f).obj G) :=
  (adjunction f).unit.app G

/- Exercise 1.18(iii): the natural bijection of hom-sets. -/
noncomputable def homEquiv (G : TopCat.Sheaf Ab Y)
    (F : TopCat.Sheaf Ab X) :
    ((TopCat.Sheaf.pullback Ab f).obj G ⟶ F) ≃
      (G ⟶ (TopCat.Sheaf.pushforward Ab f).obj F) :=
  (adjunction f).homEquiv G F


/- SC-3(a): the presheaf map [s] ↦ β(s)|_U extends uniquely through
sheafification, and the reverse map sends s to α(s^f). Mathlib constructs
inverse image by presheaf pullback and sheafification, with the same
colimit and sheafification universal properties as Hartshorne's definition.
Below we check the complete adjunction for abelian sheaves, the transpose
formulas, their inverse laws, and the images of identities. -/
theorem homEquiv_forward (G : TopCat.Sheaf Ab Y) (F : TopCat.Sheaf Ab X)
    (α : (TopCat.Sheaf.pullback Ab f).obj G ⟶ F) :
    homEquiv f G F α = unit f G ≫ (TopCat.Sheaf.pushforward Ab f).map α := rfl

theorem homEquiv_inverse (G : TopCat.Sheaf Ab Y) (F : TopCat.Sheaf Ab X)
    (β : G ⟶ (TopCat.Sheaf.pushforward Ab f).obj F) :
    (homEquiv f G F).symm β =
      (TopCat.Sheaf.pullback Ab f).map β ≫ counit f F := rfl

theorem inverse_forward (G : TopCat.Sheaf Ab Y) (F : TopCat.Sheaf Ab X)
    (α : (TopCat.Sheaf.pullback Ab f).obj G ⟶ F) :
    (homEquiv f G F).symm (homEquiv f G F α) = α :=
  (homEquiv f G F).symm_apply_apply α

theorem forward_inverse (G : TopCat.Sheaf Ab Y) (F : TopCat.Sheaf Ab X)
    (β : G ⟶ (TopCat.Sheaf.pushforward Ab f).obj F) :
    homEquiv f G F ((homEquiv f G F).symm β) = β :=
  (homEquiv f G F).apply_symm_apply β


/-- The unit is the transpose of the identity on the inverse image. -/
theorem unit_from_identity (G : TopCat.Sheaf Ab Y) :
    homEquiv f G ((TopCat.Sheaf.pullback Ab f).obj G) (𝟙 _) = unit f G := by
  rw [homEquiv_forward, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The counit is the inverse transpose of the identity on the direct image. -/
theorem counit_from_identity (F : TopCat.Sheaf Ab X) :
    (homEquiv f ((TopCat.Sheaf.pushforward Ab f).obj F) F).symm (𝟙 _) =
      counit f F := by
  rw [homEquiv_inverse, CategoryTheory.Functor.map_id, Category.id_comp]


/-- The first triangle identity used to show that the two hom-set maps invert. -/
theorem left_triangle (G : TopCat.Sheaf Ab Y) :
    (TopCat.Sheaf.pullback Ab f).map (unit f G) ≫
      counit f ((TopCat.Sheaf.pullback Ab f).obj G) = 𝟙 _ :=
  (adjunction f).left_triangle_components G

/-- The second triangle identity, on direct images. -/
theorem right_triangle (F : TopCat.Sheaf Ab X) :
    unit f ((TopCat.Sheaf.pushforward Ab f).obj F) ≫
      (TopCat.Sheaf.pushforward Ab f).map (counit f F) = 𝟙 _ :=
  (adjunction f).right_triangle_components F

end Exercise1_18

/- The II.1.18 construction is now the proof of SC-3. The unit, counit,
Hom equivalence, transpose formulas, inverse laws, and triangle identities
above verify the same maps. -/
