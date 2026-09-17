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
