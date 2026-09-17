/- Relocated from sec-2-1/lean/exercise-15-22.lean; mathematical declarations unchanged. -/
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Hartshorne II.1, Exercises 1.15 and 1.22

The declarations below connect the accompanying human-readable proofs in
the supplement applications indexed by the original exercise numbers to mathlib's internal-Hom sheaf and sheafed-space gluing APIs.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace HartshorneII1

section Exercise1_15

variable {X : TopCat}
abbrev AbSheaf (X : TopCat) := TopCat.Sheaf.{0, 0, 1} AddCommGrpCat.{0} X
variable (F G : AbSheaf X)

/-- Morphisms into a sheaf form a sheaf locally. -/
theorem sheafHom_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (presheafHom F.obj G.obj) :=
  G.2.hom F.obj

/-- Global sections of the Hom sheaf are precisely sheaf morphisms. -/
noncomputable def sheafHom_sections :
    (sheafHom F G).obj.sections ≃ (F ⟶ G) :=
  sheafHomSectionsEquiv F G

/-- The morphisms form an abelian group because the target category is
preadditive; this is the group law used pointwise by the Hom sheaf. -/
example : AddCommGroup (F ⟶ G) := by infer_instance

end Exercise1_15

section Exercise1_22

variable (D : SheafedSpace.GlueData AddCommGrpCat.{u})
  [HasLimits AddCommGrpCat.{u}]

/-- Mathlib constructs the object obtained by gluing the local sheafed spaces. -/
example : SheafedSpace AddCommGrpCat.{u} := D.toGlueData.glued

/-- Each local piece is an open subspace of the glued object. -/
example (i : D.J) :
    SheafedSpace.IsOpenImmersion (D.toGlueData.ι i) := by
  infer_instance

/-- The local pieces cover the glued object. -/
example (x : D.toGlueData.glued) :
    ∃ (i : D.J) (y : D.U i), (D.toGlueData.ι i).hom.base y = x :=
  D.ι_jointly_surjective x

/-- The prescribed pairwise overlap is the actual intersection in the glued
object. -/
example (i j : D.J) :
    IsLimit (D.toGlueData.vPullbackCone i j) :=
  D.vPullbackConeIsLimit i j

end Exercise1_22


/- The revised 1.15 proof is checked by sheafHom_isSheaf and
sheafHom_sections, with the abelian group instance above. For 1.22 the gluing
API checks the open pieces, cover and overlaps of the glued sheafed space.
The identification of its underlying space with the fixed X and the
compatible-family formula for sections are not assembled here as an
isomorphism over X; this is the remaining interface gap for that exercise. -/

end HartshorneII1
