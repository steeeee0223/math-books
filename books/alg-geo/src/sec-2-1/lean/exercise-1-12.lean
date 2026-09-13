import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Hartshorne II.1, Exercises 1.1--1.12

The declarations below are small, kernel-checked interfaces to the mathlib
results used by the accompanying human-readable proofs in `exe.typ`.

Mathlib formulates injective and surjective sheaf morphisms categorically as
monomorphisms and epimorphisms. For sheaves of abelian groups these are the
same notions as Hartshorne's kernel/image definitions.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace HartshorneII1

/- Exercise 1.1: in mathlib the constant sheaf is, by definition, the
sheafification of the constant presheaf. -/
section Exercise1_1

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (D : Type u) [Category.{v} D] [HasWeakSheafify J D]

theorem constantSheaf_eq_sheafification :
    constantSheaf J D = Functor.const Cᵒᵖ ⋙ presheafToSheaf J D :=
  rfl

end Exercise1_1

section SheavesOfAbelianGroups

variable {X : TopCat}
abbrev AbSheaf (X : TopCat) := TopCat.Sheaf.{0, 0, 1} AddCommGrpCat.{0} X

/- Exercise 1.2(a): stalks preserve finite limits and finite colimits. Thus
they preserve kernels, cokernels and images. -/
example (x : X) : PreservesFiniteLimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

example (x : X) : PreservesFiniteColimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/- Exercise 1.2(b), injective half. -/
theorem mono_iff_stalkwise_mono {F G : AbSheaf X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom) :=
  TopCat.Presheaf.mono_iff_stalk_mono φ

/- Exercises 1.2(b) and 1.3(a), surjective half. -/
theorem epi_iff_stalkwise_surjective {F G : AbSheaf X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : X,
      Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom) := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/- Exercise 1.2(c): exactness is detected on stalks. -/
theorem exact_iff_stalkwise_exact (S : ShortComplex (AbSheaf X)) :
    S.Exact ↔ ∀ x : X,
      (S.map (TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/- Exercise 1.3(a): an epimorphism is exactly a locally surjective map. -/
theorem epi_iff_locally_surjective {F G : AbSheaf X} (φ : F ⟶ G) :
    Epi φ ↔ TopCat.Presheaf.IsLocallySurjective φ.hom :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi φ).symm

/- Exercise 1.4(a): sheafification preserves monomorphisms because it is left
exact for abelian-group-valued presheaves. -/
theorem sheafification_preserves_monomorphisms :
    (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).PreservesMonomorphisms := by
  infer_instance

/- Exercise 1.5: a category of abelian-group-valued sheaves is balanced. -/
theorem isIso_iff_mono_and_epi {F G : AbSheaf X} (φ : F ⟶ G) :
    IsIso φ ↔ Mono φ ∧ Epi φ := by
  constructor
  · intro
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hmono, hepi⟩
    letI : Mono φ := hmono
    letI : Epi φ := hepi
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ).2
    intro x
    let stalkMap := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom
    haveI : Mono stalkMap := (mono_iff_stalkwise_mono φ).mp hmono x
    have hsurj : Function.Surjective stalkMap :=
      (epi_iff_stalkwise_surjective φ).mp hepi x
    haveI : Epi stalkMap := (AddCommGrpCat.epi_iff_surjective stalkMap).mpr hsurj
    exact CategoryTheory.isIso_of_mono_of_epi stalkMap

/- Exercise 1.6: the canonical kernel and cokernel sequences are exact. -/
theorem kernel_sequence_exact {F G : AbSheaf X} (φ : F ⟶ G) :
    (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).Exact :=
  ShortComplex.exact_kernel φ

theorem cokernel_sequence_exact {F G : AbSheaf X} (φ : F ⟶ G) :
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).Exact :=
  ShortComplex.exact_cokernel φ

/- Exercise 1.7: the first isomorphism theorem is the canonical
coimage--image isomorphism in an abelian category. -/
noncomputable def coimageIsoImage {F G : AbSheaf X} (φ : F ⟶ G) :
    Abelian.coimage φ ≅ Abelian.image φ :=
  Abelian.coimageIsoImage φ

/- Exercise 1.8: evaluation on an open set is left exact. -/
theorem sections_left_exact (U : TopologicalSpace.Opens X) {S : ShortComplex (AbSheaf X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s :=
  TopCat.Sheaf.sections_exact_of_left_exact hS hf s h

/- Exercise 1.9: binary sums and products coincide (biproducts). -/
example : HasBinaryBiproducts (AbSheaf X) := by
  infer_instance

/- Exercises 1.10 and 1.12: sheaf categories have all colimits and all
limits; colimits are obtained by sheafifying pointwise presheaf colimits,
whereas limits are created pointwise by the forgetful functor. -/
example {I : Type v} [Category.{v} I] :
    CreatesLimitsOfShape I (TopCat.Sheaf.forget AddCommGrpCat X) := by
  infer_instance

theorem pointwise_limit_is_sheaf {I : Type} [SmallCategory I]
    (F : I ⥤ TopCat.Presheaf.{0, 0, 1} AddCommGrpCat.{0} X)
    (hF : ∀ i, (F.obj i).IsSheaf) : (limit F).IsSheaf :=
  TopCat.limit_isSheaf (X := X) F hF

/- Exercise 1.11 uses these two formal ingredients: every open subset of a
Noetherian space is compact, and filtered colimits of abelian groups are
computed on underlying types. The finite-subcover gluing argument is written
out in `exe.typ`. -/
theorem open_isCompact [TopologicalSpace.NoetherianSpace X]
    (U : TopologicalSpace.Opens X) :
    IsCompact (U : Set X) :=
  TopologicalSpace.NoetherianSpace.isCompact (U : Set X)

example : PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat.{u}) := by
  infer_instance

end SheavesOfAbelianGroups


/- Verification boundaries for the revised exposition:
1.1: constantSheaf_eq_sheafification checks the categorical definition, not
the explicit locally constant function model. Mathlib's constant presheaf
also has value A on the empty open; Hartshorne's has zero there. Their stalks
agree since neighborhoods of a point are nonempty, so their associated
sheaves agree; this comparison is not a separate theorem in this file.
1.2--1.10, 1.12: the declarations above check the categorical terminal claims
and stalk exactness used in the prose. In 1.3(b), the elementary obstruction
to a circle lift and the local sections of the real quotient map are not
formalized here. For 1.10 the construction of the colimit cocone and its
universal factorization through sheafification are not explicitly packaged.
1.11: compactness of opens and creation of filtered colimits on underlying
types are checked. The finite-stage gluing argument, including recovery of
sections on omitted members of a cover, is not yet assembled as a sheaf theorem.
-/

end HartshorneII1
