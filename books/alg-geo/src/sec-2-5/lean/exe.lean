import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Hartshorne II.5, Exercises

Kernel-checked interfaces to the mathlib results used in the human-readable
proofs in `../exe.typ`.  The sheaf theory in mathlib presently covers
quasi-coherent presentations and locally free sheaves, but not every operation
on coherent sheaves used by Hartshorne.  In those cases we check the affine
module lemma to which the prose reduces the assertion.
-/

open CategoryTheory TensorProduct TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v w

namespace HartshorneII5

section Exercise5_1

variable (R : Type u) [CommRing R]
variable (M : Type v) (N : Type w) (P : Type*)
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- Exercise 5.1(a), on an affine trivializing open. -/
noncomputable def finiteProjectiveDoubleDual [Module.Finite R M] [Module.Projective R M] :
    M ≃ₗ[R] Module.Dual R (Module.Dual R M) := by
  exact Module.evalEquiv R M

/-- Exercise 5.1(b), on an affine trivializing open. -/
noncomputable def finiteFreeDualTensorHom [Module.Free R M] [Module.Finite R M] :
    Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N := by
  exact dualTensorHomEquiv R M N

/-- Exercise 5.1(c): the linear tensor--Hom adjunction. -/
noncomputable def tensorHomAdjunction :
    (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ[R] P := by
  exact TensorProduct.lift.equiv (.id R) M N P

variable (A : Type*) [CommRing A] [Algebra R A]
variable (L : Type*) [AddCommGroup L] [Module R L] [Module A L]
variable [IsScalarTower R A L]

/-- Exercise 5.1(d), after restricting to affine opens. -/
noncomputable def projectionFormulaAffine :
    L ⊗[A] (A ⊗[R] M) ≃ₗ[A] L ⊗[R] M := by
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange R A A L M

end Exercise5_1

section Exercises5_2_5_3

variable (R : CommRingCat.{u})

/-- Exercise 5.2(b): on an affine scheme, quasi-coherence is exactly recovery
from global sections by the tilde construction. -/
theorem quasicoherent_iff_fromTildeGamma_isIso (F : (Spec R).Modules) :
    F.IsQuasicoherent ↔ IsIso F.fromTildeΓ := by
  exact AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ F

/-- Exercise 5.3: the tilde--global-sections adjunction. -/
noncomputable def tildeGammaHomEquiv (M : ModuleCat R) (F : (Spec R).Modules) :
    ((AlgebraicGeometry.tilde.functor R).obj M ⟶ F) ≃
      (M ⟶ (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F) := by
  exact (AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv M F

end Exercises5_2_5_3

section Exercise5_4

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Sheaf J RingCat.{w})
variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Mathlib uses Hartshorne Exercise 5.4's local free-cokernel condition as
the definition of a quasi-coherent sheaf. -/
theorem localPresentations_are_quasicoherent
    (F : SheafOfModules.{w} R) (q : F.QuasicoherentData) :
    F.IsQuasicoherent := by
  exact q.isQuasicoherent

/-- Finite local presentations imply quasi-coherence (and finite type). -/
theorem finitePresentation_is_quasicoherent
    (F : SheafOfModules.{w} R) [F.IsFinitePresentation] :
    F.IsQuasicoherent := by
  infer_instance

end Exercise5_4

section Exercise5_5

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Exercise 5.5(b): a closed immersion is finite. -/
theorem closedImmersion_isFinite [IsClosedImmersion f] : IsFinite f := by
  infer_instance

variable (R A M : Type*) [CommRing R] [CommRing A]
variable [Algebra R A] [AddCommGroup M] [Module A M] [Module R M]
variable [IsScalarTower R A M]

/-- Exercise 5.5(c), affine algebra: restriction of scalars along a finite
ring map preserves finite generation. -/
theorem finite_restrictScalars [Module.Finite R A] [Module.Finite A M] :
    Module.Finite R M := by
  exact Module.Finite.trans A M

end Exercise5_5

section Exercise5_7

variable (R : Type u) (M : Type v) [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- Exercise 5.7(a): the free locus of a finitely presented module is open. -/
theorem isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (Module.freeLocus R M) := by
  exact Module.isOpen_freeLocus

variable (N : Type w) [AddCommGroup N] [Module R N]

/-- Exercise 5.7(c), affine algebra: a tensor inverse makes a module
invertible. -/
theorem invertible_of_tensor_inverse (e : N ⊗[R] M ≃ₗ[R] R) :
    Module.Invertible R M := by
  exact Module.Invertible.right e

/-- An invertible module is Zariski-locally free of rank one. -/
theorem invertible_is_locally_free [Module.Invertible R M] :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r ∈ s, Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  exact Module.Invertible.exists_finset_free_localization R M

end Exercise5_7

end HartshorneII5
