/- Relocated from sec-2-5/lean/exe.lean; mathematical declarations unchanged. -/
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.LinearAlgebra.TensorProduct.Pi
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
proofs in the supplement applications indexed by the original exercise numbers.  These declarations check the algebraic or categorical
reductions of the prose; they should not be read as formalizations of every
full sheaf statement. For Exercise 5.1(d), tensorFiniteFree checks the
finite-free calculation on the target cover. projectionFormulaAffine is an
additional affine comparison, not a substitute for that calculation.
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

/-- Exercise 5.1(d), the algebraic comparison when both the chosen target open
and its inverse image are affine and the sheaves involved come from modules. -/
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


/- The revised 5.1(d) uses finite products on every open of a trivializing
cover, without assuming the source or target affine.  This is the actual
finite-free computation; projectionFormulaAffine above is only an optional
comparison, not a verification of the general projection formula. -/
noncomputable def tensorFiniteFree (R N : Type*) [CommRing R]
    [AddCommGroup N] [Module R N] (n : ℕ) :
    N ⊗[R] (Fin n → R) ≃ₗ[R] (Fin n → N) :=
  TensorProduct.piScalarRight R R N (Fin n)

/-- The comparison sends a pure tensor to its coordinatewise scalar products. -/
theorem tensorFiniteFree_pure (R N : Type*) [CommRing R]
    [AddCommGroup N] [Module R N] (n : ℕ) (x : N) (a : Fin n → R) :
    tensorFiniteFree R N n (x ⊗ₜ[R] a) = fun i => a i • x := by
  exact TensorProduct.piScalarRightHom_tmul R R N (Fin n) x a

/-- The gluing criterion used in 5.1: local inverses on a cover give an inverse. -/
theorem iso_on_cover {C A : Type*} [Category C] [Category A]
    {J : GrothendieckTopology C} {ι : Type*} {U : ι → C}
    (hU : J.CoversTop U) {F G : Sheaf J A} (g : F ⟶ G) :
    IsIso g ↔ ∀ i, IsIso ((J.overPullback A (U i)).map g) :=
  Sheaf.isIso_iff_of_coversTop hU g

/- Verification boundaries, by revised exercise:
5.1(a,b): the evaluation and dual-tensor maps are checked for finite free
modules; iso_on_cover checks the sheaf gluing criterion. The identifications
of module-sheaf restriction, internal Hom and sheaf tensor with those local
maps are not yet assembled as a theorem of ringed-space modules.
5.1(c): tensorHomAdjunction verifies currying; its naturality with restriction
and passage through sheafification are not assembled here.
5.1(d): tensorFiniteFree and tensorFiniteFree_pure check the local map actually
used in the prose; restriction of pushforward, pullback of a finite free sheaf,
and their compatibility with this comparison still require interface lemmas.
5.2: the affine quasi-coherence criterion is checked. The two-open DVR-space
classification and its equivalence with triples are not formalized here.
5.3: tildeGammaHomEquiv checks the complete adjunction.
5.4: mathlib defines quasi-coherence by local free presentations. The affine
comparison is supplied above, and finitePresentation_of_noetherian_finite
checks the finite-presentation algebra. The comparison with Hartshorne's
finite-module definition of coherence at the sheaf level remains.
5.5(b): the complete closed-immersion claim is checked. For (c), finite
restriction of scalars is checked; the pushforward/tilde identification is not
assembled here. The Laurent-polynomial non-finiteness example in (a) remains.
5.7: openness of the free locus and the tensor-inverse implication are checked.
finitePresentation_of_noetherian_finite supplies the finite-presentation
hypothesis and free_stalk_spreads checks the distinguished-neighborhood
reduction with its rank. The sheaf/stalk bridge is not assembled here. The existing final theorem only
states local freeness; the following theorem checks rank one over a local ring.
-/
theorem tensor_inverse_over_local_ring (R M N : Type*) [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : N ⊗[R] M ≃ₗ[R] R) :
    Nonempty (M ≃ₗ[R] R) := by
  letI : Module.Invertible R M := Module.Invertible.right e
  exact (Module.Invertible.free_iff_linearEquiv (R := R) (M := M)).mp inferInstance


/-- The noetherian finite-module to finite-presentation bridge in 5.4 and 5.7. -/
theorem finitePresentation_of_noetherian_finite (R M : Type*) [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.FinitePresentation R M :=
  Module.finitePresentation_of_finite R M

/-- Exercise 5.7(a): a free stalk spreads to a distinguished neighborhood
with the same rank. This is stronger than mere openness of the free locus. -/
theorem free_stalk_spreads (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (p : PrimeSpectrum R)
    [Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M)] :
    ∃ a, a ∉ p.asIdeal ∧
      Module.Free (Localization.Away a) (LocalizedModule.Away a M) ∧
      Module.finrank (Localization.Away a) (LocalizedModule.Away a M) =
        Module.finrank (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) := by
  exact Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal)

end HartshorneII5
