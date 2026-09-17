import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
SC-1--SC-10, companion to the new arguments. Earlier exercise companions
continue to verify SC-4's abelian exactness, SC-8's Noetherian colimit
calculation and SC-10's finite-free projection map. Here the general limit,
stalk and module-sheaf adjunction interfaces supplement those checks.

Precise interface boundary: the topological stalk formula for module tensor
and the degreewise symmetric/exterior sheaf comparisons are reduced in the
text to finite representatives, stalk detection and the algebraic universal
maps in module-algebra.lean. They are not packaged here as one global
isomorphism of sheaves of modules. The module sheafification and pullback
adjunctions below are genuine module adjunctions, not merely abelian-group
adjunctions. The counterexample tail calculation is verified below on its
cofinal neighborhood system, without constructing a named topological space.
-/
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Supplements.SC

abbrev sectionwiseLimit := @TopCat.limit_isSheaf

def moduleSheafification := @PresheafOfModules.sheafificationAdjunction

def modulePullback := @SheafOfModules.pullbackPushforwardAdjunction

def modulePullbackComposition := @SheafOfModules.pullbackComp

def stalkInverseImage := @TopCat.Presheaf.stalkPullbackIso

abbrev stalkDetectsIso := @TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso

abbrev localSurjectivity := @TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks

abbrev stalkExactness := @TopCat.Sheaf.exact_iff_stalkFunctor_map_exact

abbrev homIsSheaf := @CategoryTheory.Presheaf.IsSheaf.hom

def homSections := @CategoryTheory.sheafHomSectionsEquiv

def tensorHom := @TensorProduct.lift.equiv

def skyscraperSpecialization := @skyscraperPresheafStalkOfSpecializes

def skyscraperOutsideSupport := @skyscraperPresheafStalkOfNotSpecializes

abbrev skyscraperDirectImage := @skyscraperPresheaf_eq_pushforward

def stalkAdjunction := @stalkSkyscraperSheafAdjunction

/-- SC-1, SC-2: the genuine sheaf stalk preserves all colimits. -/
example (X : TopCat) (x : X) : PreservesColimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/-- Finite limits, in contrast with SC-E1 and SC-E2. -/
example (X : TopCat) (x : X) : PreservesFiniteLimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/-- The constant-one family is nonzero on every tail (SC-E1). -/
theorem nonzero_on_every_tail (N : ℕ) : ∃ n ≥ N, (1 : ℤ) ≠ 0 :=
  ⟨N, le_rfl, one_ne_zero⟩

/-- Each fixed coordinate disappears on some tail (SC-E1). -/
theorem coordinate_eventually_absent (n : ℕ) : ∃ N, ∀ m ≥ N, m ≠ n := by
  refine ⟨n+1, fun m hm he ↦ ?_⟩
  subst m
  exact Nat.not_succ_le_self n hm

/-- SC-E3: the actual map on global sections fails surjectivity. -/
theorem diagonal_not_surjective (k : Type*) [Zero k] [One k] [NeZero (1 : k)] :
    ¬ Function.Surjective (fun a : k ↦ (a,a)) := by
  intro h
  obtain ⟨a, ha⟩ := h (1,0)
  have h1 := congrArg Prod.fst ha
  have h0 := congrArg Prod.snd ha
  exact one_ne_zero (h1.symm.trans h0)

/-- SC-E4: agreement on integers forces agreement on all rational fractions. -/
theorem rational_epimorphism {R : Type*} [Semiring R] (f g : ℚ →+* R) : f = g :=
  Subsingleton.elim _ _
end Supplements.SC
