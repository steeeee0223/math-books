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
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

/-!
SC-1–SC-11, companion to the new arguments. Earlier exercise companions
continue to verify SC-4's abelian exactness, SC-9's Noetherian colimit
calculation and SC-11's finite-free projection map. Here the general limit,
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

/-- Finite limits, in contrast with SC-12 and SC-13. -/
example (X : TopCat) (x : X) : PreservesFiniteLimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/-- The constant-one family is nonzero on every tail (SC-12). -/
theorem nonzero_on_every_tail (N : ℕ) : ∃ n ≥ N, (1 : ℤ) ≠ 0 :=
  ⟨N, le_rfl, one_ne_zero⟩

/-- Each fixed coordinate disappears on some tail (SC-12). -/
theorem coordinate_eventually_absent (n : ℕ) : ∃ N, ∀ m ≥ N, m ≠ n := by
  refine ⟨n+1, fun m hm he ↦ ?_⟩
  subst m
  exact Nat.not_succ_le_self n hm

/-- SC-14: the actual map on global sections fails surjectivity. -/
theorem diagonal_not_surjective (k : Type*) [Zero k] [One k] [NeZero (1 : k)] :
    ¬ Function.Surjective (fun a : k ↦ (a,a)) := by
  intro h
  obtain ⟨a, ha⟩ := h (1,0)
  have h1 := congrArg Prod.fst ha
  have h0 := congrArg Prod.snd ha
  exact one_ne_zero (h1.symm.trans h0)

/-- SC-15: agreement on integers forces agreement on all rational fractions. -/
theorem rational_epimorphism {R : Type*} [Semiring R] (f g : ℚ →+* R) : f = g :=
  Subsingleton.elim _ _
end Supplements.SC

/- Editorial consolidation: SC now places each proof immediately after its
property. SC-1 absorbs II.1.10/12; SC-3 absorbs II.1.9; SC-4 absorbs II.1.2-7;
SC-5 absorbs II.1.15; SC-6 absorbs II.1.8/18; SC-9 absorbs II.1.11; SC-10
absorbs II.1.1. SC-7 and SC-11 split tensor-Hom from finite locally free
duality/projection (II.5.1). Existing declarations check the same maps.
The SC-14 diagonal example replaces the redundant circle example of II.1.3(b).
Global tensor/duality gluing remains a prose reduction to the checked local
maps and the sheaf isomorphism criterion; no new full formalization is claimed. -/

namespace Supplements.SC

/-- The obstruction in the Hom-stalk example: no nonzero denominator
can invert every prime. If p does not divide a, it divides no power of a. -/
theorem prime_outside_denominator (a : ℕ) (ha : 0 < a) :
    ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, ¬ p ∣ a ^ n := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (a + 1)
  refine ⟨p, hprime, fun n hn => ?_⟩
  have hpa : p ∣ a := hprime.dvd_of_dvd_pow hn
  exact Nat.not_succ_le_self a (hp.trans (Nat.le_of_dvd ha hpa))

/- SC-5 uses this arithmetic obstruction after identifying sections of the
Hom sheaf on D(a) with families in ℤ[1/a]. The generic-point stalk map
of Hom sheaves is not assembled here: the direct-sum stalk comparison,
the local-representative reduction, and this denominator obstruction are
the checked inputs; the sheaf-level counterexample remains a prose assembly.
The earlier AL-14 single-localization example alone did not justify that
stalk assertion, since the Hom sheaf itself need not be quasi-coherent. -/

end Supplements.SC
