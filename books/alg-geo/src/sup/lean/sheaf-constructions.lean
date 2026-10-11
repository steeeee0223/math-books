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
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!

The proofs now follow the order and grouping of the final SC statements.
SC-1 proves subsheaf/quotient stalks, then kernel/image/cokernel stalks,
morphism criteria, and exact sequences. Its section-surjectivity obstruction
uses the quotient by functions vanishing at two projective-line points,
without using the later direct-image construction. diagonal_not_surjective
checks its terminal obstruction; the quotient's glued section and the
projective-line global-sections calculation are not assembled here.
SC-2 treats colimits before limits, with the contravariant/covariant Hom
universal properties below. The Noetherian result assumes a filtered diagram;
finite-stage gluing is still a prose assembly of the inputs in
II.1.1–1.12's companion. SC-3 proves direct-image left exactness sectionwise
before constructing the inverse-image adjunction, so no later part is used.
SC-4–SC-15 retain the earlier reductions, grouped under the corresponding
statement items. SC-15's injection and its failure after scalar extension
are checked explicitly below. The interface boundaries remain as recorded.
SC-1–SC-10, companion to the reorganized arguments. Earlier exercise companions
continue to verify SC-1's abelian exactness, SC-2's Noetherian colimit
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

/-- SC-2: a map out of a colimit is a compatible cocone (contravariant Hom). -/
def colimitHomUniversalProperty := @CategoryTheory.Limits.colimit.homIso

/-- SC-2: a map into a limit is a compatible cone (covariant Hom). -/
def limitHomUniversalProperty := @CategoryTheory.Limits.limit.homIso

def moduleSheafification := @PresheafOfModules.sheafificationAdjunction

def modulePullback := @SheafOfModules.pullbackPushforwardAdjunction

def modulePullbackComposition := @SheafOfModules.pullbackComp

def stalkInverseImage := @TopCat.Presheaf.stalkPullbackIso

/-- SC-3: the canonical direct-image stalk comparison, with its germ formula. -/
def stalkDirectImage := @TopCat.Presheaf.stalkPushforward

abbrev stalkDirectImageOnGerms := @TopCat.Presheaf.stalkPushforward_germ

/-- SC-3's sufficient hypothesis: inducing maps include open embeddings. -/
abbrev stalkDirectImageIso :=
  @TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing

abbrev stalkDetectsIso := @TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso

abbrev localSurjectivity := @TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks

abbrev stalkExactness := @TopCat.Sheaf.exact_iff_stalkFunctor_map_exact

/-- SC-3: a section in the kernel lifts uniquely in a left exact sequence.
The library theorem supplies the lift; monomorphy gives its uniqueness. -/
abbrev sectionsLeftExact := @TopCat.Sheaf.sections_exact_of_left_exact

abbrev homIsSheaf := @CategoryTheory.Presheaf.IsSheaf.hom

def homSections := @CategoryTheory.sheafHomSectionsEquiv

def tensorHom := @TensorProduct.lift.equiv

def skyscraperSpecialization := @skyscraperPresheafStalkOfSpecializes

def skyscraperOutsideSupport := @skyscraperPresheafStalkOfNotSpecializes

abbrev skyscraperDirectImage := @skyscraperPresheaf_eq_pushforward

def stalkAdjunction := @stalkSkyscraperSheafAdjunction

/-- SC-2: the genuine sheaf stalk preserves all colimits, including direct sums. -/
example (X : TopCat) (x : X) : PreservesColimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/-- Finite limits, in contrast with SC-11 and SC-12. -/
example (X : TopCat) (x : X) : PreservesFiniteLimits
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  infer_instance

/-- The constant-one family is nonzero on every tail (SC-11). -/
theorem nonzero_on_every_tail (N : ℕ) : ∃ n ≥ N, (1 : ℤ) ≠ 0 :=
  ⟨N, le_rfl, one_ne_zero⟩

/-- Each fixed coordinate disappears on some tail (SC-11). -/
theorem coordinate_eventually_absent (n : ℕ) : ∃ N, ∀ m ≥ N, m ≠ n := by
  refine ⟨n+1, fun m hm he ↦ ?_⟩
  subst m
  exact Nat.not_succ_le_self n hm

/-- SC-13: the actual map on global sections fails surjectivity. -/
theorem diagonal_not_surjective (k : Type*) [Zero k] [One k] [NeZero (1 : k)] :
    ¬ Function.Surjective (fun a : k ↦ (a,a)) := by
  intro h
  obtain ⟨a, ha⟩ := h (1,0)
  have h1 := congrArg Prod.fst ha
  have h0 := congrArg Prod.snd ha
  exact one_ne_zero (h1.symm.trans h0)

/-- SC-3: the terminal algebraic obstruction in the two-point pushforward example. -/
theorem direct_image_projection_not_injective :
    ¬ Function.Injective (Prod.fst : ℤ × ℤ → ℤ) := by
  intro h
  have heq := h (a₁ := (0, 0)) (a₂ := (0, 1)) rfl
  have h01 : (0 : ℤ) = 1 := congrArg Prod.snd heq
  exact zero_ne_one h01

/-- SC-8: the local-constant representative reduction for evaluation on a stalk. -/
theorem locally_constant_representative {X A : Type*} [TopologicalSpace X]
    (f : LocallyConstant X A) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x := by
  exact ⟨{y | f y = f x}, f.isLocallyConstant.isOpen_fiber (f x), rfl,
    fun _ hy => hy⟩

/-- SC-9: the locally constant functions on the irreducible closure are constant. -/
abbrev constantOnPreconnected := @IsLocallyConstant.eq_const

/-- SC-6's terminal algebraic tensor functor commutes with colimits.
The varying-ring neighborhood system still needs the sheaf-level bridge described below. -/
example (R : Type) [CommRing R] (M : ModuleCat R) :
    PreservesColimits (MonoidalCategory.tensorLeft M) := by
  infer_instance

/-- SC-14: agreement on integers forces agreement on all rational fractions. -/
theorem rational_epimorphism {R : Type*} [Semiring R] (f g : ℚ →+* R) : f = g :=
  Subsingleton.elim _ _
/-- SC-14: the underlying integer-to-rational map misses one half. -/
theorem integer_cast_not_surjective :
    ¬ Function.Surjective (fun z : ℤ => (z : ℚ)) := by
  intro h
  obtain ⟨z, hz⟩ := h (1 / 2)
  change (z : ℚ) = 1 / 2 at hz
  have hz2 : (z : ℚ) * 2 = 1 := by rw [hz]; norm_num
  have h2 : z * 2 = 1 := by exact_mod_cast hz2
  omega

/-- SC-15: the morphism before scalar extension is injective. -/
theorem multiplication_two_injective : Function.Injective (fun x : ℤ => 2 * x) := by
  intro a b h
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h

/-- SC-15: multiplication by two after scalar extension is zero and not injective. -/
theorem multiplication_two_mod_two_failure :
    (∀ x : ZMod 2, (2 : ZMod 2) * x = 0) ∧
    ¬ Function.Injective (fun x : ZMod 2 => (2 : ZMod 2) * x) := by
  have hzero (x : ZMod 2) : (2 : ZMod 2) * x = 0 := by
    rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  refine ⟨hzero, ?_⟩
  intro h
  have h01 : (0 : ZMod 2) = 1 := h (by simp [hzero])
  exact zero_ne_one h01
end Supplements.SC

/- Editorial consolidation: SC now places each proof immediately after its
property. SC-2 absorbs II.1.10/12; SC-4 absorbs II.1.9; SC-1 absorbs II.1.2-7;
SC-5 absorbs II.1.15; SC-3 absorbs II.1.8/18; SC-2 absorbs II.1.11; SC-8
absorbs II.1.1. SC-6 and SC-10 split tensor-Hom from finite locally free
duality/projection (II.5.1). Existing declarations check the same maps.
The SC-13 diagonal example replaces the redundant circle example of II.1.3(b).
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

/- Verification boundaries after the refactor:
SC-3: stalkDirectImageOnGerms checks the restriction/germ map and
stalkDirectImageIso checks the cofinal-neighborhood comparison (for the
stronger inducing-map hypothesis). The discrete two-point sheaf is not
constructed here; projection_not_injective checks its terminal obstruction.
SC-5: finite-presentation Hom comparison is reduced to a kernel between
finite powers. Stalk exactness and preservation of finite limits check those
operations; the identification of the local presentation's Hom sheaf with
that kernel is not assembled as a single module-sheaf theorem.
SC-6/7: tensorHom and colimit preservation check the algebraic universal
property. The varying rings of sections, sheafification, and tensor stalk
formula are not combined into a module-sheaf isomorphism here. Symmetric and
exterior powers use the checked universal maps in module-algebra.lean, with
the same remaining sheaf-level bridge. SC-8: local evaluation representatives
are checked above; the isomorphism from the locally constant function model
to the categorical constant sheaf is not packaged here. SC-9: skyscraper
stalks are checked in full; the constant-sheaf-on-closure identification uses
constantOnPreconnected but is not packaged as a sheaf isomorphism.
These are interface gaps, not claims of complete formalization. -/

end Supplements.SC
