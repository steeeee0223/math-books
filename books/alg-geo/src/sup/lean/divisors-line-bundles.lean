import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
DV verification companion.

DV-1–DV-4: the actual transition convention, coordinate agreement, tensor
transitions, change of rational section, multiplication frames in an arbitrary
total quotient ring, and the affine Cartier injection/quotient and flatness
interfaces are checked below. The use of units rather than nonzero elements in
the meromorphic ring is essential on a nonintegral scheme.

DV-6–DV-9: a Noetherian total quotient ring is semilocal, and every invertible
module over it is free of rank one. This is the substantive algebraic step in
the second surjectivity proof. The comparison of associated-prime conventions
is in module-algebra-2.lean.

DV-10: the actual multiplication/quotient maps in
0 -> A/(b) -> A/(ab) -> A/(a) -> 0, injectivity when a is regular,
surjectivity, exactness, and the resulting length equality are checked.
Mathlib length takes values in extended natural numbers; finiteness in the
one-dimensional Noetherian local situation is an additional reader assertion.
DV-11–DV-13: finite free length, field extension preserving dimension, and
residue-field tower degrees are exposed without a cohomology base-change claim.

Precise remaining interfaces: this file does not construct the sheaf of Cartier
divisors, globalize its meromorphic-frame equivalence, prove extension across
opens containing Ass, encode homogeneous prime avoidance and DV-8's affine
neighborhood, or assemble curve degrees from Artinian local factors. It does
not encode the P1/P1xP1 cover with its Laurent coefficient section calculation,
the cone coordinate ring and its class group, or the inseparable residue-algebra
presentation. Those are not claimed as fully formalized results. The textbook
gives their geometric reductions, and expressly leaves the pure algebra
terminals to the reader. No unrelated affine statement is offered as a proof
of these missing global assertions.

Gap map by textbook identifier:
* DV-1–DV-2: local frame algebra checked; sheaf gluing/global rational sections not encoded.
* DV-3: the complete affine exact sequence checked; its sheafification is not encoded.
* DV-4: flat tensor preservation checked; dominant field pullback and bundle comparison not encoded.
* DV-5: the quoted DVR and height-one intersection arguments are not encoded here.
* DV-6/6.1: affine meromorphic gluing and extension across Ass are not encoded.
* DV-8: homogeneous prime avoidance and the Proj affine chart construction not encoded.
* DV-9: semilocal meromorphic frames checked; spreading and sheaf extension not encoded.
* DV-10: product-length formula checked; finite length, fraction independence, DVR valuation not encoded.
* DV-11/10.1: the finite free length and tower rules checked; Artinian factor decomposition,
  torsion-free-finite-over-DVR freeness, and the global degree sum not encoded.
* DV-13: the exact tensor finrank identity checked; the scheme fiber product not encoded.
* DV-14–DV-16: the Laurent section calculation, cone presentation and class group,
  and the product-of-lines Picard calculation are reader reductions not encoded here.
-/

noncomputable section
namespace Supplements.DV
open scoped TensorProduct

section Transition
variable {Q ι : Type*} [CommRing Q]

/-- DV-1: e_i = (f_j/f_i)e_j. -/
def transition (f : ι → Qˣ) (i j : ι) : Qˣ := f j / f i

theorem transition_cocycle (f : ι → Qˣ) (i j l : ι) :
    transition f i j * transition f j l = transition f i l := by
  exact div_mul_div_cancel' (f j) (f i) (f l)

theorem inverse_frame (f : ι → Qˣ) (i j : ι) :
    (f i)⁻¹ = transition f i j * (f j)⁻¹ := by
  simp [transition, div_eq_mul_inv, mul_assoc]

/-- Equality of a rational section in two frames gives the stated coordinate rule. -/
theorem section_coordinates (a f g : Qˣ) :
    a * f⁻¹ = (a * (g / f)) * g⁻¹ := by
  simp [div_eq_mul_inv, mul_assoc]

theorem tensor_transition (f g : ι → Qˣ) (i j : ι) :
    transition (fun k ↦ f k * g k) i j = transition f i j * transition g i j := by
  simp [transition, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Multiplying every local equation by the same rational unit changes no transition. -/
theorem principal_change (f : ι → Qˣ) (q : Qˣ) (i j : ι) :
    transition (fun k ↦ q * f k) i j = transition f i j := by
  exact mul_div_mul_left_eq_div (f j) (f i) q

end Transition

section AffineFrames
variable (A Q : Type*) [CommRing A] [CommRing Q] [Algebra A Q]

/-- The fractional-ideal frame on an equation chart, a ↦ f⁻¹a. -/
def equationFrame (f : Qˣ) : A →ₗ[A] Q :=
  (LinearMap.mul A Q (↑(f⁻¹))).comp (Algebra.linearMap A Q)

theorem equationFrame_injective [IsFractionRing A Q] (f : Qˣ) :
    Function.Injective (equationFrame A Q f) := by
  intro a b h
  apply IsFractionRing.injective A Q
  have h' := congrArg (fun x : Q ↦ (↑f : Q) * x) h
  simpa [equationFrame, mul_assoc] using h'

/-- Transition coefficients really take the j-frame to the i-frame. -/
theorem equationFrame_transition (f g : Qˣ) (a : A) :
    (↑(g / f) : Q) * equationFrame A Q g a = equationFrame A Q f a := by
  change (↑(g / f) : Q) * ((↑(g⁻¹) : Q) * algebraMap A Q a) =
    (↑(f⁻¹) : Q) * algebraMap A Q a
  rw [← mul_assoc]
  congr 1
  exact congrArg Units.val (show (g / f) * g⁻¹ = f⁻¹ by
    simpa only [one_div] using div_mul_div_cancel' g f (1 : Qˣ))

/-- DV-2's map h ↦ hs sends the inverse coefficient frame to the chosen frame. -/
theorem section_frame_inverse (s : Qˣ) :
    (↑(s⁻¹) : Q) * (↑s : Q) = 1 := by simp

end AffineFrames

section Effective
variable {A : Type*} [CommRing A]

/-- The affine quotient sequence has the actual Cartier equation as its first map. -/
theorem effective_exact (a : A) :
    Function.Exact (LinearMap.mulLeft A a)
      ((Ideal.span ({a} : Set A) : Submodule A A).mkQ) := by
  intro b
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem effective_injective {a : A} (ha : IsSMulRegular A a) :
    Function.Injective (LinearMap.mulLeft A a) := ha

theorem effective_quotient_surjective (a : A) :
    Function.Surjective ((Ideal.span ({a} : Set A) : Submodule A A).mkQ) :=
  Submodule.mkQ_surjective _

/-- Multiplying a Cartier equation by a unit does not change its ideal. -/
theorem effective_unit_ideal (a : A) (u : Aˣ) :
    Ideal.span ({(↑u : A) * a} : Set A) = Ideal.span {a} :=
  Ideal.span_singleton_mul_left_unit u.isUnit a

/-- The pullback failure at the origin does not rely on a domain convention. -/
theorem zero_not_regular [Nontrivial A] : ¬ IsSMulRegular A (0 : A) := by
  intro h
  have : (0 : A) = 1 := h (by simp)
  exact zero_ne_one this

end Effective

section Multiplicity
variable {A : Type*} [CommRing A]

abbrev principalSubmodule (a : A) : Submodule A A := Ideal.span {a}

/-- The multiplication map in DV-10, defined on the actual quotient modules. -/
def productInclusion (a b : A) :
    (A ⧸ principalSubmodule b) →ₗ[A] A ⧸ principalSubmodule (a * b) :=
  (principalSubmodule b).mapQ (principalSubmodule (a * b)) (LinearMap.mulLeft A a) <| by
    intro x hx
    change a * x ∈ Ideal.span {a * b}
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    exact Ideal.mem_span_singleton.mpr ⟨y, by rw [hy]; ring⟩

def productProjection (a b : A) :
    (A ⧸ principalSubmodule (a * b)) →ₗ[A] A ⧸ principalSubmodule a :=
  (principalSubmodule (a * b)).mapQ (principalSubmodule a) (LinearMap.id) <| by
    intro x hx
    change x ∈ Ideal.span {a}
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    exact Ideal.mem_span_singleton.mpr ⟨b * y, by rw [hy]; ring⟩

theorem productInclusion_injective (a b : A) (ha : Function.Injective (a * ·)) :
    Function.Injective (productInclusion a b) := by
  intro x y h
  obtain ⟨x, rfl⟩ := (principalSubmodule b).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (principalSubmodule b).mkQ_surjective y
  change (Submodule.Quotient.mk (a * x) : A ⧸ principalSubmodule (a * b)) =
    Submodule.Quotient.mk (a * y) at h
  apply (Submodule.Quotient.eq (principalSubmodule b)).mpr
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
    ((Submodule.Quotient.eq (principalSubmodule (a * b))).mp h)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  apply ha
  linear_combination hc

theorem productProjection_surjective (a b : A) :
    Function.Surjective (productProjection a b) := by
  intro x
  obtain ⟨x, rfl⟩ := (principalSubmodule a).mkQ_surjective x
  exact ⟨(principalSubmodule (a * b)).mkQ x, rfl⟩

theorem product_exact (a b : A) :
    Function.Exact (productInclusion a b) (productProjection a b) := by
  intro x
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := (principalSubmodule (a * b)).mkQ_surjective x
    change (Submodule.Quotient.mk x : A ⧸ principalSubmodule a) = 0 at hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
      ((Submodule.Quotient.mk_eq_zero (principalSubmodule a)).mp hx)
    refine ⟨(principalSubmodule b).mkQ y, ?_⟩
    change (Submodule.Quotient.mk (a * y) : A ⧸ principalSubmodule (a * b)) =
      Submodule.Quotient.mk x
    rw [hy]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨y, rfl⟩ := (principalSubmodule b).mkQ_surjective y
    change (Submodule.Quotient.mk (a * y) : A ⧸ principalSubmodule a) = 0
    exact (Submodule.Quotient.mk_eq_zero (principalSubmodule a)).mpr
      (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩)

/-- DV-10's length additivity for a product, with no DVR hypothesis substituted. -/
theorem product_length (a b : A) (ha : Function.Injective (a * ·)) :
    Module.length A (A ⧸ principalSubmodule (a * b)) =
      Module.length A (A ⧸ principalSubmodule b) +
        Module.length A (A ⧸ principalSubmodule a) :=
  Module.length_eq_add_of_exact (productInclusion a b) (productProjection a b)
    (productInclusion_injective a b ha) (productProjection_surjective a b) (product_exact a b)

end Multiplicity

abbrev flat_preserves_regular := @IsSMulRegular.lTensor

/-- DV-9: the total quotient ring of a Noetherian ring has finitely many maximal ideals. -/
theorem total_quotient_semilocal (A Q : Type*) [CommRing A] [IsNoetherianRing A]
    [CommRing Q] [Algebra A Q] [IsFractionRing A Q] :
    Finite (MaximalSpectrum Q) := by
  letI : IsNoetherianRing Q := IsLocalization.isNoetherianRing (nonZeroDivisors A) Q inferInstance
  letI : IsFractionRing Q Q := IsFractionRing.idem A Q
  exact inferInstance

/-- DV-9's meromorphic frame, valid with embedded primes. -/
theorem meromorphic_frame (A Q P : Type*) [CommRing A] [IsNoetherianRing A]
    [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    [AddCommGroup P] [Module Q P] [Module.Invertible Q P] :
    Nonempty (P ≃ₗ[Q] Q) := by
  letI := total_quotient_semilocal A Q
  exact Module.Invertible.free_iff_linearEquiv.mp inferInstance

abbrev length_additive := @Module.length_eq_add_of_exact

abbrev finite_free_length := @Module.length_of_free_of_finite

/-- DV-13: precisely the dimension invariant of the finite divisor algebra. -/
theorem divisor_algebra_base_change (k K B : Type*) [Field k] [Field K]
    [Algebra k K] [AddCommGroup B] [Module k B] :
    Module.finrank K (K ⊗[k] B) = Module.finrank k B :=
  Module.finrank_baseChange

/-- DV-12: the residue field weights obey the required tower law. -/
theorem residue_degree_tower (k L E : Type*) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E] :
    Module.finrank k L * Module.finrank L E = Module.finrank k E :=
  Module.finrank_mul_finrank k L E

end Supplements.DV
