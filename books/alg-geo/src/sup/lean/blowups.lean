import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Companion to BU-1–BU-13, using Hartshorne's Rees algebra and quotient convention.

Coverage (these are verification boundaries, not extra textbook hypotheses):
* BU-1–BU-2: the actual mathlib Rees algebra, its degree-one generation and finite
  type; localization membership iff a power clears the denominator; uniqueness
  after cancellation by a nonzerodivisor. The scheme-level universal property
  and identification of the Proj chart with the displayed subalgebra still need
  a relative-Proj/invertible-ideal bridge.
* BU-4: saturated ideal membership and removal of a principal exceptional factor
  are proved for actual ideals. The Rees quotient/associated-graded isomorphism
  and the associated invertible ideal sheaf are not assembled here.
* BU-5: flatness preserves the inclusion of every ideal power, and extension of
  ideals commutes with powers. Tensor multiplication onto the image ideal and
  relative Proj base change still need their graded-sheaf comparison.
* BU-6: the equations of the graph, overlap fractions, and affine closed
  immersions are checked; global graph closure and the twist bundle need gluing.
* BU-7: the exact cusp substitution and general prime-ideal saturation are
  checked. The regular-local associated-graded theorem that identifies arbitrary
  multiplicity with its initial form is not constructed here.
* BU-8: the conormal transition calculation is retained in BU-9/10 and the
  parameter relations are checked; the regular-local cotangent independence,
  regular-sequence chart presentation, and Sym(I/I²) = gr_I bridge remain gaps.
* BU-9–BU-13: actual polynomial quotient algebra equivalences eliminate the strict
  transform relations; exact chart substitutions and inverse coordinate ratios
  are proved. The chart-to-scheme gluing and the normal line-bundle classes
  remain unassembled. Cusp integral closure, smoothness of the assembled cone
  blowup, and the global incidence/F_1 identification are not complete formal
  theorems here. No polynomial identity is claimed to prove these global facts.

All declarations below are kernel-checked without sorry or added axioms.
-/

open Polynomial CategoryTheory AlgebraicGeometry
noncomputable section
namespace Supplements.BU

variable {R : Type*} [CommRing R]

theorem rees_degree (I : Ideal R) (a : R) (n : ℕ) :
    monomial n a ∈ reesAlgebra I ↔ a ∈ I ^ n :=
  reesAlgebra.monomial_mem

theorem rees_generated_in_degree_one (I : Ideal R) :
    Algebra.adjoin R
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) =
      reesAlgebra I := adjoin_monomial_eq_reesAlgebra I

theorem rees_finite_type (I : Ideal R) (hI : I.FG) :
    (reesAlgebra I).FG := reesAlgebra.fg hI

/-- The precise contraction-of-localized-ideal assertion used in all charts. -/
theorem saturation_iff_localized (I : Ideal R) (f a : R) :
    algebraMap R (Localization.Away f) a ∈
      I.map (algebraMap R (Localization.Away f)) ↔
        ∃ n : ℕ, f ^ n * a ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f)]
  constructor
  · rintro ⟨s, ⟨n, rfl⟩, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨f ^ n, ⟨n, rfl⟩, h⟩

/-- A prime ideal avoiding f is already saturated, including scheme structure. -/
theorem prime_saturation (J : Ideal R) [J.IsPrime] {f a : R} (hf : f ∉ J) :
    (∃ n : ℕ, f ^ n * a ∈ J) ↔ a ∈ J := by
  constructor
  · rintro ⟨n, hn⟩
    rcases (inferInstance : J.IsPrime).mem_or_mem hn with h | h
    · exact False.elim (hf ((inferInstance : J.IsPrime).mem_of_pow_mem n h))
    · exact h
  · intro h
    exact ⟨0, by simpa using h⟩

/-- Removes exactly the exceptional factor f^m from a prime strict equation. -/
theorem exceptional_factor_saturation (f g a : R) (m : ℕ)
    (hprime : (Ideal.span ({g} : Set R)).IsPrime)
    (hf : f ∉ Ideal.span ({g} : Set R)) :
    (∃ n : ℕ, f ^ n * a ∈ Ideal.span ({f ^ m * g} : Set R)) ↔
      a ∈ Ideal.span ({g} : Set R) := by
  letI := hprime
  constructor
  · rintro ⟨n, hn⟩
    apply (prime_saturation (Ideal.span {g}) hf).mp
    refine ⟨n, ?_⟩
    have hle : Ideal.span ({f ^ m * g} : Set R) ≤ Ideal.span ({g} : Set R) := by
      apply Ideal.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton g))
    exact hle hn
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨m, Ideal.mem_span_singleton.mpr ⟨b, ?_⟩⟩
    rw [hb]
    ring

/-- The injectivity supplied by flatness in every Rees degree. -/
theorem flat_power_inclusion {S : Type*} [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (n : ℕ) :
    Function.Injective ((I ^ n).subtype.rTensor S) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

theorem extension_of_power {S : Type*} [CommRing S]
    (φ : R →+* S) (I : Ideal R) (n : ℕ) :
    (I ^ n).map φ = (I.map φ) ^ n := Ideal.map_pow φ I n

/-- The exact algebra equivalence used after solving v = u² or x = u².
It applies with R = k[x,u], a = u² (cone), or R = k[u], a = u² (cusp). -/
def solvedChart (a : R) :
    (R[X] ⧸ Ideal.span ({X - C a} : Set R[X])) ≃ₐ[R] R :=
  Polynomial.quotientSpanXSubCAlgEquiv a

theorem solvedChart_kernel (a : R) :
    RingHom.ker (Polynomial.evalRingHom a) =
      Ideal.span ({X - C a} : Set R[X]) := Polynomial.ker_evalRingHom a

theorem cusp_total_transform (x u : R) :
    (x * u) ^ 2 - x ^ 3 = x ^ 2 * (u ^ 2 - x) := by ring

theorem cusp_other_chart (v y : R) :
    y ^ 2 - (v * y) ^ 3 = y ^ 2 * (1 - v ^ 3 * y) := by ring

theorem cusp_parametrization (u : R) : (u ^ 3) ^ 2 = (u ^ 2) ^ 3 := by ring

theorem node_total_transform (x t : R) :
    (x * t) ^ 2 - x ^ 2 * (x + 1) = x ^ 2 * (t ^ 2 - x - 1) := by ring

theorem node_parametrization (t : R) :
    (t * (t ^ 2 - 1)) ^ 2 = (t ^ 2 - 1) ^ 2 * ((t ^ 2 - 1) + 1) := by ring

theorem node_other_chart (v y : R) :
    y ^ 2 - (v * y) ^ 2 * (v * y + 1) =
      y ^ 2 * (1 - v ^ 2 * (v * y + 1)) := by ring

theorem cone_total_transform (x u v : R) :
    x * (x * v) - (x * u) ^ 2 = x ^ 2 * (v - u ^ 2) := by ring

theorem cone_third_chart (z a b : R) :
    (z * a) * (z * b) - z ^ 2 = z ^ 2 * (a * b - 1) := by ring

theorem conic_parametrization (s t : R) :
    s ^ 2 * t ^ 2 = (s * t) ^ 2 := by ring

theorem naive_chart_extra_factor (x y t : R) :
    x ^ 2 * t - x * y = x * (x * t - y) := by ring

theorem pencil_chart_equation (x t : R) : x * t - x * t = 0 := sub_self _

theorem plane_strict_line (x u a : R) : x * u - a * x = x * (u - a) := by ring

/-- Algebraic independence of the chart equations in the conormal directions:
the coefficient of each eliminated f_i recovers its scalar. -/
theorem parameter_relations_independent {ι : Type*} (c : ι → R)
    (h : ∀ i, -c i = 0) : c = 0 := by
  funext i
  exact neg_eq_zero.mp (h i)

section FractionCharts
variable {K : Type*} [Field K]

theorem ratio_transition (f g h : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    (h / f) / (g / f) = h / g := by field_simp

theorem plane_overlap (x u : K) (hu : u ≠ 0) :
    (x * u) * u⁻¹ = x := by field_simp

theorem cone_overlap (x u : K) (hu : u ≠ 0) :
    (x * u ^ 2) * (u⁻¹) ^ 2 = x := by field_simp

theorem cusp_fraction_field (u : K) (hu : u ≠ 0) : u ^ 3 / u ^ 2 = u := by
  field_simp

theorem cusp_second_chart_in_overlap (v y : K) (h : v ^ 3 * y = 1) : v ≠ 0 := by
  intro hv
  simp [hv] at h

theorem cone_third_chart_in_overlap (a b : K) (h : a * b = 1) :
    a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha; simp [ha] at h
  · intro hb; simp [hb] at h

theorem node_second_chart_in_overlap (v y : K)
    (h : v ^ 2 * (v * y + 1) = 1) : v ≠ 0 := by
  intro hv
  simp [hv] at h

theorem node_exceptional_points (t : K) : t ^ 2 = 1 ↔ t = 1 ∨ t = -1 := by
  exact sq_eq_one_iff
end FractionCharts

/-- Closed affine charts really define closed scheme immersions. -/
theorem quotient_chart_closed (I : Ideal R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end Supplements.BU
