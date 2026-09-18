import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring

/-!
PJ2 companion, using degree-preserving maps and quotient projectivization.

PJ2-1–PJ2-2: symmetric-algebra extension, factoring through the relations, and
uniqueness of compatible quotient isomorphisms are checked. Homogeneous charts
and their intersections use the actual Proj API. The equivalence between sheaf
quotient data and relative-Proj morphisms has not been constructed in Lean.
PJ2-4: the scheme pullback universal property is proved with the exact pair of
morphisms and compatibility equation; tensor associativity and localization maps
are available below. The graded direct-limit/base-change isomorphism and the
tautological sheaf identification remain interface gaps.
PJ2-5: actual homogeneous fraction representatives and exact localization are
recorded; graded module sheafification and its pullback comparison are not
assembled here, so the full theorem is not claimed verified.
PJ2-6–PJ2-7: quotient uniqueness, rescaling, and ratio transition are checked.
The conormal sheaf identification K tensor L^-1 and the projective-bundle
twisting isomorphism still need their sheaf/module gluing bridges.
PJ2-8: the generic fiber relation and special fiber reduction are checked as
ring equations; the symmetric-algebra presentation and gluing remain gaps.
PJ2-9: common divisible exponent and actual homogeneous chart APIs are checked;
degree-one generation of a sufficiently divisible Veronese and the graded
module comparison remain unformalized.
PJ2-10: this file constructs the ACTUAL quadric-cone quotient ring, its vertex
augmentation, and the two-generator odd-module presentation. It proves that the
vertex ideal is proper and that the presentation has a semilinear quotient k²,
so cannot be cyclic. The identification of this presentation with the localized
odd graded module, the complete polynomial presentation kernel and localization
of the noncyclicity assertion at the vertex still need proof. The proper vertex
ideal verifies the multiplication obstruction once its image is identified with
that ideal; it does not substitute for that bridge.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.PJ2

def affineChart := @Proj.basicOpenIsoSpec
abbrev chartOverlap := @Proj.basicOpen_mul
abbrev chartCover := @Proj.iSup_basicOpen_eq_top
abbrev fractionRepresentatives := @HomogeneousLocalization.Away.mk_surjective
abbrev fractionComposition := @HomogeneousLocalization.map_comp
def symmetricExtension := @SymmetricAlgebra.lift
def tensorAssociativity := @TensorProduct.assoc

/-- The exact base-change reduction on morphisms into the scheme fiber product. -/
def pullbackData (X Y Y' T : Scheme) (p : X ⟶ Y) (g : Y' ⟶ Y) :
    (T ⟶ pullback p g) ≃
      {q : (T ⟶ X) × (T ⟶ Y') // q.1 ≫ p = q.2 ≫ g} where
  toFun h := ⟨(h ≫ pullback.fst p g, h ≫ pullback.snd p g), by
    simp only [Category.assoc]
    rw [pullback.condition]⟩
  invFun q := pullback.lift q.1.1 q.1.2 q.2
  left_inv h := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _

section Algebra
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The relation condition in PJ2-2 is precisely existence of a quotient map. -/
theorem factor_through_relations (J : Ideal R) (φ : R →+* S) :
    (∃ ψ : R ⧸ J →+* S, ψ.comp (Ideal.Quotient.mk J) = φ) ↔
      ∀ a ∈ J, φ a = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ a ha
    rw [← hψ]
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro h
    exact ⟨Ideal.Quotient.lift J φ h, rfl⟩

theorem factor_unique (J : Ideal R) (ψ χ : R ⧸ J →+* S)
    (h : ψ.comp (Ideal.Quotient.mk J) = χ.comp (Ideal.Quotient.mk J)) : ψ = χ := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h a

theorem quotient_isomorphism_unique {M N P : Type*} (q : M → N)
    (hq : Function.Surjective q) (a b : N → P) (h : a ∘ q = b ∘ q) : a = b := by
  funext x
  obtain ⟨y, rfl⟩ := hq x
  exact congrFun h y

theorem relation_nonexample [Nontrivial R] :
    (1 : R) * 0 ≠ (1 : R) ^ 2 := by simp

theorem rescaling_preserves_relation (a b c u : R) :
    (u * a) * (u * c) - (u * b) ^ 2 = u ^ 2 * (a * c - b ^ 2) := by ring

theorem jumping_fiber_generic {t v : R} (ht : IsUnit t) (h : t * v = 0) : v = 0 := by
  rcases ht with ⟨u, rfl⟩
  simpa using congrArg (fun z => (↑u⁻¹ : R) * z) h

theorem jumping_fiber_special (v : R) : (0 : R) * v = 0 := zero_mul _

theorem weighted_cone_relation (x y : R) : x ^ 2 * y ^ 2 - (x * y) ^ 2 = 0 := by ring

theorem odd_module_relations (x y : R) :
    (x * y) * x = x ^ 2 * y ∧ y ^ 2 * x = (x * y) * y := by
  constructor <;> ring

theorem odd_multiplication (x y z : R) :
    (x ^ 2) * z = x * (x * z) ∧ (x * y) * z = x * (y * z) := by
  constructor <;> ring
end Algebra

theorem divisible_denominator (n d : ℕ) (hd : 0 < d) :
    ∃ m e : ℕ, n + m = e * d := by
  cases d with
  | zero => exact False.elim (Nat.not_lt_zero _ hd)
  | succ d =>
    refine ⟨n * d, n, ?_⟩
    ring

theorem quotient_coordinate_transition {K : Type*} [Field K]
    (a b t : K) (n : ℕ) : (t ^ n * b) / a = t ^ n * (b / a) := by ring

section ActualCone
variable (k : Type*) [Field k]

abbrev ConePolynomial := MvPolynomial (Fin 3) k
def coneRelation : ConePolynomial k :=
  MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2
def coneIdeal : Ideal (ConePolynomial k) := Ideal.span {coneRelation k}
abbrev ConeRing := ConePolynomial k ⧸ coneIdeal k

def vertexEval : ConePolynomial k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)

theorem vertexEval_relation : vertexEval k (coneRelation k) = 0 := by
  simp [vertexEval, coneRelation]

def vertexMap : ConeRing k →+* k :=
  Ideal.Quotient.lift (coneIdeal k) (vertexEval k) (by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    rw [hb, map_mul, vertexEval_relation, zero_mul])

def coordinate (i : Fin 3) : ConeRing k :=
  Ideal.Quotient.mk (coneIdeal k) (MvPolynomial.X i)

theorem vertexMap_coordinate (i : Fin 3) : vertexMap k (coordinate k i) = 0 := by
  simp [vertexMap, coordinate, vertexEval]

theorem cone_equation :
    coordinate k 0 * coordinate k 2 = coordinate k 1 ^ 2 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (coneIdeal k) (coneRelation k) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def vertexIdeal : Ideal (ConeRing k) := Ideal.span (Set.range (coordinate k))

theorem vertexIdeal_proper : vertexIdeal k ≠ ⊤ := by
  intro htop
  have hle : vertexIdeal k ≤ RingHom.ker (vertexMap k) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact vertexMap_coordinate k i
  have h1 : (1 : ConeRing k) ∈ RingHom.ker (vertexMap k) := by
    apply hle
    rw [htop]
    trivial
  change vertexMap k 1 = 0 at h1
  simpa using h1

theorem vertexIdeal_not_surjective :
    ¬ Function.Surjective (fun a : vertexIdeal k => (a : ConeRing k)) := by
  intro h
  obtain ⟨a, ha⟩ := h 1
  exact vertexIdeal_proper k (Ideal.eq_top_of_isUnit_mem _ (ha ▸ a.2) isUnit_one)

/-- The literal presentation by b e - a f and c e - b f. -/
def oddRelations : Submodule (ConeRing k) (ConeRing k × ConeRing k) :=
  Submodule.span (ConeRing k)
    {(coordinate k 1, -coordinate k 0), (coordinate k 2, -coordinate k 1)}

abbrev OddPresentation := (ConeRing k × ConeRing k) ⧸ oddRelations k

def vertexReduction : (ConeRing k × ConeRing k) →ₛₗ[vertexMap k] (k × k) where
  toFun v := (vertexMap k v.1, vertexMap k v.2)
  map_add' v w := by ext <;> simp
  map_smul' r v := by ext <;> simp [smul_eq_mul]

theorem oddRelations_vanish : oddRelations k ≤ LinearMap.ker (vertexReduction k) := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl <;>
    simp [LinearMap.mem_ker, vertexReduction, vertexMap_coordinate]

def oddFiberMap : OddPresentation k →ₛₗ[vertexMap k] (k × k) :=
  (oddRelations k).liftQ (vertexReduction k) (oddRelations_vanish k)

theorem oddFiberMap_surjective : Function.Surjective (oddFiberMap k) := by
  intro v
  let liftc (c : k) : ConeRing k :=
    Ideal.Quotient.mk (coneIdeal k) (MvPolynomial.C c)
  refine ⟨Submodule.Quotient.mk (liftc v.1, liftc v.2), ?_⟩
  change (vertexMap k (liftc v.1), vertexMap k (liftc v.2)) = v
  simp [liftc, vertexMap, vertexEval]

theorem pair_not_cyclic (w : k × k) : ¬ (∀ v : k × k, ∃ c : k, c • w = v) := by
  intro h
  obtain ⟨a, ha⟩ := h (1, 0)
  obtain ⟨b, hb⟩ := h (0, 1)
  have ha1 : a * w.1 = 1 := congrArg Prod.fst ha
  have ha2 : a * w.2 = 0 := congrArg Prod.snd ha
  have hb1 : b * w.1 = 0 := congrArg Prod.fst hb
  have hb2 : b * w.2 = 1 := congrArg Prod.snd hb
  have hdet : (a * w.1) * (b * w.2) - (a * w.2) * (b * w.1) = 0 := by ring
  rw [ha1, ha2, hb1, hb2] at hdet
  simp at hdet

/-- Noncyclicity of the concrete presentation; a sheaf identification is still
needed to transfer this statement to O(1), as recorded above. -/
theorem oddPresentation_not_cyclic (w : OddPresentation k) :
    ¬ (∀ v : OddPresentation k, ∃ r : ConeRing k, r • w = v) := by
  intro h
  apply pair_not_cyclic k (oddFiberMap k w)
  intro v
  obtain ⟨n, hn⟩ := oddFiberMap_surjective k v
  obtain ⟨r, hr⟩ := h n
  refine ⟨vertexMap k r, ?_⟩
  rw [← (oddFiberMap k).map_smulₛₗ, hr, hn]
end ActualCone

end Supplements.PJ2
