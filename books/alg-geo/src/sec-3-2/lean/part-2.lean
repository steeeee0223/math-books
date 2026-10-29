import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Order.RelSeries

/-!
# III.2, proof-sketch companions

The prose now groups the same reductions into Roman-numbered stages and
bullets. In 2.B, exactness supplies stage II; in 2.E, the filtered-colimit
comparison is stage IV; in 2.G, the chain bound is in stage II and the
restriction diagram chase is in stage III. The verification scope is unchanged.

These declarations check the following actual reductions in part-2.typ:
* 2.B: the site-theoretic Mayer--Vietoris sequence is exact.
* 2.G: appending a strict specialization increases chain length by one.
* 2.E: a filtered colimit of abelian-group diagrams preserves homology.
* 2.G: the diagram chase that makes the middle restriction surjective.
* 2.C, 2.F, 2.G and 2.7: the final exactness/vanishing implications.

Remaining gaps: this file does not construct the Mayer--Vietoris square of
two topological opens or compare H' with the textbook's resolution model.
The general topology inputs now belong to the XP companion,
sup/lean/scheme-properties.lean. This file does not formalize the descent
of sheaf sections in 2.E or the acyclic-resolution/dimension-shifting interfaces in 2.C and
2.G. In particular it is not a verification of full Grothendieck vanishing.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HartshorneIII2

section MayerVietoris

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- 2.B, at the site-theoretic interface supplied by mathlib. -/
theorem mayerVietoris_exact (S : J.MayerVietorisSquare)
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).Exact :=
  S.sequence_exact F n (n + 1) rfl

end MayerVietoris

/-- 2.G: the terminal chain-length calculation, after identifying
dimension with a bound on strict specialization chains. -/
theorem extended_chain_bound {P : Type*} {r : SetRel P P} (d : ℕ)
    (bound : ∀ c : RelSeries r, c.length ≤ d)
    (c : RelSeries r) (z : P) (hz : (c.last, z) ∈ r) : c.length + 1 ≤ d := by
  simpa using bound (c.snoc z hz)

section FilteredColimits

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 2.E: the algebraic comparison in each degree of a complex. A short
complex encodes its incoming and outgoing differential in that degree. -/
noncomputable def filtered_colimit_homology
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) :
    (S.map (colim (J := J) (C := AddCommGrpCat.{u}))).homology ≅
      (colim (J := J) (C := AddCommGrpCat.{u})).obj S.homology :=
  S.mapHomologyIso _

end FilteredColimits

section ExactRows

variable {A B C A' B' C' : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']

/-- 2.G: in a map of right-exact rows, surjectivity of the outside
vertical maps implies surjectivity of the middle vertical map. -/
theorem middle_restriction_surjective
    (f : A →+ B) (g : B →+ C) (f' : A' →+ B') (g' : B' →+ C')
    (a : A →+ A') (b : B →+ B') (c : C →+ C')
    (bottom_exact : Function.Exact f' g')
    (g_surjective : Function.Surjective g)
    (a_surjective : Function.Surjective a)
    (c_surjective : Function.Surjective c)
    (left_commutes : ∀ x, b (f x) = f' (a x))
    (right_commutes : ∀ x, c (g x) = g' (b x)) :
    Function.Surjective b := by
  intro y'
  obtain ⟨z, hz⟩ := c_surjective (g' y')
  obtain ⟨y, hy⟩ := g_surjective z
  have hzero : g' (y' - b y) = 0 := by
    rw [map_sub, ← right_commutes y, hy, hz, sub_self]
  obtain ⟨x', hx'⟩ := (bottom_exact (y' - b y)).mp hzero
  obtain ⟨x, hx⟩ := a_surjective x'
  refine ⟨y + f x, ?_⟩
  rw [map_add, left_commutes, hx, hx']
  abel

/-- 2.C/2.G: the final long-exact-sequence implication when the
preceding group vanishes. -/
theorem zero_of_exact_and_zero_predecessor
    (delta : A →+ B) (r : B →+ C) (h : Function.Exact delta r)
    [Subsingleton A] (x : B) (hx : r x = 0) : x = 0 := by
  obtain ⟨a, ha⟩ := (h x).mp hx
  rw [← ha, Subsingleton.elim a 0, map_zero]

/-- 2.F: a surjective connecting map out of a zero group has zero target. -/
theorem zero_of_surjection_from_zero (f : A →+ B)
    (hf : Function.Surjective f) [Subsingleton A] (b : B) : b = 0 := by
  obtain ⟨a, rfl⟩ := hf b
  simp [Subsingleton.elim a 0]

/-- 2.7: specializing a theorem for all admissible subspaces to the
whole space requires no additional cohomological argument. -/
theorem specialize_to_whole {X : Type*} (admissible : Set X → Prop)
    (vanishes : Set X → Prop) (h : ∀ T, admissible T → vanishes T)
    (hX : admissible Set.univ) : vanishes Set.univ :=
  h Set.univ hX

end ExactRows

end HartshorneIII2
