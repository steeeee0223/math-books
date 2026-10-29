import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# III.3, Kempf proof-sketch companions

The prose now groups the same reductions into Roman-numbered stages and
bullets. The naturality check for 3.A is in stage II, the two terminal
arguments for 3.5 are in stage III, and the unit-ideal argument for 3.7
is in stage IV. The verification scope is unchanged.

3.B is checked at its terminal module level: a distinguished-open cover
gives a unit-ideal spanning family, the diagonal localization map is
injective, and its quotient is the required module cokernel. Finite products
here identify canonically with finite direct sums in the prose.

For 3.A, `naturality_kills_class` checks the connecting-map argument for
local lifts. For 3.5, the two exact-sequence terminal arguments are checked
separately, including the distinct degree-one case. For 3.7, the unit-ideal
consequence of surjectivity on global sections is checked.

Remaining gaps: these declarations do not construct the sheaf maps and
connecting morphisms in 3.A, their dimension-shifting isomorphisms, or the
cover of local lifts. Nor do they formalize the tilde/direct-image comparison,
the induction over all affine schemes, or the geometric part of Serre's
criterion (closed-point ideals, affine principal opens, and the filtration of
the kernel). These are partial checks, not full formal proofs of 3.A--3.7.
-/

open CategoryTheory

universe u v

namespace HartshorneIII3

section Localization

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

/-- 3.B: the module map whose sheafification is the stated embedding. -/
noncomputable def localizationDiagonal (s : Set A) :
    M →ₗ[A] ((r : s) → LocalizedModule.Away r.val M) :=
  LinearMap.pi (fun r => LocalizedModule.mkLinearMap (.powers r.val) M)

/-- 3.B: injectivity needs no Noetherian or finiteness hypothesis. -/
theorem localizationDiagonal_injective (s : Set A) (hs : Ideal.span s = ⊤) :
    Function.Injective (localizationDiagonal A M s) := by
  intro x y hxy
  apply Module.eq_of_isLocalized_span s hs
    (fun r : s => LocalizedModule.Away r.val M)
    (fun r => LocalizedModule.mkLinearMap (.powers r.val) M) x y
  intro r
  exact congrFun hxy r

/-- 3.B: exactness at the target of the diagonal localization map. -/
theorem localizationDiagonal_quotient_exact (s : Set A) :
    Function.Exact (localizationDiagonal A M s)
      (LinearMap.range (localizationDiagonal A M s)).mkQ := by
  intro y
  change y ∈ LinearMap.ker (LinearMap.range (localizationDiagonal A M s)).mkQ ↔ _
  rw [Submodule.ker_mkQ]
  rfl

/-- 3.B: the module quotient map is surjective. -/
theorem localizationDiagonal_quotient_surjective (s : Set A) :
    Function.Surjective (LinearMap.range (localizationDiagonal A M s)).mkQ := by
  exact Submodule.mkQ_surjective _

/-- 3.B: the cover condition is exactly the unit-ideal condition used above. -/
theorem distinguished_cover_iff_span (s : Set A) :
    (⨆ r ∈ s, PrimeSpectrum.basicOpen r) = ⊤ ↔ Ideal.span s = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff'

end Localization

section ConnectingMaps

variable {A B C D E : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E]

/-- 3.A: a local lift kills the image of a class by naturality of delta. -/
theorem naturality_kills_class
    (delta : A →+ B) (delta' : C →+ D)
    (r : A →+ C) (s : B →+ D) (u : E →+ C)
    (commutes : ∀ a, s (delta a) = delta' (r a))
    (complex : ∀ e, delta' (u e) = 0)
    (a : A) (e : E) (lift : u e = r a) : s (delta a) = 0 := by
  rw [commutes, ← lift]
  exact complex e

/-- 3.5 in positive degrees above one: the predecessor vanishes. -/
theorem vanish_above_one
    (delta : A →+ B) (r : B →+ C) (exactness : Function.Exact delta r)
    [Subsingleton A] (alpha : B) (halpha : r alpha = 0) : alpha = 0 := by
  obtain ⟨a, ha⟩ := (exactness alpha).mp halpha
  rw [← ha, Subsingleton.elim a 0, map_zero]

/-- 3.5 in degree one: surjectivity of the map on sections kills delta,
even though its source need not be zero. -/
theorem vanish_in_degree_one
    (p : D →+ A) (delta : A →+ B) (r : B →+ C)
    (p_surjective : Function.Surjective p)
    (complex : ∀ d, delta (p d) = 0)
    (exactness : Function.Exact delta r)
    (alpha : B) (halpha : r alpha = 0) : alpha = 0 := by
  obtain ⟨a, ha⟩ := (exactness alpha).mp halpha
  obtain ⟨d, rfl⟩ := p_surjective a
  simpa [complex] using ha.symm

end ConnectingMaps

section Affineness

/-- 3.7: surjectivity of the section map gives a linear combination equal
to one, hence the selected functions generate the unit ideal. -/
theorem span_eq_top_of_surjective_linear_combination
    {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
    (f : ι → A)
    (h : Function.Surjective (fun a : ι → A => ∑ i, f i * a i)) :
    Ideal.span (Set.range f) = ⊤ := by
  obtain ⟨a, ha⟩ := h 1
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← ha]
  apply Submodule.sum_mem
  intro i hi
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Affineness

end HartshorneIII3
