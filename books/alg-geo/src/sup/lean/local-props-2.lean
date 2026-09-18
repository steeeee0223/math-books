import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Etale.Kaehler

/-!
Companion to LP2. Definition comparison is essential here. Mathlib's scheme
`Smooth` is defined through formally smooth finitely presented affine maps;
Hartshorne/Liu's flat + geometrically regular fibers formulation is used in
the prose. We check the affine/standard-smooth equivalence, flatness, and
fiberwise smooth criterion, but the comparison of formally smooth algebras
over fields with geometrically regular algebras is a remaining gap. We do
not silently identify these two definitions.

Unramified is represented by a repo-local predicate containing precisely
local finite type and an open diagonal. Its equivalence with finite type +
mathlib's `FormallyUnramified` is proved below, so the diagonal convention
agrees literally with the text. The latter algebra class has Ω=0 as its
definition, and its square-zero uniqueness theorem is also checked.

Coverage: LP2-2/3 lift existence/uniqueness, Ω=0, étale=flat+unramified with
finite presentation, and conormal splitting; LP2-4 standard-smooth affine
charts and their differential rank; LP2-5 actual source/target locality,
composition and base change on schemes; LP2-7 flat preservation of the
multiplication injection; LP2-8 regular-sequence concatenation and flat
tensoring; LP2-9 the split conormal map for a smooth quotient; LP2-12 the
proper closed-image removal step, with its missing-fiber hypothesis explicit.

Precise remaining gaps: the geometrically regular comparison above, complete
Jacobian/local-equation presentation construction, perfect-field regularity,
regular-local quotient theorem, scheme-level effective Cartier and regular
immersion predicates, and the counterexample computations are not assembled
in this companion. LP2-11 line-bundle ampleness and LP2-12 localization of
coherent global sections and spreading a projective closed immersion are
not formalized. The topological closed-image lemma below verifies the final
neighborhood removal only, not the whole spreading theorem. There is no
claim of complete verification of either positivity result.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TensorProduct

noncomputable section
universe u

namespace SupplementLP2

section SchemeCriteria
variable {X Y Z S : Scheme.{u}}

/-- LP2-1: the literal textbook diagonal definition. -/
def Unramified (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)

/-- LP2-3: bridge the diagonal convention before using the differential API. -/
theorem unramified_iff (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := by
  constructor
  · rintro ⟨hft, hd⟩
    letI := hft
    letI := hd
    exact ⟨hft, inferInstance⟩
  · rintro ⟨hft, hu⟩
    letI := hft
    letI := hu
    exact ⟨hft, inferInstance⟩

/-- LP2-3: finite presentation is retained, including beyond Noetherian schemes. -/
theorem etale_iff_flat_unramified (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Etale f ↔ Flat f ∧ Unramified f := by
  rw [unramified_iff, Etale.iff_flat_and_formallyUnramified]
  constructor
  · rintro ⟨hf, hu, _⟩
    exact ⟨hf, inferInstance, hu⟩
  · rintro ⟨hf, _, hu⟩
    exact ⟨hf, hu, inferInstance⟩

/-- LP2-1/3: the relative-dimension-zero definition of étale. -/
theorem etale_relative_dimension_zero (f : X ⟶ Y) :
    Etale f ↔ SmoothOfRelativeDimension 0 f :=
  Etale.iff_smoothOfRelativeDimension_zero f

/-- LP2-4: affine chart criterion, with both neighborhoods and containment recorded. -/
theorem smooth_standard_charts (f : X ⟶ Y) :
    Smooth f ↔ ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U)
      (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth :=
  Smooth.iff_forall_exists_isStandardSmooth f

/-- LP2-5: locality on an arbitrary source cover. -/
theorem smooth_source_cover (f : X ⟶ Y) (c : X.OpenCover) :
    Smooth f ↔ ∀ i, Smooth (c.f i ≫ f) :=
  IsZariskiLocalAtSource.iff_of_openCover c

theorem etale_source_cover (f : X ⟶ Y) (c : X.OpenCover) :
    Etale f ↔ ∀ i, Etale (c.f i ≫ f) :=
  IsZariskiLocalAtSource.iff_of_openCover c

theorem formallyUnramified_source_cover (f : X ⟶ Y) (c : X.OpenCover) :
    FormallyUnramified f ↔ ∀ i, FormallyUnramified (c.f i ≫ f) :=
  IsZariskiLocalAtSource.iff_of_openCover c

/-- LP2-5: target locality uses the whole inverse image of each open. -/
theorem smooth_target_cover (f : X ⟶ Y) (c : Y.OpenCover) :
    Smooth f ↔ ∀ i, Smooth (c.pullbackHom f i) :=
  IsZariskiLocalAtTarget.iff_of_openCover c

theorem etale_target_cover (f : X ⟶ Y) (c : Y.OpenCover) :
    Etale f ↔ ∀ i, Etale (c.pullbackHom f i) :=
  IsZariskiLocalAtTarget.iff_of_openCover c

theorem formallyUnramified_target_cover (f : X ⟶ Y) (c : Y.OpenCover) :
    FormallyUnramified f ↔ ∀ i, FormallyUnramified (c.pullbackHom f i) :=
  IsZariskiLocalAtTarget.iff_of_openCover c

/-- LP2-5: genuine scheme compositions. -/
theorem smooth_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) := inferInstance

theorem etale_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) := inferInstance

theorem unramified_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Unramified f) (hg : Unramified g) : Unramified (f ≫ g) := by
  obtain ⟨hft, hfu⟩ := (unramified_iff f).mp hf
  obtain ⟨hgt, hgu⟩ := (unramified_iff g).mp hg
  letI := hft; letI := hfu; letI := hgt; letI := hgu
  exact (unramified_iff _).mpr ⟨inferInstance,
    MorphismProperty.comp_mem (@FormallyUnramified) f g hfu hgu⟩

/-- LP2-5: actual arbitrary base-change projections. -/
theorem smooth_baseChange (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] :
    Smooth (pullback.snd f g) := inferInstance

theorem etale_baseChange (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) := inferInstance

theorem unramified_baseChange (f : X ⟶ S) (g : Y ⟶ S)
    (hf : Unramified f) : Unramified (pullback.snd f g) := by
  obtain ⟨hft, hfu⟩ := (unramified_iff f).mp hf
  letI := hft; letI := hfu
  exact (unramified_iff _).mpr ⟨inferInstance,
    MorphismProperty.pullback_snd (P := @FormallyUnramified) f g hfu⟩

/-- LP2-3/6: smooth morphisms are flat. -/
theorem smooth_flat (f : X ⟶ Y) [Smooth f] : Flat f := inferInstance

/-- LP2-6: the precise fiber criterion available in the affine smooth convention. -/
theorem smooth_of_smooth_fibers (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f]
    (h : ∀ y, Smooth (f.fiberToSpecResidueField y)) : Smooth f :=
  Smooth.of_smooth_fiberToSpecResidueField f h
end SchemeCriteria

section Lifting
variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- LP2-2: Ω=0 is exactly the formal unramified algebra condition. -/
theorem unramified_differentials :
    Algebra.FormallyUnramified R A ↔ Subsingleton Ω[A⁄R] :=
  Algebra.formallyUnramified_iff R A

/-- LP2-2/3: uniqueness of lifts with fixed reduction. -/
theorem unramified_lift_unique [Algebra.FormallyUnramified R A]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Injective (fun f : A →ₐ[R] B => (Ideal.Quotient.mkₐ R I).comp f) :=
  Algebra.FormallyUnramified.comp_injective I hI

/-- LP2-2/3: affine smooth lifts exist; scheme existence is local on the test. -/
theorem smooth_lift_exists [Algebra.FormallySmooth R A]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Surjective (fun f : A →ₐ[R] B => (Ideal.Quotient.mkₐ R I).comp f) :=
  Algebra.FormallySmooth.comp_surjective R A I hI

/-- LP2-2/3: combining existence and uniqueness for étale algebras. -/
theorem etale_lifts [Algebra.FormallyEtale R A]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective (fun f : A →ₐ[R] B => (Ideal.Quotient.mkₐ R I).comp f) :=
  Algebra.FormallyEtale.comp_bijective R A I hI
end Lifting

section Conormal
variable (R P A : Type*) [CommRing R] [CommRing P] [CommRing A]
variable [Algebra R P] [Algebra P A] [Algebra R A] [IsScalarTower R P A]
variable [Algebra.FormallySmooth R P] [Algebra.FormallySmooth R A]

/-- LP2-9 / DF-10: the full conormal map of a smooth quotient splits. -/
theorem smooth_quotient_conormal_split (h : Function.Surjective (algebraMap P A)) :
    ∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor R P A = LinearMap.id :=
  (Algebra.FormallySmooth.iff_split_injection h).mp inferInstance

theorem smooth_quotient_conormal_injective (h : Function.Surjective (algebraMap P A)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R P A) := by
  obtain ⟨l, hl⟩ := smooth_quotient_conormal_split R P A h
  intro x y hxy
  have h := congrArg l hxy
  simpa only [← LinearMap.comp_apply, hl, LinearMap.id_apply] using h
end Conormal

section StandardCharts
variable {R A ι σ : Type*} [CommRing R] [CommRing A] [Algebra R A] [Finite σ]

/-- LP2-4: elimination produces freeness, and the expected rank. -/
theorem standard_differentials_free (P : Algebra.SubmersivePresentation R A ι σ) :
    Module.Free A Ω[A⁄R] := P.free_kaehlerDifferential

theorem standard_differentials_rank [Finite ι] [Nontrivial A]
    (P : Algebra.SubmersivePresentation R A ι σ) :
    Module.rank A Ω[A⁄R] = P.dimension := P.rank_kaehlerDifferential
end StandardCharts

section CartierAndRegular
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- LP2-7: the exact flat-tensor injectivity used for a Cartier equation. -/
theorem flat_preserves_equation [Module.Flat R N] (a : R)
    (ha : Function.Injective (LinearMap.lsmul R M a)) :
    Function.Injective ((LinearMap.lsmul R M a).rTensor N) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ ha

/-- LP2-8: the successive-quotient criterion for concatenating regular sequences. -/
theorem regular_sequence_composition (s t : List R) :
    RingTheory.Sequence.IsWeaklyRegular M (s ++ t) ↔
      RingTheory.Sequence.IsWeaklyRegular M s ∧
      RingTheory.Sequence.IsWeaklyRegular (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M)) t :=
  RingTheory.Sequence.isWeaklyRegular_append_iff M s t

/-- LP2-8: flat tensoring preserves each multiplication injection.
Weak regularity permits an empty pullback; nonempty localizations restore
properness of the generated ideal, as explicitly explained in the text. -/
theorem regular_sequence_flat_baseChange [Module.Flat R N] {s : List R}
    (hs : RingTheory.Sequence.IsWeaklyRegular M s) :
    RingTheory.Sequence.IsWeaklyRegular (M ⊗[R] N) s :=
  hs.isWeaklyRegular_rTensor
end CartierAndRegular

section ProperNeighborhood
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- LP2-12: the exact closed-image removal, not the entire spreading theorem. -/
theorem remove_bad_closed_set (Z : Set X) (hZ : IsClosed Z) (y : Y)
    (hy : ∀ x ∈ Z, f x ≠ y) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ Disjoint (f ⁻¹' V) Z := by
  refine ⟨(f '' Z)ᶜ, (f.isClosedMap Z hZ).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hy x hx hxy
  · rw [Set.disjoint_left]
    intro x hx hxZ
    exact hx ⟨x, hxZ, rfl⟩
end ProperNeighborhood

end SupplementLP2
