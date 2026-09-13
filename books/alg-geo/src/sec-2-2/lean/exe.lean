import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties

/-!
# Hartshorne II.2, Exercises 2.1--2.4, 2.12, 2.16 and 2.17

These declarations are kernel-checked versions of the mathlib results used by
the human-readable proofs in `exe.typ`.  For Exercise 2.3 we define the
reduction as the subscheme cut out by the nilradical and verify its universal
property.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace HartshorneII2

def unopHomEquiv {C : Type*} [Category C] {A B : C} :
    (op A ⟶ op B) ≃ (B ⟶ A) where
  toFun f := f.unop
  invFun f := f.op
  left_inv f := Quiver.Hom.op_unop f
  right_inv f := Quiver.Hom.unop_op f

section Exercises2_1_2_4

variable (R : CommRingCat.{u}) (f : R)

/-- Exercise 2.1: `D(f)` is the spectrum of the localization away from `f`. -/
noncomputable def basicOpen_iso_Spec_away :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅
      Spec (.of <| Localization.Away f) :=
  basicOpenIsoSpecAway f

/-- Exercise 2.2: every open subset has a canonical scheme structure. -/
example {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} := U

/-- Its inclusion into the original scheme is an open immersion. -/
example {X : Scheme.{u}} (U : X.Opens) : IsOpenImmersion U.ι := by
  infer_instance

/-- Exercise 2.4: the global-sections--spectrum adjunction. -/
noncomputable def hom_Spec_equiv {X : Scheme.{u}} :
    (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op R)).symm.trans unopHomEquiv

end Exercises2_1_2_4

section Exercise2_3

variable (X : Scheme.{u})

/-- Reducedness is equivalent to reducedness of every local ring. -/
theorem isReduced_iff_stalks :
    IsReduced X ↔ ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  · intro _ x
    infer_instance
  · intro h
    letI (x : X) : _root_.IsReduced (X.presheaf.stalk x) := h x
    exact isReduced_of_isReduced_stalk X

/-- The reduction of a scheme is the subscheme defined by its nilradical. -/
abbrev reduction : Scheme.{u} := X.nilradical.subscheme

/-- The reduction is reduced. -/
theorem reduction_isReduced : IsReduced (reduction X) := by
  have h : ∀ U : X.affineOpens,
      IsReduced (Spec (X.nilradical.subschemeCover.X U)) := by
    intro U
    rw [affine_isReduced_iff]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp
      (Ideal.radical_isRadical _)
  letI (U : X.nilradical.subschemeCover.I₀) :
      IsReduced (X.nilradical.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (X.nilradical.subschemeCover.X U))
    exact h U
  exact IsReduced.of_openCover _ X.nilradical.subschemeCover.openCover

/-- The reduction morphism is a homeomorphism on underlying spaces. -/
theorem reduction_isHomeomorph :
    IsHomeomorph (X.nilradical.subschemeι : reduction X → X) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · exact X.nilradical.subschemeι.isEmbedding
  · rw [← Set.range_eq_univ]
    simp

/-- A morphism from a reduced scheme factors uniquely through the reduction
of its target. -/
theorem existsUnique_lift_reduction {Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) :
    ∃! g : X ⟶ reduction Y, g ≫ Y.nilradical.subschemeι = f := by
  have h : Y.nilradical ≤ f.ker := by
    change Y.nilradical ≤ Scheme.IdealSheafData.ofIdeals _
    rw [Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U s hs
    apply RingHom.mem_ker.mpr
    have hn : IsNilpotent s := by
      change s ∈ (⊥ : Ideal Γ(Y, U)).radical at hs
      change ∃ n, s ^ n = 0
      simpa only [Ideal.mem_radical_iff, Ideal.mem_bot] using hs
    exact (hn.map (f.app U).hom).eq_zero
  let g := f.toImage ≫ Scheme.IdealSheafData.inclusion h
  refine ⟨g, ?_, ?_⟩
  · simp [g]
  · intro g' hg'
    apply (cancel_mono Y.nilradical.subschemeι).mp
    rw [hg', Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι h, f.toImage_imageι]

end Exercise2_3

section Exercise2_12

variable (D : Scheme.GlueData.{u})

/-- The scheme obtained from compatible open gluing data. -/
example : Scheme.{u} := D.glued

/-- Each input scheme is an open subscheme of the gluing. -/
example (i : D.J) : IsOpenImmersion (D.ι i) := by infer_instance

/-- The input schemes cover the gluing. -/
example (x : D.glued) : ∃ (i : D.J) (y : D.U i), D.ι i y = x :=
  D.ι_jointly_surjective x

/-- The prescribed overlaps are the pullback intersections in the gluing. -/
example (i j : D.J) : IsLimit (D.vPullbackCone i j) :=
  D.vPullbackConeIsLimit i j

end Exercise2_12

section Exercise2_16

variable (X : Scheme.{u})

/-- Restricting a global section to `U` cuts its basic open down by
intersection with `U`.  On an affine `U` this is Hartshorne's
`X_f ∩ U = D(f|_U)`. -/
theorem basicOpen_restrict_eq (f : Γ(X, ⊤)) (U : X.Opens) :
    X.basicOpen (X.presheaf.map
      (homOfLE (x := U) (y := (⊤ : X.Opens)) le_top).op f) =
      U ⊓ X.basicOpen f :=
  X.basicOpen_res (f := f) (homOfLE le_top).op

/-- On a quasi-compact scheme, vanishing on `X_f` is killed by a power of
`f`. -/
theorem pow_mul_eq_zero_of_restrict [CompactSpace X]
    {a f : Γ(X, ⊤)} (ha : a |_ X.basicOpen f = 0) :
    ∃ n, f ^ n * a = 0 :=
  exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    X isCompact_univ a f ha

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- The qcqs lemma: sections on `X_f` are the localization of global
sections away from `f`. -/
theorem sections_basicOpen_isLocalization (f : Γ(X, ⊤)) :
    IsLocalization.Away f Γ(X, X.basicOpen f) :=
  isLocalization_basicOpen_of_qcqs isCompact_univ
    isQuasiSeparated_univ f

/-- Every section on `X_f` has, after multiplication by a power of `f`, a
global numerator. -/
theorem exists_global_numerator (f : Γ(X, ⊤))
    (b : Γ(X, X.basicOpen f)) :
    ∃ n a, b * algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) f ^ n =
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) a := by
  letI : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ
      isQuasiSeparated_univ f
  exact IsLocalization.Away.surj f b

end Exercise2_16

section Exercise2_17

/-- Being an isomorphism is local on the target for the Zariski topology. -/
theorem isIso_of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.OpenCover) (h : ∀ i, IsIso (U.pullbackHom f i)) : IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff]
  exact (IsZariskiLocalAtTarget.iff_of_openCover
    (P := MorphismProperty.isomorphisms Scheme) U).mpr h

/-- The finite-basic-open criterion for affineness. -/
theorem isAffine_iff_exists_basicOpen_cover {X : Scheme.{u}} :
    IsAffine X ↔
      ∃ s : Finset Γ(X, ⊤), Ideal.span (s : Set Γ(X, ⊤)) = ⊤ ∧
        ∀ i ∈ s, IsAffineOpen (X.basicOpen i) := by
  constructor
  · intro hX
    letI : IsAffine X := hX
    refine ⟨{1}, by simp, ?_⟩
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simpa using isAffineOpen_top X
  · rintro ⟨s, hs, haff⟩
    exact isAffine_of_isAffineOpen_basicOpen
      (s : Set Γ(X, ⊤)) hs haff

end Exercise2_17


/- Comparison with the revised Hartshorne construction in 2.3:
X.nilradical records radical ideals on affine opens. On arbitrary opens the
associated ideal sheaf consists of locally nilpotent sections, not necessarily
sections killed by one global exponent. The prose sheafifies the nilradical
presheaf before taking its quotient. reduction_isReduced,
reduction_isHomeomorph, and existsUnique_lift_reduction check the resulting
scheme-level conclusions. The identification of that explicit sheafification
with the ideal-sheaf-data construction is not assembled here.
The other revised exercises are checked by the scheme isomorphisms,
adjunction, gluing cover/intersection theorems and localization statements
above. For 2.12 the compatible-family formula is not separately identified
with Scheme.GlueData.glued. In 2.16 the stated finite affine-cover hypothesis
is represented by CompactSpace and QuasiSeparatedSpace; the finite-cover
criterion establishing these instances is not packaged in this file. -/

end HartshorneII2
