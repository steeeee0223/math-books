import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Constructible
import Mathlib.Topology.KrullDimension
import Mathlib.Order.Disjointed
import Mathlib.Tactic

/-!
XP: Hartshorne's irreducible spaces are nonempty, as is IsIrreducible here.
Normality means integrally closed DOMAIN stalks, not merely reduced stalks.
The generic-point, affine-specialization, function-field, dominance,
idempotent, compactness, and finite-type/Noetherian interfaces below retain
all hypotheses of the cited theorems. XP-9 now includes its full II.2.3
statement and proof, with reducedness, reduction, and its universal property
covered by ii-2-exe.lean. The nilradical/localization identities in that proof
are explicitly left as algebraic checks.
XP-4 verifies sobriety and the component correspondence for generization-stable subspaces. XP-12--XP-14
verify constructible compactness and the closed-set/density/inverse-image
criteria, the Boolean normal-form input, compact-open traces and lifts,
spectral subspaces, compact generization hulls, descent of finite relations,
and the zero-dimensional clopen and finite partition arguments. Mathlib's
retrocompact generators agree with quasi-compact opens in spectral spaces;
this comparison is used explicitly below. Compactness of the constructible
topology is supplied by mathlib, with the same spectral hypotheses.
For XP-1(b)--(c), the hit-open lattice identities and the canonical-map
bijectivity criterion are checked. The topology on t(X) and its assembly
as a sober space are not separately implemented here.
The normal scheme assembly and explicit example schemes are not defined here;
normality is checked through the localization algebra and the finite-component
argument in the prose. The locality table uses the existing XL/LP companions.
-/
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Topology
noncomputable section
namespace Supplements.XP

/-- XP-1, the complete assertion for an arbitrary scheme. -/
theorem unique_generic (X : Scheme) (C : Set X) (hC : IsClosed C)
    (hi : IsIrreducible C) : ∃! x, IsGenericPoint x C := by
  refine ⟨hi.genericPoint, hi.isGenericPoint_genericPoint hC, ?_⟩
  intro y hy
  exact hy.eq (hi.isGenericPoint_genericPoint hC)

abbrev closedPointDensity := @LocallyOfFiniteType.jacobsonSpace
abbrev finiteResidueField := @finite_of_finite_type_of_isJacobsonRing
abbrev primeSpecialization := @PrimeSpectrum.le_iff_specializes
abbrev primeClosure := @PrimeSpectrum.closure_singleton
abbrev closedPointMaximal := @PrimeSpectrum.isClosed_singleton_iff_isMaximal
abbrev primeComponents := @PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents
abbrev componentsRestrict := @preimage_mem_irreducibleComponents
abbrev normalDomainDescent := @IsIntegrallyClosed.of_localization_maximal
abbrev genericInOpen := @IsGenericPoint.mem_open_set_iff
abbrev genericImage := @IsGenericPoint.image
abbrev integralCriterion := @isIntegral_iff_irreducibleSpace_and_isReduced
abbrev functionFieldFractions := @functionField_isFractionRing_of_isAffineOpen
abbrev sectionsEmbedInFunctionField := @Scheme.germToFunctionField_injective
abbrev dominantAffine := @PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
abbrev clopenIdempotent := @PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
abbrev noetherianOpens := @noetherianSpace_iff_opens
abbrev finiteComponents := @NoetherianSpace.finite_irreducibleComponents
abbrev noetherianAffine := @isNoetherian_Spec
abbrev locallyNoetherianCover := @isLocallyNoetherian_iff_openCover
abbrev finiteTypeNoetherianCharts := @LocallyOfFiniteType.isLocallyNoetherian
abbrev quasiSeparatedAffineIntersections := @quasiSeparatedSpace_iff_forall_affineOpens
abbrev quasiSeparatedDiagonal := @quasiSeparatedSpace_iff_quasiSeparated
abbrev normalDomainLocalization := @isIntegrallyClosed_of_isLocalization

/-- Reduced stalks imply reducedness with Hartshorne's sheaf convention. -/
theorem reduced_of_stalks (X : Scheme)
    [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] : IsReduced X :=
  isReduced_of_isReduced_stalk X

/-- XP-16 includes quasi-compactness, not just local finite type. -/
theorem finite_type_noetherian {X Y : Scheme} (f : X ⟶ Y)
    [IsNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- XP-22: in a square-zero ideal a prime contains every element. -/
theorem square_zero_in_prime {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (e : R) (h : e * e = 0) : e ∈ p := by
  exact ((inferInstance : p.IsPrime).mem_or_mem_of_mul_eq_zero h).elim id id

/-- XP-23's actual strictly increasing sequence of ideals in the Boolean product. -/
def initialSupport (n : ℕ) : Ideal (ℕ → ZMod 2) where
  carrier := {a | ∀ i, n ≤ i → a i = 0}
  zero_mem' := by simp
  add_mem' := by intros a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intros a b hb i hi; simp [hb i hi]

theorem initialSupport_strict (n : ℕ) : initialSupport n < initialSupport (n+1) := by
  constructor
  · intro a ha i hi
    exact ha i (by omega)
  · intro h
    let a : ℕ → ZMod 2 := fun i => if i = n then 1 else 0
    have ha : a ∈ initialSupport (n+1) := by
      intro i hi
      simp [a, show i ≠ n by omega]
    have hzero := h ha n (le_refl n)
    simp [a] at hzero
variable {X : Type*} [TopologicalSpace X]

/-- XP-4: generization-stable subspaces inherit sobriety. -/
theorem generization_quasiSober [QuasiSober X] {T : Set X}
    (hT : StableUnderGeneralization T) : QuasiSober T where
  sober hD hDclosed := by
    have hI := hD.image (Subtype.val : T → X) continuous_subtype_val.continuousOn
    obtain ⟨η, hη⟩ := QuasiSober.sober hI.closure isClosed_closure
    obtain ⟨d, hd⟩ := hD.nonempty
    have hηT : η ∈ T := hT (hη.specializes (subset_closure ⟨d, hd, rfl⟩)) d.property
    refine ⟨⟨η, hηT⟩, ?_⟩
    change closure ({⟨η, hηT⟩} : Set T) = _
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, image_singleton, hη.def]
    rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hDclosed.closure_eq]

/-- XP-4: the generic point is unique even when the subspace is not a scheme. -/
theorem subspace_unique_generic [QuasiSober X] [T0Space X] {T : Set X}
    (hT : StableUnderGeneralization T) (D : Set T) (hi : IsIrreducible D)
    (hc : IsClosed D) : ∃! x, IsGenericPoint x D := by
  letI := generization_quasiSober hT
  refine ⟨hi.genericPoint, hi.isGenericPoint_genericPoint hc, ?_⟩
  intro x hx
  exact hx.eq (hi.isGenericPoint_genericPoint hc)

/-- Transfer a set to the same points with the constructible topology. -/
def patch (E : Set X) : Set (WithConstructibleTopology X) :=
  WithTopology.ofTopology ⁻¹' E

theorem patch_open_iff (E : Set X) :
    IsOpen (patch E) ↔ IsOpen[constructibleTopology X] E := by
  rw [patch, WithTopology.isOpen_iff]
  rfl

theorem patch_closed_iff (E : Set X) :
    IsClosed (patch E) ↔ IsClosed[constructibleTopology X] E := by
  rw [patch, WithTopology.isClosed_iff]
  rfl

theorem image_patch (E : Set X) : WithTopology.ofTopology '' patch E = E :=
  image_preimage_eq_of_subset (by
    rw [(WithTopology.ofTopology_surjective (constructibleTopology X)).range_eq]
    exact subset_univ E)

/-- The identity from the constructible topology to the original topology is continuous. -/
theorem continuous_from_constructible [PrespectralSpace X] :
    Continuous (WithTopology.ofTopology : WithConstructibleTopology X → X) := by
  apply PrespectralSpace.isTopologicalBasis.continuous_iff.mpr
  intro U hU
  exact hU.2.isOpen_constructibleTopology_of_isOpen hU.1

theorem compact_open_patch_clopen {U : Set X} (ho : IsOpen U) (hc : IsCompact U) :
    IsClopen (patch U) := by
  have hop : IsOpen[constructibleTopology X] Uᶜ :=
    IsCompact.isOpen_constructibleTopology_of_isClosed (by simpa using hc) ho.isClosed_compl
  have hp : IsOpen (patch Uᶜ) := (patch_open_iff _).mpr hop
  exact ⟨by simpa only [patch, preimage_compl, compl_compl] using hp.isClosed_compl,
    (patch_open_iff U).mpr (hc.isOpen_constructibleTopology_of_isOpen ho)⟩

/-- XP-12: mathlib's retrocompact opens are compact opens under these assumptions. -/
theorem constructible_clopen [SpectralSpace X] {E : Set X}
    (hE : Topology.IsConstructible E) : IsClopen (patch E) := by
  induction hE using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U ho hc => exact compact_open_patch_clopen ho hc.isCompact
  | union s hs t ht ihs iht => exact ihs.union iht
  | compl s hs ih => exact ih.compl

/-- XP-12: every constructible set is compact in the finer topology. -/
theorem constructible_patch_compact [SpectralSpace X] {E : Set X}
    (hE : Topology.IsConstructible E) : IsCompact (patch E) :=
  (constructible_clopen hE).isClosed.isCompact

/-- XP-13: the compact-open neighborhood separation used in the intersection formula. -/
theorem stable_compact_separation [PrespectralSpace X] {T : Set X}
    (hc : IsCompact T) (hg : StableUnderGeneralization T) {x : X} (hx : x ∉ T) :
    ∃ U : Set X, IsCompact U ∧ IsOpen U ∧ T ⊆ U ∧ x ∉ U := by
  have hd : T ⊆ (closure ({x} : Set X))ᶜ := by
    intro y hy hxy
    exact hx (hg (specializes_iff_mem_closure.mpr hxy) hy)
  obtain ⟨U, hUc, hUo, hTU, hU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hc isClosed_closure.isOpen_compl hd
  exact ⟨U, hUc, hUo, hTU, fun hxu => hU hxu (subset_closure (by simp))⟩

/-- XP-13(a): a compact stable subset is the intersection of its compact-open neighborhoods. -/
theorem stable_compact_eq_inter [PrespectralSpace X] {T : Set X}
    (hc : IsCompact T) (hg : StableUnderGeneralization T) :
    T = ⋂₀ {U : Set X | IsCompact U ∧ IsOpen U ∧ T ⊆ U} := by
  ext x
  constructor
  · intro hx
    exact mem_sInter.mpr fun U hU => hU.2.2 hx
  · intro hx
    by_contra h
    obtain ⟨U, hUc, hUo, hTU, hxU⟩ := stable_compact_separation hc hg h
    exact hxU (mem_sInter.mp hx U ⟨hUc, hUo, hTU⟩)

/-- XP-13(a): these subsets are closed in the constructible topology. -/
theorem stable_compact_patch_closed [PrespectralSpace X] {T : Set X}
    (hc : IsCompact T) (hg : StableUnderGeneralization T) : IsClosed (patch T) := by
  rw [stable_compact_eq_inter hc hg]
  simp only [patch, preimage_sInter]
  apply isClosed_biInter
  intro U hU
  exact (compact_open_patch_clopen hU.2.1 hU.1).isClosed

/-- XP-13(a): intersections of compact opens are compact, without Noetherianity. -/
theorem compact_open_intersection [SpectralSpace X] (S : Set (Set X))
    (hS : ∀ U ∈ S, IsOpen U ∧ IsCompact U) : IsCompact (⋂₀ S) := by
  have hclosed : IsClosed (patch (⋂₀ S)) := by
    simp only [patch, preimage_sInter]
    apply isClosed_biInter
    intro U hU
    exact (constructible_clopen ((hS U hU).2.isConstructible (hS U hU).1)).isClosed
  rw [← image_patch (⋂₀ S)]
  exact hclosed.isCompact.image continuous_from_constructible

/-- XP-13(a): tracing a compact open to a compact stable subset preserves compactness. -/
theorem stable_compact_trace [SpectralSpace X] {T V : Set X}
    (hc : IsCompact T) (hg : StableUnderGeneralization T) (ho : IsOpen V)
    (hv : IsCompact V) : IsCompact (T ∩ V) := by
  have hT := stable_compact_patch_closed hc hg
  have hV := (constructible_clopen (hv.isConstructible ho)).isClosed
  have hclosed : IsClosed (patch (T ∩ V)) := hT.inter hV
  rw [← image_patch (T ∩ V)]
  exact hclosed.isCompact.image continuous_from_constructible

/-- Every compact open of a subspace lifts to a compact open of the ambient
prespectral space; no assertion that the inclusion is open is used. -/
theorem compact_open_lift [PrespectralSpace X] (T : Set X) {U : Set T}
    (ho : IsOpen U) (hc : IsCompact U) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ Subtype.val ⁻¹' V = U := by
  obtain ⟨O, hOo, hOU⟩ := IsInducing.subtypeVal.isOpen_iff.mp ho
  have hsub : Subtype.val '' U ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ Subtype.val ⁻¹' O
    rw [hOU]
    exact hx
  obtain ⟨V, hVc, hVo, hUV, hVO⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between (hc.image continuous_subtype_val) hOo hsub
  refine ⟨V, hVo, hVc, subset_antisymm ?_ ?_⟩
  · intro x hx
    rw [← hOU]
    exact hVO hx
  · intro x hx
    exact hUV ⟨x, hx, rfl⟩

/-- XP-13(a): the full spectral-space conclusion for a compact stable subspace. -/
theorem stable_subspace_spectral [SpectralSpace X] {T : Set X}
    (hc : IsCompact T) (hg : StableUnderGeneralization T) : SpectralSpace T := by
  have hmap : IsSpectralMap (Subtype.val : T → X) := by
    refine ⟨continuous_subtype_val, fun V hVo hVc => ?_⟩
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa [image_preimage_eq_inter_range, inter_comm] using stable_compact_trace hc hg hVo hVc
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hc
  letI : QuasiSober T := generization_quasiSober hg
  letI : PrespectralSpace T :=
    PrespectralSpace.of_isInducing Subtype.val IsInducing.subtypeVal hmap
  letI : QuasiSeparatedSpace T := by
    constructor
    intro U V hUo hUc hVo hVc
    obtain ⟨A, hAo, hAc, rfl⟩ := compact_open_lift T hUo hUc
    obtain ⟨B, hBo, hBc, rfl⟩ := compact_open_lift T hVo hVc
    rw [← preimage_inter]
    exact hmap.isCompact_preimage_of_isOpen (hAo.inter hBo)
      (hAc.inter_of_isOpen hBc hAo hBo)
  exact ⟨⟩

/-- The set of points specializing to some point of E. -/
def generizations (E : Set X) : Set X := {x | ∃ e ∈ E, x ⤳ e}

/-- XP-13(b): the generization hull is stable and compact. -/
theorem compact_generizations {E : Set X} (hc : IsCompact E) :
    IsCompact (generizations E) ∧ StableUnderGeneralization (generizations E) := by
  constructor
  · apply isCompact_iff_finite_subcover.mpr
    intro ι U hU hcover
    have hEcover : E ⊆ ⋃ i, U i := by
      intro x hx
      exact hcover ⟨x, hx, specializes_rfl⟩
    obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hU hEcover
    refine ⟨s, ?_⟩
    rintro x ⟨e, he, hxe⟩
    obtain ⟨i, hi, heU⟩ := mem_iUnion₂.mp (hs he)
    exact mem_iUnion₂.mpr ⟨i, hi, hxe.mem_open (hU i) heU⟩
  · rintro x y hyx ⟨e, he, hxe⟩
    exact ⟨e, he, hyx.trans hxe⟩

/-- XP-13(c): the closed-complement construction stays in the admissible class. -/
theorem complement_generizations [SpectralSpace X] {U : Set X}
    (ho : IsOpen U) (hc : IsCompact U) :
    IsCompact (generizations Uᶜ ∩ U) ∧
      StableUnderGeneralization (generizations Uᶜ ∩ U) := by
  have hW := compact_generizations ho.isClosed_compl.isCompact
  refine ⟨stable_compact_trace hW.1 hW.2 ho hc, ?_⟩
  intro x y hyx hx
  exact ⟨hW.2 hyx hx.1, ho.stableUnderGeneralization hyx hx.2⟩

/-- XP-13(d): a finite constructible relation descends to a single stage. -/
theorem finite_stage_relation [SpectralSpace X] {ι : Type*} [Nonempty ι]
    (V : ι → Set X) (hVo : ∀ i, IsOpen (V i)) (hVc : ∀ i, IsCompact (V i))
    (hd : Directed (· ⊇ ·) V) {A B : Set X}
    (hA : Topology.IsConstructible A) (hB : Topology.IsConstructible B)
    (h : (⋂ i, V i) ∩ A ⊆ B) : ∃ i, V i ∩ A ⊆ B := by
  let C : ι → Set (WithConstructibleTopology X) := fun i => patch (V i ∩ (A \ B))
  have hCc : ∀ i, IsClosed (C i) := fun i =>
    (constructible_clopen ((hVc i).isConstructible (hVo i) |>.inter (hA.sdiff hB))).isClosed
  have hCd : Directed (· ⊇ ·) C := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hd i j
    exact ⟨k, fun x hx => ⟨hki hx.1, hx.2⟩, fun x hx => ⟨hkj hx.1, hx.2⟩⟩
  have hempty : (⋂ i, C i) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxV : WithTopology.ofTopology x ∈ ⋂ i, V i :=
      mem_iInter.mpr fun i => (mem_iInter.mp hx i).1
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hxAB := (mem_iInter.mp hx i).2
    exact hxAB.2 (h ⟨hxV, hxAB.1⟩)
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_compactSpace hCd hCc (U := ∅) (by simp [hempty])
  refine ⟨i, ?_⟩
  intro x hx
  by_contra hxB
  exact hi (show WithTopology.toTopology (constructibleTopology X) x ∈ C i from
    ⟨hx.1, hx.2, hxB⟩)

/-- XP-4/XP-14: dimension zero really excludes strict specializations. -/
theorem t1_of_dimension_nonpos [T0Space X] (hd : topologicalKrullDim X ≤ 0) : T1Space X := by
  apply t1Space_iff_specializes_imp_eq.mpr
  intro x y hxy
  let C : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let D : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hDC : D ≤ C := hxy.closure_subset
  have hCD : C ≤ D := Order.krullDim_nonpos_iff_forall_isMax.mp hd D hDC
  exact (specializes_iff_closure_subset.mpr hCD).antisymm hxy |>.eq.symm


/-- XP-12(c): closedness follows from constructible compactness and stability. -/
theorem patch_closed_isClosed [SpectralSpace X] {E : Set X}
    (hE : IsClosed (patch E)) (hs : StableUnderSpecialization E) : IsClosed E := by
  classical
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have sep : ∀ y : E, ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ x ∈ U ∧ (y : X) ∉ U := by
    intro y
    have hxcl : x ∉ closure ({(y : X)} : Set X) :=
      fun h => hx (hs (specializes_iff_mem_closure.mpr h) y.property)
    obtain ⟨U, ⟨hUo, hUc⟩, hxU, hUsub⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxcl isClosed_closure.isOpen_compl
    exact ⟨U, hUo, hUc, hxU, fun hyU => hUsub hyU (subset_closure (by simp))⟩
  choose U hUo hUc hxU hyU using sep
  obtain ⟨s, hscover⟩ := hE.isCompact.elim_finite_subcover
    (fun y : E => patch (U y)ᶜ)
    (fun y => (compact_open_patch_clopen (hUo y) (hUc y)).compl.isOpen) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨WithTopology.ofTopology y, hy⟩, hyU _⟩)
  have hNopen : IsOpen (⋂ y ∈ s, U y) := isOpen_biInter_finset fun y _ => hUo y
  apply Filter.mem_of_superset (hNopen.mem_nhds (mem_iInter₂.mpr fun y _ => hxU y))
  intro z hz hzE
  have hzpatch : WithTopology.toTopology (constructibleTopology X) z ∈ patch E := hzE
  obtain ⟨y, hy, hznot⟩ := mem_iUnion₂.mp (hscover hzpatch)
  exact hznot (mem_iInter₂.mp hz y hy)

/-- XP-12(c): the full constructible closed-set criterion. -/
theorem constructible_closed_iff [SpectralSpace X] {E : Set X}
    (hE : Topology.IsConstructible E) : IsClosed E ↔ StableUnderSpecialization E :=
  ⟨IsClosed.stableUnderSpecialization,
    patch_closed_isClosed (constructible_clopen hE).isClosed⟩

/-- XP-14: quasi-compact opens in dimension zero are clopen. -/
theorem zero_dimensional_clopen [SpectralSpace X] (hd : topologicalKrullDim X ≤ 0)
    {U : Set X} (ho : IsOpen U) (hc : IsCompact U) : IsClopen U := by
  letI : T1Space X := t1_of_dimension_nonpos hd
  refine ⟨(constructible_closed_iff (hc.isConstructible ho)).mpr ?_, ho⟩
  intro x y hxy hx
  rwa [← hxy.eq]


/-- XP-12(e): the inverse-image theorem with its exact map hypothesis. -/
theorem constructible_preimage {Y : Type*} [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] {f : X → Y} (hf : IsSpectralMap f)
    {E : Set Y} (hE : Topology.IsConstructible E) : Topology.IsConstructible (f ⁻¹' E) :=
  hE.preimage hf.continuous fun _ ho hc =>
    (hf.isCompact_preimage_of_isOpen ho hc.isCompact).isRetrocompact (ho.preimage hf.continuous)

/-- The finite Boolean reduction behind XP-12(d). -/
theorem constructible_generic_neighborhood [SpectralSpace X] {η : X}
    (hη : IsGenericPoint η univ) {E : Set X} (hE : Topology.IsConstructible E) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ ∀ x ∈ U, (x ∈ E ↔ η ∈ E) := by
  induction hE using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact V ho hc =>
    by_cases hηV : η ∈ V
    · exact ⟨V, ho, hηV, fun x hx => iff_of_true hx hηV⟩
    · have hV : V = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hηV ((hη.mem_open_set_iff ho).mpr ⟨x, trivial, hx⟩)
      exact ⟨univ, isOpen_univ, trivial, by simp [hV]⟩
  | union s hs t ht ihs iht =>
    obtain ⟨U, hUo, hηU, hU⟩ := ihs
    obtain ⟨V, hVo, hηV, hV⟩ := iht
    exact ⟨U ∩ V, hUo.inter hVo, ⟨hηU, hηV⟩,
      fun x hx => or_congr (hU x hx.1) (hV x hx.2)⟩
  | compl s hs ih =>
    obtain ⟨U, hUo, hηU, hU⟩ := ih
    exact ⟨U, hUo, hηU, fun x hx => not_congr (hU x hx)⟩

/-- XP-12(d): the complete density criterion and its open-subset consequence. -/
theorem constructible_dense_generic [SpectralSpace X] {η : X}
    (hη : IsGenericPoint η univ) {E : Set X} (hE : Topology.IsConstructible E) :
    (Dense E ↔ η ∈ E) ∧ (η ∈ E → ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ E) := by
  obtain ⟨U, hUo, hηU, hU⟩ := constructible_generic_neighborhood hη hE
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hd
    obtain ⟨x, hxE, hxU⟩ := hd.exists_mem_open hUo ⟨η, hηU⟩
    exact (hU x hxU).mp hxE
  · intro hηE x
    have hsub := closure_mono (singleton_subset_iff.mpr hηE)
    rw [hη.def] at hsub
    exact hsub (mem_univ x)
  · intro hηE
    exact ⟨U, hUo, ⟨η, hηU⟩, fun x hx => (hU x hx).mpr hηE⟩

/-- XP-14: the finite clopen partition used after compactness gives a finite cover. -/
theorem finite_clopen_refinement {n : ℕ} (U : Fin n → Set X)
    (hU : ∀ i, IsClopen (U i)) :
    (∀ i, IsClopen (disjointed U i) ∧ disjointed U i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (disjointed U i) (disjointed U j)) ∧
      (⋃ i, disjointed U i) = ⋃ i, U i := by
  refine ⟨fun i => ⟨?_, disjointed_le U i⟩, disjoint_disjointed U, iSup_disjointed U⟩
  exact disjointedRec (fun {t i} ht => ht.diff (hU i)) (hU i)

/-- XP-1(b): the basic opens of t(X), as sets of irreducible closed subsets. -/
def hits (U : Set X) : Set (IrreducibleCloseds X) := {C | ((C : Set X) ∩ U).Nonempty}

/-- XP-1(b): irreducibility is exactly what makes the basic opens closed under intersections. -/
theorem hits_inter {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) :
    hits (U ∩ V) = hits U ∩ hits V := by
  ext C
  constructor
  · rintro ⟨x, hxC, hxU, hxV⟩
    exact ⟨⟨x, hxC, hxU⟩, ⟨x, hxC, hxV⟩⟩
  · rintro ⟨hCU, hCV⟩
    exact C.isIrreducible.isPreirreducible U V hU hV hCU hCV

/-- XP-1(b): arbitrary unions are preserved. -/
theorem hits_iUnion {ι : Type*} (U : ι → Set X) : hits (⋃ i, U i) = ⋃ i, hits (U i) := by
  ext C
  constructor
  · rintro ⟨x, hxC, hxU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨i, x, hxC, hi⟩
  · intro h
    obtain ⟨i, x, hxC, hxU⟩ := mem_iUnion.mp h
    exact ⟨x, hxC, mem_iUnion.mpr ⟨i, hxU⟩⟩

/-- XP-1(c): the canonical map to nonempty irreducible closed subsets. -/
def pointClosure (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- XP-1(b): inverse image recovers the original open, proving injectivity of the open correspondence. -/
theorem pointClosure_preimage_hits {U : Set X} (hU : IsOpen U) :
    pointClosure ⁻¹' hits U = U := by
  ext x
  exact ((isGenericPoint_closure : IsGenericPoint x (closure {x})).mem_open_set_iff hU).symm

/-- XP-1(c): bijectivity of the canonical map is precisely sobriety. -/
theorem pointClosure_bijective_iff : Function.Bijective (pointClosure (X := X)) ↔
    ∀ C : Set X, IsIrreducible C → IsClosed C → ∃! x, IsGenericPoint x C := by
  constructor
  · rintro ⟨hinj, hsurj⟩ C hi hc
    obtain ⟨x, hx⟩ := hsurj ⟨C, hi, hc⟩
    have hxC : IsGenericPoint x C := congrArg (fun D : IrreducibleCloseds X => (D : Set X)) hx
    refine ⟨x, hxC, fun y hy => hinj ?_⟩
    exact IrreducibleCloseds.ext (hy.def.trans hxC.def.symm)
  · intro h
    constructor
    · intro x y hxy
      have heq : closure ({x} : Set X) = closure {y} :=
        congrArg (fun D : IrreducibleCloseds X => (D : Set X)) hxy
      obtain ⟨z, hz, huniq⟩ := h _ isIrreducible_singleton.closure isClosed_closure
      exact (huniq x heq).trans (huniq y isGenericPoint_closure).symm
    · intro C
      obtain ⟨x, hx, _⟩ := h C C.isIrreducible C.isClosed
      exact ⟨x, IrreducibleCloseds.ext hx.def⟩


/-- XP-12(a): the terminal Boolean normal-form assertion, with exactly the
open-retrocompact generators used by mathlib. In a spectral space these
are the quasi-compact opens. -/
theorem constructible_normal_form [SpectralSpace X] {E : Set X}
    (hE : Topology.IsConstructible E) :
    ∃ t : Finset ({U : Set X // IsOpen U ∧ IsRetrocompact U} ×
      {V : Set X // IsOpen V ∧ IsRetrocompact V}),
      E = t.sup (fun p => p.1.val \ p.2.val) := by
  apply (BooleanSubalgebra.mem_closure_iff_sup_sdiff (s := {U : Set X | IsOpen U ∧ IsRetrocompact U})
    ⟨fun s hs t ht => ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht => ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
    ⟨isOpen_empty, IsRetrocompact.empty⟩ ⟨isOpen_univ, IsRetrocompact.univ⟩).mp hE


/-- XP-4: restricting a generic point uses the subspace closure formula. -/
theorem generic_in_subspace {T C : Set X} {η : X} (hη : IsGenericPoint η C) (hT : η ∈ T) :
    IsGenericPoint (⟨η, hT⟩ : T) (Subtype.val ⁻¹' C) := by
  change closure ({⟨η, hT⟩} : Set T) = _
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, image_singleton, hη.def]

/-- XP-4: every nonempty component trace is a component, without a finite-component assumption. -/
theorem component_trace [QuasiSober X] {T : Set X} (hT : StableUnderGeneralization T)
    {C : Set X} (hC : C ∈ irreducibleComponents X) (hne : (C ∩ T).Nonempty) :
    Subtype.val ⁻¹' C ∈ irreducibleComponents T := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨x, hxC, hxT⟩ := hne
  have hηT := hT (hη.specializes hxC) hxT
  have hgen := generic_in_subspace hη hηT
  refine ⟨hgen.isIrreducible, ?_⟩
  intro D hD hCD
  have hηD : (⟨η, hηT⟩ : T) ∈ D := hCD hη.mem
  have hηimg : η ∈ Subtype.val '' D := ⟨⟨η, hηT⟩, hηD, rfl⟩
  have hDC := hD.image Subtype.val continuous_subtype_val.continuousOn
  have hCclosure : C ⊆ closure (Subtype.val '' D) := by
    rw [← hη.def]
    exact closure_mono (singleton_subset_iff.mpr hηimg)
  have hclosureC := hC.2 hDC.closure hCclosure
  intro d hd
  exact hclosureC (subset_closure ⟨d, hd, rfl⟩)

/-- XP-4: the complete component correspondence for stable subspaces. -/
theorem component_trace_iff [QuasiSober X] {T : Set X} (hT : StableUnderGeneralization T)
    (D : Set T) : D ∈ irreducibleComponents T ↔
      ∃ C ∈ irreducibleComponents X, (C ∩ T).Nonempty ∧ Subtype.val ⁻¹' C = D := by
  constructor
  · intro hD
    have hi := hD.1.image Subtype.val continuous_subtype_val.continuousOn
    obtain ⟨C, hC, hDC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hi
    obtain ⟨d, hd⟩ := hD.1.nonempty
    have hne : (C ∩ T).Nonempty := ⟨d, hDC ⟨d, hd, rfl⟩, d.property⟩
    have htrace := component_trace hT hC hne
    have hsub : D ⊆ Subtype.val ⁻¹' C := fun x hx => hDC ⟨x, hx, rfl⟩
    exact ⟨C, hC, hne, subset_antisymm (hD.2 htrace.1 hsub) hsub⟩
  · rintro ⟨C, hC, hne, rfl⟩
    exact component_trace hT hC hne

/-- XP-4: chains of irreducible closed sets and specialization chains
are identified by this order isomorphism. -/
noncomputable def closedPointOrder [QuasiSober X] [T0Space X] :=
  @irreducibleSetEquivPoints X _ _ _


end Supplements.XP
