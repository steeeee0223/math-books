import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maps

/-!
Companion for LP-54–LP-58 and LP-59–LP-64.

Definition comparison: `IsDominant` is dense range, exactly LP-59.
`IsSchemeTheoreticallyDominant` uses the quasi-coherent kernel. Its
sectionwise interpretation below retains QuasiCompact; it is not silently
identified with sheaf injectivity for arbitrary maps. The flat-base-change
scheme theorem below assumes a reduced target. The general nonreduced
LP-61 reduction is supported by the nil-kernel spectrum equivalence,
flat tensor kernel comparison, and nil-ideal extension theorem separately.

LP-57: PicOverlap and nodalTransition encode the *computed* Picard group
coordinates (unit, Laurent exponent, degree). compatible_degree_zero is
the exact terminal obstruction; it does not construct C, its conductor,
the classification Pic(C_R), or its projective degree interpretation.
LP-54–LP-56 projective embeddings and their counterexample schemes, LP-58's
ample criterion, LP-61's finite affine-cover assembly in the nonreduced case,
LP-62's coherent-sheaf associated-point bridge, and LP-64's normal-domain
height-one intersection and its sheaf assembly are outstanding interfaces.
These are verification gaps, not additional axioms or completed theorems.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.LPExtensions

theorem dominant_composition {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) := by infer_instance

theorem dominant_source_restriction {X Y : Scheme} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) :
    IsDominant (U.ι ≫ f) := by
  letI := Opens.isDominant_ι hU
  infer_instance

-- Actual target locality, not a ring-local surrogate for projectivity.
example : IsZariskiLocalAtTarget @IsDominant := inferInstance
abbrev densityCriterion := @PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
abbrev finiteAffineDisjointUnion := @PrimeSpectrum.sigmaToPi_bijective
abbrev tensorKernel := @Module.Flat.ker_lTensor_eq

/-- Extending a nil ideal along any ring map remains a nil ideal (LP-61). -/
theorem extended_nil_ideal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : I ≤ nilradical R) :
    I.map f ≤ nilradical S := by
  apply le_trans (Ideal.map_mono hI)
  simpa [nilradical, Ideal.zero_eq_bot] using
    (Ideal.map_radical_le (f := f) (I := (⊥ : Ideal R)))

/-- The scheme-level flat comparison, with its reduced-target hypothesis visible. -/
theorem dominant_flat_base_change_reduced {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [IsDominant f]
    [IsReduced S] [Flat g] : IsDominant (pullback.snd f g) := by
  letI := IsSchemeTheoreticallyDominant.of_isDominant f
  infer_instance

abbrev restriction_injective := @Scheme.Hom.app_injective
abbrev reduced_density_bridge := @isSchemeTheoreticallyDominant_iff_isDominant
abbrev dense_open_agreement := @ext_of_isDominant_of_isSeparated
abbrev affine_base_change := @pullbackSpecIso
abbrev glue_maps := @Scheme.Cover.glueMorphisms
abbrev glue_unique := @Scheme.Cover.hom_ext

variable (G : Type*)
abbrev PicOverlap := G × ℤ × ℤ

/-- The overlap automorphism (a,d,n) ↦ (a,d+n,n) from LP-57. -/
def nodalTransition : PicOverlap G ≃ PicOverlap G where
  toFun p := (p.1, p.2.1 + p.2.2, p.2.2)
  invFun p := (p.1, p.2.1 - p.2.2, p.2.2)
  left_inv p := by rcases p with ⟨a,d,n⟩; simp
  right_inv p := by rcases p with ⟨a,d,n⟩; simp

/-- Global compatibility kills degree for every unit coordinate, not a chosen O(1). -/
theorem compatible_degree_zero {G : Type*} (a b : G) (m n : ℤ)
    (h : (a, (0 : ℤ), m) = nodalTransition G (b, 0, n)) : m = 0 ∧ n = 0 := by
  have hn := congrArg (fun p : PicOverlap G => p.2.1) h
  have hm := congrArg (fun p : PicOverlap G => p.2.2) h
  simp only [nodalTransition, Equiv.coe_fn_mk, zero_add] at hn hm
  omega

theorem no_positive_compatible_degree {G : Type*} (a b : G) (m n : ℤ)
    (hm : 0 < m) : (a, (0 : ℤ), m) ≠ nodalTransition G (b, 0, n) := by
  intro h
  have := (compatible_degree_zero a b m n h).1
  omega

end Supplements.LPExtensions

/- LP-63 is now the schematically dense extension of MG-6, with a single
equalizer-ideal argument. The reduced case and embedded-point counterexample
are cited from MG/AL2 rather than reproduced. The sectionwise injectivity
interfaces in this file check its terminal zero-kernel reduction; the general
global equalizer assembly remains a prose argument as before. -/
