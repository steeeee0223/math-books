import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
QC-1 and QC-7's existing proofs are verified in ii-5-exe.lean. The affine
comparison below bridges mathlib's local-free-presentation definition of
quasi-coherence with Hartshorne's associated-module definition.
QC-2 uses the actual adjunction to ALL module sheaves. QC-3 uses finite
presentation only for localization; QC-4 uses finite freeness, not finite
presentation, for arbitrary base change. QC-5's finite Cech equalizer is
checked through localizationExact and finiteProductLocalization. The
identification of those algebraic maps with the full qcqs pushforward and
its overlap restriction maps is not yet packaged as a global theorem.
Likewise coherent closure is checked at finite modules over Noetherian
rings; no differently defined sheaf-coherence class is substituted.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
noncomputable section
namespace Supplements.QC

def affineEquivalence := @tildeEquiv
abbrev affineComparison := @isQuasicoherent_iff_isIso_fromTildeΓ
def ambientAdjunction := @tilde.adjunction
abbrev adjointColimits := @Adjunction.leftAdjoint_preservesColimits
abbrev tildeBasisRestriction := @tilde.toOpen_res
abbrev localizationCriterion := @isIso_fromTildeΓ_iff_isLocalizing
abbrev homLocalization := @Module.FinitePresentation.linearEquivMapExtendScalars
abbrev homLocalizationFormula := @Module.FinitePresentation.linearEquivMapExtendScalars_apply
abbrev localizationExact := @IsLocalizedModule.map_exact
abbrev finiteProductLocalization := @IsLocalizedModule.pi
abbrev affinePushforward := @isLocalizing_pushforward_of_isLocalizing
def finiteFreeDualHom := @dualTensorHomEquiv
def finiteFreeTensor := @TensorProduct.piScalarRight
abbrev finiteFreeTensorFormula := @TensorProduct.piScalarRightHom_tmul
abbrev finitePresentation := @Module.finitePresentation_of_finite
abbrev finiteRestrictionOfScalars := @Module.Finite.trans
abbrev finiteKernel := @Module.FinitePresentation.fg_ker

/-- QC-5's equalizer is the kernel of the difference of restriction maps. -/
theorem equalizer_as_kernel {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (u v : M →ₗ[R] N) (x : M) : x ∈ LinearMap.ker (u-v) ↔ u x = v x := by
  simp [sub_eq_zero]

/-- QC-E3: every integral linear map from Z/2 to Z vanishes. -/
theorem hom_mod_two_zero (f : ZMod 2 →ₗ[ℤ] ℤ) : f = 0 := by
  ext x
  have h : (2 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul]
    change (2 : ZMod 2) * x = 0
    rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  have hh := congrArg f h
  simp only [map_smul, map_zero, smul_eq_mul] at hh
  change f x = 0
  omega

/-- The target in QC-E3 is nonzero (the identity survives base change). -/
theorem hom_mod_two_nonzero : (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) ≠ 0 := by
  intro h
  have := congrArg (fun f : ZMod 2 →ₗ[ZMod 2] ZMod 2 => f 1) h
  norm_num at this

/-- QC-E1: no common power of two represents the proposed tuple. -/
theorem no_uniform_denominator (r : ℕ) :
    ¬ ∃ a : ℤ, (a : ℚ) / 2^r = 1 / 2^(r+1) := by
  rintro ⟨a, ha⟩
  rw [pow_succ] at ha
  have he : (a : ℚ) * 2 = 1 := by
    field_simp at ha
    nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) r]
  have he' : a * 2 = 1 := by exact_mod_cast he
  omega
end Supplements.QC
