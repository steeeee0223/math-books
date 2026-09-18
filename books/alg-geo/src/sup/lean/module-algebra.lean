import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
AL companion. The following declarations expose the exact algebraic interfaces
used in AL-1–AL-11: no field hypothesis is substituted for a commutative ring,
and no invertibility of 2 is assumed for exterior powers. The latter is why
CliffordAlgebra.BaseChange is not used (its present interface requires 2⁻¹).
The dual-tensor argument is checked for an explicitly given finite dual basis
below, so it applies to projective summands, not only to free modules.
The graded decomposition/filtration is checked through its universal maps and
lift-independence reduction; the assembly into a graded sheaf is not encoded.
-/
open TensorProduct Module
open scoped TensorProduct
noncomputable section
namespace Supplements.AL

abbrev finiteProjectivePresentation := @Module.finitePresentation_of_projective

abbrev noetherianPresentation := @Module.finitePresentation_of_finite

abbrev localizationExact := @LocalizedModule.map_exact

abbrev localizationInjective := @LocalizedModule.map_injective

abbrev localizationSurjective := @LocalizedModule.map_surjective

def localizationTensor := @LocalizedModule.equivTensorProduct

def homLocalization := @Module.FinitePresentation.linearEquivMapExtendScalars

abbrev homLocalizationFormula := @Module.FinitePresentation.linearEquivMapExtendScalars_apply

def tensorHom := @TensorProduct.lift.equiv

def tensorUniversal := @TensorAlgebra.lift

def symmetricUniversal := @SymmetricAlgebra.lift

def exteriorUniversal := @ExteriorAlgebra.lift

def alternatingUniversal := @exteriorPower.alternatingMapLinearEquiv

def tensorQuotient := @TensorProduct.tensorQuotientEquiv

abbrev tensorGeneratorExt := @TensorAlgebra.hom_ext

abbrev symmetricGeneratorExt := @SymmetricAlgebra.algHom_ext

abbrev exteriorGeneratorExt := @ExteriorAlgebra.hom_ext

def tensorPowerBasis := @Basis.piTensorProduct

def symmetricBasis := @SymmetricAlgebra.equivMvPolynomial

def exteriorBasis := @Module.Basis.exteriorPower

abbrev exteriorRank := @exteriorPower.finrank_eq

abbrev exteriorCoordinateDiagonal := @exteriorPower.ιMultiDual_apply_diag

abbrev exteriorCoordinateOffDiagonal := @exteriorPower.ιMultiDual_apply_nondiag

abbrev nakayama := @Submodule.eq_bot_of_le_smul_of_le_jacobson_bot

abbrev spreadIsomorphism := @Module.FinitePresentation.exists_notMem_bijective

abbrev spreadLocalizedIsomorphism := @Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule

abbrev spreadBasisWithSameIndex := @Module.FinitePresentation.exists_basis_localizedModule_powers

abbrev finiteKernel := @Module.FinitePresentation.fg_ker

section DualBasis
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] {ι : Type*} [Fintype ι]
variable (m : ι → M) (l : ι → Module.Dual R M)
  (h : ∀ x, ∑ i, l i x • m i = x)

include h

/-- Finite dual basis reconstruction of any linear map (AL-5). -/
theorem dualBasis_hom (u : M →ₗ[R] N) (x : M) :
    ∑ i, l i x • u (m i) = u x := by
  calc
    _ = u (∑ i, l i x • m i) := by simp only [map_sum, map_smul]
    _ = u x := by rw [h]

/-- The complementary dual basis identity needed by the tensor inverse. -/
theorem dualBasis_functional (q : Module.Dual R M) :
    ∑ i, q (m i) • l i = q := by
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  conv_rhs => rw [← h x]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The other composite of the dual-tensor comparison, on pure tensors. -/
theorem dualBasis_tensor (q : Module.Dual R M) (n : N) :
    ∑ i, l i ⊗ₜ[R] (q (m i) • n) = q ⊗ₜ[R] n := by
  simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [← TensorProduct.sum_tmul, dualBasis_functional m l h q]

/-- Checking the inverse of evaluation uses arbitrary functionals, not a chosen free basis. -/
theorem dualBasis_eval (q : Module.Dual R (Module.Dual R M))
    (f : Module.Dual R M) :
    f (∑ i, q (l i) • m i) = q f := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  conv_rhs => rw [← dualBasis_functional m l h f]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

example [Module.Finite R M] [Module.Projective R M] :
    M ≃ₗ[R] Module.Dual R (Module.Dual R M) := Module.evalEquiv R M
end DualBasis

/-- The polarized square relation: no division by two (AL-6). -/
theorem square_relation {A : Type*} [Ring A] (x y : A)
    (hx : x * x = 0) (hy : y * y = 0) (hxy : (x+y)*(x+y)=0) :
    x*y+y*x=0 := by
  simpa [add_mul, mul_add, hx, hy, add_assoc, add_comm] using hxy

/-- AL-9: changing a lift by a filtration element leaves its quotient class unchanged. -/
theorem quotient_lift_independent {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (F : Submodule R M) (x y : M) (h : x-y ∈ F) :
    F.mkQ x = F.mkQ y := by
  exact (Submodule.Quotient.eq F).mpr h

/-- AL-9's terminal quotient calculation after a splitting of consecutive degrees. -/
def splitFiltrationQuotient (R P Q : Type*) [Ring R] [AddCommGroup P]
    [AddCommGroup Q] [Module R P] [Module R Q] :
    ((P × Q) ⧸ LinearMap.ker (LinearMap.fst R P Q)) ≃ₗ[R] P :=
  (LinearMap.fst R P Q).quotKerEquivOfSurjective (fun p ↦ ⟨(p,0), rfl⟩)

/-- AL-12 and SC-16: the actual residue-field multiplication map is zero. -/
theorem multiplication_two_mod_two (x : ZMod 2) : (2 : ZMod 2) * x = 0 := by
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- AL-13: the coordinate r+1 cannot have an integer numerator with denominator 2^r. -/
theorem unbounded_denominator (r : ℕ) :
    ¬ ∃ a : ℤ, (a : ℚ) / 2^r = 1 / 2^(r+1) := by
  rintro ⟨a, ha⟩
  have h2 : (2 : ℚ)^r ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_succ] at ha
  have he : (a : ℚ) * 2 = 1 := by
    field_simp at ha
    nlinarith
  have he' : a * 2 = 1 := by exact_mod_cast he
  omega

/-- AL-15: the vanishing of the dual, including all linear maps. -/
theorem dual_zmod_two_zero (f : ZMod 2 →ₗ[ℤ] ℤ) : f = 0 := by
  ext x
  have h : (2 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul]
    exact multiplication_two_mod_two x
  have hf := congrArg f h
  simp only [map_smul, map_zero, smul_eq_mul] at hf
  change f x = 0
  omega
/-- AL-11, both tensor factors, over the stated local base ring. -/
theorem tensor_inverse_rank_one (R M N : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : N ⊗[R] M ≃ₗ[R] R) :
    Nonempty (M ≃ₗ[R] R) ∧ Nonempty (N ≃ₗ[R] R) := by
  letI : Module.Invertible R M := Module.Invertible.right e
  letI : Module.Invertible R N := Module.Invertible.right ((TensorProduct.comm R M N).trans e)
  exact ⟨Module.Invertible.free_iff_linearEquiv.mp inferInstance,
    Module.Invertible.free_iff_linearEquiv.mp inferInstance⟩

end Supplements.AL

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
