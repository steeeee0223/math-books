import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
RV uses Hartshorne's V(E) = Spec Sym(E), whose sections are E-dual.
The relative gluing interfaces below are actual scheme constructions over a
base, with cartesian chart squares; they are not an assumption that arbitrary
ring-sheaf spectra exist. The quasi-coherent localization data must still be
fed into this gluing object. affineTargetAdjunction, affineModules, and
baseChangeSpectrum check the local universal properties used by RV-1--5.
Their assembly into a single functor on quasi-coherent algebra sheaves, and
the action-retaining module equivalence over a general base, are not yet
packaged in this file. RV-6--7 check the symmetric algebra's actual universal
map, its basis identification, the coordinate formula and double dual.
The gluing of linear transition data and the two fibers of the final
A[z]/(tz) example are described in the prose, not as full bundle objects here.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Supplements.RV

def relativeSchemeGluing := @Scheme.Cover.RelativeGluingData.toBase
abbrev relativeChart := @Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase
abbrev chartPreimage := @Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι
abbrev chartStructuralMap := @Scheme.Cover.RelativeGluingData.ι_toBase

def affineTargetAdjunction := @ΓSpec.adjunction
def affineSpectrumHom := @Spec.homEquiv
abbrev affineSpectrumFaithful := @Spec.map_injective
abbrev glueMaps := @Scheme.Cover.glueMorphisms
abbrev glueRestrictions := @Scheme.Cover.ι_glueMorphisms
abbrev glueUniqueness := @Scheme.Cover.hom_ext

def affineModules := @tildeEquiv
abbrev affineModulePushforward := @isLocalizing_pushforward_of_isLocalizing
abbrev localizedModuleRestrictions := @tilde.toOpen_res
def baseChangeSpectrum := @pullbackSpecIso
abbrev baseChangeFirstMap := @pullbackSpecIso_inv_fst
abbrev baseChangeSecondMap := @pullbackSpecIso_inv_snd

def symmetricUniversal := @SymmetricAlgebra.lift
abbrev symmetricGeneratorFormula := @SymmetricAlgebra.lift_ι_apply
abbrev symmetricUniqueness := @SymmetricAlgebra.algHom_ext
def symmetricPolynomial := @SymmetricAlgebra.equivMvPolynomial
def doubleDual := @Module.evalEquiv

/-- RV-7's affine Hom bijection, in the same direction as the textbook's convention. -/
def sectionsAsDual (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    (SymmetricAlgebra R M →ₐ[R] R) ≃ Module.Dual R M :=
  (SymmetricAlgebra.lift : (M →ₗ[R] R) ≃ (SymmetricAlgebra R M →ₐ[R] R)).symm

/-- RV-6: the transpose in the coordinate formula is forced by linear evaluation. -/
theorem transition_coordinates {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {ι : Type*} [Fintype ι] (e : ι → M) (G : Matrix ι ι R)
    (l : Module.Dual R M) (j : ι) :
    l (∑ i, G i j • e i) = ∑ i, G.transpose j i * l (e i) := by
  simp [map_sum, map_smul, Matrix.transpose_apply]

/-- RV-6: transition cocycles compose in the correct reversed transpose order. -/
theorem transpose_cocycle {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (G H : Matrix ι ι R) : (G * H).transpose = H.transpose * G.transpose :=
  Matrix.transpose_mul G H
end Supplements.RV
