import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic

/-!
CS-1–CS-6, with Hartshorne's closed immersion and quasi-coherent ideal convention.
IdealSheafData records ideals on every affine chart with localization compatibility;
closedDictionary is the actual anti-equivalence for closed subschemes, not a
point-set correspondence. baseChange compares actual scheme pullbacks. The
image of the pulled-back module ideal is computed by tensorQuotient; the
identification of this algebra equivalence with the sheaf-module image functor
is not packaged here. CS-6 uses the Nullstellensatz and quotient kernel on all
affine charts; the classical variety functor and its comparison to ring sheaves
remain an interface gap. Examples: the zero multiplication after quotient and
the square-zero prime calculation and the actual nonzero class of t modulo t²
are verified; the explicit k[t] module isomorphism I ≅ A is not constructed here.
-/
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
noncomputable section
namespace Supplements.CS

def closedDictionary := @IsClosedImmersion.overEquivIdealSheafData
def affineIdealDictionary := @Scheme.IdealSheafData.equivOfIsAffine
abbrev quotientChart := @Scheme.IdealSheafData.subschemeObjIso
abbrev quotientKernel := @Scheme.IdealSheafData.ker_subschemeι_app
abbrev quotientSurjective := @Scheme.IdealSheafData.subschemeι_app_surjective
abbrev chartLocalization := @Scheme.IdealSheafData.isLocalization_away
abbrev idealRestriction := @Scheme.IdealSheafData.map_ideal
abbrev affineClosed := @IsClosedImmersion.spec_of_surjective
def quotientOfSurjection := @RingHom.quotientKerEquivOfSurjective

def baseChange := @Scheme.IdealSheafData.comapIso
abbrev openRestriction := @Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
def affineTensorQuotient := @Algebra.TensorProduct.quotIdealMapEquivTensorQuot
def pointQuotient := @Polynomial.quotientSpanXSubCAlgEquiv
def tensorQuotient := @Algebra.TensorProduct.tensorQuotientEquiv
abbrev radicalLocalization := @IsLocalization.map_radical
abbrev reducedQuotient := @Ideal.isRadical_iff_quotient_reduced
abbrev radicalSupport := @Scheme.IdealSheafData.support_radical
abbrev recoverRadical := @Scheme.IdealSheafData.vanishingIdeal_support
def reversedInclusion := @Scheme.IdealSheafData.inclusion
abbrev inclusionComposition := @Scheme.IdealSheafData.inclusion_comp
abbrev idealGluingUniqueness := @Scheme.IdealSheafData.ext_of_iSup_eq_top
abbrev classicalVanishing := @MvPolynomial.vanishingIdeal_zeroLocus_eq_radical

/-- CS-4: the affine reduced closed structure is uniquely determined by its point set. -/
theorem radical_ideal_unique {R : Type*} [CommRing R] (I J : Ideal R)
    (hI : I.IsRadical) (hJ : J.IsRadical)
    (h : PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R)) :
    I = J := by
  have hh := congrArg PrimeSpectrum.vanishingIdeal h
  simpa only [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    hI.radical, hJ.radical] using hh

/-- CS-2 example: multiplication by an element killed in the quotient is zero. -/
theorem quotient_multiplication_zero {R : Type*} [CommRing R] (I : Ideal R)
    (t : R) (ht : t ∈ I) (b : R ⧸ I) : Ideal.Quotient.mk I t * b = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht, zero_mul]

/-- CS-4 example: primes cannot distinguish t from t². -/
theorem square_in_prime_iff {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (t : R) : t ^ 2 ∈ p ↔ t ∈ p := by
  constructor
  · exact (inferInstance : p.IsPrime).mem_of_pow_mem 2
  · intro h
    exact p.pow_mem_of_mem h 2 (by omega)

/-- CS-4's actual nonzero square-zero class, over every field. -/
theorem polynomial_thickening {k : Type*} [Field k] :
    let I : Ideal k[X] := Ideal.span {Polynomial.X ^ 2}
    let e := Ideal.Quotient.mk I Polynomial.X
    e ≠ 0 ∧ e ^ 2 = 0 := by
  dsimp
  constructor
  · intro h
    have hd : (Polynomial.X ^ 2 : k[X]) ∣ Polynomial.X :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hn := Polynomial.natDegree_le_of_dvd hd (Polynomial.X_ne_zero (R := k))
    norm_num at hn
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
end Supplements.CS

/- Reader-check annotations now identify the terminal algebraic/topological
inputs in the prose. The mathematical reductions and the verification coverage
of the declarations in this companion are unchanged. -/
