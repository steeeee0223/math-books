import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Ring

/-!
VS2 links to the companions of DV, PJ2, BU, DF, PM and RM for the
single-source computations in cases 1--9. This file verifies additional
transition identities, both inverse coordinate substitutions in the
incidence chart, and the conic family's central affine elimination and
its actual flat k[t]-algebra structure, with t mapping to xy.

The conic quotient is written k[x,y][t]/(t-xy), the same presentation
as the textbook after ordering variables and multiplying the relation
by -1. `conicChart` checks the quotient by that displayed relation;
`conicBaseMap` records the structure map, not the constant k[t]-action.
The polynomial derivative checks below are the entries of the relative
Jacobian. They are not a proof of smoothness of a glued projective scheme.

Remaining gaps: the global F1 quotient-chart identification; the global
line-bundle and degree comparisons of cases 1--8; the power-map fibers
in case 9; assembling the three affine charts into the conic Proj,
transporting their flatness through scheme locality, the relative
Jacobian criterion on that scheme, and its polarization degrees in
case 10. The topic companions document their own remaining reductions;
the presence of this file must not be counted as complete verification
of all ten cases.
-/

open Polynomial
noncomputable section
namespace Supplements.VS2

variable (k : Type*) [Field k]

abbrev Plane := MvPolynomial (Fin 2) k

def conicBaseMap : k[X] →ₐ[k] Plane k :=
  Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1)

def conicRetraction : Plane k →ₐ[k] k[X] :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.X else 1)

theorem conic_retraction :
    (conicRetraction k).comp (conicBaseMap k) = AlgHom.id k k[X] := by
  ext
  simp [conicRetraction, conicBaseMap]

theorem conic_base_injective : Function.Injective (conicBaseMap k) := by
  intro p q h
  have h' := congrArg (conicRetraction k) h
  simpa only [← AlgHom.comp_apply, conic_retraction, AlgHom.id_apply] using h'

/-- The central chart has the specified nonconstant structure map t ↦ xy. -/
abbrev conicAlgebra : Algebra k[X] (Plane k) := (conicBaseMap k).toRingHom.toAlgebra

theorem conic_flat : letI := conicAlgebra k; Module.Flat k[X] (Plane k) := by
  letI := conicAlgebra k
  haveI : Module.IsTorsionFree k[X] (Plane k) :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 (conic_base_injective k)
  infer_instance

/-- Eliminates t in the actual central chart equation. -/
def conicChart :
    ((Plane k)[X] ⧸ Ideal.span
      ({Polynomial.X - Polynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)} :
        Set (Plane k)[X])) ≃ₐ[Plane k] Plane k :=
  Polynomial.quotientSpanXSubCAlgEquiv _

theorem conic_chart_parameter :
    conicChart k (Ideal.Quotient.mk _ Polynomial.X) =
      MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [conicChart]

/-- The two entries of the central-chart relative Jacobian. -/
theorem conic_partials :
    MvPolynomial.pderiv 0 (MvPolynomial.X 0 * MvPolynomial.X 1 : Plane k) =
      MvPolynomial.X 1 ∧
    MvPolynomial.pderiv 1 (MvPolynomial.X 0 * MvPolynomial.X 1 : Plane k) =
      MvPolynomial.X 0 := by simp

theorem nonzero_conic_parameterization {R : Type*} [CommRing R] (a r s : R) :
    r^2 * (a*s^2) = a * (r*s)^2 := by ring

/-- VS2-5's total-transform factorization, with multiplicity one. -/
theorem line_total_transform {R : Type*} [CommRing R] (x a c : R) :
    a*x-c*x = x*(a-c) := by ring

/-- VS2-3: the chart coordinate map lands in the quadric. -/
theorem quadric_chart {R : Type*} [CommRing R] (x a : R) :
    x*(x*a^2) = (x*a)^2 := by ring

/-- VS2-5: quotient-coordinate transition and inverse on the overlap. -/
theorem ruled_overlap {K : Type*} [Field K] (a x z : K) (ha : a ≠ 0) :
    (a⁻¹*(a*x), z) = (x,z) := by simp [ha]

end Supplements.VS2

/- VS2-1,4,9 now cite the full coordinate/module computations in DV-14,
PJ2-10, and DF-8. Their cross-topic conclusions and reader variations remain.
No mathematical statement or verification boundary changes: this companion
and the cited section companions still check the same terminal calculations. -/
