import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound

noncomputable section

/-!
# Structural lower bound for the endpoint potential

The logarithmic endpoint potential dominates an explicit even quartic.  This
is the low-even-sector coercivity input used alongside the Legendre gap.
-/

/-- The scaled archimedean potential on the open endpoint interval. -/
def yoshidaEndpointPotential (x : ℝ) : ℝ :=
  -Real.log (1 - x ^ 2) / 2

/-- The first two positive terms forced by the logarithmic potential. -/
def yoshidaEndpointQuartic (x : ℝ) : ℝ :=
  x ^ 2 / 2 + x ^ 4 / 4

/-- Structural pointwise quartic lower bound on the open interval. -/
theorem quartic_le_endpointPotential {x : ℝ} (hx : |x| < 1) :
    yoshidaEndpointQuartic x ≤ yoshidaEndpointPotential x := by
  let R : ℝ → ℝ := fun u ↦ -Real.log (1 - u) - u - u ^ 2 / 2
  have hu0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hu1 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  have hRderiv (u : ℝ) (hu : u < 1) :
      HasDerivAt R (u ^ 2 / (1 - u)) u := by
    have hinner : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) u := by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1
      ring
    have hne : 1 - u ≠ 0 := by linarith
    have hlog := (Real.hasDerivAt_log hne).comp u hinner
    have hpoly := ((hasDerivAt_id u).pow 2).div_const 2
    dsimp only [R]
    convert (hlog.neg.sub (hasDerivAt_id u)).sub hpoly using 1
    simp only [id_eq, Nat.cast_ofNat]
    field_simp [hne]
    ring
  have hRcont : ContinuousOn R (Icc 0 (x ^ 2)) := by
    intro u hu
    exact (hRderiv u (lt_of_le_of_lt hu.2 hu1)).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn R (Icc 0 (x ^ 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (x ^ 2)) hRcont ?_ ?_
    · intro u hu
      exact (hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).differentiableAt
        |>.differentiableWithinAt
    · intro u hu
      rw [(hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).deriv]
      exact div_nonneg (sq_nonneg u) (by linarith [(interior_subset hu).2])
  have hRnonneg : 0 ≤ R (x ^ 2) := by
    have hmono := hRmono (by exact ⟨le_rfl, hu0⟩)
      (by exact ⟨hu0, le_rfl⟩) hu0
    simpa [R] using hmono
  dsimp only [yoshidaEndpointQuartic, yoshidaEndpointPotential]
  dsimp only [R] at hRnonneg
  nlinarith

/-- Integrated potential lower bound on the open endpoint interval.  The
integrability hypotheses make the statement reusable for any eventual form
domain, independently of how that domain proves endpoint integrability. -/
theorem integral_quartic_normSq_le_endpointPotential
    (f : ℝ → ℂ)
    (hquartic : IntegrableOn
      (fun x ↦ yoshidaEndpointQuartic x * Complex.normSq (f x))
        (Ioo (-1) 1) volume)
    (hpotential : IntegrableOn
      (fun x ↦ yoshidaEndpointPotential x * Complex.normSq (f x))
        (Ioo (-1) 1) volume) :
    (∫ x : ℝ in Ioo (-1) 1,
        yoshidaEndpointQuartic x * Complex.normSq (f x) ∂volume) ≤
      ∫ x : ℝ in Ioo (-1) 1,
        yoshidaEndpointPotential x * Complex.normSq (f x) ∂volume := by
  apply setIntegral_mono_on hquartic hpotential measurableSet_Ioo
  intro x hx
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg (f x))
  apply quartic_le_endpointPotential
  rw [abs_lt]
  exact hx

end


end ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
