import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRawGap

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredParity
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# The exact odd one/three raw-energy gap

This file records the purely algebraic last step in the odd Fourier-tail
argument.  Once the degree-one and degree-three centered Legendre
coefficients satisfy their sharp Fourier-tail bounds, the existing
one/three/tail spectral estimate gives the exact constant `383 / 180`.
-/

/-- The exact `383 / 180` consequence of the centered one/three/tail
estimate.  The two coefficient hypotheses are precisely the Fourier-tail
bounds supplied by frequencies `n ≥ 11`; no slack is introduced in this
algebraic assembly step. -/
theorem centeredRawLogEnergy_ge_three_hundred_eighty_three_div_one_hundred_eighty
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w ^ 2 ≤
      (1 / 10 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2)
    (hthree : centeredOddP3Coefficient w ^ 2 ≤
      (49 / 90 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2) :
    (383 / 180 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w / 4 := by
  have hspectral := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hresidual := integral_centeredOddOneThreeResidual_sq w hwcont
  rw [hresidual] at hspectral
  nlinarith [sq_nonneg (centeredOddP1Coefficient w),
    sq_nonneg (centeredOddP3Coefficient w)]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRawGap
