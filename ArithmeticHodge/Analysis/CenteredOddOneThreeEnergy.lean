import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeThreeL2
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity
import ArithmeticHodge.Analysis.ShiftedLegendreOddOneThreeTail
import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
import ArithmeticHodge.Analysis.YoshidaEndpointOcticTwoModeSchurData

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy

open ShiftedLegendreCenteredLowModeL2
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOddOneThreeTail
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData

noncomputable section

/-!
# Exact centered odd one/three/tail energy decomposition

The degree-one and degree-three centered Legendre coefficients are retained
exactly, while every remaining odd degree is controlled uniformly at the
degree-five harmonic weight.  The result is an infinite spectral estimate;
the only explicit modes are the two modes forced by the fixed octic
potential Schur complement.
-/

def centeredOddP1Coefficient (w : ℝ → ℝ) : ℝ :=
  (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x * centeredP1 x

def centeredOddP3Coefficient (w : ℝ → ℝ) : ℝ :=
  (7 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x * centeredP3 x

def centeredOddOneThreeResidual (w : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  w x - centeredOddP1Coefficient w * centeredP1 x -
    centeredOddP3Coefficient w * centeredP3 x

theorem integral_mul_centeredP1_eq
    (w : ℝ → ℝ) :
    (∫ x : ℝ in -1..1, w x * centeredP1 x) =
      (2 / 3 : ℝ) * centeredOddP1Coefficient w := by
  unfold centeredOddP1Coefficient
  ring

theorem integral_mul_centeredP3_eq
    (w : ℝ → ℝ) :
    (∫ x : ℝ in -1..1, w x * centeredP3 x) =
      (2 / 7 : ℝ) * centeredOddP3Coefficient w := by
  unfold centeredOddP3Coefficient
  ring

theorem integral_centeredOddOneThreeResidual_sq
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1, centeredOddOneThreeResidual w x ^ 2) =
      (∫ x : ℝ in -1..1, w x ^ 2) -
        (2 / 3 : ℝ) * centeredOddP1Coefficient w ^ 2 -
        (2 / 7 : ℝ) * centeredOddP3Coefficient w ^ 2 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  rw [show (fun x : ℝ ↦ centeredOddOneThreeResidual w x ^ 2) = fun x ↦
      w x ^ 2 + (-2 * a) * (w x * centeredP1 x) +
        (-2 * b) * (w x * centeredP3 x) +
        a ^ 2 * centeredP1 x ^ 2 +
        (2 * a * b) * (centeredP1 x * centeredP3 x) +
        b ^ 2 * centeredP3 x ^ 2 by
    funext x
    dsimp only [centeredOddOneThreeResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    exact Continuous.intervalIntegrable (hwcont.pow 2) (-1) 1
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredP1_eq, integral_mul_centeredP3_eq,
    integral_centeredP1_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  dsimp only [a, b]
  ring

theorem repr_centeredPullback_one_sq_eq_coefficient
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2) :
    (shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 1) ^ 2 =
      (1 / 3 : ℝ) * centeredOddP1Coefficient w ^ 2 := by
  rw [shiftedLegendreHilbertBasis_repr_centeredPullback_one_sq w hf]
  unfold centeredOddP1Coefficient centeredP1
  rw [show (∫ x : ℝ in -1..1, w x * x) =
      ∫ x : ℝ in -1..1, x * w x by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring]
  ring

theorem repr_centeredPullback_three_sq_eq_coefficient
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2) :
    (shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 3) ^ 2 =
      (1 / 7 : ℝ) * centeredOddP3Coefficient w ^ 2 := by
  rw [shiftedLegendreHilbertBasis_repr_centeredPullback_three_sq w hf]
  unfold centeredOddP3Coefficient centeredP3
  rw [show (∫ x : ℝ in -1..1,
      w x * ((5 * x ^ 3 - 3 * x) / 2)) =
      (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring]
  ring

theorem centered_odd_one_three_tail_energy_le
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w) :
    (2 / 3 : ℝ) * centeredOddP1Coefficient w ^ 2 +
        (11 / 6 : ℝ) * (2 / 7 : ℝ) * centeredOddP3Coefficient w ^ 2 +
        (137 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredOddOneThreeResidual w x ^ 2) ≤
      centeredRawLogEnergy w / 4 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let F : UnitIntervalL2 := hf.toLp f
  have hparity : ∀ n : ℕ, Even n →
      shiftedLegendreHilbertBasis.repr F n = 0 := by
    intro n hn
    dsimp only [F, f]
    exact centeredPullback_repr_eq_zero_of_odd_of_even w hf hwodd n hn
  have hspectral := odd_one_three_tail_norm_sq_le_of_partialSpectralEnergy_le
    F hparity (unitIntervalLogEnergy f)
      (fun N ↦ partialSpectralEnergy_le_unitIntervalLogEnergy f hf henergy N)
  have hnorm : ‖F‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
    calc
      ‖F‖ ^ 2 = ∫ t : unitInterval, f t ^ 2 :=
        norm_sq_toLp_eq_integral_sq f hf
      _ = _ := integral_unitInterval_centeredPullback_sq w
  have hone : (shiftedLegendreHilbertBasis.repr F 1) ^ 2 =
      (1 / 3 : ℝ) * centeredOddP1Coefficient w ^ 2 := by
    dsimp only [F, f]
    exact repr_centeredPullback_one_sq_eq_coefficient w hf
  have hthree : (shiftedLegendreHilbertBasis.repr F 3) ^ 2 =
      (1 / 7 : ℝ) * centeredOddP3Coefficient w ^ 2 := by
    dsimp only [F, f]
    exact repr_centeredPullback_three_sq_eq_coefficient w hf
  have hresidual := integral_centeredOddOneThreeResidual_sq w hwcont
  have henergyBridge := unitIntervalLogEnergy_centeredPullback w henergy
  rw [hnorm, hone, hthree, henergyBridge] at hspectral
  rw [hresidual]
  norm_num at hspectral ⊢
  linarith

end

end ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
