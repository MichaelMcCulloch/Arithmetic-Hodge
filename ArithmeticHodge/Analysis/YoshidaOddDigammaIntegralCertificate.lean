import ArithmeticHodge.Analysis.YoshidaOddDigammaRationalCertificate
import ArithmeticHodge.Analysis.YoshidaOddDigammaLoss
import ArithmeticHodge.Analysis.YoshidaConstantBounds

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaOddDigammaIntegralCertificate

open DigammaTrapezoid
open YoshidaCoercivityNumerics
open YoshidaOddDigammaLoss
open YoshidaOddDigammaRationalCertificate
open YoshidaConstantBounds
open YoshidaSectionSixAnalytic
open YoshidaTZeroTailBounds
open YoshidaWeightedTailBounds

/-!
# Certified odd low-digamma integral

This module interprets `riemannLossQ_lt_target` as an exact upper Riemann
majorant for the negative part of the quarter-line digamma kernel.  On the
interval from zero to `51 / 25`, monotonicity lets each left endpoint control
one grid cell.  A finite lower partial sum of the convergent digamma series,
together with the certified Euler--Mascheroni upper bound, supplies that
endpoint control.

The resulting theorem proves `LowDigammaHalfIntegralBound` for every Yoshida
zero admitted by the production bounds.  Consequently the actual N = 10 odd
tail low-digamma estimate no longer carries a numerical integration premise.
-/

def partialLowerR (v : ℝ) : ℝ :=
  -(5773 / 10000 : ℝ) -
      shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
    ∑ n ∈ Finset.range seriesCount, quarterDigammaSeriesTerm v n

def gridPointR (j : ℕ) : ℝ :=
  (((j : ℚ) * gridStepQ : ℚ) : ℝ)

def cellLossR (j : ℕ) : ℝ :=
  ((cellLossQ j : ℚ) : ℝ)

theorem coe_shiftedReciprocalQ (v : ℚ) (k : ℕ) :
    ((shiftedReciprocalQ v k : ℚ) : ℝ) =
      shiftedReciprocalRealPart (1 / 4) (((v : ℚ) : ℝ) / 2) k := by
  norm_num [shiftedReciprocalQ, shiftedReciprocalRealPart,
    reciprocalRealPart]

theorem coe_quarterTermQ (v : ℚ) (n : ℕ) :
    ((quarterTermQ v n : ℚ) : ℝ) =
      quarterDigammaSeriesTerm ((v : ℚ) : ℝ) n := by
  rw [quarterTermQ, quarterDigammaSeriesTerm,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one]
  rw [coe_shiftedReciprocalQ]
  norm_num

theorem coe_partialLowerQ (v : ℚ) :
    ((partialLowerQ v : ℚ) : ℝ) = partialLowerR ((v : ℚ) : ℝ) := by
  unfold partialLowerQ partialLowerR
  rw [Rat.cast_add, Rat.cast_sub, Rat.cast_neg, coe_shiftedReciprocalQ]
  norm_num [gammaUpperQ]
  simp_rw [coe_quarterTermQ]

theorem quarterDigammaSeriesTerm_nonneg (v : ℝ) (n : ℕ) :
    0 ≤ quarterDigammaSeriesTerm v n := by
  unfold quarterDigammaSeriesTerm shiftedReciprocalRealPart reciprocalRealPart
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hu : 0 < (1 / 4 : ℝ) + ((n : ℝ) + 1) := by positivity
  have hden : 0 < ((1 / 4 : ℝ) + ((n : ℝ) + 1)) ^ 2 +
      (v / 2) ^ 2 := by positivity
  rw [sub_nonneg, inv_eq_one_div]
  apply (div_le_div_iff₀ hden hm).2
  nlinarith [sq_nonneg (v / 2)]

theorem partialLowerR_le_digammaQuarterVerticalRe (v : ℝ) :
    partialLowerR v ≤ digammaQuarterVerticalRe v := by
  have hgamma : Real.eulerMascheroniConstant < (5773 / 10000 : ℝ) :=
    yoshida_euler_gamma_bounds.2
  have hsum :
      (∑ n ∈ Finset.range seriesCount, quarterDigammaSeriesTerm v n) ≤
        ∑' n : ℕ, quarterDigammaSeriesTerm v n :=
    (summable_quarterDigammaSeriesTerm v).sum_le_tsum
      (Finset.range seriesCount) (fun n hn ↦ quarterDigammaSeriesTerm_nonneg v n)
  unfold digammaQuarterVerticalRe
  rw [digamma_quarter_vertical_re_eq_trapezoid_series]
  unfold partialLowerR
  linarith

def negativeDigammaPart (v : ℝ) : ℝ :=
  max (-digammaQuarterVerticalRe v) 0

theorem coe_cellLossQ (j : ℕ) :
    cellLossR j = max (-partialLowerR (gridPointR j)) 0 := by
  unfold cellLossR cellLossQ gridPointR
  push_cast
  rw [coe_partialLowerQ]
  push_cast
  rfl

theorem coe_riemannLossQ :
    ((riemannLossQ : ℚ) : ℝ) =
      ((gridStepQ : ℚ) : ℝ) *
        ∑ j ∈ Finset.range gridCount, cellLossR j := by
  unfold riemannLossQ cellLossR
  push_cast
  rfl

@[simp] theorem gridPointR_zero : gridPointR 0 = 0 := by
  norm_num [gridPointR]

theorem gridPointR_gridCount : gridPointR gridCount = (51 / 25 : ℝ) := by
  norm_num [gridPointR, gridStepQ, gridEndpointQ, gridCount]

theorem gridPointR_succ_sub (j : ℕ) :
    gridPointR (j + 1) - gridPointR j = ((gridStepQ : ℚ) : ℝ) := by
  norm_num [gridPointR]
  ring

theorem gridPointR_nonneg (j : ℕ) : 0 ≤ gridPointR j := by
  unfold gridPointR gridStepQ gridEndpointQ gridCount
  positivity

theorem gridPointR_mono_step (j : ℕ) :
    gridPointR j ≤ gridPointR (j + 1) := by
  have hstep : (0 : ℝ) ≤ ((gridStepQ : ℚ) : ℝ) := by
    norm_num [gridStepQ, gridEndpointQ, gridCount]
  linarith [gridPointR_succ_sub j]

theorem negativeDigammaPart_le_cellLossR
    {j : ℕ} {v : ℝ}
    (hv : v ∈ Set.Icc (gridPointR j) (gridPointR (j + 1))) :
    negativeDigammaPart v ≤ cellLossR j := by
  have hmono := re_digamma_quarter_vertical_monotoneOn
    (show gridPointR j ∈ Set.Ici (0 : ℝ) by exact gridPointR_nonneg j)
    (show v ∈ Set.Ici (0 : ℝ) by
      exact (gridPointR_nonneg j).trans hv.1)
    hv.1
  change digammaQuarterVerticalRe (gridPointR j) ≤
    digammaQuarterVerticalRe v at hmono
  have hlower := partialLowerR_le_digammaQuarterVerticalRe (gridPointR j)
  rw [coe_cellLossQ]
  unfold negativeDigammaPart
  exact max_le_max (neg_le_neg (hlower.trans hmono)) le_rfl

theorem continuous_negativeDigammaPart : Continuous negativeDigammaPart := by
  unfold negativeDigammaPart
  exact continuous_re_digamma_quarter_vertical.neg.max continuous_const

theorem integral_negativeDigammaPart_cell_le (j : ℕ) :
    (∫ v : ℝ in gridPointR j..gridPointR (j + 1),
      negativeDigammaPart v) ≤
      ((gridStepQ : ℚ) : ℝ) * cellLossR j := by
  calc
    (∫ v : ℝ in gridPointR j..gridPointR (j + 1),
        negativeDigammaPart v) ≤
      ∫ _v : ℝ in gridPointR j..gridPointR (j + 1),
        cellLossR j := by
          exact intervalIntegral.integral_mono_on (gridPointR_mono_step j)
            (continuous_negativeDigammaPart.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _)
            (fun v hv ↦ negativeDigammaPart_le_cellLossR hv)
    _ = (gridPointR (j + 1) - gridPointR j) * cellLossR j := by
      simp
    _ = ((gridStepQ : ℚ) : ℝ) * cellLossR j := by
      rw [gridPointR_succ_sub]

theorem integral_negativeDigammaPart_grid_le :
    (∫ v : ℝ in 0..(51 / 25 : ℝ), negativeDigammaPart v) ≤
      ((riemannLossQ : ℚ) : ℝ) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := negativeDigammaPart) (a := gridPointR) (n := gridCount)
    (μ := volume)
    (fun k hk ↦ continuous_negativeDigammaPart.intervalIntegrable _ _)
  rw [gridPointR_zero, gridPointR_gridCount] at hsum
  rw [← hsum]
  calc
    ∑ j ∈ Finset.range gridCount,
        ∫ v : ℝ in gridPointR j..gridPointR (j + 1),
          negativeDigammaPart v ≤
      ∑ j ∈ Finset.range gridCount,
        ((gridStepQ : ℚ) : ℝ) * cellLossR j := by
          exact Finset.sum_le_sum fun j hj ↦ integral_negativeDigammaPart_cell_le j
    _ = ((riemannLossQ : ℚ) : ℝ) := by
      rw [coe_riemannLossQ, Finset.mul_sum]

theorem integral_digamma_neg_zero_eq_zero_pos (t : ℝ) :
    (∫ v : ℝ in -t..0, digammaQuarterVerticalRe v) =
      ∫ v : ℝ in 0..t, digammaQuarterVerticalRe v := by
  calc
    (∫ v : ℝ in -t..0, digammaQuarterVerticalRe v) =
      ∫ v : ℝ in 0..t, digammaQuarterVerticalRe (-v) := by
        have h := (intervalIntegral.integral_comp_neg
          (f := digammaQuarterVerticalRe) (a := 0) (b := t)).symm
        convert h using 1
        norm_num
    _ = ∫ v : ℝ in 0..t, digammaQuarterVerticalRe v := by
      apply intervalIntegral.integral_congr
      intro v _
      exact digammaQuarterVerticalRe_neg v

theorem half_symmetric_digamma_integral_eq_negativePart
    {tZero : ℝ} (ht : IsYoshidaTZero tZero) :
    -(1 / 2 : ℝ) *
        (∫ v : ℝ in -tZero..tZero, digammaQuarterVerticalRe v) =
      ∫ v : ℝ in 0..tZero, negativeDigammaPart v := by
  have hgInt (a b : ℝ) : IntervalIntegrable digammaQuarterVerticalRe
      volume a b :=
    continuous_re_digamma_quarter_vertical.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgInt (-tZero) 0) (hgInt 0 tZero)
  rw [integral_digamma_neg_zero_eq_zero_pos] at hsplit
  have hsym :
      (∫ v : ℝ in -tZero..tZero, digammaQuarterVerticalRe v) =
        2 * (∫ v : ℝ in 0..tZero, digammaQuarterVerticalRe v) := by
    linarith
  rw [hsym]
  have hneg :
      -(∫ v : ℝ in 0..tZero, digammaQuarterVerticalRe v) =
        ∫ v : ℝ in 0..tZero, negativeDigammaPart v := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht.1.le] at hv
    have habs : |v| ≤ tZero := by
      rw [abs_of_nonneg hv.1]
      exact hv.2
    have hg0 :=
      digammaQuarterVerticalRe_nonpos_of_abs_le_yoshidaTZero ht habs
    unfold negativeDigammaPart
    rw [max_eq_left (neg_nonneg.mpr hg0)]
  rw [← hneg]
  ring

/-- Exact grid certification of the half-integral constant used in the
production odd low-digamma estimate. -/
theorem lowDigammaHalfIntegralBound_of_isYoshidaTZero
    {tZero : ℝ} (ht : IsYoshidaTZero tZero) :
    LowDigammaHalfIntegralBound tZero := by
  have htUpper : tZero ≤ (51 / 25 : ℝ) :=
    yoshidaTZero_le_51_div_25 ht
  have hextend :
      (∫ v : ℝ in 0..tZero, negativeDigammaPart v) ≤
        ∫ v : ℝ in 0..(51 / 25 : ℝ), negativeDigammaPart v := by
    apply intervalIntegral.integral_mono_interval
      (c := 0) (d := (51 / 25 : ℝ)) le_rfl ht.1.le htUpper
    · filter_upwards with v
      exact le_max_right _ _
    · exact continuous_negativeDigammaPart.intervalIntegrable _ _
  have hcertR :
      ((riemannLossQ : ℚ) : ℝ) < (2773 / 1000 : ℝ) := by
    have hq :
        ((riemannLossQ : ℚ) : ℝ) < ((2773 / 1000 : ℚ) : ℝ) :=
      (Rat.cast_lt (K := ℝ)).2 riemannLossQ_lt_target
    norm_num at hq ⊢
    exact hq
  unfold LowDigammaHalfIntegralBound
  rw [half_symmetric_digamma_integral_eq_negativePart ht]
  exact (hextend.trans integral_negativeDigammaPart_grid_le).trans hcertR.le

/-- The N = 10 odd-tail low-digamma estimate with its former numerical
half-integral premise discharged by the exact rational grid certificate. -/
theorem oddTenTail_low_digamma_loss_le_lowIntervalPenalty_of_isYoshidaTZero
    {tZero : ℝ} (ht : IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1) :
    -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) ≤
      lowIntervalPenalty 10 tZero := by
  exact oddTenTail_low_digamma_loss_le_lowIntervalPenalty ht
    (lowDigammaHalfIntegralBound_of_isYoshidaTZero ht) f hf henergy

end ArithmeticHodge.Analysis.YoshidaOddDigammaIntegralCertificate
