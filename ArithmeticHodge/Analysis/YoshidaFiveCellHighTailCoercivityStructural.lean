import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
import ArithmeticHodge.Analysis.YoshidaFactorTwoIntegrableLagRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFiveCellHighTailCoercivityStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFiveCellSingleProfileStructural
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointScalarStructuralUpper
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicRankResidualBound
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellWidthPerturbationStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Infinite high-tail coercivity for the five-cell operator

The five-cell prime atom is not sign-definite in either reflection parity.
This file instead pays for its adverse endpoint strip with the exact
shifted-Legendre harmonic gap.  All modes at and above the ninth gap are
controlled simultaneously; no modal enumeration or sampled inequality is
used.
-/

theorem fiveCellOperatorHalfWidth_pos :
    0 < fiveCellOperatorHalfWidth := by
  unfold fiveCellOperatorHalfWidth
  positivity

theorem fiveCellOperatorHalfWidth_lt_three_fifths :
    fiveCellOperatorHalfWidth < (3 / 5 : ℝ) := by
  have hlog := Real.log_two_lt_d9
  unfold fiveCellOperatorHalfWidth
  linarith

theorem two_mul_fiveCellOperatorHalfWidth_le_log_three :
    2 * fiveCellOperatorHalfWidth ≤ Real.log 3 := by
  have hpow : (2 : ℝ) ^ 3 < (3 : ℝ) ^ 2 := by norm_num
  have hlog := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  unfold fiveCellOperatorHalfWidth
  linarith

private theorem fiveCellScalar_eq_clean_add_log_three_halves :
    Real.log (2 * fiveCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi =
      yoshidaEndpointScalarMassLoss + Real.log (3 / 2 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show 2 * fiveCellOperatorHalfWidth =
      (3 / 2 : ℝ) * Real.log 2 by
    unfold fiveCellOperatorHalfWidth
    ring,
    Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) hlogTwo]
  unfold yoshidaEndpointScalarMassLoss
  rw [Real.log_mul Real.pi_ne_zero hlogTwo]
  ring

theorem fiveCellScalar_lt_177_div_100 :
    Real.log (2 * fiveCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      (177 / 100 : ℝ) := by
  rw [fiveCellScalar_eq_clean_add_log_three_halves]
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hshift := strict_log_three_halves_fine_bounds.2
  linarith

theorem fiveCellRegularCorrelation_le_one_fourth_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t) ≤
      (1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let q : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fiveCellOperatorHalfWidth * t)
  have hC : Continuous C := by
    simpa only [C] using
      continuous_centeredEndpointCorrelation_of_continuous w hw
  have hqMeas : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hqBound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ 1 / 4 := by
    intro t ht
    have ha0 : 0 ≤ fiveCellOperatorHalfWidth :=
      fiveCellOperatorHalfWidth_pos.le
    have harg0 : 0 ≤ fiveCellOperatorHalfWidth * t :=
      mul_nonneg ha0 ht.1
    have hargUpper : fiveCellOperatorHalfWidth * t ≤ Real.log 3 := by
      calc
        fiveCellOperatorHalfWidth * t ≤
            fiveCellOperatorHalfWidth * 2 :=
          mul_le_mul_of_nonneg_left ht.2 ha0
        _ = 2 * fiveCellOperatorHalfWidth := by ring
        _ ≤ Real.log 3 := two_mul_fiveCellOperatorHalfWidth_le_log_three
    have hq0 :=
      yoshidaRegularKernel_nonneg_of_le_log_three harg0 hargUpper
    have hq1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [q]
    rw [abs_of_nonneg hq0]
    exact hq1
  have hqC : IntervalIntegrable (fun t ↦ q t * C t) volume 0 2 :=
    intervalIntegrable_boundedLag_mul_continuous q C hqMeas hC (1 / 4)
      hqBound
  have habs : IntervalIntegrable (fun t ↦ |q t * C t|) volume 0 2 :=
    hqC.abs
  have hmajor : IntervalIntegrable (fun t ↦ (1 / 4 : ℝ) * |C t|)
      volume 0 2 := (hC.abs.intervalIntegrable _ _).const_mul (1 / 4)
  have hmono : (∫ t : ℝ in 0..2, |q t * C t|) ≤
      ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habs hmajor
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hqBound t ht) (abs_nonneg (C t))
  rw [intervalIntegral.integral_const_mul] at hmono
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ q t * C t)
      (μ := volume)
  have hL1 := integral_abs_centeredEndpointCorrelation_le_energy w hw
  have hself := le_abs_self (∫ t : ℝ in 0..2, q t * C t)
  simp only [Real.norm_eq_abs] at hnorm
  dsimp only [q, C] at hself hnorm hmono ⊢
  linarith

theorem two_mul_fiveCellWidth_mul_regularCorrelation_le_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * fiveCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t) ≤
      (21 / 80 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hI : I ≤ (1 / 4 : ℝ) * M := by
    simpa only [I, M] using
      fiveCellRegularCorrelation_le_one_fourth_mass w hw
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hwidth0 : 0 ≤ 2 * fiveCellOperatorHalfWidth := by
    exact mul_nonneg (by norm_num) fiveCellOperatorHalfWidth_pos.le
  have hwidth : 2 * fiveCellOperatorHalfWidth < (21 / 20 : ℝ) := by
    have hlog := Real.log_two_lt_d9
    unfold fiveCellOperatorHalfWidth
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hI hwidth0
  have hwidthScaled := mul_le_mul_of_nonneg_right hwidth.le
    (show 0 ≤ (1 / 4 : ℝ) * M by positivity)
  dsimp only [I, M] at hscaled hwidthScaled ⊢
  calc
    _ ≤ 2 * fiveCellOperatorHalfWidth *
        ((1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)) := hscaled
    _ ≤ (21 / 20 : ℝ) *
        ((1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)) :=
      hwidthScaled
    _ = (21 / 80 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by ring

theorem fiveCellBoundaryTail_le_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredEndpointBoundaryTail w (2 / 3 : ℝ) ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  let q : ℝ → ℝ := fun x ↦ w x ^ 2
  have hq : Continuous q := hw.pow 2
  have hleft := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hq.intervalIntegrable (-1 : ℝ) (-1 / 3 : ℝ))
    (hq.intervalIntegrable (-1 / 3 : ℝ) (1 / 3 : ℝ))
  have hright := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hq.intervalIntegrable (-1 : ℝ) (1 / 3 : ℝ))
    (hq.intervalIntegrable (1 / 3 : ℝ) (1 : ℝ))
  have hmiddle : 0 ≤ ∫ x : ℝ in (-1 / 3)..(1 / 3), q x := by
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  unfold centeredEndpointBoundaryTail
  norm_num
  dsimp only [q] at hleft hright hmiddle ⊢
  linarith

theorem fiveCellEndpointPairing_eq_centeredEndpointCorrelation
    (w : ℝ → ℝ) :
    fiveCellEndpointPairing w = centeredEndpointCorrelation w (4 / 3) := by
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun y : ℝ ↦ w y * w (y - 4 / 3))
    (a := (-1 : ℝ)) (b := (-1 / 3 : ℝ)) (4 / 3)
  unfold fiveCellEndpointPairing centeredEndpointCorrelation
  norm_num at hshift ⊢
  simpa only [show (-1 / 3 : ℝ) = -(1 / 3) by ring] using hshift.symm

theorem two_mul_abs_fiveCellEndpointPairing_le_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * |fiveCellEndpointPairing w| ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  have hpair :=
    two_mul_abs_centeredEndpointCorrelation_two_sub_le_boundaryTail
      w hw (t := (2 / 3 : ℝ)) (by norm_num)
  have htail := fiveCellBoundaryTail_le_mass w hw
  rw [fiveCellEndpointPairing_eq_centeredEndpointCorrelation]
  norm_num at hpair ⊢
  exact hpair.trans htail

theorem abs_fiveCellEndpointPairing_le_half_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    |fiveCellEndpointPairing w| ≤
      (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  have h := two_mul_abs_fiveCellEndpointPairing_le_mass w hw
  linarith

theorem sqrt_two_mul_log_two_lt_one :
    Real.sqrt 2 * Real.log 2 < 1 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hratio := factorTwoDyadicWeight_bounds.2
  have heq : Real.sqrt 2 * Real.log 2 =
      2 * (Real.log 2 / Real.sqrt 2) := by
    field_simp [hsqrtPos.ne']
    nlinarith
  rw [heq]
  linarith

theorem fiveCellPrimePairing_le_half_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    Real.sqrt 2 * Real.log 2 * fiveCellEndpointPairing w ≤
      (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let c : ℝ := Real.sqrt 2 * Real.log 2
  let P : ℝ := fiveCellEndpointPairing w
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    exact sqrt_two_mul_log_two_lt_one.le
  have hP : P ≤ |P| := le_abs_self P
  have hPabs : |P| ≤ (1 / 2 : ℝ) * M := by
    simpa only [P, M] using abs_fiveCellEndpointPairing_le_half_mass w hw
  have hM0 : 0 ≤ (1 / 2 : ℝ) * M := by
    dsimp only [M]
    exact mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg (by norm_num)
        (fun _ _ ↦ sq_nonneg _))
  calc
    c * P ≤ c * |P| := mul_le_mul_of_nonneg_left hP hc0
    _ ≤ c * ((1 / 2 : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hPabs hc0
    _ ≤ 1 * ((1 / 2 : ℝ) * M) :=
      mul_le_mul_of_nonneg_right hc1 hM0
    _ = (1 / 2 : ℝ) * M := by ring

theorem fiveCell_sinh_sub_width_lt_one_twentieth :
    Real.sinh fiveCellOperatorHalfWidth - fiveCellOperatorHalfWidth <
      (1 / 20 : ℝ) := by
  let a : ℝ := fiveCellOperatorHalfWidth
  let b : ℝ := 3 / 5
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact fiveCellOperatorHalfWidth_pos.le
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact fiveCellOperatorHalfWidth_lt_three_fifths.le
  have hb0 : 0 ≤ b := by norm_num [b]
  have ha2 : a ^ 2 ≤ b ^ 2 := by
    have hprod : 0 ≤ (b - a) * (b + a) :=
      mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb0 ha0)
    nlinarith
  have ha3 : a ^ 3 ≤ b ^ 3 := by
    have h := mul_le_mul ha2 hab ha0 (sq_nonneg b)
    simpa [pow_succ] using h
  have ha4 : a ^ 4 ≤ b ^ 4 := by
    have h := mul_le_mul ha2 ha2 (sq_nonneg a) (sq_nonneg b)
    convert h using 1 <;> ring
  have ha5 : a ^ 5 ≤ b ^ 5 := by
    have h := mul_le_mul ha4 hab ha0 (by positivity : 0 ≤ b ^ 4)
    simpa [pow_succ] using h
  let u : ℝ := a ^ 2 / 2
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu : u ≤ (9 / 50 : ℝ) := by
    dsimp only [u, b] at ha2 ⊢
    norm_num at ha2 ⊢
    linarith
  have hu1 : u < 1 := hu.trans_lt (by norm_num)
  have hexp : Real.exp u ≤ 1 / (1 - u) :=
    Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - u) ≤ (50 / 41 : ℝ) := by
    rw [div_le_iff₀ (sub_pos.mpr hu1)]
    nlinarith
  have hcosh : Real.cosh a ≤ (5 / 4 : ℝ) := by
    have h := Real.cosh_le_exp_half_sq a
    change Real.cosh a ≤ Real.exp u at h
    exact h.trans (hexp.trans (hfrac.trans (by norm_num)))
  have htaylor := abs_sinh_sub_cubic_le a
  have hupper :
      Real.sinh a - a - a ^ 3 / 6 ≤ Real.cosh a * a ^ 5 / 120 := by
    have hself := le_abs_self (Real.sinh a - a - a ^ 3 / 6)
    have h := hself.trans htaylor
    simpa [abs_of_nonneg ha0] using h
  have hproduct : Real.cosh a * a ^ 5 ≤
      (5 / 4 : ℝ) * b ^ 5 :=
    mul_le_mul hcosh ha5 (by positivity) (by norm_num)
  dsimp only [a, b] at ha3 hupper hproduct ⊢
  norm_num at ha3 hproduct ⊢
  nlinarith

theorem fiveCellCenteredSinhMoment_sq_le
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredSinhMoment w (fiveCellOperatorHalfWidth / 2) ^ 2 ≤
      ((Real.sinh fiveCellOperatorHalfWidth - fiveCellOperatorHalfWidth) /
        fiveCellOperatorHalfWidth) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  have h := normSq_integral_sinh_scaled_le fiveCellOperatorHalfWidth_pos
    (fun x : ℝ ↦ (w x : ℂ)) (by fun_prop)
  have hint :
      (∫ x : ℝ in -1..1,
        (Real.sinh (fiveCellOperatorHalfWidth * x / 2) : ℂ) *
          (w x : ℂ)) =
        (centeredSinhMoment w (fiveCellOperatorHalfWidth / 2) : ℂ) := by
    unfold centeredSinhMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    change (Real.sinh (fiveCellOperatorHalfWidth * x / 2) : ℂ) *
        (w x : ℂ) =
      ((Real.sinh ((fiveCellOperatorHalfWidth / 2) * x) * w x : ℝ) : ℂ)
    rw [show fiveCellOperatorHalfWidth * x / 2 =
      (fiveCellOperatorHalfWidth / 2) * x by ring]
    push_cast
    rfl
  rw [hint] at h
  simpa only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    pow_two, abs_mul_abs_self] using h

theorem two_mul_fiveCellWidth_mul_sinhMoment_sq_le_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * fiveCellOperatorHalfWidth *
        centeredSinhMoment w (fiveCellOperatorHalfWidth / 2) ^ 2 ≤
      (1 / 10 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let a : ℝ := fiveCellOperatorHalfWidth
  let S : ℝ := centeredSinhMoment w (a / 2) ^ 2
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hS : S ≤ ((Real.sinh a - a) / a) * M := by
    simpa only [a, S, M] using fiveCellCenteredSinhMoment_sq_le w hw
  have ha : 0 < a := by
    simpa only [a] using fiveCellOperatorHalfWidth_pos
  have hscaled := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ 2 * a by positivity)
  have hcancel :
      2 * a * (((Real.sinh a - a) / a) * M) =
        2 * (Real.sinh a - a) * M := by
    field_simp [ha.ne']
  rw [hcancel] at hscaled
  have hsmall : 2 * (Real.sinh a - a) ≤ (1 / 10 : ℝ) := by
    dsimp only [a]
    linarith [fiveCell_sinh_sub_width_lt_one_twentieth]
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hsmallScaled := mul_le_mul_of_nonneg_right hsmall hM
  dsimp only [S, M, a] at hscaled hsmallScaled ⊢
  exact hscaled.trans hsmallScaled

theorem fiveCellPolarProduct_nonnegative_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    0 ≤ 2 * fiveCellOperatorHalfWidth *
        (∫ x : ℝ in -1..1,
          Real.exp (-fiveCellOperatorHalfWidth * x / 2) * w x) *
        (∫ x : ℝ in -1..1,
          Real.exp (fiveCellOperatorHalfWidth * x / 2) * w x) := by
  rw [physicalPolarProduct_eq_positiveCoshSquare_of_even
    w hw heven fiveCellOperatorHalfWidth]
  exact mul_nonneg
    (mul_nonneg (by norm_num) fiveCellOperatorHalfWidth_pos.le)
    (sq_nonneg _)

theorem fiveCellPolarProduct_lower_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(1 / 10 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      2 * fiveCellOperatorHalfWidth *
        (∫ x : ℝ in -1..1,
          Real.exp (-fiveCellOperatorHalfWidth * x / 2) * w x) *
        (∫ x : ℝ in -1..1,
          Real.exp (fiveCellOperatorHalfWidth * x / 2) * w x) := by
  have hbound := two_mul_fiveCellWidth_mul_sinhMoment_sq_le_mass w hw
  rw [centeredSinhMoment_eq_two_mul_positive_of_odd w hw hodd] at hbound
  rw [physicalPolarProduct_eq_neg_positiveSinhSquare_of_odd
    w hw hodd fiveCellOperatorHalfWidth]
  nlinarith

/-- The ninth shifted-Legendre gap pays every adverse five-cell term once
the polar rank has its parity-uniform `1/10` mass lower bound. -/
theorem fiveCellEndpointOperator_nonnegative_of_tailNine_of_polarLower
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hlow : centeredLegendreMomentsVanishBelow w 9)
    (hpolar :
      -(1 / 10 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
        2 * fiveCellOperatorHalfWidth *
          (∫ x : ℝ in -1..1,
            Real.exp (-fiveCellOperatorHalfWidth * x / 2) * w x) *
          (∫ x : ℝ in -1..1,
            Real.exp (fiveCellOperatorHalfWidth * x / 2) * w x)) :
    0 ≤ fiveCellEndpointOperator w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let A : ℝ := Real.log (2 * fiveCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let Z : ℝ := fiveCellEndpointPairing w
  let H : ℝ :=
    2 * fiveCellOperatorHalfWidth *
      (∫ x : ℝ in -1..1,
        Real.exp (-fiveCellOperatorHalfWidth * x / 2) * w x) *
      (∫ x : ℝ in -1..1,
        Real.exp (fiveCellOperatorHalfWidth * x / 2) * w x)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    w hw hlocal 9 hlow
  change (harmonic 9 : ℝ) * M ≤ centeredRawLogEnergy w / 4 at hraw
  have hpotential := factorTwoIntrinsicPotentialEnergy_nonneg w
  change 0 ≤ ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * w x ^ 2 at hpotential
  have hA : A ≤ (177 / 100 : ℝ) := by
    dsimp only [A]
    exact fiveCellScalar_lt_177_div_100.le
  have hAScaled := mul_le_mul_of_nonneg_right hA hM
  have hregular :=
    two_mul_fiveCellWidth_mul_regularCorrelation_le_mass w hw
  change 2 * fiveCellOperatorHalfWidth * R ≤ (21 / 80 : ℝ) * M
    at hregular
  have hprime := fiveCellPrimePairing_le_half_mass w hw
  change Real.sqrt 2 * Real.log 2 * Z ≤ (1 / 2 : ℝ) * M at hprime
  change -(1 / 10 : ℝ) * M ≤ H at hpolar
  dsimp only [A, M] at hAScaled
  unfold fiveCellEndpointOperator centeredClippedPhysicalQuadratic
  dsimp only [M, A, R, Z, H] at hraw hpotential hregular hprime hpolar ⊢
  norm_num [harmonic, Finset.sum_range_succ] at hraw
  nlinarith

/-- Reflection-even profiles above the ninth shifted-Legendre gap satisfy
the complete five-cell endpoint operator inequality. -/
theorem fiveCellEndpointOperator_nonnegative_of_even_tailNine
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    0 ≤ fiveCellEndpointOperator w := by
  apply fiveCellEndpointOperator_nonnegative_of_tailNine_of_polarLower
    w hw hlocal hlow
  have hM : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hp := fiveCellPolarProduct_nonnegative_of_even w hw heven
  nlinarith

/-- Reflection-odd profiles above the ninth shifted-Legendre gap satisfy
the complete five-cell endpoint operator inequality, including the negative
sinh rank. -/
theorem fiveCellEndpointOperator_nonnegative_of_odd_tailNine
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    0 ≤ fiveCellEndpointOperator w := by
  exact fiveCellEndpointOperator_nonnegative_of_tailNine_of_polarLower
    w hw hlocal hlow (fiveCellPolarProduct_lower_of_odd w hw hodd)

end

end ArithmeticHodge.Analysis.YoshidaFiveCellHighTailCoercivityStructural
