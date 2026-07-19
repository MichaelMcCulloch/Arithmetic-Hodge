import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCoshSchurStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Endpoint-preserving even cosh Schur reduction

The constant cosh pivot does not preserve the endpoint-zero production
domain.  The normalized seed `1 - x^2` does.  This file proves the exact
homogeneity needed to use that seed and packages the resulting production
Schur reduction.  Its residual is simultaneously even, endpoint-zero, and
zero in the wide-cosh coordinate, so it enters the existing coupled-core
estimate without a separate universal constant-row obligation.
-/

/-- The exact even four-cell bracket, named to expose its homogeneity. -/
def fourCellEvenExactBracket (w : ℝ → ℝ) : ℝ :=
  centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

/-- The one fixed mixed row left after normalizing the endpoint-cosh low
coordinate to the endpoint-zero seed. -/
def fourCellEvenEndpointSeedRow (v : ℝ → ℝ) : ℝ :=
  fourCellExactBracketPolarization fourCellEvenEndpointCoshSeed v

private theorem fourCellPositiveCoshMoment_const_mul
    (c lambda : ℝ) (w : ℝ → ℝ) :
    fourCellPositiveCoshMoment (fun x ↦ c * w x) lambda =
      c * fourCellPositiveCoshMoment w lambda := by
  unfold fourCellPositiveCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (c * w x)) =
      fun x ↦ c * (Real.cosh (lambda * x) * w x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredEndpointCorrelation_const_mul
    (c : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    centeredEndpointCorrelation (fun x ↦ c * w x) t =
      c ^ 2 * centeredEndpointCorrelation w t := by
  unfold centeredEndpointCorrelation
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem fourCellEndpointPairing_const_mul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEndpointPairing (fun x ↦ c * w x) =
      c ^ 2 * fourCellEndpointPairing w := by
  unfold fourCellEndpointPairing
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem centeredClippedPhysicalQuadratic_const_mul
    (a c : ℝ) (w : ℝ → ℝ) :
    centeredClippedPhysicalQuadratic a (fun x ↦ c * w x) =
      c ^ 2 * centeredClippedPhysicalQuadratic a w := by
  have hpotential :
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * (c * w x) ^ 2) =
        c ^ 2 *
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hmass :
      (∫ x : ℝ in -1..1, (c * w x) ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hregular :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (a * t) *
            centeredEndpointCorrelation (fun x ↦ c * w x) t) =
        c ^ 2 *
          ∫ t : ℝ in 0..2,
            yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t := by
    simp_rw [centeredEndpointCorrelation_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hnegative :
      (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * (c * w x)) =
        c * ∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hpositive :
      (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * (c * w x)) =
        c * ∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_const_mul, hpotential, hmass, hregular,
    hnegative, hpositive]
  ring

/-- Exact degree-two homogeneity of the complete production bracket. -/
theorem fourCellEvenExactBracket_const_mul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEvenExactBracket (fun x ↦ c * w x) =
      c ^ 2 * fourCellEvenExactBracket w := by
  unfold fourCellEvenExactBracket
  rw [centeredClippedPhysicalQuadratic_const_mul,
    fourCellEndpointPairing_const_mul]
  ring

private theorem integral_polynomial_five
    (a₀ a₁ a₂ a₃ a₄ a₅ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
          a₃ * (r ^ 4 - l ^ 4) / 4 +
            a₄ * (r ^ 5 - l ^ 5) / 5 +
              a₅ * (r ^ 6 - l ^ 6) / 6 := by
  rw [show (fun x : ℝ ↦
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      fun x ↦ a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 +
        a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 by
    funext x
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem endpointCoshSeed_eq_evenLowProfile :
    fourCellEvenEndpointCoshSeed =
      yoshidaEndpointEvenLowProfile (2 / 3) (-2 / 3) := by
  funext x
  unfold fourCellEvenEndpointCoshSeed yoshidaEndpointEvenLowProfile
    centeredEvenP2
  ring

private theorem integral_endpointCoshSeed_sq :
    (∫ x : ℝ in -1..1, fourCellEvenEndpointCoshSeed x ^ 2) =
      16 / 15 := by
  rw [endpointCoshSeed_eq_evenLowProfile,
    integral_yoshidaEndpointEvenLowProfile_sq]
  norm_num

private theorem centeredRawLogEnergy_endpointCoshSeed :
    centeredRawLogEnergy fourCellEvenEndpointCoshSeed = 16 / 15 := by
  rw [endpointCoshSeed_eq_evenLowProfile,
    centeredRawLogEnergy_yoshidaEndpointEvenLowProfile]
  norm_num

private theorem integral_endpointPotential_mul_endpointCoshSeed_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x ^ 2) =
        188 / 225 - (16 / 15 : ℝ) * Real.log 2 := by
  rw [endpointCoshSeed_eq_evenLowProfile,
    integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq]
  ring

private theorem centeredEndpointCorrelation_endpointCoshSeed (t : ℝ) :
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t =
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellEvenEndpointCoshSeed (t + x) *
        fourCellEvenEndpointCoshSeed x) =
      fun x ↦
        (1 - t ^ 2) + (-2 * t) * x + (t ^ 2 - 2) * x ^ 2 +
          (2 * t) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 by
    funext x
    unfold fourCellEvenEndpointCoshSeed
    ring,
    integral_polynomial_five]
  ring

private theorem centeredEndpointCorrelation_endpointCoshSeed_nonnegative
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t := by
  rw [centeredEndpointCorrelation_endpointCoshSeed]
  have hcube : 0 ≤ (2 - t) ^ 3 := pow_nonneg (sub_nonneg.mpr ht.2) 3
  have hquad : 0 ≤ t ^ 2 + 6 * t + 4 := by
    nlinarith [sq_nonneg t, ht.1]
  have hfactor :
      30 * (16 / 15 - (4 / 3 : ℝ) * t ^ 2 +
        (2 / 3 : ℝ) * t ^ 3 - t ^ 5 / 30) =
          (2 - t) ^ 3 * (t ^ 2 + 6 * t + 4) := by
    ring
  nlinarith [mul_nonneg hcube hquad]

private theorem integral_centeredEndpointCorrelation_endpointCoshSeed :
    (∫ t : ℝ in 0..2,
      centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t) = 8 / 9 := by
  simp_rw [centeredEndpointCorrelation_endpointCoshSeed]
  rw [show (fun t : ℝ ↦
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30) =
      fun t ↦ (16 / 15) + 0 * t + (-4 / 3) * t ^ 2 +
        (2 / 3) * t ^ 3 + 0 * t ^ 4 + (-1 / 30) * t ^ 5 by
    funext t
    ring,
    integral_polynomial_five]
  norm_num

private theorem endpointCoshSeed_regularMoment_le_two_ninths :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t) ≤
      2 / 9 := by
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  have hC : Continuous C := by
    rw [show C = fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30 by
      funext t
      exact centeredEndpointCorrelation_endpointCoshSeed t]
    fun_prop
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
    apply intervalIntegrable_boundedLag_mul_continuous
      (fun t : ℝ ↦ yoshidaRegularKernel (fourCellOperatorHalfWidth * t))
      C (measurable_yoshidaRegularKernel.comp
        (measurable_const.mul measurable_id)) hC (1 / 4)
    intro t ht
    have hwidth0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg hwidth0 ht.1
    have hargUpper : fourCellOperatorHalfWidth * t ≤
        5 * Real.log 2 / 4 := by
      unfold fourCellOperatorHalfWidth
      nlinarith [ht.2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 hargUpper
    rw [abs_of_nonneg hk0]
    exact yoshidaRegularKernel_le_quarter harg0
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 4 : ℝ) * C t) volume 0 2 :=
    (continuous_const.mul hC).intervalIntegrable _ _
  have hmono :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) ≤
        ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    exact mul_le_mul_of_nonneg_right
      (yoshidaRegularKernel_le_quarter harg0)
      (centeredEndpointCorrelation_endpointCoshSeed_nonnegative ht)
  calc
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t) =
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t := rfl
    _ ≤ ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * C t := hmono
    _ = (1 / 4 : ℝ) * ∫ t : ℝ in 0..2, C t := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 / 9 := by
      rw [show (∫ t : ℝ in 0..2, C t) = 8 / 9 by
        simpa only [C] using
          integral_centeredEndpointCorrelation_endpointCoshSeed]
      norm_num

private theorem fourCellEndpointPairing_endpointCoshSeed :
    fourCellEndpointPairing fourCellEvenEndpointCoshSeed = 1616 / 46875 := by
  unfold fourCellEndpointPairing
  rw [show (fun x : ℝ ↦ fourCellEvenEndpointCoshSeed x *
      fourCellEvenEndpointCoshSeed (x - 8 / 5)) =
      fun x ↦ (-39 / 25) + (16 / 5) * x + (14 / 25) * x ^ 2 +
        (-16 / 5) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 by
    funext x
    unfold fourCellEvenEndpointCoshSeed
    ring,
    integral_polynomial_five]
  norm_num

private theorem one_add_sq_div_two_le_cosh {z : ℝ} (hz : 0 ≤ z) :
    1 + z ^ 2 / 2 ≤ Real.cosh z := by
  have hs : z / 2 ≤ Real.sinh (z / 2) :=
    Real.self_le_sinh_iff.mpr (by linarith)
  have hs0 : 0 ≤ Real.sinh (z / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  have hz0 : 0 ≤ z / 2 := by linarith
  have hsSq : (z / 2) ^ 2 ≤ Real.sinh (z / 2) ^ 2 := by
    nlinarith
  have htwo := Real.cosh_two_mul (z / 2)
  have hdiff := Real.cosh_sq_sub_sinh_sq (z / 2)
  rw [show 2 * (z / 2) = z by ring] at htwo
  nlinarith

private theorem endpointCoshSeed_coshMoment_lower :
    2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 ≤
      fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
        (fourCellOperatorHalfWidth / 2) := by
  let p : ℝ → ℝ := fun x ↦
    (1 + ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2) *
      fourCellEvenEndpointCoshSeed x
  let q : ℝ → ℝ := fun x ↦
    Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
      fourCellEvenEndpointCoshSeed x
  have hpCont : Continuous p := by
    dsimp only [p]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      1 + ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2)).mul
        fourCellEvenEndpointCoshSeed_continuous
  have hqCont : Continuous q := by
    dsimp only [q]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.cosh ((fourCellOperatorHalfWidth / 2) * x))).mul
        fourCellEvenEndpointCoshSeed_continuous
  have hp : IntervalIntegrable p volume 0 1 := hpCont.intervalIntegrable _ _
  have hq : IntervalIntegrable q volume 0 1 := hqCont.intervalIntegrable _ _
  have hmono : (∫ x : ℝ in 0..1, p x) ≤ ∫ x : ℝ in 0..1, q x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hp hq
    intro x hx
    have hxSq : x ^ 2 ≤ 1 := by
      nlinarith [hx.1, hx.2, sq_nonneg x]
    have hseed0 : 0 ≤ fourCellEvenEndpointCoshSeed x := by
      unfold fourCellEvenEndpointCoshSeed
      linarith
    have hz0 : 0 ≤ (fourCellOperatorHalfWidth / 2) * x :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) hx.1
    exact mul_le_mul_of_nonneg_right (one_add_sq_div_two_le_cosh hz0) hseed0
  have hpValue : (∫ x : ℝ in 0..1, p x) =
      2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 := by
    dsimp only [p]
    rw [show (fun x : ℝ ↦
        (1 + ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2) *
          fourCellEvenEndpointCoshSeed x) =
        fun x ↦ 1 + 0 * x +
          ((25 * Real.log 2 ^ 2 / 512) - 1) * x ^ 2 +
            0 * x ^ 3 + (-25 * Real.log 2 ^ 2 / 512) * x ^ 4 +
              0 * x ^ 5 by
      funext x
      unfold fourCellEvenEndpointCoshSeed fourCellOperatorHalfWidth
      ring,
      integral_polynomial_five]
    ring
  rw [← hpValue]
  simpa only [q, fourCellPositiveCoshMoment] using hmono

private theorem log_five_four_lt_4463_div_20000 :
    Real.log (5 / 4 : ℝ) < 4463 / 20000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_eq_clean_add_log_five_four :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi =
      yoshidaEndpointScalarMassLoss + Real.log (5 / 4 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show 2 * fourCellOperatorHalfWidth =
      (5 / 4 : ℝ) * Real.log 2 by
    unfold fourCellOperatorHalfWidth
    ring,
    Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  unfold yoshidaEndpointScalarMassLoss
  rw [Real.log_mul Real.pi_ne_zero hlogTwo]
  ring

private theorem fourCellScalar_lt_15787_div_10000 :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      15787 / 10000 := by
  rw [fourCellScalar_eq_clean_add_log_five_four]
  linarith [yoshidaEndpointScalarMassLoss_lt_338887_div_250000,
    log_five_four_lt_4463_div_20000]

private theorem sqrt_two_lt_70711_div_50000 :
    Real.sqrt 2 < (70711 / 50000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  nlinarith

private theorem fourCellEvenExactBracket_endpointCoshSeed_eq :
    fourCellEvenExactBracket fourCellEvenEndpointCoshSeed =
      248 / 225 - (16 / 15 : ℝ) * Real.log 2 -
        (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) * (16 / 15) -
        (5 * Real.log 2 / 4) *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t) +
        5 * Real.log 2 *
          fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
            (fourCellOperatorHalfWidth / 2) ^ 2 -
        Real.sqrt 2 * Real.log 2 * (1616 / 46875) := by
  have hpolar := physicalPolarProduct_eq_positiveCoshSquare_of_even
    fourCellEvenEndpointCoshSeed fourCellEvenEndpointCoshSeed_continuous
      fourCellEvenEndpointCoshSeed_even fourCellOperatorHalfWidth
  unfold fourCellEvenExactBracket centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_endpointCoshSeed,
    integral_endpointPotential_mul_endpointCoshSeed_sq,
    integral_endpointCoshSeed_sq, fourCellEndpointPairing_endpointCoshSeed,
    hpolar]
  unfold fourCellOperatorHalfWidth
  ring

/-- The fixed endpoint-zero cosh seed has strictly positive complete
four-cell bracket.  This is a one-dimensional structural estimate: exact
polynomial moments, the global kernel quarter bound, and the quadratic cosh
minorant suffice. -/
theorem fourCellEvenExactBracket_endpointCoshSeed_pos :
    0 < fourCellEvenExactBracket fourCellEvenEndpointCoshSeed := by
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  let S₁ : ℝ := 15787 / 10000
  let T₁ : ℝ := 70711 / 50000
  let H₀ : ℝ := 2 / 3 + (5 / 768) * L₀ ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  let H : ℝ := fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
    (fourCellOperatorHalfWidth / 2)
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  have hL := strict_log_two_bounds
  have hL0 : L₀ < Real.log 2 := by simpa only [L₀] using hL.1
  have hL1 : Real.log 2 < L₁ := by simpa only [L₁] using hL.2
  have hL0nonneg : 0 ≤ L₀ := by norm_num [L₀]
  have hLnonneg : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hLsq : L₀ ^ 2 ≤ Real.log 2 ^ 2 :=
    (sq_le_sq₀ hL0nonneg hLnonneg).2 hL0.le
  have hHlower :
      2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 ≤ H := by
    simpa only [H] using endpointCoshSeed_coshMoment_lower
  have hH0 : H₀ ≤ H := by
    have hmid : H₀ ≤ 2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 := by
      dsimp only [H₀]
      nlinarith
    exact hmid.trans hHlower
  have hH0nonneg : 0 ≤ H₀ := by
    dsimp only [H₀, L₀]
    positivity
  have hHnonneg : 0 ≤ H := hH0nonneg.trans hH0
  have hHsq : H₀ ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ hH0nonneg hHnonneg).2 hH0
  have hPolar0 : 5 * L₀ * H₀ ^ 2 ≤ 5 * Real.log 2 * H ^ 2 := by
    calc
      5 * L₀ * H₀ ^ 2 ≤ 5 * Real.log 2 * H₀ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL0.le (by norm_num)) (sq_nonneg H₀)
      _ ≤ 5 * Real.log 2 * H ^ 2 := by
        exact mul_le_mul_of_nonneg_left hHsq (by positivity)
  have hR : R ≤ 2 / 9 := by
    simpa only [R] using endpointCoshSeed_regularMoment_le_two_ninths
  have hRscaled : (5 * Real.log 2 / 4) * R ≤
      (5 * L₁ / 4) * (2 / 9) := by
    calc
      (5 * Real.log 2 / 4) * R ≤
          (5 * Real.log 2 / 4) * (2 / 9) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (5 * L₁ / 4) * (2 / 9) := by
        exact mul_le_mul_of_nonneg_right (by linarith [hL1]) (by norm_num)
  have hS : S < S₁ := by
    simpa only [S, S₁] using fourCellScalar_lt_15787_div_10000
  have hSscaled : S * (16 / 15) ≤ S₁ * (16 / 15) :=
    (mul_lt_mul_of_pos_right hS (by norm_num)).le
  have hLscaled : (16 / 15 : ℝ) * Real.log 2 ≤
      (16 / 15) * L₁ :=
    mul_le_mul_of_nonneg_left hL1.le (by norm_num)
  have hTL : Real.sqrt 2 * Real.log 2 ≤ T₁ * L₁ := by
    calc
      Real.sqrt 2 * Real.log 2 ≤ T₁ * Real.log 2 :=
        mul_le_mul_of_nonneg_right
          (by simpa only [T₁] using sqrt_two_lt_70711_div_50000.le)
          hLnonneg
      _ ≤ T₁ * L₁ :=
        mul_le_mul_of_nonneg_left hL1.le (by norm_num [T₁])
  have hPrime : Real.sqrt 2 * Real.log 2 * (1616 / 46875) ≤
      T₁ * L₁ * (1616 / 46875) :=
    mul_le_mul_of_nonneg_right hTL (by norm_num)
  have hrat :
      0 < 248 / 225 - (16 / 15 : ℝ) * L₁ -
          S₁ * (16 / 15) - (5 * L₁ / 4) * (2 / 9) +
          5 * L₀ * H₀ ^ 2 - T₁ * L₁ * (1616 / 46875) := by
    norm_num [L₀, L₁, S₁, T₁, H₀]
  rw [fourCellEvenExactBracket_endpointCoshSeed_eq]
  dsimp only [R, H, S] at hRscaled hPolar0 hSscaled ⊢
  linarith

/-- The endpoint-adapted low component is a scalar multiple of the fixed
endpoint-zero seed, rather than a constant function. -/
theorem fourCellEvenEndpointCoshLow_eq_const_mul_seed (w : ℝ → ℝ) :
    fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit =
      fun x ↦
        (fourCellPositiveCoshMoment w (fourCellOperatorHalfWidth / 2) *
          (fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
            (fourCellOperatorHalfWidth / 2))⁻¹) *
          fourCellEvenEndpointCoshSeed x := by
  funext x
  unfold fourCellEvenCoshLow fourCellEvenEndpointCoshUnit
  ring

/-- Positivity of the one fixed endpoint seed propagates to every low line
selected by the endpoint-preserving cosh coordinate. -/
theorem fourCellEvenExactBracket_endpointCoshLow_nonnegative
    (w : ℝ → ℝ)
    (hseed : 0 ≤ fourCellEvenExactBracket fourCellEvenEndpointCoshSeed) :
    0 ≤ fourCellEvenExactBracket
      (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit) := by
  rw [fourCellEvenEndpointCoshLow_eq_const_mul_seed,
    fourCellEvenExactBracket_const_mul]
  exact mul_nonneg (sq_nonneg _) hseed

/-- Production-only endpoint-cosh Schur reduction.  The tail hypothesis is
the existing coupled-core target on the endpoint-zero, zero-cosh residual;
the only other profile-dependent obligation is its exact mixed determinant.
-/
theorem fourCell_evenBracket_nonnegative_of_endpointCoshSchur
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hweven : Function.Even w) (hend : w (-1) = 0 ∧ w 1 = 0)
    (hseed : 0 ≤ fourCellEvenExactBracket fourCellEvenEndpointCoshSeed)
    (hcore : (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit))
    (hdet : fourCellExactBracketPolarization
          (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit)
          (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit) ^ 2 ≤
        fourCellEvenExactBracket
            (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit) *
          fourCellEvenPolarFreeOperator
            (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit)) :
    0 ≤ fourCellEvenExactBracket w := by
  let v : ℝ → ℝ :=
    fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit
  have hv : Continuous v :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).1
  have hveven : Function.Even v :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).2.1
  have hvzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0 :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).2.2.2
  have hvDiff : ContDiff ℝ 1 v := by
    dsimp only [v]
    unfold fourCellEvenCoshResidual fourCellEvenCoshLow
      fourCellEvenEndpointCoshUnit fourCellEvenEndpointCoshSeed
    fun_prop
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hvDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  have htail : 0 ≤ fourCellEvenPolarFreeOperator v := by
    apply fourCellEvenPolarFreeOperator_nonnegative_of_coupledCore
      v hv hvLocal hveven hvzero
    simpa only [v] using hcore
  apply fourCell_evenBracket_nonnegative_of_normalizedCoshSchur
    w fourCellEvenEndpointCoshUnit hw.continuous
      fourCellEvenEndpointCoshUnit_continuous hweven
      fourCellEvenEndpointCoshUnit_even hvLocal
      fourCellPositiveCoshMoment_endpointCoshUnit
  · simpa only [fourCellEvenExactBracket] using
      fourCellEvenExactBracket_endpointCoshLow_nonnegative w hseed
  · simpa only [v] using htail
  · simpa only [fourCellEvenExactBracket, v] using hdet

/-- Final endpoint-adapted interface with the fixed low pivot discharged.
Compared with the constant split, only the zero-cosh endpoint residual core
and its one exact endpoint-seed mixed determinant remain. -/
theorem fourCell_evenBracket_nonnegative_of_endpointCoshCoreSchur
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hweven : Function.Even w) (hend : w (-1) = 0 ∧ w 1 = 0)
    (hcore : (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit))
    (hdet : fourCellExactBracketPolarization
          (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit)
          (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit) ^ 2 ≤
        fourCellEvenExactBracket
            (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit) *
          fourCellEvenPolarFreeOperator
            (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit)) :
    0 ≤ fourCellEvenExactBracket w := by
  exact fourCell_evenBracket_nonnegative_of_endpointCoshSchur
    w hw hweven hend fourCellEvenExactBracket_endpointCoshSeed_pos.le
      hcore hdet

/-- Universal fixed-row closure for the endpoint-preserving cosh split.

The variable low coefficient is removed by normalizing the *whole* profile,
not by separately polarizing every kernel term.  If the coefficient vanishes,
the profile is already a zero-cosh residual.  Otherwise quadratic homogeneity
reduces it to `seed + residual / coefficient`, so the only mixed functional
that ever occurs is `fourCellEvenEndpointSeedRow`. -/
theorem fourCell_evenBracket_nonnegative_of_endpointSeedUniversalSchur
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hweven : Function.Even w) (hend : w (-1) = 0 ∧ w 1 = 0)
    (hcore : ∀ v : ℝ → ℝ,
      ContDiff ℝ 1 v → Function.Even v →
      v (-1) = 0 ∧ v 1 = 0 →
      fourCellPositiveCoshMoment v
          (fourCellOperatorHalfWidth / 2) = 0 →
      (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, v x ^ 2) ≤
        fourCellEvenZeroCoshCoupledCore v)
    (hrow : ∀ v : ℝ → ℝ,
      ContDiff ℝ 1 v → Function.Even v →
      v (-1) = 0 ∧ v 1 = 0 →
      fourCellPositiveCoshMoment v
          (fourCellOperatorHalfWidth / 2) = 0 →
      fourCellEvenEndpointSeedRow v ^ 2 ≤
        fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          fourCellEvenPolarFreeOperator v) :
    0 ≤ fourCellEvenExactBracket w := by
  let c : ℝ :=
    fourCellPositiveCoshMoment w (fourCellOperatorHalfWidth / 2) *
      (fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
        (fourCellOperatorHalfWidth / 2))⁻¹
  let v : ℝ → ℝ :=
    fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit
  have hvConstraints :=
    fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend
  have hv : Continuous v := by
    simpa only [v] using hvConstraints.1
  have hveven : Function.Even v := by
    simpa only [v] using hvConstraints.2.1
  have hvend : v (-1) = 0 ∧ v 1 = 0 := by
    simpa only [v] using hvConstraints.2.2.1
  have hvzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0 := by
    simpa only [v] using hvConstraints.2.2.2
  have hvDiff : ContDiff ℝ 1 v := by
    dsimp only [v]
    unfold fourCellEvenCoshResidual fourCellEvenCoshLow
      fourCellEvenEndpointCoshUnit fourCellEvenEndpointCoshSeed
    fun_prop
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hvDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  have hlow : fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit =
      fun x ↦ c * fourCellEvenEndpointCoshSeed x := by
    simpa only [c] using fourCellEvenEndpointCoshLow_eq_const_mul_seed w
  by_cases hc : c = 0
  · have hvw : v = w := by
      funext x
      dsimp only [v]
      unfold fourCellEvenCoshResidual
      rw [hlow]
      simp only [hc, zero_mul, sub_zero]
    have htail : 0 ≤ fourCellEvenPolarFreeOperator v := by
      apply fourCellEvenPolarFreeOperator_nonnegative_of_coupledCore
        v hv hvLocal hveven hvzero
      exact hcore v hvDiff hveven hvend hvzero
    have hdiag := fourCell_evenBracket_eq_polarFree_add_coshRank
      v hv hvLocal hveven
    rw [hvzero] at hdiag
    norm_num at hdiag
    rw [← hvw]
    simpa only [fourCellEvenExactBracket, hdiag] using htail
  · let r : ℝ → ℝ := fun x ↦ c⁻¹ * v x
    have hrDiff : ContDiff ℝ 1 r := by
      dsimp only [r]
      fun_prop
    have hr : Continuous r := hrDiff.continuous
    have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r :=
      hrDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
    have hreven : Function.Even r := by
      intro x
      dsimp only [r]
      rw [hveven x]
    have hrend : r (-1) = 0 ∧ r 1 = 0 := by
      dsimp only [r]
      rw [hvend.1, hvend.2]
      simp
    have hrzero : fourCellPositiveCoshMoment r
        (fourCellOperatorHalfWidth / 2) = 0 := by
      dsimp only [r]
      rw [fourCellPositiveCoshMoment_const_mul, hvzero]
      ring
    have htail : 0 ≤ fourCellEvenPolarFreeOperator r := by
      apply fourCellEvenPolarFreeOperator_nonnegative_of_coupledCore
        r hr hrLocal hreven hrzero
      exact hcore r hrDiff hreven hrend hrzero
    have hdiag := fourCell_evenBracket_eq_polarFree_add_coshRank
      r hr hrLocal hreven
    rw [hrzero] at hdiag
    norm_num at hdiag
    have htailBracket : 0 ≤ fourCellEvenExactBracket r := by
      simpa only [fourCellEvenExactBracket, hdiag] using htail
    have hdet := hrow r hrDiff hreven hrend hrzero
    have hdetBracket : fourCellExactBracketPolarization
          fourCellEvenEndpointCoshSeed r ^ 2 ≤
        fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          fourCellEvenExactBracket r := by
      simpa only [fourCellEvenEndpointSeedRow, fourCellEvenExactBracket,
        hdiag] using hdet
    have hseedPlus : 0 ≤ fourCellEvenExactBracket
        (fourCellEvenEndpointCoshSeed + r) := by
      apply fourCell_evenBracket_add_nonnegative_of_exactSchur
        fourCellEvenEndpointCoshSeed r
          fourCellEvenEndpointCoshSeed_continuous hr
      · exact fourCellEvenExactBracket_endpointCoshSeed_pos.le
      · exact htailBracket
      · simpa only [fourCellEvenExactBracket] using hdetBracket
    have hwScale : w = fun x ↦
        c * (fourCellEvenEndpointCoshSeed + r) x := by
      funext x
      have hdecomp := congrFun
        (fourCellEvenCoshResidual_decomposition
          w fourCellEvenEndpointCoshUnit) x
      rw [hlow] at hdecomp
      simp only [Pi.add_apply] at hdecomp ⊢
      dsimp only [r]
      calc
        w x = c * fourCellEvenEndpointCoshSeed x + v x := hdecomp.symm
        _ = c * (fourCellEvenEndpointCoshSeed x + c⁻¹ * v x) := by
          field_simp [hc]
    rw [hwScale, fourCellEvenExactBracket_const_mul]
    exact mul_nonneg (sq_nonneg c) hseedPlus

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCoshSchurStructural
