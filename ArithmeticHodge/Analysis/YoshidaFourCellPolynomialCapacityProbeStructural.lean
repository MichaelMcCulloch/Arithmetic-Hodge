import ArithmeticHodge.Analysis.YoshidaFourCellEndpointSquareStructural
import ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelSquareStructural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialEvenMomentStructural
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
import ArithmeticHodge.Analysis.YoshidaConstantBounds

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellPolynomialCapacityProbeStructural

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialEvenMomentStructural
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScalarStructuralUpper
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoEndpointClean
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaFourCellEndpointSquareStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaRegularKernelBound

noncomputable section

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_polynomial_thirteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10 + a₁₁ * x ^ 11 +
            a₁₂ * x ^ 12 + a₁₃ * x ^ 13) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                  a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                    a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                      a₁₃ * (r ^ 14 - l ^ 14) / 14 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-!
# Structural polynomial probes of four-cell endpoint capacity

The two lowest endpoint-zero parity profiles are evaluated exactly in every
singular, scalar, and retained-prime coordinate.  The only terms left
unevaluated are the smooth regular-kernel and hyperbolic ranks.
-/

/-- Lowest even endpoint-zero polynomial profile. -/
def fourCellPolynomialEven (x : ℝ) : ℝ := 1 - x ^ 2

/-- Lowest odd endpoint-zero polynomial profile. -/
def fourCellPolynomialOdd (x : ℝ) : ℝ := x * (1 - x ^ 2)

theorem fourCellPolynomialEven_continuous : Continuous fourCellPolynomialEven := by
  unfold fourCellPolynomialEven
  fun_prop

theorem fourCellPolynomialOdd_continuous : Continuous fourCellPolynomialOdd := by
  unfold fourCellPolynomialOdd
  fun_prop

theorem fourCellPolynomialEven_even : Function.Even fourCellPolynomialEven := by
  intro x
  unfold fourCellPolynomialEven
  ring

theorem fourCellPolynomialOdd_odd : Function.Odd fourCellPolynomialOdd := by
  intro x
  unfold fourCellPolynomialOdd
  ring

@[simp] theorem fourCellPolynomialEven_neg_one : fourCellPolynomialEven (-1) = 0 := by
  norm_num [fourCellPolynomialEven]

@[simp] theorem fourCellPolynomialEven_one : fourCellPolynomialEven 1 = 0 := by
  norm_num [fourCellPolynomialEven]

@[simp] theorem fourCellPolynomialOdd_neg_one : fourCellPolynomialOdd (-1) = 0 := by
  norm_num [fourCellPolynomialOdd]

@[simp] theorem fourCellPolynomialOdd_one : fourCellPolynomialOdd 1 = 0 := by
  norm_num [fourCellPolynomialOdd]

theorem fourCellPolynomialEven_eq_lowProfile :
    fourCellPolynomialEven = yoshidaEndpointEvenLowProfile (2 / 3) (-2 / 3) := by
  funext x
  unfold fourCellPolynomialEven yoshidaEndpointEvenLowProfile centeredEvenP2
  ring

theorem fourCellPolynomialOdd_eq_lowProfile :
    fourCellPolynomialOdd = factorTwoOddStructuralLowProfile (2 / 5) (-2 / 5) := by
  funext x
  unfold fourCellPolynomialOdd factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem integral_fourCellPolynomialEven_sq :
    (∫ x : ℝ in -1..1, fourCellPolynomialEven x ^ 2) = 16 / 15 := by
  rw [fourCellPolynomialEven_eq_lowProfile,
    integral_yoshidaEndpointEvenLowProfile_sq]
  norm_num

theorem integral_fourCellPolynomialOdd_sq :
    (∫ x : ℝ in -1..1, fourCellPolynomialOdd x ^ 2) = 16 / 105 := by
  rw [show (fun x : ℝ ↦ fourCellPolynomialOdd x ^ 2) =
      fun x ↦ 0 * x ^ 0 + 0 * x ^ 1 + 1 * x ^ 2 + 0 * x ^ 3 + (-2) * x ^ 4 +
        0 * x ^ 5 + 1 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 +
          0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialOdd
    ring,
    integral_polynomial_ten]
  norm_num

theorem centeredRawLogEnergy_fourCellPolynomialEven :
    centeredRawLogEnergy fourCellPolynomialEven = 16 / 15 := by
  rw [fourCellPolynomialEven_eq_lowProfile,
    centeredRawLogEnergy_yoshidaEndpointEvenLowProfile]
  norm_num

theorem centeredRawLogEnergy_fourCellPolynomialOdd :
    centeredRawLogEnergy fourCellPolynomialOdd = 16 / 21 := by
  rw [fourCellPolynomialOdd_eq_lowProfile,
    centeredRawLogEnergy_factorTwoOddStructuralLowProfile]
  norm_num

theorem centeredEndpointCorrelation_fourCellPolynomialEven (t : ℝ) :
    centeredEndpointCorrelation fourCellPolynomialEven t =
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellPolynomialEven (t + x) * fourCellPolynomialEven x) =
      fun x ↦ (1 - t ^ 2) * x ^ 0 + (-2 * t) * x ^ 1 +
        (t ^ 2 - 2) * x ^ 2 + (2 * t) * x ^ 3 + 1 * x ^ 4 +
          0 * x ^ 5 + 0 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 +
            0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialEven
    ring,
    integral_polynomial_ten]
  ring

theorem centeredEndpointCorrelation_fourCellPolynomialOdd (t : ℝ) :
    centeredEndpointCorrelation fourCellPolynomialOdd t =
      16 / 105 - (4 / 5 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 10 + t ^ 7 / 140 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellPolynomialOdd (t + x) * fourCellPolynomialOdd x) =
      fun x ↦ 0 * x ^ 0 + (t - t ^ 3) * x ^ 1 +
        (1 - 3 * t ^ 2) * x ^ 2 + (t ^ 3 - 4 * t) * x ^ 3 +
          (3 * t ^ 2 - 2) * x ^ 4 + (3 * t) * x ^ 5 + 1 * x ^ 6 +
            0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialOdd
    ring,
    integral_polynomial_ten]
  ring

theorem integral_centeredEndpointCorrelation_fourCellPolynomialEven :
    (∫ t : ℝ in 0..2,
      centeredEndpointCorrelation fourCellPolynomialEven t) = 8 / 9 := by
  simp_rw [centeredEndpointCorrelation_fourCellPolynomialEven]
  rw [show (fun t : ℝ ↦
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30) =
      fun t ↦ (16 / 15) * t ^ 0 + 0 * t ^ 1 + (-4 / 3) * t ^ 2 +
        (2 / 3) * t ^ 3 + 0 * t ^ 4 + (-1 / 30) * t ^ 5 +
          0 * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 + 0 * t ^ 10 by
    funext t
    ring,
    integral_polynomial_ten]
  norm_num

/-- Oddness annihilates the constant regular-kernel coordinate exactly. -/
theorem integral_centeredEndpointCorrelation_fourCellPolynomialOdd :
    (∫ t : ℝ in 0..2,
      centeredEndpointCorrelation fourCellPolynomialOdd t) = 0 := by
  simp_rw [centeredEndpointCorrelation_fourCellPolynomialOdd]
  rw [show (fun t : ℝ ↦
      16 / 105 - (4 / 5 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 10 + t ^ 7 / 140) =
      fun t ↦ (16 / 105) * t ^ 0 + 0 * t ^ 1 + (-4 / 5) * t ^ 2 +
        (2 / 3) * t ^ 3 + 0 * t ^ 4 + (-1 / 10) * t ^ 5 +
          0 * t ^ 6 + (1 / 140) * t ^ 7 + 0 * t ^ 8 +
            0 * t ^ 9 + 0 * t ^ 10 by
    funext t
    ring,
    integral_polynomial_ten]
  norm_num

/-- Exact sixth-order regular-kernel envelope moment on the part of the odd
correlation where the envelope is valid. -/
theorem integral_regularPolynomial6_mul_fourCellPolynomialOdd_correlation :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellPolynomialOdd t) =
      8672 / 13671875 + (223556 / 369140625 : ℝ) * Real.log 2 +
        (159892 / 205078125 : ℝ) * Real.log 2 ^ 2 -
          (827027 / 69609375000 : ℝ) * Real.log 2 ^ 3 -
            (4943 / 98437500 : ℝ) * Real.log 2 ^ 4 +
              (317938573 / 1596282187500000 : ℝ) * Real.log 2 ^ 5 +
                (4207109 / 1240312500000 : ℝ) * Real.log 2 ^ 6 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellPolynomialOdd t) =
      fun t ↦
        (4 / 105) * t ^ 0 +
        (-(1 / 504) * Real.log 2) * t ^ 1 +
        (-(1 / 5) - (5 / 2688) * Real.log 2 ^ 2) * t ^ 2 +
        (1 / 6 + (1 / 96) * Real.log 2 +
          (5 / 221184) * Real.log 2 ^ 3) * t ^ 3 +
        (-(5 / 576) * Real.log 2 + (5 / 512) * Real.log 2 ^ 2 +
          (625 / 8257536) * Real.log 2 ^ 4) * t ^ 4 +
        (-(1 / 40) - (25 / 3072) * Real.log 2 ^ 2 -
          (35 / 294912) * Real.log 2 ^ 3 -
            (3875 / 16647192576) * Real.log 2 ^ 5) * t ^ 5 +
        ((1 / 768) * Real.log 2 + (175 / 1769472) * Real.log 2 ^ 3 -
          (625 / 1572864) * Real.log 2 ^ 4 -
            (38125 / 12683575296) * Real.log 2 ^ 6) * t ^ 6 +
        (1 / 560 + (5 / 4096) * Real.log 2 ^ 2 +
          (3125 / 9437184) * Real.log 2 ^ 4 +
            (3875 / 3170893824) * Real.log 2 ^ 5) * t ^ 7 +
        (-(1 / 10752) * Real.log 2 - (35 / 2359296) * Real.log 2 ^ 3 -
          (19375 / 19025362944) * Real.log 2 ^ 5 +
            (38125 / 2415919104) * Real.log 2 ^ 6) * t ^ 8 +
        (-(5 / 57344) * Real.log 2 ^ 2 -
          (625 / 12582912) * Real.log 2 ^ 4 -
            (190625 / 14495514624) * Real.log 2 ^ 6) * t ^ 9 +
        ((5 / 4718592) * Real.log 2 ^ 3 +
          (3875 / 25367150592) * Real.log 2 ^ 5) * t ^ 10 +
        ((625 / 176160768) * Real.log 2 ^ 4 +
          (38125 / 19327352832) * Real.log 2 ^ 6) * t ^ 11 +
        (-(3875 / 355140108288) * Real.log 2 ^ 5) * t ^ 12 +
        (-(38125 / 270582939648) * Real.log 2 ^ 6) * t ^ 13 by
    funext t
    rw [centeredEndpointCorrelation_fourCellPolynomialOdd]
    unfold yoshidaRegularKernelPolynomial6
    ring,
    integral_polynomial_thirteen]
  ring

theorem integral_regularPolynomial6_mul_fourCellPolynomialOdd_correlation_le :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellPolynomialOdd t) ≤
      (143 / 100000 : ℝ) := by
  let L₁ : ℝ := 6932 / 10000
  have hL0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hL1 : Real.log 2 ≤ L₁ := by
    dsimp only [L₁]
    exact strict_log_two_bounds.2.le
  have hpow2 := pow_le_pow_left₀ hL0 hL1 2
  have hpow5 := pow_le_pow_left₀ hL0 hL1 5
  have hpow6 := pow_le_pow_left₀ hL0 hL1 6
  have hpow3 : 0 ≤ Real.log 2 ^ 3 := pow_nonneg hL0 3
  have hpow4 : 0 ≤ Real.log 2 ^ 4 := pow_nonneg hL0 4
  rw [integral_regularPolynomial6_mul_fourCellPolynomialOdd_correlation]
  have hdrop :
      8672 / 13671875 + (223556 / 369140625 : ℝ) * Real.log 2 +
          (159892 / 205078125 : ℝ) * Real.log 2 ^ 2 -
            (827027 / 69609375000 : ℝ) * Real.log 2 ^ 3 -
              (4943 / 98437500 : ℝ) * Real.log 2 ^ 4 +
                (317938573 / 1596282187500000 : ℝ) * Real.log 2 ^ 5 +
                  (4207109 / 1240312500000 : ℝ) * Real.log 2 ^ 6 ≤
        8672 / 13671875 + (223556 / 369140625 : ℝ) * Real.log 2 +
          (159892 / 205078125 : ℝ) * Real.log 2 ^ 2 +
            (317938573 / 1596282187500000 : ℝ) * Real.log 2 ^ 5 +
              (4207109 / 1240312500000 : ℝ) * Real.log 2 ^ 6 := by
    nlinarith
  have hmono :
      8672 / 13671875 + (223556 / 369140625 : ℝ) * Real.log 2 +
          (159892 / 205078125 : ℝ) * Real.log 2 ^ 2 +
            (317938573 / 1596282187500000 : ℝ) * Real.log 2 ^ 5 +
              (4207109 / 1240312500000 : ℝ) * Real.log 2 ^ 6 ≤
        8672 / 13671875 + (223556 / 369140625 : ℝ) * L₁ +
          (159892 / 205078125 : ℝ) * L₁ ^ 2 +
            (317938573 / 1596282187500000 : ℝ) * L₁ ^ 5 +
              (4207109 / 1240312500000 : ℝ) * L₁ ^ 6 := by
    gcongr
  have hrat :
      8672 / 13671875 + (223556 / 369140625 : ℝ) * L₁ +
          (159892 / 205078125 : ℝ) * L₁ ^ 2 +
            (317938573 / 1596282187500000 : ℝ) * L₁ ^ 5 +
              (4207109 / 1240312500000 : ℝ) * L₁ ^ 6 <
        143 / 100000 := by
    norm_num [L₁]
  exact hdrop.trans (hmono.trans hrat.le)

private theorem intervalIntegrable_fourCellRegularKernel_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦ yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) ht.1.le
    have harg : (5 * Real.log 2 / 8) * t ≤ 5 * Real.log 2 / 4 := by
      have ha : 0 ≤ 5 * Real.log 2 / 8 := by positivity
      have := mul_le_mul_of_nonneg_left ht.2 ha
      linarith
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem centeredEndpointCorrelation_fourCellPolynomialOdd_nonpos_tail
    {t : ℝ} (ht : t ∈ Icc (8 / 5 : ℝ) 2) :
    centeredEndpointCorrelation fourCellPolynomialOdd t ≤ 0 := by
  let u : ℝ := 2 - t
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    linarith [ht.2]
  have huTwoFifths : u ≤ 2 / 5 := by
    dsimp only [u]
    linarith [ht.1]
  have hcoef : 0 ≤ 1 / 2 - u / 10 := by linarith
  have hmiddle : 0 ≤ u ^ 2 * (1 / 2 - u / 10) :=
    mul_nonneg (sq_nonneg u) hcoef
  have hbase : 0 ≤ 2 / 3 - u := by linarith
  have hquartic : 0 ≤ u ^ 4 / 140 := by positivity
  have hq :
      0 ≤ 2 / 3 - u + u ^ 2 / 2 - u ^ 3 / 10 + u ^ 4 / 140 := by
    nlinarith
  have hcube : 0 ≤ u ^ 3 := pow_nonneg hu0 3
  rw [centeredEndpointCorrelation_fourCellPolynomialOdd]
  rw [show 16 / 105 - (4 / 5 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
      t ^ 5 / 10 + t ^ 7 / 140 =
      -(u ^ 3) *
        (2 / 3 - u + u ^ 2 / 2 - u ^ 3 / 10 + u ^ 4 / 140) by
    dsimp only [u]
    ring]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcube) hq

theorem centeredEndpointCorrelation_fourCellPolynomialEven_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ centeredEndpointCorrelation fourCellPolynomialEven t := by
  unfold centeredEndpointCorrelation
  apply intervalIntegral.integral_nonneg (by linarith [ht.2])
  intro x hx
  have hxI : x ∈ Icc (-1 : ℝ) (1 - t) := by
    simpa only [uIcc_of_le (by linarith [ht.2] : (-1 : ℝ) ≤ 1 - t)] using hx
  have hxSq : x ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact abs_le.mpr ⟨hxI.1, by linarith [hxI.2, ht.1]⟩
  have htxSq : (t + x) ^ 2 ≤ 1 := by
    have hlo : -1 ≤ t + x := by linarith [ht.1, hxI.1]
    have hhi : t + x ≤ 1 := by linarith [hxI.2]
    rw [sq_le_one_iff_abs_le_one]
    exact abs_le.mpr ⟨hlo, hhi⟩
  unfold fourCellPolynomialEven
  exact mul_nonneg (sub_nonneg.mpr htxSq) (sub_nonneg.mpr hxSq)

theorem fourCellPolynomialEven_regularMoment_le_two_ninths :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellPolynomialEven t) ≤ 2 / 9 := by
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellPolynomialEven t
  have hC : Continuous C := by
    rw [show C = fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30 by
      funext t
      exact centeredEndpointCorrelation_fourCellPolynomialEven t]
    fun_prop
  have hf := intervalIntegrable_fourCellRegularKernel_mul C hC
  have hg : IntervalIntegrable (fun t : ℝ ↦ (1 / 4 : ℝ) * C t)
      volume 0 2 := (continuous_const.mul hC).intervalIntegrable _ _
  have hmono :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) * C t) ≤
        ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf hg
    intro t ht
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) ht.1
    have hC0 : 0 ≤ C t :=
      centeredEndpointCorrelation_fourCellPolynomialEven_nonneg ht
    exact mul_le_mul_of_nonneg_right
      (yoshidaRegularKernel_le_quarter harg0) hC0
  calc
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellPolynomialEven t) =
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) * C t := rfl
    _ ≤ ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * C t := hmono
    _ = (1 / 4 : ℝ) * ∫ t : ℝ in 0..2, C t := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 / 9 := by
      rw [show (∫ t : ℝ in 0..2, C t) = 8 / 9 by
        exact integral_centeredEndpointCorrelation_fourCellPolynomialEven]
      norm_num

/-- The odd constant kernel coordinate cancels.  On `[0,8/5]` the exact
sixth-order envelope captures the surviving moment; on `[8/5,2]` the
correlation is nonpositive, so the nonnegative kernel tail can be discarded. -/
theorem fourCellPolynomialOdd_regularMoment_le_nine_div_6250 :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellPolynomialOdd t) ≤
      (9 / 6250 : ℝ) := by
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellPolynomialOdd t
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t)
  let ε : ℝ := 1 / 500000
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous
      fourCellPolynomialOdd fourCellPolynomialOdd_continuous
  have hP : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K, C] using
      intervalIntegrable_fourCellRegularKernel_mul C hC
  have hleft : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have htail : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume (8 / 5) 2 :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (8 / 5 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2)
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hP.mul hC).intervalIntegrable _ _
  have herr : IntervalIntegrable (fun t : ℝ ↦ ε * |C t|)
      volume 0 (8 / 5) :=
    (continuous_const.mul hC.abs).intervalIntegrable _ _
  have hmajor : IntervalIntegrable
      (fun t : ℝ ↦ P t * C t + ε * |C t|)
      volume 0 (8 / 5) := hpoly.add herr
  have hpoint {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (8 / 5)) :
      K t * C t ≤ P t * C t + ε * |C t| := by
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) ht.1
    have hargLog : (5 * Real.log 2 / 8) * t ≤ Real.log 2 := by
      have htScaled := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    calc
      K t * C t = P t * C t + (K t - P t) * C t := by
        dsimp only [K, P]
        ring
      _ ≤ P t * C t + |(K t - P t) * C t| :=
        by linarith [le_abs_self ((K t - P t) * C t)]
      _ = P t * C t + |K t - P t| * |C t| := by rw [abs_mul]
      _ ≤ P t * C t + ε * |C t| := by
        gcongr
        rw [abs_of_nonneg]
        · simpa only [K, P, ε] using henv.2.le
        · simpa only [K, P] using henv.1
  have hleftMono :
      (∫ t : ℝ in 0..8 / 5, K t * C t) ≤
        ∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hmajor
    exact fun t ht ↦ hpoint ht
  have htailNonpos : (∫ t : ℝ in 8 / 5..2, K t * C t) ≤ 0 := by
    have hzero : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ)) volume
        (8 / 5 : ℝ) (2 : ℝ) :=
      continuous_const.intervalIntegrable _ _
    have hmono :
        (∫ t : ℝ in 8 / 5..2, K t * C t) ≤
          ∫ _t : ℝ in 8 / 5..2, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) htail hzero
      intro t ht
      have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
        mul_nonneg (by positivity) (by linarith [ht.1])
      have harg : (5 * Real.log 2 / 8) * t ≤
          5 * Real.log 2 / 4 := by
        have := mul_le_mul_of_nonneg_left ht.2
          (by positivity : 0 ≤ 5 * Real.log 2 / 8)
        linarith
      have hk0 : 0 ≤ K t := by
        dsimp only [K]
        exact yoshidaRegularKernel_nonneg_fourCellRange harg0 harg
      have hCt : C t ≤ 0 := by
        dsimp only [C]
        exact centeredEndpointCorrelation_fourCellPolynomialOdd_nonpos_tail ht
      exact mul_nonpos_of_nonneg_of_nonpos hk0 hCt
    simpa using hmono
  have habsFull :
      (∫ t : ℝ in 0..2, |C t|) ≤ (16 / 105 : ℝ) := by
    calc
      (∫ t : ℝ in 0..2, |C t|) ≤
          ∫ x : ℝ in -1..1, fourCellPolynomialOdd x ^ 2 := by
        simpa only [C] using
          integral_abs_centeredEndpointCorrelation_le_energy
            fourCellPolynomialOdd fourCellPolynomialOdd_continuous
      _ = 16 / 105 := integral_fourCellPolynomialOdd_sq
  have habsSub :
      (∫ t : ℝ in 0..8 / 5, |C t|) ≤ (16 / 105 : ℝ) := by
    have hmono :
        (∫ t : ℝ in 0..8 / 5, |C t|) ≤
          ∫ t : ℝ in 0..2, |C t| := by
      apply intervalIntegral.integral_mono_interval
        (c := (0 : ℝ)) (d := 2) le_rfl (by norm_num) (by norm_num)
      · filter_upwards with t
        exact abs_nonneg (C t)
      · exact hC.abs.intervalIntegrable _ _
    exact hmono.trans habsFull
  have hpolyUpper :
      (∫ t : ℝ in 0..8 / 5, P t * C t) ≤
        (143 / 100000 : ℝ) := by
    simpa only [P, C] using
      integral_regularPolynomial6_mul_fourCellPolynomialOdd_correlation_le
  have hmajorEq :
      (∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t|) =
        (∫ t : ℝ in 0..8 / 5, P t * C t) +
          ε * ∫ t : ℝ in 0..8 / 5, |C t| := by
    rw [intervalIntegral.integral_add hpoly herr,
      intervalIntegral.integral_const_mul]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft htail
  calc
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellPolynomialOdd t) =
        (∫ t : ℝ in 0..8 / 5, K t * C t) +
          ∫ t : ℝ in 8 / 5..2, K t * C t := by
      simpa only [K, C] using hsplit.symm
    _ ≤ ∫ t : ℝ in 0..8 / 5, K t * C t := by linarith
    _ ≤ ∫ t : ℝ in 0..8 / 5, P t * C t + ε * |C t| := hleftMono
    _ = (∫ t : ℝ in 0..8 / 5, P t * C t) +
          ε * ∫ t : ℝ in 0..8 / 5, |C t| := hmajorEq
    _ ≤ (143 / 100000 : ℝ) + (1 / 500000) * (16 / 105) := by
      dsimp only [ε]
      exact add_le_add hpolyUpper
        (mul_le_mul_of_nonneg_left habsSub (by norm_num))
    _ ≤ 9 / 6250 := by norm_num

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

private theorem sinh_le_mul_exp_self_probe {z : ℝ} :
    Real.sinh z ≤ z * Real.exp z := by
  have hbase := Real.add_one_le_exp (-2 * z)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos z).le
  have hprod : Real.exp z * (1 - 2 * z) ≤ Real.exp (-z) := by
    calc
      Real.exp z * (1 - 2 * z) = Real.exp z * (-2 * z + 1) := by ring
      _ ≤ Real.exp z * Real.exp (-2 * z) := hmul
      _ = Real.exp (-z) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.sinh_eq]
  nlinarith [Real.exp_pos z]

private theorem fourCellPolynomialOdd_sinh_pointwise_upper
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.sinh ((5 * Real.log 2 / 16) * x) ≤ (7 / 25 : ℝ) * x := by
  let z : ℝ := (5 * Real.log 2 / 16) * x
  have hlambda : 5 * Real.log 2 / 16 ≤ (7 / 32 : ℝ) := by
    linarith [strict_log_two_bounds.2]
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num)
        (Real.log_pos (by norm_num)).le) (by norm_num)) hx.1
  have hzScaled : z ≤ (7 / 32 : ℝ) * x := by
    dsimp only [z]
    exact mul_le_mul_of_nonneg_right hlambda hx.1
  have hzUpper : z ≤ (7 / 32 : ℝ) := by
    nlinarith [hx.2]
  have hzOne : z < 1 := by nlinarith
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzOne
  have hcoef : (7 / 32 : ℝ) ≤ (7 / 25) * (1 - z) := by
    nlinarith
  have hscaledCoef : (7 / 32 : ℝ) * x ≤
      ((7 / 25) * (1 - z)) * x :=
    mul_le_mul_of_nonneg_right hcoef hx.1
  change Real.sinh z ≤ (7 / 25 : ℝ) * x
  calc
    Real.sinh z ≤ z * Real.exp z := sinh_le_mul_exp_self_probe
    _ ≤ z * (1 / (1 - z)) :=
      mul_le_mul_of_nonneg_left hexp hz0
    _ = z / (1 - z) := by ring
    _ ≤ (7 / 25 : ℝ) * x := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
      calc
        z ≤ (7 / 32 : ℝ) * x := hzScaled
        _ ≤ ((7 / 25) * (1 - z)) * x := hscaledCoef
        _ = (7 / 25 : ℝ) * x * (1 - z) := by ring

theorem fourCellPolynomialOdd_sinhMoment_nonneg :
    0 ≤ fourCellPositiveSinhMoment fourCellPolynomialOdd
      (5 * Real.log 2 / 16) := by
  unfold fourCellPositiveSinhMoment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  have hsinh : 0 ≤ Real.sinh ((5 * Real.log 2 / 16) * x) := by
    rw [Real.sinh_nonneg_iff]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num)
        (Real.log_pos (by norm_num)).le) (by norm_num)) hx.1
  have hw : 0 ≤ fourCellPolynomialOdd x := by
    unfold fourCellPolynomialOdd
    have hxsq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, sq_nonneg x]
    exact mul_nonneg hx.1 (sub_nonneg.mpr hxsq)
  exact mul_nonneg hsinh hw

theorem fourCellPolynomialOdd_sinhMoment_le_fourteen_div_375 :
    fourCellPositiveSinhMoment fourCellPolynomialOdd
        (5 * Real.log 2 / 16) ≤ (14 / 375 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    Real.sinh ((5 * Real.log 2 / 16) * x) * fourCellPolynomialOdd x
  let g : ℝ → ℝ := fun x ↦
    ((7 / 25 : ℝ) * x) * fourCellPolynomialOdd x
  have hf : Continuous f := by
    dsimp only [f]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.sinh ((5 * Real.log 2 / 16) * x))).mul
        fourCellPolynomialOdd_continuous
  have hg : Continuous g := by
    dsimp only [g]
    exact (continuous_const.mul continuous_id).mul
      fourCellPolynomialOdd_continuous
  have hmono : (∫ x : ℝ in 0..1, f x) ≤ ∫ x : ℝ in 0..1, g x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro x hx
    have hxsq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, sq_nonneg x]
    have hw : 0 ≤ fourCellPolynomialOdd x := by
      unfold fourCellPolynomialOdd
      exact mul_nonneg hx.1 (sub_nonneg.mpr hxsq)
    exact mul_le_mul_of_nonneg_right
      (fourCellPolynomialOdd_sinh_pointwise_upper hx) hw
  have hgValue : (∫ x : ℝ in 0..1, g x) = (14 / 375 : ℝ) := by
    dsimp only [g]
    rw [show (fun x : ℝ ↦
        ((7 / 25 : ℝ) * x) * fourCellPolynomialOdd x) =
      fun x ↦ 0 * x ^ 0 + 0 * x ^ 1 + (7 / 25) * x ^ 2 +
        0 * x ^ 3 + (-7 / 25) * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
          0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
      funext x
      unfold fourCellPolynomialOdd
      ring,
      integral_polynomial_ten]
    norm_num
  unfold fourCellPositiveSinhMoment
  change (∫ x : ℝ in 0..1, f x) ≤ _
  rw [← hgValue]
  exact hmono

theorem fourCellPolynomialEven_coshMoment_lower :
    2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 ≤
      fourCellPositiveCoshMoment fourCellPolynomialEven
        (5 * Real.log 2 / 16) := by
  let p : ℝ → ℝ := fun x ↦
    (1 + ((5 * Real.log 2 / 16) * x) ^ 2 / 2) *
      fourCellPolynomialEven x
  let q : ℝ → ℝ := fun x ↦
    Real.cosh ((5 * Real.log 2 / 16) * x) * fourCellPolynomialEven x
  have hpCont : Continuous p := by
    dsimp only [p]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      1 + ((5 * Real.log 2 / 16) * x) ^ 2 / 2)).mul
        fourCellPolynomialEven_continuous
  have hqCont : Continuous q := by
    dsimp only [q]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.cosh ((5 * Real.log 2 / 16) * x))).mul
        fourCellPolynomialEven_continuous
  have hp : IntervalIntegrable p volume 0 1 := hpCont.intervalIntegrable _ _
  have hq : IntervalIntegrable q volume 0 1 := hqCont.intervalIntegrable _ _
  have hmono : (∫ x : ℝ in 0..1, p x) ≤ ∫ x : ℝ in 0..1, q x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hp hq
    intro x hx
    have hxSq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, sq_nonneg x]
    have hw0 : 0 ≤ fourCellPolynomialEven x := by
      unfold fourCellPolynomialEven
      linarith
    have hz0 : 0 ≤ (5 * Real.log 2 / 16) * x :=
      mul_nonneg (by positivity) hx.1
    exact mul_le_mul_of_nonneg_right (one_add_sq_div_two_le_cosh hz0) hw0
  have hpValue : (∫ x : ℝ in 0..1, p x) =
      2 / 3 + (5 / 768 : ℝ) * Real.log 2 ^ 2 := by
    dsimp only [p]
    rw [show (fun x : ℝ ↦
        (1 + ((5 * Real.log 2 / 16) * x) ^ 2 / 2) *
          fourCellPolynomialEven x) =
        fun x ↦ 1 * x ^ 0 + 0 * x ^ 1 +
          ((25 * Real.log 2 ^ 2 / 512) - 1) * x ^ 2 + 0 * x ^ 3 +
            (-25 * Real.log 2 ^ 2 / 512) * x ^ 4 +
              0 * x ^ 5 + 0 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 +
                0 * x ^ 9 + 0 * x ^ 10 by
      funext x
      unfold fourCellPolynomialEven
      ring,
      integral_polynomial_ten]
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
    Real.log (2 * (5 * Real.log 2 / 8)) +
        Real.eulerMascheroniConstant + Real.log Real.pi =
      yoshidaEndpointScalarMassLoss + Real.log (5 / 4 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show 2 * (5 * Real.log 2 / 8) =
      (5 / 4 : ℝ) * Real.log 2 by ring,
    Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  unfold yoshidaEndpointScalarMassLoss
  rw [Real.log_mul Real.pi_ne_zero hlogTwo]
  ring

private theorem fourCellScalar_lt_15787_div_10000 :
    Real.log (2 * (5 * Real.log 2 / 8)) +
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

private theorem sqrt_two_gt_141421_div_100000 :
    (141421 / 100000 : ℝ) < Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  nlinarith

theorem integral_endpointPotential_mul_fourCellPolynomialEven_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * fourCellPolynomialEven x ^ 2) =
        188 / 225 - (16 / 15 : ℝ) * Real.log 2 := by
  rw [fourCellPolynomialEven_eq_lowProfile,
    integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq]
  ring

theorem integral_endpointPotential_mul_fourCellPolynomialOdd_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * fourCellPolynomialOdd x ^ 2) =
        1556 / 11025 - (16 / 105 : ℝ) * Real.log 2 := by
  have h1 := endpointPotentialEvenMoment_succ 0
  have h2 := endpointPotentialEvenMoment_succ 1
  have h3 := endpointPotentialEvenMoment_succ 2
  rw [endpointPotentialEvenMoment_zero] at h1
  norm_num at h1 h2 h3
  have hV2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 := by
    simpa only [one_mul] using
      intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x)
        continuous_id
  have hV4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
    apply h.congr
    intro x _hx
    ring
  have hV6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)
    apply h.congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * fourCellPolynomialOdd x ^ 2) =
      fun x ↦ yoshidaEndpointPotential x * x ^ 2 -
        2 * (yoshidaEndpointPotential x * x ^ 4) +
          yoshidaEndpointPotential x * x ^ 6 by
    funext x
    unfold fourCellPolynomialOdd
    ring]
  rw [intervalIntegral.integral_add
      (hV2.sub (hV4.const_mul 2)) hV6,
    intervalIntegral.integral_sub hV2 (hV4.const_mul 2),
    intervalIntegral.integral_const_mul]
  change endpointPotentialEvenMoment 1 -
      2 * endpointPotentialEvenMoment 2 + endpointPotentialEvenMoment 3 = _
  linarith

theorem fourCellEndpointPairing_fourCellPolynomialEven :
    fourCellEndpointPairing fourCellPolynomialEven = 1616 / 46875 := by
  unfold fourCellEndpointPairing
  rw [show (fun x : ℝ ↦ fourCellPolynomialEven x *
      fourCellPolynomialEven (x - 8 / 5)) =
      fun x ↦ (-39 / 25) * x ^ 0 + (16 / 5) * x ^ 1 + (14 / 25) * x ^ 2 +
        (-16 / 5) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
          0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialEven
    ring,
    integral_polynomial_ten]
  norm_num

theorem fourCellEndpointPairing_fourCellPolynomialOdd :
    fourCellEndpointPairing fourCellPolynomialOdd = -178736 / 8203125 := by
  unfold fourCellEndpointPairing
  rw [show (fun x : ℝ ↦ fourCellPolynomialOdd x *
      fourCellPolynomialOdd (x - 8 / 5)) =
      fun x ↦ 0 * x ^ 0 + (312 / 125) * x ^ 1 + (-167 / 25) * x ^ 2 +
        (288 / 125) * x ^ 3 + (142 / 25) * x ^ 4 + (-24 / 5) * x ^ 5 +
          1 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialOdd
    ring,
    integral_polynomial_ten]
  norm_num

theorem fourCellEndpointMatchedSquare_fourCellPolynomialEven :
    fourCellEndpointMatchedSquare fourCellPolynomialEven = 3008 / 15625 := by
  unfold fourCellEndpointMatchedSquare
  rw [show (fun x : ℝ ↦
      (fourCellPolynomialEven (8 / 5 + x) + fourCellPolynomialEven x) ^ 2) =
      fun x ↦ (196 / 625) * x ^ 0 + (448 / 125) * x ^ 1 + (312 / 25) * x ^ 2 +
        (64 / 5) * x ^ 3 + 4 * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
          0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialEven
    ring,
    integral_polynomial_ten]
  norm_num

theorem fourCellEndpointAntimatchedSquare_fourCellPolynomialEven :
    fourCellEndpointAntimatchedSquare fourCellPolynomialEven = 512 / 9375 := by
  unfold fourCellEndpointAntimatchedSquare
  rw [show (fun x : ℝ ↦
      (fourCellPolynomialEven (8 / 5 + x) - fourCellPolynomialEven x) ^ 2) =
      fun x ↦ (4096 / 625) * x ^ 0 + (2048 / 125) * x ^ 1 + (256 / 25) * x ^ 2 +
        0 * x ^ 3 + 0 * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
          0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialEven
    ring,
    integral_polynomial_ten]
  norm_num

theorem fourCellEndpointMatchedSquare_fourCellPolynomialOdd :
    fourCellEndpointMatchedSquare fourCellPolynomialOdd = 155968 / 8203125 := by
  unfold fourCellEndpointMatchedSquare
  rw [show (fun x : ℝ ↦
      (fourCellPolynomialOdd (8 / 5 + x) + fourCellPolynomialOdd x) ^ 2) =
      fun x ↦ (97344 / 15625) * x ^ 0 + (88608 / 3125) * x ^ 1 +
        (7028 / 125) * x ^ 2 + (8064 / 125) * x ^ 3 +
          (1144 / 25) * x ^ 4 + (96 / 5) * x ^ 5 + 4 * x ^ 6 +
            0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialOdd
    ring,
    integral_polynomial_ten]
  norm_num

theorem fourCellEndpointAntimatchedSquare_fourCellPolynomialOdd :
    fourCellEndpointAntimatchedSquare fourCellPolynomialOdd = 41472 / 390625 := by
  unfold fourCellEndpointAntimatchedSquare
  rw [show (fun x : ℝ ↦
      (fourCellPolynomialOdd (8 / 5 + x) - fourCellPolynomialOdd x) ^ 2) =
      fun x ↦ (97344 / 15625) * x ^ 0 + (119808 / 3125) * x ^ 1 +
        (10368 / 125) * x ^ 2 + (9216 / 125) * x ^ 3 +
          (576 / 25) * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
            0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fourCellPolynomialOdd
    ring,
    integral_polynomial_ten]
  norm_num

/-! ## Exact complete-bracket normal forms -/

/-- The complete even probe, with only its smooth regular-kernel moment and
positive cosh rank left in analytic form. -/
theorem fourCellBracket_fourCellPolynomialEven_eq :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellPolynomialEven -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellPolynomialEven =
      248 / 225 - (16 / 15 : ℝ) * Real.log 2 -
        (Real.log (2 * (5 * Real.log 2 / 8)) +
            Real.eulerMascheroniConstant + Real.log Real.pi) * (16 / 15) -
        (5 * Real.log 2 / 4) *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
              centeredEndpointCorrelation fourCellPolynomialEven t) +
        5 * Real.log 2 *
          fourCellPositiveCoshMoment fourCellPolynomialEven
            (5 * Real.log 2 / 16) ^ 2 -
        Real.sqrt 2 * Real.log 2 * (1616 / 46875) := by
  have hpolar := physicalPolarProduct_eq_positiveCoshSquare_of_even
    fourCellPolynomialEven fourCellPolynomialEven_continuous
      fourCellPolynomialEven_even (5 * Real.log 2 / 8)
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_fourCellPolynomialEven,
    integral_endpointPotential_mul_fourCellPolynomialEven_sq,
    integral_fourCellPolynomialEven_sq,
    fourCellEndpointPairing_fourCellPolynomialEven, hpolar]
  ring

/-- The complete odd probe.  Its polar rank is negative, while its exact
retained prime contribution has the opposite sign and is larger. -/
theorem fourCellBracket_fourCellPolynomialOdd_eq :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellPolynomialOdd -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellPolynomialOdd =
      3656 / 11025 - (16 / 105 : ℝ) * Real.log 2 -
        (Real.log (2 * (5 * Real.log 2 / 8)) +
            Real.eulerMascheroniConstant + Real.log Real.pi) * (16 / 105) -
        (5 * Real.log 2 / 4) *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
              centeredEndpointCorrelation fourCellPolynomialOdd t) -
        5 * Real.log 2 *
          fourCellPositiveSinhMoment fourCellPolynomialOdd
            (5 * Real.log 2 / 16) ^ 2 +
        Real.sqrt 2 * Real.log 2 * (178736 / 8203125) := by
  have hpolar := physicalPolarProduct_eq_neg_positiveSinhSquare_of_odd
    fourCellPolynomialOdd fourCellPolynomialOdd_continuous
      fourCellPolynomialOdd_odd (5 * Real.log 2 / 8)
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_fourCellPolynomialOdd,
    integral_endpointPotential_mul_fourCellPolynomialOdd_sq,
    integral_fourCellPolynomialOdd_sq,
    fourCellEndpointPairing_fourCellPolynomialOdd, hpolar]
  ring

/-- A fully rigorous positive-capacity certificate for the lowest even
endpoint-zero polynomial.  It uses only the global quarter bound for the
regular kernel and the quadratic lower Taylor term of `cosh`. -/
theorem fourCellBracket_fourCellPolynomialEven_pos :
    0 < centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellPolynomialEven -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellPolynomialEven := by
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  let S₁ : ℝ := 15787 / 10000
  let T₁ : ℝ := 70711 / 50000
  let H₀ : ℝ := 2 / 3 + (5 / 768) * L₀ ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
      centeredEndpointCorrelation fourCellPolynomialEven t
  let H : ℝ := fourCellPositiveCoshMoment fourCellPolynomialEven
    (5 * Real.log 2 / 16)
  let S : ℝ := Real.log (2 * (5 * Real.log 2 / 8)) +
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
    simpa only [H] using fourCellPolynomialEven_coshMoment_lower
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
  have hPolar0 : 5 * L₀ * H₀ ^ 2 ≤
      5 * Real.log 2 * H ^ 2 := by
    calc
      5 * L₀ * H₀ ^ 2 ≤ 5 * Real.log 2 * H₀ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL0.le (by norm_num)) (sq_nonneg H₀)
      _ ≤ 5 * Real.log 2 * H ^ 2 := by
        exact mul_le_mul_of_nonneg_left hHsq (by positivity)
  have hR : R ≤ 2 / 9 := by
    simpa only [R] using fourCellPolynomialEven_regularMoment_le_two_ninths
  have hRscaled : (5 * Real.log 2 / 4) * R ≤
      (5 * L₁ / 4) * (2 / 9) := by
    calc
      (5 * Real.log 2 / 4) * R ≤
          (5 * Real.log 2 / 4) * (2 / 9) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (5 * L₁ / 4) * (2 / 9) := by
        have hc : 5 * Real.log 2 / 4 ≤ 5 * L₁ / 4 := by
          linarith [hL1]
        exact mul_le_mul_of_nonneg_right hc (by norm_num)
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
      _ ≤ T₁ * L₁ := by
        exact mul_le_mul_of_nonneg_left hL1.le (by norm_num [T₁])
  have hPrime : Real.sqrt 2 * Real.log 2 * (1616 / 46875) ≤
      T₁ * L₁ * (1616 / 46875) :=
    mul_le_mul_of_nonneg_right hTL (by norm_num)
  have hrat :
      0 < 248 / 225 - (16 / 15 : ℝ) * L₁ -
          S₁ * (16 / 15) - (5 * L₁ / 4) * (2 / 9) +
          5 * L₀ * H₀ ^ 2 -
            T₁ * L₁ * (1616 / 46875) := by
    norm_num [L₀, L₁, S₁, T₁, H₀]
  rw [fourCellBracket_fourCellPolynomialEven_eq]
  dsimp only [R, H, S] at hRscaled hPolar0 hSscaled ⊢
  linarith

/-- A fully rigorous positive-capacity certificate for the lowest odd
endpoint-zero polynomial.  The proof uses the exact cancellation of the
constant regular-kernel coordinate, the sixth-order kernel envelope through
the sign-changing point, and a one-sided structural bound for `sinh`. -/
theorem fourCellBracket_fourCellPolynomialOdd_pos :
    0 < centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellPolynomialOdd -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellPolynomialOdd := by
  let L₀ : ℝ := 6931 / 10000
  let L₁ : ℝ := 6932 / 10000
  let S₁ : ℝ := 15787 / 10000
  let T₀ : ℝ := 141421 / 100000
  let R₁ : ℝ := 9 / 6250
  let H₁ : ℝ := 14 / 375
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
      centeredEndpointCorrelation fourCellPolynomialOdd t
  let H : ℝ := fourCellPositiveSinhMoment fourCellPolynomialOdd
    (5 * Real.log 2 / 16)
  let S : ℝ := Real.log (2 * (5 * Real.log 2 / 8)) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  have hL := strict_log_two_bounds
  have hL0 : L₀ < Real.log 2 := by simpa only [L₀] using hL.1
  have hL1 : Real.log 2 < L₁ := by simpa only [L₁] using hL.2
  have hL0nonneg : 0 ≤ L₀ := by norm_num [L₀]
  have hLnonneg : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hR : R ≤ R₁ := by
    simpa only [R, R₁] using
      fourCellPolynomialOdd_regularMoment_le_nine_div_6250
  have hRscaled : (5 * Real.log 2 / 4) * R ≤
      (5 * L₁ / 4) * R₁ := by
    calc
      (5 * Real.log 2 / 4) * R ≤
          (5 * Real.log 2 / 4) * R₁ :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (5 * L₁ / 4) * R₁ := by
        exact mul_le_mul_of_nonneg_right (by linarith [hL1])
          (by norm_num [R₁])
  have hH0 : 0 ≤ H := by
    simpa only [H] using fourCellPolynomialOdd_sinhMoment_nonneg
  have hH1 : H ≤ H₁ := by
    simpa only [H, H₁] using
      fourCellPolynomialOdd_sinhMoment_le_fourteen_div_375
  have hHsq : H ^ 2 ≤ H₁ ^ 2 := by
    exact (sq_le_sq₀ hH0 (by norm_num [H₁])).2 hH1
  have hPolar : 5 * Real.log 2 * H ^ 2 ≤ 5 * L₁ * H₁ ^ 2 := by
    calc
      5 * Real.log 2 * H ^ 2 ≤ 5 * L₁ * H ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith [hL1]) (sq_nonneg H)
      _ ≤ 5 * L₁ * H₁ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hHsq (by norm_num [L₁])
  have hS : S < S₁ := by
    simpa only [S, S₁] using fourCellScalar_lt_15787_div_10000
  have hSscaled : S * (16 / 105) ≤ S₁ * (16 / 105) :=
    (mul_lt_mul_of_pos_right hS (by norm_num)).le
  have hLscaled : (16 / 105 : ℝ) * Real.log 2 ≤
      (16 / 105) * L₁ :=
    mul_le_mul_of_nonneg_left hL1.le (by norm_num)
  have hT0 : T₀ < Real.sqrt 2 := by
    simpa only [T₀] using sqrt_two_gt_141421_div_100000
  have hTL : T₀ * L₀ ≤ Real.sqrt 2 * Real.log 2 := by
    calc
      T₀ * L₀ ≤ Real.sqrt 2 * L₀ :=
        mul_le_mul_of_nonneg_right hT0.le hL0nonneg
      _ ≤ Real.sqrt 2 * Real.log 2 :=
        mul_le_mul_of_nonneg_left hL0.le (Real.sqrt_nonneg 2)
  have hPrime : T₀ * L₀ * (178736 / 8203125) ≤
      Real.sqrt 2 * Real.log 2 * (178736 / 8203125) :=
    mul_le_mul_of_nonneg_right hTL (by norm_num)
  have hrat :
      0 < 3656 / 11025 - (16 / 105 : ℝ) * L₁ -
          S₁ * (16 / 105) - (5 * L₁ / 4) * R₁ -
            5 * L₁ * H₁ ^ 2 +
              T₀ * L₀ * (178736 / 8203125) := by
    norm_num [L₀, L₁, S₁, T₀, R₁, H₁]
  rw [fourCellBracket_fourCellPolynomialOdd_eq]
  dsimp only [R, H, S] at hRscaled hPolar hSscaled hPrime ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellPolynomialCapacityProbeStructural
