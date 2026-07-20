import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11FormDualProbeStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModeL2
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaRegularKernelBound

private theorem centeredRawLogBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (a : ℝ) :
    centeredRawLogBilinear u (fun x ↦ a * v x) =
      a * centeredRawLogBilinear u v := by
  unfold centeredRawLogBilinear
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      ((u x - u y) * (a * v x - a * v y)) / |x - y|) =
      fun x ↦ a * ∫ y : ℝ in -1..1,
        ((u x - u y) * (v x - v y)) / |x - y| by
    funext x
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring,
    intervalIntegral.integral_const_mul]

private theorem endpointStripOdd_const_mul_probe
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOdd (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripOdd v z := by
  funext z
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  ring

private theorem endpointStripOddRawPolarization_const_mul_right_probe
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (a : ℝ) :
    fourCellOddEndpointStripOddRawPolarization u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddRawPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear u _ hu hav,
    fourCellOddEndpointStripOddRawPolarization_eq_bilinear u v hu hv,
    endpointStripOdd_const_mul_probe,
    centeredRawLogBilinear_const_mul_right_probe]
  ring

private theorem rawStripPolarization_const_mul_right_probe
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddRawStripCancellationPolarization u (fun x ↦ a * v x) =
      a * fourCellOddRawStripCancellationPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u _ hu hav huodd havodd,
    fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u v hu hv huodd hvodd,
    centeredRawLogBilinear_const_mul_right_probe,
    endpointStripOddRawPolarization_const_mul_right_probe u v hu hv]
  ring

private theorem endpointStripEven_const_mul_probe
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEven (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripEven v z := by
  funext z
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  ring

private theorem endpointStripEvenMassBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripEvenMassBilinear u v := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [endpointStripEven_const_mul_probe]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripEven u z *
      (a * fourCellOddEndpointStripEven v z)) =
      fun z ↦ a * (fourCellOddEndpointStripEven u z *
        fourCellOddEndpointStripEven v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddMassBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddMassBilinear u v := by
  unfold fourCellOddEndpointStripOddMassBilinear
  rw [endpointStripOdd_const_mul_probe]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripOdd u z *
      (a * fourCellOddEndpointStripOdd v z)) =
      fun z ↦ a * (fourCellOddEndpointStripOdd u z *
        fourCellOddEndpointStripOdd v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_weight_mul_const_mul_right_probe
    (W u v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, W x * u x * (a * v x)) =
      a * ∫ x : ℝ in l..r, W x * u x * v x := by
  rw [show (fun x : ℝ ↦ W x * u x * (a * v x)) =
      fun x ↦ a * (W x * u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem integral_mul_const_mul_right_probe
    (u v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, u x * (a * v x)) =
      a * ∫ x : ℝ in l..r, u x * v x := by
  rw [show (fun x : ℝ ↦ u x * (a * v x)) =
      fun x ↦ a * (u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem correlationBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (a t : ℝ) :
    factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t =
      a * factorTwoCenteredCorrelationBilinear u v t := by
  have hv : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv]
  simpa only [one_mul, one_smul] using
    factorTwoCenteredCorrelationBilinear_smul_smul 1 a u v t

private theorem stripReducedBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddStripReducedBilinear u (fun x ↦ a * v x) =
      a * fourCellOddStripReducedBilinear u v := by
  unfold fourCellOddStripReducedBilinear
  rw [endpointStripEvenMassBilinear_const_mul_right_probe,
    endpointStripOddMassBilinear_const_mul_right_probe,
    integral_weight_mul_const_mul_right_probe,
    integral_mul_const_mul_right_probe]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t) =
      fun t ↦ a *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) by
    funext t
    rw [correlationBilinear_const_mul_right_probe]
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem coreLocalBilinear_const_mul_right_probe
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddCoreLocalBilinear u (fun x ↦ a * v x) =
      a * fourCellOddCoreLocalBilinear u v := by
  unfold fourCellOddCoreLocalBilinear
  rw [rawStripPolarization_const_mul_right_probe u v hu hv huodd hvodd,
    stripReducedBilinear_const_mul_right_probe]
  ring

private theorem endpointStripEvenMass_const_mul_probe
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripEvenMass v := by
  unfold fourCellOddEndpointStripEvenMass
  rw [endpointStripEven_const_mul_probe]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripEven v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripEven v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddMass_const_mul_probe
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddMass v := by
  unfold fourCellOddEndpointStripOddMass
  rw [endpointStripOdd_const_mul_probe]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripOdd v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripOdd v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddRawEnergy_const_mul_probe
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddRawEnergy (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddRawEnergy v := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [endpointStripOdd_const_mul_probe,
    YoshidaEndpointOddOneThreeRawPolarization.centeredRawLogEnergy_const_mul]
  ring

private theorem rawStripReserve_const_mul_probe
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddRawStripCancellationReserve (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddRawStripCancellationReserve v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hv.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have havLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ a * v x) :=
    hav.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfoldV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    v hvLocal hvodd
  have hfoldAV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (fun x ↦ a * v x) havLocal havodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfoldAV, ← hfoldV,
    endpointStripOddRawEnergy_const_mul_probe,
    YoshidaEndpointOddOneThreeRawPolarization.centeredRawLogEnergy_const_mul]
  ring

private theorem integral_weight_mul_sq_const_mul_probe
    (W v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, W x * (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in l..r, W x * v x ^ 2 := by
  rw [show (fun x : ℝ ↦ W x * (a * v x) ^ 2) =
      fun x ↦ a ^ 2 * (W x * v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem integral_sq_const_mul_probe
    (v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in l..r, v x ^ 2 := by
  rw [show (fun x : ℝ ↦ (a * v x) ^ 2) =
      fun x ↦ a ^ 2 * v x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredCorrelation_const_mul_probe
    (v : ℝ → ℝ) (a t : ℝ) :
    centeredEndpointCorrelation (fun x ↦ a * v x) t =
      a ^ 2 * centeredEndpointCorrelation v t := by
  have hav : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hav, ← factorTwoCenteredCorrelationBilinear_self,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_self]
  ring

private theorem coreLocalQuadratic_const_mul_probe
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddCoreLocalQuadratic (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddCoreLocalQuadratic v := by
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed,
    fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddSignedMassRegularQuadratic
  rw [rawStripReserve_const_mul_probe v hv hvodd a,
    endpointStripEvenMass_const_mul_probe,
    endpointStripOddMass_const_mul_probe,
    integral_weight_mul_sq_const_mul_probe,
    integral_sq_const_mul_probe]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (fun x ↦ a * v x) t) =
      fun t ↦ a ^ 2 *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation v t) by
    funext t
    rw [centeredCorrelation_const_mul_probe]
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem sq_le_mul_of_forall_quadratic_nonneg_probe
    (A B C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ t : ℝ, 0 ≤ A + 2 * B * t + C * t ^ 2) :
    B ^ 2 ≤ A * C := by
  by_cases hC0 : C = 0
  · subst C
    have hB : B = 0 := by
      by_contra hB0
      let t : ℝ := -(A + 1) / (2 * B)
      have hq := hquad t
      have ht : 2 * B * t = -(A + 1) := by
        dsimp only [t]
        field_simp [hB0]
      simp only [zero_mul] at hq
      rw [ht] at hq
      linarith
    rw [hB]
    norm_num
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hq := hquad (-B / C)
    have heq :
        A + 2 * B * (-B / C) + C * (-B / C) ^ 2 =
          (A * C - B ^ 2) / C := by
      field_simp [ne_of_gt hCpos]
      ring
    rw [heq] at hq
    have hmul := mul_nonneg hq hC
    have hcancel : ((A * C - B ^ 2) / C) * C =
        A * C - B ^ 2 := by
      field_simp [ne_of_gt hCpos]
    rw [hcancel] at hmul
    linarith

private theorem centeredOddP1Coefficient_add_const_mul_probe
    (u v : ℝ → ℝ) (a : ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredOddP1Coefficient (u + fun x ↦ a * v x) =
      centeredOddP1Coefficient u + a * centeredOddP1Coefficient v := by
  unfold centeredOddP1Coefficient
  have huI : IntervalIntegrable (fun x : ℝ ↦ u x * centeredP1 x)
      volume (-1) 1 :=
    (hu.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hvI : IntervalIntegrable (fun x : ℝ ↦
      a * (v x * centeredP1 x)) volume (-1) 1 :=
    (continuous_const.mul
      (hv.mul (by unfold centeredP1; fun_prop))).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      (u + fun y ↦ a * v y) x * centeredP1 x) =
      fun x ↦ u x * centeredP1 x + a * (v x * centeredP1 x) by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huI hvI,
    intervalIntegral.integral_const_mul]
  ring

/-- Uniform coercivity of the complete odd core on the whole
`P₁`-orthogonal odd subspace.  The other retained-mode equations in the
earlier `P₁₁+` interface are unnecessary for diagonal positivity. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_P1_zero
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  have hmargin := one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
    w hw hodd hone
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
    fourCellOddCoreLocalQuadratic w at hmargin
  nlinarith

/-- The complete odd core is a positive quadratic form on the entire
`P₁`-orthogonal odd subspace.  This is stronger than the existing
`P₁₁+` diagonal statement: no higher moment hypotheses occur. -/
theorem fourCellOddCoreLocalBilinear_sq_le_mul_of_P1_zero
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (huone : centeredOddP1Coefficient u = 0)
    (hvone : centeredOddP1Coefficient v = 0) :
    fourCellOddCoreLocalBilinear u v ^ 2 ≤
      fourCellOddCoreLocalQuadratic u * fourCellOddCoreLocalQuadratic v := by
  let A := fourCellOddCoreLocalQuadratic u
  let B := fourCellOddCoreLocalBilinear u v
  let C := fourCellOddCoreLocalQuadratic v
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact fourCellOddCoreLocalQuadratic_nonneg_of_P1_zero v hv hvodd hvone
  apply sq_le_mul_of_forall_quadratic_nonneg_probe A B C hC
  intro t
  let tv : ℝ → ℝ := fun x ↦ t * v x
  have htv : ContDiff ℝ 1 tv := by
    dsimp only [tv]
    exact contDiff_const.mul hv
  have htvodd : Function.Odd tv := by
    intro x
    dsimp only [tv]
    rw [hvodd]
    ring
  have hone : centeredOddP1Coefficient (u + tv) = 0 := by
    dsimp only [tv]
    rw [centeredOddP1Coefficient_add_const_mul_probe
      u v t hu.continuous hv.continuous, huone, hvone]
    ring
  have hnonneg : 0 ≤ fourCellOddCoreLocalQuadratic (u + tv) :=
    fourCellOddCoreLocalQuadratic_nonneg_of_P1_zero
      (u + tv) (hu.add htv) (huodd.add htvodd) hone
  have hadd := fourCellOddCoreLocalQuadratic_add u tv hu.continuous htv.continuous
  dsimp only [tv] at hadd
  rw [coreLocalBilinear_const_mul_right_probe u v hu hv huodd hvodd,
    coreLocalQuadratic_const_mul_probe v hv hvodd] at hadd
  dsimp only [A, B, C]
  rw [hadd] at hnonneg
  convert hnonneg using 1
  ring

/-- The only extension premise left after the unconditional positivity of
the `P₁`-orthogonal subspace: the degree-one row must be continuous in the
complete core norm on that entire subspace. -/
def FourCellOddP1OrthogonalFormDualBound : Prop :=
  ∀ (v : ℝ → ℝ),
    ContDiff ℝ 1 v → Function.Odd v →
    centeredOddP1Coefficient v = 0 →
    fourCellOddCoreLocalBilinear centeredP1 v ^ 2 ≤
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddCoreLocalQuadratic v

/-- Canonical projection onto the `P₁`-orthogonal odd subspace. -/
def fourCellOddP1Residual (w : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  w x - centeredOddP1Coefficient w * centeredP1 x

private theorem centeredOddP1Coefficient_centeredP1_probe :
    centeredOddP1Coefficient centeredP1 = 1 := by
  unfold centeredOddP1Coefficient
  rw [show (fun x : ℝ ↦ centeredP1 x * centeredP1 x) =
      fun x ↦ centeredP1 x ^ 2 by
    funext x
    ring,
    integral_centeredP1_sq]
  norm_num

theorem centeredOddP1Coefficient_fourCellOddP1Residual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP1Coefficient (fourCellOddP1Residual w) = 0 := by
  have hp : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h := centeredOddP1Coefficient_add_const_mul_probe
    w centeredP1 (-(centeredOddP1Coefficient w)) hw hp
  have hfun : fourCellOddP1Residual w =
      w + fun x ↦ -(centeredOddP1Coefficient w) * centeredP1 x := by
    funext x
    unfold fourCellOddP1Residual
    simp only [Pi.add_apply]
    ring
  rw [hfun, h, centeredOddP1Coefficient_centeredP1_probe]
  ring

theorem contDiff_fourCellOddP1Residual
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (fourCellOddP1Residual w) := by
  unfold fourCellOddP1Residual centeredP1
  fun_prop

theorem odd_fourCellOddP1Residual
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    Function.Odd (fourCellOddP1Residual w) := by
  intro x
  unfold fourCellOddP1Residual centeredP1
  rw [hodd]
  ring

theorem fourCellOddP1Residual_add_projection
    (w : ℝ → ℝ) :
    fourCellOddP1Residual w +
        (fun x ↦ centeredOddP1Coefficient w * centeredP1 x) = w := by
  funext x
  unfold fourCellOddP1Residual
  simp only [Pi.add_apply]
  ring

private theorem coreLocalBilinear_comm_probe
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddCoreLocalBilinear u v =
      fourCellOddCoreLocalBilinear v u := by
  have huv := fourCellOddCoreLocalQuadratic_add u v hu hv
  have hvu := fourCellOddCoreLocalQuadratic_add v u hv hu
  have hadd : u + v = v + u := add_comm u v
  rw [hadd] at huv
  linarith

theorem fourCellOddCoreLocalQuadratic_centeredP1_nonneg :
    0 ≤ fourCellOddCoreLocalQuadratic centeredP1 := by
  have h := fourCellOddHalfCoreReserve_add_localWidthDefect_low_nonneg 1 0
  have hp : factorTwoOddStructuralLowProfile 1 0 = centeredP1 := by
    funext x
    unfold factorTwoOddStructuralLowProfile
    simp
  rw [hp] at h
  exact h

private theorem add_two_mul_add_nonneg_of_sq_le_mul_probe
    (A B C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hschur : B ^ 2 ≤ A * C) :
    0 ≤ A + 2 * B + C := by
  by_cases hB : 0 ≤ B
  · linarith
  · have hminus : 0 ≤ -2 * B := by linarith
    have hsum : 0 ≤ A + C := add_nonneg hA hC
    have hsquares : (-2 * B) ^ 2 ≤ (A + C) ^ 2 := by
      nlinarith [sq_nonneg (A - C)]
    have hlinear := (sq_le_sq₀ hminus hsum).mp hsquares
    linarith

/-- A single `P₁` extension-row bound upgrades the already proved
`P₁⊥` coercivity to the complete odd space. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_P1OrthogonalFormDual
    (hdual : FourCellOddP1OrthogonalFormDualBound)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  let c := centeredOddP1Coefficient w
  let r := fourCellOddP1Residual w
  let p : ℝ → ℝ := fun x ↦ c * centeredP1 x
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    unfold centeredP1
    fun_prop
  have hpodd : Function.Odd p := by
    intro x
    dsimp only [p]
    unfold centeredP1
    ring
  have hr : ContDiff ℝ 1 r := by
    dsimp only [r]
    exact contDiff_fourCellOddP1Residual w hw
  have hrodd : Function.Odd r := by
    dsimp only [r]
    exact odd_fourCellOddP1Residual w hodd
  have hrone : centeredOddP1Coefficient r = 0 := by
    dsimp only [r]
    exact centeredOddP1Coefficient_fourCellOddP1Residual_eq_zero
      w hw.continuous
  have hQr : 0 ≤ fourCellOddCoreLocalQuadratic r :=
    fourCellOddCoreLocalQuadratic_nonneg_of_P1_zero r hr hrodd hrone
  have hQp : 0 ≤ fourCellOddCoreLocalQuadratic p := by
    have hscale := coreLocalQuadratic_const_mul_probe
      centeredP1 (by unfold centeredP1; fun_prop)
        (by intro x; unfold centeredP1; ring) c
    dsimp only [p]
    rw [hscale]
    exact mul_nonneg (sq_nonneg c)
      fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hbase := hdual r hr hrodd hrone
  have hBscale : fourCellOddCoreLocalBilinear r p =
      c * fourCellOddCoreLocalBilinear centeredP1 r := by
    dsimp only [p]
    rw [coreLocalBilinear_const_mul_right_probe r centeredP1 hr
      (by unfold centeredP1; fun_prop)
      hrodd (by intro x; unfold centeredP1; ring),
      coreLocalBilinear_comm_probe r centeredP1 hr.continuous
        (by unfold centeredP1; fun_prop)]
  have hQpscale : fourCellOddCoreLocalQuadratic p =
      c ^ 2 * fourCellOddCoreLocalQuadratic centeredP1 := by
    dsimp only [p]
    exact coreLocalQuadratic_const_mul_probe
      centeredP1 (by unfold centeredP1; fun_prop)
        (by intro x; unfold centeredP1; ring) c
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  have hschur : fourCellOddCoreLocalBilinear r p ^ 2 ≤
      fourCellOddCoreLocalQuadratic r * fourCellOddCoreLocalQuadratic p := by
    rw [hBscale, hQpscale]
    nlinarith
  have hsum : 0 ≤
      fourCellOddCoreLocalQuadratic r +
        2 * fourCellOddCoreLocalBilinear r p +
          fourCellOddCoreLocalQuadratic p :=
    add_two_mul_add_nonneg_of_sq_le_mul_probe _ _ _ hQr hQp hschur
  have hadd := fourCellOddCoreLocalQuadratic_add
    r p hr.continuous hp.continuous
  have hreconstruct : r + p = w := by
    dsimp only [r, p, c]
    exact fourCellOddP1Residual_add_projection w
  rw [hreconstruct] at hadd
  linarith

/-- Consequently the same single extension premise supplies Cauchy--Schwarz
for the complete core on arbitrary smooth odd profiles. -/
theorem fourCellOddCoreLocalBilinear_sq_le_mul_of_P1OrthogonalFormDual
    (hdual : FourCellOddP1OrthogonalFormDualBound)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear u v ^ 2 ≤
      fourCellOddCoreLocalQuadratic u * fourCellOddCoreLocalQuadratic v := by
  let A := fourCellOddCoreLocalQuadratic u
  let B := fourCellOddCoreLocalBilinear u v
  let C := fourCellOddCoreLocalQuadratic v
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact fourCellOddCoreLocalQuadratic_nonneg_of_P1OrthogonalFormDual
      hdual v hv hvodd
  apply sq_le_mul_of_forall_quadratic_nonneg_probe A B C hC
  intro t
  let tv : ℝ → ℝ := fun x ↦ t * v x
  have htv : ContDiff ℝ 1 tv := by
    dsimp only [tv]
    exact contDiff_const.mul hv
  have htvodd : Function.Odd tv := by
    intro x
    dsimp only [tv]
    rw [hvodd]
    ring
  have hnonneg : 0 ≤ fourCellOddCoreLocalQuadratic (u + tv) :=
    fourCellOddCoreLocalQuadratic_nonneg_of_P1OrthogonalFormDual
      hdual (u + tv) (hu.add htv) (huodd.add htvodd)
  have hadd := fourCellOddCoreLocalQuadratic_add u tv hu.continuous htv.continuous
  dsimp only [tv] at hadd
  rw [coreLocalBilinear_const_mul_right_probe u v hu hv huodd hvodd,
    coreLocalQuadratic_const_mul_probe v hv hvodd] at hadd
  dsimp only [A, B, C]
  rw [hadd] at hnonneg
  convert hnonneg using 1
  ring

/-- The original five-mode/`P₁₁+` form-dual proposition follows from
exactly the one rank-one extension premise.  Its endpoint and higher-moment
conditions are not consumed by this implication. -/
theorem fourCellOddOneThreeFiveSevenNineEndpointFormDualBound_of_P1Orthogonal
    (hdual : FourCellOddP1OrthogonalFormDualBound) :
    fourCellOddOneThreeFiveSevenNineEndpointFormDualBound := by
  intro c d e f g r hr hrodd _hr1 _hr3 _hr5 _hr7 _hr9 _hendpoint
  exact fourCellOddCoreLocalBilinear_sq_le_mul_of_P1OrthogonalFormDual
    hdual
    (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) hr
    (odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) hrodd

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11FormDualProbeStructural
