import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenQuantitativeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRegularKernelBound

noncomputable section

/-!
# The analytic `P6/P7`--residual Schur border

Only the global analytic kernel remainders are charged here.  The symmetric
rows use the degree-six pole-free residual, while the alternating rows use
the affine antisymmetric residual.  Both estimates retain the full
correlation and are therefore infinite-dimensional rather than a finite
phase or mode certificate.
-/

/-! ## Square-valued cross-correlation bounds -/

private theorem centeredEndpointCorrelation_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (t : ℝ) :
    centeredEndpointCorrelation (u - v) t =
      centeredEndpointCorrelation u t -
        2 * factorTwoCenteredCorrelationBilinear u v t +
      centeredEndpointCorrelation v t := by
  have h := centeredEndpointCorrelation_add u (-v) hu hv.neg t
  have hbil : factorTwoCenteredCorrelationBilinear u (-v) t =
      -factorTwoCenteredCorrelationBilinear u v t := by
    simpa using factorTwoCenteredCorrelationBilinear_smul_smul
      1 (-1) u v t
  have hself : centeredEndpointCorrelation (-v) t =
      centeredEndpointCorrelation v t := by
    calc
      centeredEndpointCorrelation (-v) t =
          factorTwoCenteredCorrelationBilinear (-v) (-v) t :=
        (factorTwoCenteredCorrelationBilinear_self (-v) t).symm
      _ = (-1 : ℝ) * (-1) *
          factorTwoCenteredCorrelationBilinear v v t := by
        simpa using factorTwoCenteredCorrelationBilinear_smul_smul
          (-1) (-1) v v t
      _ = centeredEndpointCorrelation v t := by
        rw [factorTwoCenteredCorrelationBilinear_self]
        ring
  simpa [sub_eq_add_neg, hbil, hself] using h

private theorem correlationBilinear_eq_quarter_add_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear u v t =
      (centeredEndpointCorrelation (u + v) t -
        centeredEndpointCorrelation (u - v) t) / 4 := by
  rw [centeredEndpointCorrelation_add u v hu hv t,
    centeredEndpointCorrelation_sub u v hu hv t]
  ring

private theorem intrinsicEnergy_add_add_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    factorTwoIntrinsicEnergy (u + v) +
        factorTwoIntrinsicEnergy (u - v) =
      2 * (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
  have huI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume (-1) 1 := (hu.pow 2).intervalIntegrable _ _
  have hvI : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2)
      volume (-1) 1 := (hv.pow 2).intervalIntegrable _ _
  have huvI : IntervalIntegrable (fun x : ℝ ↦ u x * v x)
      volume (-1) 1 := (hu.mul hv).intervalIntegrable _ _
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ (u + v) x ^ 2) =
      fun x ↦ u x ^ 2 + 2 * (u x * v x) + v x ^ 2 by
    funext x
    simp only [Pi.add_apply]
    ring,
    show (fun x : ℝ ↦ (u - v) x ^ 2) =
      fun x ↦ u x ^ 2 - 2 * (u x * v x) + v x ^ 2 by
    funext x
    simp only [Pi.sub_apply]
    ring,
    intervalIntegral.integral_add (huI.add (huvI.const_mul 2)) hvI,
    intervalIntegral.integral_add huI (huvI.const_mul 2),
    intervalIntegral.integral_add (huI.sub (huvI.const_mul 2)) hvI,
    intervalIntegral.integral_sub huI (huvI.const_mul 2),
    intervalIntegral.integral_const_mul]
  ring

/-- The `L¹` norm of the symmetric ordered correlation is controlled by
the arithmetic mean of the two `L²` energies. -/
theorem integral_abs_factorTwoCenteredCorrelationBilinear_le_half_energy_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2, |factorTwoCenteredCorrelationBilinear u v t|) ≤
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
  let Cp : ℝ → ℝ := centeredEndpointCorrelation (u + v)
  let Cm : ℝ → ℝ := centeredEndpointCorrelation (u - v)
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u v
  have hCp : Continuous Cp := by
    dsimp only [Cp]
    exact continuous_centeredEndpointCorrelation_of_continuous (u + v)
      (hu.add hv)
  have hCm : Continuous Cm := by
    dsimp only [Cm]
    exact continuous_centeredEndpointCorrelation_of_continuous (u - v)
      (hu.sub hv)
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hpoint (t : ℝ) : |B t| ≤ (|Cp t| + |Cm t|) / 4 := by
    have hid := correlationBilinear_eq_quarter_add_sub u v hu hv t
    dsimp only [B, Cp, Cm]
    rw [hid, abs_div]
    norm_num
    nlinarith [abs_sub (centeredEndpointCorrelation (u + v) t)
      (centeredEndpointCorrelation (u - v) t)]
  have hmono : (∫ t : ℝ in 0..2, |B t|) ≤
      ∫ t : ℝ in 0..2, (|Cp t| + |Cm t|) / 4 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hB.abs.intervalIntegrable 0 2)
      (((hCp.abs.add hCm.abs).div_const 4).intervalIntegrable 0 2)
    intro t _ht
    exact hpoint t
  have hp := integral_abs_centeredEndpointCorrelation_le_energy
    (u + v) (hu.add hv)
  have hm := integral_abs_centeredEndpointCorrelation_le_energy
    (u - v) (hu.sub hv)
  have hp' : (∫ t : ℝ in 0..2, |Cp t|) ≤
      factorTwoIntrinsicEnergy (u + v) := by
    simpa only [Cp] using hp
  have hm' : (∫ t : ℝ in 0..2, |Cm t|) ≤
      factorTwoIntrinsicEnergy (u - v) := by
    simpa only [Cm] using hm
  have henergy := intrinsicEnergy_add_add_sub u v hu hv
  calc
    (∫ t : ℝ in 0..2, |factorTwoCenteredCorrelationBilinear u v t|) =
        ∫ t : ℝ in 0..2, |B t| := by rfl
    _ ≤ ∫ t : ℝ in 0..2, (|Cp t| + |Cm t|) / 4 := hmono
    _ = (1 / 4 : ℝ) *
        ((∫ t : ℝ in 0..2, |Cp t|) +
          ∫ t : ℝ in 0..2, |Cm t|) := by
      rw [show (fun t : ℝ ↦ (|Cp t| + |Cm t|) / 4) =
          fun t ↦ (1 / 4 : ℝ) * (|Cp t| + |Cm t|) by
        funext t
        ring,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          (hCp.abs.intervalIntegrable 0 2)
          (hCm.abs.intervalIntegrable 0 2)]
    _ ≤ (1 / 4 : ℝ) *
        (factorTwoIntrinsicEnergy (u + v) +
          factorTwoIntrinsicEnergy (u - v)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hp' hm') (by norm_num)
    _ = (1 / 2 : ℝ) *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
      rw [henergy]
      ring

/-- Optimizing the arithmetic-mean estimate under reciprocal rescaling gives
the product-form `L¹` Cauchy bound, stated without square roots. -/
theorem integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredCorrelationBilinear u v t|) ^ 2 ≤
      factorTwoIntrinsicEnergy u * factorTwoIntrinsicEnergy v := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear u v t|
  let Eu := factorTwoIntrinsicEnergy u
  let Ev := factorTwoIntrinsicEnergy v
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ abs_nonneg _
  have hEu0 : 0 ≤ Eu := by
    dsimp only [Eu]
    exact factorTwoIntrinsicEnergy_nonneg u
  have hEv0 : 0 ≤ Ev := by
    dsimp only [Ev]
    exact factorTwoIntrinsicEnergy_nonneg v
  by_cases hEu : Eu = 0
  · by_cases hI : I = 0
    · change I ^ 2 ≤ Eu * Ev
      rw [hI, hEu]
      norm_num
    · have hIpos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hI)
      let r : ℝ := Ev / I + 1
      have hr : 0 < r := by
        dsimp only [r]
        positivity
      have hbase :=
        integral_abs_factorTwoCenteredCorrelationBilinear_le_half_energy_add
          (r • u) v (hu.const_smul r) hv
      have hcorr (t : ℝ) :
          |factorTwoCenteredCorrelationBilinear (r • u) v t| =
            r * |factorTwoCenteredCorrelationBilinear u v t| := by
        rw [show factorTwoCenteredCorrelationBilinear (r • u) v t =
            r * factorTwoCenteredCorrelationBilinear u v t by
          simpa using factorTwoCenteredCorrelationBilinear_smul_smul
            r 1 u v t,
          abs_mul, abs_of_pos hr]
      have hscaledEnergy : factorTwoIntrinsicEnergy (r • u) = r ^ 2 * Eu := by
        unfold factorTwoIntrinsicEnergy
        rw [show (fun x : ℝ ↦ (r • u) x ^ 2) =
            fun x ↦ r ^ 2 * u x ^ 2 by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring,
          intervalIntegral.integral_const_mul]
        rfl
      simp_rw [hcorr] at hbase
      rw [intervalIntegral.integral_const_mul, hscaledEnergy] at hbase
      change r * I ≤ (1 / 2 : ℝ) * (r ^ 2 * Eu + Ev) at hbase
      rw [hEu] at hbase
      dsimp only [r] at hbase
      field_simp [hI] at hbase
      nlinarith
  · have hEupos : 0 < Eu := lt_of_le_of_ne hEu0 (Ne.symm hEu)
    let r : ℝ := I / Eu
    have hr : 0 ≤ r := by
      dsimp only [r]
      positivity
    have hbase :=
      integral_abs_factorTwoCenteredCorrelationBilinear_le_half_energy_add
        (r • u) v (hu.const_smul r) hv
    have hcorr (t : ℝ) :
        |factorTwoCenteredCorrelationBilinear (r • u) v t| =
          r * |factorTwoCenteredCorrelationBilinear u v t| := by
      rw [show factorTwoCenteredCorrelationBilinear (r • u) v t =
          r * factorTwoCenteredCorrelationBilinear u v t by
        simpa using factorTwoCenteredCorrelationBilinear_smul_smul
          r 1 u v t,
        abs_mul, abs_of_nonneg hr]
    have hscaledEnergy : factorTwoIntrinsicEnergy (r • u) = r ^ 2 * Eu := by
      unfold factorTwoIntrinsicEnergy
      rw [show (fun x : ℝ ↦ (r • u) x ^ 2) =
          fun x ↦ r ^ 2 * u x ^ 2 by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        intervalIntegral.integral_const_mul]
      rfl
    simp_rw [hcorr] at hbase
    rw [intervalIntegral.integral_const_mul, hscaledEnergy] at hbase
    change r * I ≤ (1 / 2 : ℝ) * (r ^ 2 * Eu + Ev) at hbase
    dsimp only [r] at hbase
    field_simp [hEu] at hbase
    nlinarith

/-! ## The alternating ordered cross difference -/

/-- The ordering convention used by the endpoint alternating channel. -/
def factorTwoP67ResidualAlternatingCrossDifference
    (e o : ℝ → ℝ) (t : ℝ) : ℝ :=
  factorTwoCenteredCrossCorrelation o e t -
    factorTwoCenteredCrossCorrelation e o t

private theorem continuous_factorTwoP67ResidualAlternatingCrossDifference
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    Continuous (factorTwoP67ResidualAlternatingCrossDifference e o) := by
  unfold factorTwoP67ResidualAlternatingCrossDifference
  exact (continuous_factorTwoCenteredCrossCorrelation o e hoc hec).sub
    (continuous_factorTwoCenteredCrossCorrelation e o hec hoc)

private theorem factorTwoIntrinsicEnergy_smul_real
    (r : ℝ) (w : ℝ → ℝ) :
    factorTwoIntrinsicEnergy (r • w) =
      r ^ 2 * factorTwoIntrinsicEnergy w := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ (r • w) x ^ 2) =
      fun x ↦ r ^ 2 * w x ^ 2 by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem sq_le_energy_mul_of_scaled_half_sum
    (I Eu Ev : ℝ) (hI0 : 0 ≤ I) (hEu0 : 0 ≤ Eu) (hEv0 : 0 ≤ Ev)
    (hscale : ∀ r : ℝ, 0 ≤ r →
      r * I ≤ (1 / 2 : ℝ) * (r ^ 2 * Eu + Ev)) :
    I ^ 2 ≤ Eu * Ev := by
  by_cases hEu : Eu = 0
  · by_cases hI : I = 0
    · rw [hI, hEu]
      norm_num
    · have hIpos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hI)
      let r : ℝ := Ev / I + 1
      have hr : 0 < r := by
        dsimp only [r]
        positivity
      have h := hscale r hr.le
      rw [hEu] at h
      dsimp only [r] at h
      field_simp [hI] at h
      nlinarith
  · have hEupos : 0 < Eu := lt_of_le_of_ne hEu0 (Ne.symm hEu)
    let r : ℝ := I / Eu
    have hr : 0 ≤ r := by
      dsimp only [r]
      positivity
    have h := hscale r hr
    dsimp only [r] at h
    field_simp [hEu] at h
    nlinarith

private theorem integral_abs_factorTwoCenteredCrossCorrelation_sq_le_energy_mul
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredCrossCorrelation e o t|) ^ 2 ≤
      factorTwoIntrinsicEnergy e * factorTwoIntrinsicEnergy o := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCrossCorrelation e o t|
  let Ee := factorTwoIntrinsicEnergy e
  let Eo := factorTwoIntrinsicEnergy o
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ abs_nonneg _
  have hEe0 : 0 ≤ Ee := by
    dsimp only [Ee]
    exact factorTwoIntrinsicEnergy_nonneg e
  have hEo0 : 0 ≤ Eo := by
    dsimp only [Eo]
    exact factorTwoIntrinsicEnergy_nonneg o
  apply sq_le_energy_mul_of_scaled_half_sum I Ee Eo hI0 hEe0 hEo0
  intro r hr
  have hbase := integral_abs_crossCorrelation_le_half_energy_add
    (r • e) o (hec.const_smul r) hoc
    (he.const_smul r) ho
  have hcorr (t : ℝ) :
      |factorTwoCenteredCrossCorrelation (r • e) o t| =
        r * |factorTwoCenteredCrossCorrelation e o t| := by
    rw [factorTwoCenteredCrossCorrelation_smul_left, abs_mul,
      abs_of_nonneg hr]
  simp_rw [hcorr] at hbase
  rw [intervalIntegral.integral_const_mul,
    factorTwoIntrinsicEnergy_smul_real] at hbase
  exact hbase

/-- The ordered even--odd cross difference has a square-valued `L¹` bound.
The factor four records the exact parity identity `difference = -2 * cross`.
-/
theorem integral_abs_factorTwoP67ResidualAlternatingCrossDifference_sq_le_four_energy_mul
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
        |factorTwoP67ResidualAlternatingCrossDifference e o t|) ^ 2 ≤
      4 * factorTwoIntrinsicEnergy e * factorTwoIntrinsicEnergy o := by
  have hcross :=
    integral_abs_factorTwoCenteredCrossCorrelation_sq_le_energy_mul
      e o hec hoc he ho
  have hparity (t : ℝ) :
      factorTwoP67ResidualAlternatingCrossDifference e o t =
        -2 * factorTwoCenteredCrossCorrelation e o t := by
    exact factorTwo_crossDifference_eq_neg_two_cross_of_even_odd he ho t
  simp_rw [hparity, abs_mul, abs_neg, abs_of_nonneg (by norm_num :
    (0 : ℝ) ≤ 2), intervalIntegral.integral_const_mul]
  nlinarith

/-! ## The two analytic border errors -/

/-- Symmetric degree-six analytic remainder between two profiles.  This is
already the half-cross term appearing in a low--tail phase polarization. -/
def factorTwoP67ResidualSymmetricAnalyticBorder
    (u r : ℝ → ℝ) : ℝ :=
  poleFreeAnalyticError
    (fun t ↦ factorTwoCenteredCorrelationBilinear u r t)

/-- Alternating affine-kernel remainder between an even and an odd profile. -/
def factorTwoP67ResidualAlternatingAnalyticBorder
    (e o : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) *
      factorTwoP67ResidualAlternatingCrossDifference e o t

private theorem measurable_yoshidaRegularKernel_p67Residual :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredAntisymmetricRegularWeight_p67Residual :
    Measurable factorTwoCenteredAntisymmetricRegularWeight := by
  unfold factorTwoCenteredAntisymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).sub
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_p67Residual.comp (by fun_prop))).add
        (measurable_yoshidaRegularKernel_p67Residual.comp (by fun_prop))

private theorem intervalIntegrable_alternatingAnalyticBorder
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredAntisymmetricRegularWeight_p67Residual).sub
        (measurable_id.div_const 10)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1.le ht.2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- The alternating analytic border is bounded by one thousandth of the
ordered cross-difference `L¹` norm. -/
theorem abs_factorTwoP67ResidualAlternatingAnalyticBorder_le
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    |factorTwoP67ResidualAlternatingAnalyticBorder e o| ≤
      (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2,
          |factorTwoP67ResidualAlternatingCrossDifference e o t|) := by
  let C : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference e o
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_factorTwoP67ResidualAlternatingCrossDifference e o hec hoc
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_alternatingAnalyticBorder C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 1000 : ℝ)).intervalIntegrable 0 2
  have hmono : (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1 ht.2
    dsimp only [f, g]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  calc
    |factorTwoP67ResidualAlternatingAnalyticBorder e o| =
        |∫ t : ℝ in 0..2, f t| := by rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2, |C t|) := by
      rw [intervalIntegral.integral_const_mul]

/-- The symmetric analytic row has squared coefficient
`(3 / 8000)^2 = 9 / 64000000`. -/
theorem factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r) :
    factorTwoP67ResidualSymmetricAnalyticBorder u r ^ 2 ≤
      (9 / 64000000 : ℝ) *
        factorTwoIntrinsicEnergy u * factorTwoIntrinsicEnergy r := by
  let C : ℝ → ℝ := fun t ↦ factorTwoCenteredCorrelationBilinear u r t
  let I : ℝ := ∫ t : ℝ in 0..2, |C t|
  let E : ℝ := factorTwoP67ResidualSymmetricAnalyticBorder u r
  let k : ℝ := 3 / 8000
  have hC : Continuous C := by
    dsimp only [C]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u r hu hr).add
      (continuous_factorTwoCenteredCrossCorrelation r u hr hu)).div_const 2
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ abs_nonneg _
  have hk0 : 0 ≤ k := by norm_num [k]
  have herr : |E| ≤ k * I := by
    simpa only [E, k, I, C, factorTwoP67ResidualSymmetricAnalyticBorder]
      using abs_poleFreeAnalyticError_le C hC
  have herrProduct :
      0 ≤ (k * I - |E|) * (k * I + |E|) :=
    mul_nonneg (sub_nonneg.mpr herr)
      (add_nonneg (mul_nonneg hk0 hI0) (abs_nonneg E))
  have herrSq : E ^ 2 ≤ k ^ 2 * I ^ 2 := by
    nlinarith [sq_abs E]
  have hI := integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
    u r hu hr
  have hscaled := mul_le_mul_of_nonneg_left hI (sq_nonneg k)
  dsimp only [E, k] at herrSq ⊢
  norm_num at herrSq hscaled ⊢
  nlinarith

/-- The alternating analytic error has squared coefficient `1 / 250000`
before the phase mixed-term factor `b / 2` is applied. -/
theorem factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    factorTwoP67ResidualAlternatingAnalyticBorder e o ^ 2 ≤
      (1 / 250000 : ℝ) *
        factorTwoIntrinsicEnergy e * factorTwoIntrinsicEnergy o := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoP67ResidualAlternatingCrossDifference e o t|
  let E : ℝ := factorTwoP67ResidualAlternatingAnalyticBorder e o
  let k : ℝ := 1 / 1000
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ abs_nonneg _
  have hk0 : 0 ≤ k := by norm_num [k]
  have herr : |E| ≤ k * I := by
    simpa only [E, k, I] using
      abs_factorTwoP67ResidualAlternatingAnalyticBorder_le e o hec hoc
  have herrProduct :
      0 ≤ (k * I - |E|) * (k * I + |E|) :=
    mul_nonneg (sub_nonneg.mpr herr)
      (add_nonneg (mul_nonneg hk0 hI0) (abs_nonneg E))
  have herrSq : E ^ 2 ≤ k ^ 2 * I ^ 2 := by
    nlinarith [sq_abs E]
  have hI :=
    integral_abs_factorTwoP67ResidualAlternatingCrossDifference_sq_le_four_energy_mul
      e o hec hoc he ho
  have hscaled := mul_le_mul_of_nonneg_left hI (sq_nonneg k)
  dsimp only [E, k] at herrSq ⊢
  norm_num at herrSq hscaled ⊢
  nlinarith

/-! ## The four-row Schur assembly -/

/-- A square-root-free weighted Cauchy estimate for the four Cartesian
rows of a two-by-two low--residual border.  The normalized row weights are
`9/2560`, `1/4`, `1/40`, and `9/256`; their sum is the strict Schur budget
`803/2560 < 1`.
-/
private theorem four_row_schur_of_normalized_sq_bounds
    (z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁)
    (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hz₀₀ : z₀₀ ^ 2 ≤ (9 / 2560 : ℝ) * x₀ * y₀)
    (hz₀₁ : z₀₁ ^ 2 ≤ (1 / 4 : ℝ) * x₀ * y₁)
    (hz₁₀ : z₁₀ ^ 2 ≤ (1 / 40 : ℝ) * x₁ * y₀)
    (hz₁₁ : z₁₁ ^ 2 ≤ (9 / 256 : ℝ) * x₁ * y₁) :
    (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
      (x₀ + x₁) * (y₀ + y₁) := by
  have h₀₀ : z₀₀ ^ 2 / (9 / 2560 : ℝ) ≤ x₀ * y₀ := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 2560)).2
    nlinarith
  have h₀₁ : z₀₁ ^ 2 / (1 / 4 : ℝ) ≤ x₀ * y₁ := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)).2
    nlinarith
  have h₁₀ : z₁₀ ^ 2 / (1 / 40 : ℝ) ≤ x₁ * y₀ := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 40)).2
    nlinarith
  have h₁₁ : z₁₁ ^ 2 / (9 / 256 : ℝ) ≤ x₁ * y₁ := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 256)).2
    nlinarith
  have hidentity :
      (803 / 2560 : ℝ) *
          (z₀₀ ^ 2 / (9 / 2560 : ℝ) +
            z₀₁ ^ 2 / (1 / 4 : ℝ) +
            z₁₀ ^ 2 / (1 / 40 : ℝ) +
            z₁₁ ^ 2 / (9 / 256 : ℝ)) -
          (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 =
        (((1 / 4 : ℝ) * z₀₀ - (9 / 2560 : ℝ) * z₀₁) ^ 2 /
            ((9 / 2560 : ℝ) * (1 / 4 : ℝ)) +
          (((1 / 40 : ℝ) * z₀₀ - (9 / 2560 : ℝ) * z₁₀) ^ 2 /
            ((9 / 2560 : ℝ) * (1 / 40 : ℝ)) +
          (((9 / 256 : ℝ) * z₀₀ - (9 / 2560 : ℝ) * z₁₁) ^ 2 /
            ((9 / 2560 : ℝ) * (9 / 256 : ℝ)) +
          (((1 / 40 : ℝ) * z₀₁ - (1 / 4 : ℝ) * z₁₀) ^ 2 /
            ((1 / 4 : ℝ) * (1 / 40 : ℝ)) +
          (((9 / 256 : ℝ) * z₀₁ - (1 / 4 : ℝ) * z₁₁) ^ 2 /
            ((1 / 4 : ℝ) * (9 / 256 : ℝ)) +
          (((9 / 256 : ℝ) * z₁₀ - (1 / 40 : ℝ) * z₁₁) ^ 2 /
            ((1 / 40 : ℝ) * (9 / 256 : ℝ)))))))) := by
    ring
  have hweighted :
      (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
        (803 / 2560 : ℝ) *
          (z₀₀ ^ 2 / (9 / 2560 : ℝ) +
            z₀₁ ^ 2 / (1 / 4 : ℝ) +
            z₁₀ ^ 2 / (1 / 40 : ℝ) +
            z₁₁ ^ 2 / (9 / 256 : ℝ)) := by
    rw [← sub_nonneg, hidentity]
    positivity
  have hrows :
      z₀₀ ^ 2 / (9 / 2560 : ℝ) +
          z₀₁ ^ 2 / (1 / 4 : ℝ) +
          z₁₀ ^ 2 / (1 / 40 : ℝ) +
          z₁₁ ^ 2 / (9 / 256 : ℝ) ≤
        x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁ := by
    linarith
  have hpairs : 0 ≤ x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁ := by
    positivity
  calc
    (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 ≤
        (803 / 2560 : ℝ) *
          (z₀₀ ^ 2 / (9 / 2560 : ℝ) +
            z₀₁ ^ 2 / (1 / 4 : ℝ) +
            z₁₀ ^ 2 / (1 / 40 : ℝ) +
            z₁₁ ^ 2 / (9 / 256 : ℝ)) := hweighted
    _ ≤ (803 / 2560 : ℝ) *
        (x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁) :=
      mul_le_mul_of_nonneg_left hrows (by norm_num)
    _ ≤ x₀ * y₀ + x₀ * y₁ + x₁ * y₀ + x₁ * y₁ :=
      mul_le_of_le_one_left hpairs (by norm_num)
    _ = (x₀ + x₁) * (y₀ + y₁) := by ring

/-- The four analytic error rows coupling a degree-six/seven block to an
even/odd residual.  This deliberately names only the analytic kernel
remainders; it is not an identification with the complete endpoint mixed
phase block.
-/
def factorTwoP67ResidualAnalyticMixed
    (p₆ p₇ eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  a * (factorTwoP67ResidualSymmetricAnalyticBorder p₆ eR +
      factorTwoP67ResidualSymmetricAnalyticBorder p₇ oR) +
    (b / 2) * (factorTwoP67ResidualAlternatingAnalyticBorder p₆ oR +
      factorTwoP67ResidualAlternatingAnalyticBorder eR p₇)

/-- The complete analytic `P6/P7`--residual border fits inside the retained
`1/100` low reserves and `1/250`, `1/2500` residual reserves.  The normalized
four-row budget is exactly `803/2560`, so the proof retains strict Schur
slack and does not enumerate residual modes.
-/
theorem factorTwoP67ResidualAnalyticMixed_sq_le_reserve_mul
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (hp₆e : Function.Even p₆) (hp₇o : Function.Odd p₇)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP67ResidualAnalyticMixed p₆ p₇ eR oR a b ^ 2 ≤
      ((1 / 100 : ℝ) * factorTwoIntrinsicEnergy p₆ +
          (1 / 100 : ℝ) * factorTwoIntrinsicEnergy p₇) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
  let E₆ := factorTwoIntrinsicEnergy p₆
  let E₇ := factorTwoIntrinsicEnergy p₇
  let Ee := factorTwoIntrinsicEnergy eR
  let Eo := factorTwoIntrinsicEnergy oR
  let z₀₀ := a * factorTwoP67ResidualSymmetricAnalyticBorder p₆ eR
  let z₀₁ := (b / 2) * factorTwoP67ResidualAlternatingAnalyticBorder p₆ oR
  let z₁₀ := (b / 2) * factorTwoP67ResidualAlternatingAnalyticBorder eR p₇
  let z₁₁ := a * factorTwoP67ResidualSymmetricAnalyticBorder p₇ oR
  let x₀ := (1 / 100 : ℝ) * E₆
  let x₁ := (1 / 100 : ℝ) * E₇
  let y₀ := (1 / 250 : ℝ) * Ee
  let y₁ := (1 / 2500 : ℝ) * Eo
  have hE₆ : 0 ≤ E₆ := factorTwoIntrinsicEnergy_nonneg p₆
  have hE₇ : 0 ≤ E₇ := factorTwoIntrinsicEnergy_nonneg p₇
  have hEe : 0 ≤ Ee := factorTwoIntrinsicEnergy_nonneg eR
  have hEo : 0 ≤ Eo := factorTwoIntrinsicEnergy_nonneg oR
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hsym₆ := factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
    p₆ eR hp₆c heRc
  have hsym₇ := factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
    p₇ oR hp₇c hoRc
  have halt₆ := factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
    p₆ oR hp₆c hoRc hp₆e hoRo
  have halt₇ := factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
    eR p₇ heRc hp₇c heRe hp₇o
  have hz₀₀ : z₀₀ ^ 2 ≤ (9 / 2560 : ℝ) * x₀ * y₀ := by
    have hscale := mul_le_mul_of_nonneg_left hsym₆ (sq_nonneg a)
    have hrow : 0 ≤ (9 / 64000000 : ℝ) * E₆ * Ee := by positivity
    have hcontract := mul_le_mul_of_nonneg_right ha hrow
    dsimp only [z₀₀, x₀, y₀, E₆, Ee] at ⊢
    rw [mul_pow]
    norm_num at hscale hcontract ⊢
    nlinarith
  have hz₀₁ : z₀₁ ^ 2 ≤ (1 / 4 : ℝ) * x₀ * y₁ := by
    have hscale := mul_le_mul_of_nonneg_left halt₆ (sq_nonneg (b / 2))
    have hbquarter : (b / 2) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
    have hrow : 0 ≤ (1 / 250000 : ℝ) * E₆ * Eo := by positivity
    have hcontract := mul_le_mul_of_nonneg_right hbquarter hrow
    dsimp only [z₀₁, x₀, y₁, E₆, Eo] at ⊢
    rw [mul_pow]
    norm_num at hscale hcontract ⊢
    nlinarith
  have hz₁₀ : z₁₀ ^ 2 ≤ (1 / 40 : ℝ) * x₁ * y₀ := by
    have hscale := mul_le_mul_of_nonneg_left halt₇ (sq_nonneg (b / 2))
    have hbquarter : (b / 2) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
    have hrow : 0 ≤ (1 / 250000 : ℝ) * Ee * E₇ := by positivity
    have hcontract := mul_le_mul_of_nonneg_right hbquarter hrow
    dsimp only [z₁₀, x₁, y₀, E₇, Ee] at ⊢
    rw [mul_pow]
    norm_num at hscale hcontract ⊢
    nlinarith
  have hz₁₁ : z₁₁ ^ 2 ≤ (9 / 256 : ℝ) * x₁ * y₁ := by
    have hscale := mul_le_mul_of_nonneg_left hsym₇ (sq_nonneg a)
    have hrow : 0 ≤ (9 / 64000000 : ℝ) * E₇ * Eo := by positivity
    have hcontract := mul_le_mul_of_nonneg_right ha hrow
    dsimp only [z₁₁, x₁, y₁, E₇, Eo] at ⊢
    rw [mul_pow]
    norm_num at hscale hcontract ⊢
    nlinarith
  have hschur := four_row_schur_of_normalized_sq_bounds
    z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁
    (by dsimp only [x₀]; positivity)
    (by dsimp only [x₁]; positivity)
    (by dsimp only [y₀]; positivity)
    (by dsimp only [y₁]; positivity)
    hz₀₀ hz₀₁ hz₁₀ hz₁₁
  dsimp only [factorTwoP67ResidualAnalyticMixed, z₀₀, z₀₁,
    z₁₀, z₁₁, x₀, x₁, y₀, y₁, E₆, E₇, Ee, Eo] at hschur ⊢
  convert hschur using 1
  all_goals ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
