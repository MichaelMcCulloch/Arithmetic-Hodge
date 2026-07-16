import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural

noncomputable section

open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenLowPotential
open YoshidaConstantBounds
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointRegularCorrelation
open YoshidaRegularKernelBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaFactorTwoPhaseSymmetricCoercivity

/-!
# Structural clean `P1/P3`--`P5` crosses

The singular potential part is evaluated exactly from four even logarithmic
moments.  Its logarithmic terms cancel by Legendre orthogonality.  The
remaining regular and hyperbolic crosses are treated by global analytic
envelopes below; no interval subdivision or finite certificate is used.
-/

private theorem measurable_yoshidaRegularKernel_local :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

/-- The regular kernel paired with any continuous correlation is integrable
on the complete overlap interval. -/
private theorem intervalIntegrable_regularKernel_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ yoshidaRegularKernel (yoshidaEndpointA * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (yoshidaEndpointA * t) * C t
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
    exact (measurable_yoshidaRegularKernel_local.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have harg0 : 0 ≤ yoshidaEndpointA * t :=
      mul_nonneg yoshidaEndpointA_pos.le htIcc.1
    have harg2 : yoshidaEndpointA * t ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left htIcc.2
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hK := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK.1]
    exact mul_le_mul_of_nonneg_right hK.2 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- Polarizing the regular quadratic turns its symmetric cross exactly into
the symmetric overlap correlation. -/
theorem re_yoshidaEndpointRegularRealBilinear_add_eq_correlation
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (yoshidaEndpointRegularRealBilinear u v +
        yoshidaEndpointRegularRealBilinear v u).re =
      4 * ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t := by
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous (factorTwoCenteredCorrelationBilinear u v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hIu := intervalIntegrable_regularKernel_mul
    (centeredEndpointCorrelation u) hCu
  have hIv := intervalIntegrable_regularKernel_mul
    (centeredEndpointCorrelation v) hCv
  have hIb := intervalIntegrable_regularKernel_mul
    (factorTwoCenteredCorrelationBilinear u v) hB
  have hsum := re_yoshidaEndpointRegularQuadratic_eq_correlation
    (u + v) (hu.add hv)
  have huq := re_yoshidaEndpointRegularQuadratic_eq_correlation u hu
  have hvq := re_yoshidaEndpointRegularQuadratic_eq_correlation v hv
  have hpolar := congrArg Complex.re
    (yoshidaEndpointRegularQuadratic_add_ofReal u v hu hv)
  simp only [add_re] at hpolar
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        centeredEndpointCorrelation (u + v) t) =
      fun t ↦
        yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation u t +
          2 * (yoshidaRegularKernel (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u v t) +
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation v t by
    funext t
    rw [centeredEndpointCorrelation_add u v hu hv t]
    ring,
    intervalIntegral.integral_add (hIu.add (hIb.const_mul 2)) hIv,
    intervalIntegral.integral_add hIu (hIb.const_mul 2),
    intervalIntegral.integral_const_mul] at hsum
  simp only [Pi.add_apply] at hsum
  rw [hsum, huq, hvq] at hpolar
  simp only [add_re]
  linarith

private theorem integral_tenth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 10 * Real.log (1 - x)) =
      -83711 / 304920 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 10 * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ 10 * Real.log (1 - x)) =
        ∫ x : ℝ in 0..1, g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ∫ x : ℝ in 0..1, g x := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := g)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = ∫ x : ℝ in 0..1,
        x ^ 10 * Real.log x - 10 * (x ^ 9 * Real.log x) +
          45 * (x ^ 8 * Real.log x) - 120 * (x ^ 7 * Real.log x) +
          210 * (x ^ 6 * Real.log x) - 252 * (x ^ 5 * Real.log x) +
          210 * (x ^ 4 * Real.log x) - 120 * (x ^ 3 * Real.log x) +
          45 * (x ^ 2 * Real.log x) - 10 * (x ^ 1 * Real.log x) +
          x ^ 0 * Real.log x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = (∫ x : ℝ in 0..1, x ^ 10 * Real.log x) -
          10 * (∫ x : ℝ in 0..1, x ^ 9 * Real.log x) +
          45 * (∫ x : ℝ in 0..1, x ^ 8 * Real.log x) -
          120 * (∫ x : ℝ in 0..1, x ^ 7 * Real.log x) +
          210 * (∫ x : ℝ in 0..1, x ^ 6 * Real.log x) -
          252 * (∫ x : ℝ in 0..1, x ^ 5 * Real.log x) +
          210 * (∫ x : ℝ in 0..1, x ^ 4 * Real.log x) -
          120 * (∫ x : ℝ in 0..1, x ^ 3 * Real.log x) +
          45 * (∫ x : ℝ in 0..1, x ^ 2 * Real.log x) -
          10 * (∫ x : ℝ in 0..1, x ^ 1 * Real.log x) +
          ∫ x : ℝ in 0..1, x ^ 0 * Real.log x := by
      have hJ (n : ℕ) : IntervalIntegrable
          (fun x : ℝ ↦ x ^ n * Real.log x) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.continuousOn_mul
          (continuous_pow n).continuousOn
      rw [intervalIntegral.integral_add
          (((((((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120)).add
            ((hJ 6).const_mul 210)).sub ((hJ 5).const_mul 252)).add
            ((hJ 4).const_mul 210)).sub ((hJ 3).const_mul 120)).add
            ((hJ 2).const_mul 45) |>.sub ((hJ 1).const_mul 10)) (hJ 0),
        intervalIntegral.integral_sub
          ((((((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120)).add
            ((hJ 6).const_mul 210)).sub ((hJ 5).const_mul 252)).add
            ((hJ 4).const_mul 210)).sub ((hJ 3).const_mul 120) |>.add
            ((hJ 2).const_mul 45)) ((hJ 1).const_mul 10),
        intervalIntegral.integral_add
          (((((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120)).add
            ((hJ 6).const_mul 210)).sub ((hJ 5).const_mul 252)).add
            ((hJ 4).const_mul 210) |>.sub ((hJ 3).const_mul 120))
            ((hJ 2).const_mul 45),
        intervalIntegral.integral_sub
          ((((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120)).add
            ((hJ 6).const_mul 210)).sub ((hJ 5).const_mul 252) |>.add
            ((hJ 4).const_mul 210)) ((hJ 3).const_mul 120),
        intervalIntegral.integral_add
          (((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120)).add
            ((hJ 6).const_mul 210) |>.sub ((hJ 5).const_mul 252))
            ((hJ 4).const_mul 210),
        intervalIntegral.integral_sub
          ((((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45)).sub ((hJ 7).const_mul 120) |>.add
            ((hJ 6).const_mul 210)) ((hJ 5).const_mul 252),
        intervalIntegral.integral_add
          (((hJ 10).sub ((hJ 9).const_mul 10)).add
            ((hJ 8).const_mul 45) |>.sub ((hJ 7).const_mul 120))
            ((hJ 6).const_mul 210),
        intervalIntegral.integral_sub
          ((hJ 10).sub ((hJ 9).const_mul 10) |>.add
            ((hJ 8).const_mul 45)) ((hJ 7).const_mul 120),
        intervalIntegral.integral_add
          ((hJ 10).sub ((hJ 9).const_mul 10)) ((hJ 8).const_mul 45),
        intervalIntegral.integral_sub (hJ 10) ((hJ 9).const_mul 10)]
      repeat rw [intervalIntegral.integral_const_mul]
    _ = -83711 / 304920 := by
      repeat rw [integral_pow_mul_log_zero_one]
      norm_num

private theorem integral_tenth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 10 * Real.log (1 + x)) =
      (2 / 11 : ℝ) * Real.log 2 - 20417 / 304920 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 11 / 11 * Real.log (1 + x) - x ^ 11 / 121 + x ^ 10 / 110 -
      x ^ 9 / 99 + x ^ 8 / 88 - x ^ 7 / 77 + x ^ 6 / 66 -
      x ^ 5 / 55 + x ^ 4 / 44 - x ^ 3 / 33 + x ^ 2 / 22 -
      x / 11 + Real.log (1 + x) / 11
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (x ^ 10 * Real.log (1 + x)) x := by
    have hone : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
        ((1 + x)⁻¹) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_log hx).comp x hone
    dsimp only [F]
    convert (((hasDerivAt_id x).pow 11).div_const 11 |>.mul hlog)
      |>.sub (((hasDerivAt_id x).pow 11).div_const 121)
      |>.add (((hasDerivAt_id x).pow 10).div_const 110)
      |>.sub (((hasDerivAt_id x).pow 9).div_const 99)
      |>.add (((hasDerivAt_id x).pow 8).div_const 88)
      |>.sub (((hasDerivAt_id x).pow 7).div_const 77)
      |>.add (((hasDerivAt_id x).pow 6).div_const 66)
      |>.sub (((hasDerivAt_id x).pow 5).div_const 55)
      |>.add (((hasDerivAt_id x).pow 4).div_const 44)
      |>.sub (((hasDerivAt_id x).pow 3).div_const 33)
      |>.add (((hasDerivAt_id x).pow 2).div_const 22)
      |>.sub ((hasDerivAt_id x).div_const 11)
      |>.add (hlog.div_const 11) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ 10 * Real.log (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow 10).mul hlog).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  ring

private theorem intervalIntegrable_tenth_mul_log_one_sub :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 10 * Real.log (1 - x))
      volume 0 1 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 10 * Real.log y
  have hg : IntervalIntegrable g volume 0 1 := by
    have hbase : IntervalIntegrable
        (fun y : ℝ ↦ (1 - y) ^ 10 * Real.log y) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
        |>.continuousOn_mul
          ((continuous_const.sub continuous_id).pow 10).continuousOn
    simpa only [g] using hbase
  have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
      volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
  apply hreflect.congr
  intro x _hx
  dsimp only [g]
  ring

private theorem intervalIntegrable_tenth_mul_log_one_add :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 10 * Real.log (1 + x))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxu : x ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
  have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
    exact ((Real.hasDerivAt_log hxne).comp x
      (by simpa using
        (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
  exact ((continuousAt_id.pow 10).mul hlog).continuousWithinAt

/-- Exact tenth moment of the logarithmic endpoint potential. -/
theorem integral_endpointPotential_mul_pow_ten :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 10) =
      13016 / 38115 - (2 / 11 : ℝ) * Real.log 2 := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 10
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    congr 1
    · congr 3
      ring
    · ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ 10 * Real.log (1 - x) + x ^ 10 * Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hrRight : IntervalIntegrable r volume 0 1 := by
    have hsum := intervalIntegrable_tenth_mul_log_one_sub.add
      intervalIntegrable_tenth_mul_log_one_add
    have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
    simpa only [r] using hscaled
  have hqRight : IntervalIntegrable q volume 0 1 := by
    have hrev : r =ᵐ[volume] q := by
      filter_upwards [hpoint] with x hx
      exact hx.symm
    apply hrRight.congr_ae
    exact hrev.filter_mono (ae_mono Measure.restrict_le_self)
  have hqLeft : IntervalIntegrable q volume (-1) 0 := by
    have hneg : IntervalIntegrable (fun x : ℝ ↦ q (-x)) volume (-1) 0 := by
      simpa only [zero_sub, sub_zero] using (hqRight.comp_sub_left 0).symm
    apply hneg.congr
    intro x _hx
    exact hqEven x
  have hfold : (∫ x : ℝ in -1..1, q x) =
      2 * ∫ x : ℝ in 0..1, q x := by
    have hreflect : (∫ x : ℝ in 0..1, q (-x)) =
        ∫ x : ℝ in -1..0, q x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := q) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, q x) =
          (∫ x : ℝ in -1..0, q x) + ∫ x : ℝ in 0..1, q x :=
        (intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight).symm
      _ = (∫ x : ℝ in 0..1, q x) + ∫ x : ℝ in 0..1, q x := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hqEven x
      _ = _ := by ring
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * x ^ 10) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ 10 * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ 10 * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ 10 * Real.log (1 - x) +
                x ^ 10 * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ 10 * Real.log (1 - x) +
              x ^ 10 * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add
          intervalIntegrable_tenth_mul_log_one_sub
          intervalIntegrable_tenth_mul_log_one_add]
  rw [hsplit, integral_tenth_mul_log_one_sub,
    integral_tenth_mul_log_one_add]
  ring

/-- Exact endpoint-potential mass of the centered fifth Legendre mode. -/
theorem integral_endpointPotential_mul_factorTwoCenteredP5_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP5 x ^ 2) =
        19157 / 76230 - (2 / 11 : ℝ) * Real.log 2 := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 4) (continuous_id.pow 4)).congr
    intro x _hx
    ring
  have h10 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 10) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 5) (continuous_id.pow 5)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP5 x ^ 2) =
      fun x ↦ (3969 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 10) -
        (8820 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) +
        (6790 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (2100 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
        (225 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold factorTwoCenteredP5
    ring,
    intervalIntegral.integral_add
      (((h10.const_mul (3969 / 64 : ℝ)).sub
        (h8.const_mul (8820 / 64 : ℝ))).add
          (h6.const_mul (6790 / 64 : ℝ)) |>.sub
          (h4.const_mul (2100 / 64 : ℝ)))
      (h2.const_mul (225 / 64 : ℝ)),
    intervalIntegral.integral_sub
      (((h10.const_mul (3969 / 64 : ℝ)).sub
        (h8.const_mul (8820 / 64 : ℝ))).add
          (h6.const_mul (6790 / 64 : ℝ)))
      (h4.const_mul (2100 / 64 : ℝ)),
    intervalIntegral.integral_add
      ((h10.const_mul (3969 / 64 : ℝ)).sub
        (h8.const_mul (8820 / 64 : ℝ)))
      (h6.const_mul (6790 / 64 : ℝ)),
    intervalIntegral.integral_sub
      (h10.const_mul (3969 / 64 : ℝ))
      (h8.const_mul (8820 / 64 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_ten,
    integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact potential part of the clean `P1`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP1_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP5 x) = (1 / 14 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP5 x) =
      fun x ↦ (63 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (70 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
        (15 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP1 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_add
      ((h6.const_mul (63 / 8 : ℝ)).sub (h4.const_mul (70 / 8 : ℝ)))
      (h2.const_mul (15 / 8 : ℝ)),
    intervalIntegral.integral_sub
      (h6.const_mul (63 / 8 : ℝ)) (h4.const_mul (70 / 8 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact potential part of the clean `P3`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP3_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP5 x) = (1 / 9 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 4) (continuous_id.pow 4)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP5 x) =
      fun x ↦ (315 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (539 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
        (285 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (45 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP3 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_sub
      (((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ))).add
          (h4.const_mul (285 / 16 : ℝ)))
      (h2.const_mul (45 / 16 : ℝ)),
    intervalIntegral.integral_add
      ((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ)))
      (h4.const_mul (285 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h8.const_mul (315 / 16 : ℝ)) (h6.const_mul (539 / 16 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-! ## The single global regular-kernel polynomial -/

/-- Sixth-order regular-kernel model for the `P1`--`P5` cross. -/
def oddP5CleanRegularPolynomial15 : ℝ :=
  yoshidaEndpointA ^ 3 / 712800 +
    31 * yoshidaEndpointA ^ 5 / 90810720 +
      61 * yoshidaEndpointA ^ 6 / 1995840

/-- Sixth-order regular-kernel model for the `P3`--`P5` cross. -/
def oddP5CleanRegularPolynomial35 : ℝ :=
  -yoshidaEndpointA / 8316 - yoshidaEndpointA ^ 3 / 772200 -
    31 * yoshidaEndpointA ^ 5 / 544864320

private def regularKernelCoefficient : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => -1 / 48
  | 2 => -1 / 32
  | 3 => 7 / 11520
  | 4 => 5 / 1536
  | 5 => -31 / 1935360
  | 6 => -61 / 184320
  | _ => 0

private def oddP5Correlation15Coefficient : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => 7
  | 3 => -15
  | 4 => 105 / 8
  | 5 => -35 / 8
  | 6 => 0
  | 7 => 3 / 16
  | _ => 0

private def oddP5Correlation35Coefficient : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => 9 / 2
  | 3 => -5
  | 4 => 0
  | 5 => 15 / 8
  | 6 => 0
  | 7 => -7 / 16
  | 8 => 0
  | 9 => 5 / 128
  | _ => 0

private theorem integral_double_polynomial_zero_two
    (N M : ℕ) (a : ℕ → ℕ → ℝ) :
    (∫ t : ℝ in 0..2,
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        a i j * t ^ (i + j)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        a i j * (2 : ℝ) ^ (i + j + 1) / (i + j + 1) := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    · intro j hj
      exact ((continuous_id.pow (i + j)).const_mul (a i j))
        |>.intervalIntegrable 0 2
  · intro i hi
    apply Continuous.intervalIntegrable
    fun_prop

private theorem regularKernelPolynomial_eq_sum (t : ℝ) :
    yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) =
      ∑ i ∈ Finset.range 7,
        regularKernelCoefficient i * yoshidaEndpointA ^ i * t ^ i := by
  simp [yoshidaRegularKernelPolynomial6, regularKernelCoefficient,
    Finset.sum_range_succ]
  ring

private theorem oddP5Correlation15_eq_sum (t : ℝ) :
    oddP5Correlation15 t =
      ∑ j ∈ Finset.range 8,
        oddP5Correlation15Coefficient j * t ^ j := by
  simp [oddP5Correlation15, oddP5Correlation15Coefficient,
    Finset.sum_range_succ]
  ring

private theorem oddP5Correlation35_eq_sum (t : ℝ) :
    oddP5Correlation35 t =
      ∑ j ∈ Finset.range 10,
        oddP5Correlation35Coefficient j * t ^ j := by
  simp [oddP5Correlation35, oddP5Correlation35Coefficient,
    Finset.sum_range_succ]
  ring

/-- Exact polynomial regular-kernel integral for the `P1`--`P5` cross. -/
theorem integral_regularKernelPolynomial_mul_oddP5Correlation15 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation15 t) = oddP5CleanRegularPolynomial15 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation15 t) =
      fun t ↦ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 8,
        (regularKernelCoefficient i * oddP5Correlation15Coefficient j *
          yoshidaEndpointA ^ i) * t ^ (i + j) by
    funext t
    rw [regularKernelPolynomial_eq_sum, oddP5Correlation15_eq_sum]
    simp [regularKernelCoefficient, oddP5Correlation15Coefficient,
      Finset.sum_range_succ]
    ring,
    integral_double_polynomial_zero_two]
  norm_num [regularKernelCoefficient, oddP5Correlation15Coefficient,
    oddP5CleanRegularPolynomial15, Finset.sum_range_succ]
  ring

/-- Exact polynomial regular-kernel integral for the `P3`--`P5` cross. -/
theorem integral_regularKernelPolynomial_mul_oddP5Correlation35 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation35 t) = oddP5CleanRegularPolynomial35 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation35 t) =
      fun t ↦ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 10,
        (regularKernelCoefficient i * oddP5Correlation35Coefficient j *
          yoshidaEndpointA ^ i) * t ^ (i + j) by
    funext t
    rw [regularKernelPolynomial_eq_sum, oddP5Correlation35_eq_sum]
    simp [regularKernelCoefficient, oddP5Correlation35Coefficient,
      Finset.sum_range_succ]
    ring,
    integral_double_polynomial_zero_two]
  norm_num [regularKernelCoefficient, oddP5Correlation35Coefficient,
    oddP5CleanRegularPolynomial35, Finset.sum_range_succ]
  ring

/-! ## Uniform regular-kernel errors -/

/-- Global sixth-order envelope error for the `P1`--`P5` correlation. -/
def oddP5CleanRegularEnvelopeError15 : ℝ :=
  oddCleanRegularEnvelopeError oddP5Correlation15

/-- Global sixth-order envelope error for the `P3`--`P5` correlation. -/
def oddP5CleanRegularEnvelopeError35 : ℝ :=
  oddCleanRegularEnvelopeError oddP5Correlation35

theorem abs_oddP5CleanRegularEnvelopeError15_lt :
    |oddP5CleanRegularEnvelopeError15| < (1 / 3000000 : ℝ) := by
  have herr := abs_oddCleanRegularEnvelopeError_le oddP5Correlation15
    (by unfold oddP5Correlation15; fun_prop)
  have hmass := integral_abs_oddP5Correlation15_lt
  unfold oddP5CleanRegularEnvelopeError15
  nlinarith

theorem abs_oddP5CleanRegularEnvelopeError35_lt :
    |oddP5CleanRegularEnvelopeError35| < (1 / 2800000 : ℝ) := by
  have herr := abs_oddCleanRegularEnvelopeError_le oddP5Correlation35
    (by unfold oddP5Correlation35; fun_prop)
  have hmass := integral_abs_oddP5Correlation35_lt
  unfold oddP5CleanRegularEnvelopeError35
  nlinarith

/-- The actual regular `P1`--`P5` integral is its exact polynomial model
plus the one global envelope error. -/
theorem integral_regularKernel_mul_oddP5Correlation15_eq :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) * oddP5Correlation15 t) =
      oddP5CleanRegularPolynomial15 + oddP5CleanRegularEnvelopeError15 := by
  have hactual := intervalIntegrable_regularKernel_mul oddP5Correlation15
    (by unfold oddP5Correlation15; fun_prop)
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          oddP5Correlation15 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaRegularKernelPolynomial6 oddP5Correlation15
    fun_prop
  unfold oddP5CleanRegularEnvelopeError15 oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          oddP5Correlation15 t) =
      fun t ↦
        yoshidaRegularKernel (yoshidaEndpointA * t) * oddP5Correlation15 t -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
            oddP5Correlation15 t by
    funext t
    ring,
    intervalIntegral.integral_sub hactual hpoly]
  have hmodel := integral_regularKernelPolynomial_mul_oddP5Correlation15
  linarith

/-- The actual regular `P3`--`P5` integral has the analogous decomposition. -/
theorem integral_regularKernel_mul_oddP5Correlation35_eq :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) * oddP5Correlation35 t) =
      oddP5CleanRegularPolynomial35 + oddP5CleanRegularEnvelopeError35 := by
  have hactual := intervalIntegrable_regularKernel_mul oddP5Correlation35
    (by unfold oddP5Correlation35; fun_prop)
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          oddP5Correlation35 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaRegularKernelPolynomial6 oddP5Correlation35
    fun_prop
  unfold oddP5CleanRegularEnvelopeError35 oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          oddP5Correlation35 t) =
      fun t ↦
        yoshidaRegularKernel (yoshidaEndpointA * t) * oddP5Correlation35 t -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
            oddP5Correlation35 t by
    funext t
    ring,
    intervalIntegral.integral_sub hactual hpoly]
  have hmodel := integral_regularKernelPolynomial_mul_oddP5Correlation35
  linarith

theorem re_regularBilinear_p1_p5_eq :
    (yoshidaEndpointRegularRealBilinear centeredP1 factorTwoCenteredP5 +
        yoshidaEndpointRegularRealBilinear factorTwoCenteredP5 centeredP1).re =
      2 * (oddP5CleanRegularPolynomial15 +
        oddP5CleanRegularEnvelopeError15) := by
  have hpolar := re_yoshidaEndpointRegularRealBilinear_add_eq_correlation
    centeredP1 factorTwoCenteredP5
    (by unfold centeredP1; fun_prop) continuous_factorTwoCenteredP5
  have hcorr :
      factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP5 =
        oddP5Correlation15 := by
    funext t
    exact factorTwoCenteredCorrelationBilinear_p1_p5 t
  rw [hcorr] at hpolar
  have hmodel := integral_regularKernel_mul_oddP5Correlation15_eq
  linarith

theorem re_regularBilinear_p3_p5_eq :
    (yoshidaEndpointRegularRealBilinear centeredP3 factorTwoCenteredP5 +
        yoshidaEndpointRegularRealBilinear factorTwoCenteredP5 centeredP3).re =
      2 * (oddP5CleanRegularPolynomial35 +
        oddP5CleanRegularEnvelopeError35) := by
  have hpolar := re_yoshidaEndpointRegularRealBilinear_add_eq_correlation
    centeredP3 factorTwoCenteredP5
    (by unfold centeredP3; fun_prop) continuous_factorTwoCenteredP5
  have hcorr :
      factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP5 =
        oddP5Correlation35 := by
    funext t
    exact factorTwoCenteredCorrelationBilinear_p3_p5 t
  rw [hcorr] at hpolar
  have hmodel := integral_regularKernel_mul_oddP5Correlation35_eq
  linarith

/-! ## Tiny hyperbolic crosses -/

private theorem endpointA_coarse_bounds :
    (693 / 2000 : ℝ) < yoshidaEndpointA ∧
      yoshidaEndpointA < (7 / 20 : ℝ) := by
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

/-- The endpoint sinh moment of `P5`. -/
def oddP5CleanSinhMoment : ℝ :=
  yoshidaEndpointSinhMoment factorTwoCenteredP5

private theorem oddP5CleanSinhMoment_eq_centered :
    oddP5CleanSinhMoment =
      centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) := by
  unfold oddP5CleanSinhMoment yoshidaEndpointSinhMoment centeredSinhMoment
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

theorem oddP5CleanSinhMoment_nonneg : 0 ≤ oddP5CleanSinhMoment := by
  rw [oddP5CleanSinhMoment_eq_centered,
    centeredSinhMoment_P5_rodrigues]
  have hI : 0 ≤ ∫ t : ℝ in 0..1,
      Real.exp (2 * (yoshidaEndpointA / 2) * t) *
        (t ^ 5 * (1 - t) ^ 5) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    positivity
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (by norm_num) (Real.exp_pos _).le
    · exact div_nonneg
        (pow_nonneg (mul_nonneg (by norm_num)
          (div_nonneg yoshidaEndpointA_pos.le (by norm_num))) 5)
        (by norm_num)
  · exact hI

/-- Rodrigues' formula makes the `P5` endpoint sinh moment microscopic. -/
theorem oddP5CleanSinhMoment_lt :
    oddP5CleanSinhMoment < (1 / 125000 : ℝ) := by
  let lambda : ℝ := yoshidaEndpointA / 2
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    exact half_pos yoshidaEndpointA_pos
  have hweighted := exp_neg_mul_centeredSinhMoment_P5_le lambda hlambda.le
  have htwoLambda : 0 ≤ 2 * lambda := by positivity
  have htwoLambdaLt : 2 * lambda < (1 / 2 : ℝ) := by
    dsimp only [lambda]
    linarith [endpointA_coarse_bounds.2]
  have hpowNum : (2 * lambda) ^ 5 < (1 / 2 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ htwoLambdaLt htwoLambda (by norm_num)
  have hpowDen : (5 : ℝ) ^ 6 ≤ (2 * lambda + 5) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 6
  have hprofile :
      2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6 <
        (1 / 250000 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    norm_num at hpowNum hpowDen ⊢
    nlinarith
  have hprofilePos :
      0 < 2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6 := by
    positivity
  have hlambdaLog : lambda < Real.log 2 := by
    dsimp only [lambda, yoshidaEndpointA]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexp : Real.exp lambda < 2 := by
    calc
      Real.exp lambda < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr hlambdaLog
      _ = 2 := Real.exp_log (by norm_num)
  rw [oddP5CleanSinhMoment_eq_centered]
  calc
    centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) =
        Real.exp lambda *
          (Real.exp (-lambda) * centeredSinhMoment factorTwoCenteredP5 lambda) := by
      dsimp only [lambda]
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp lambda *
        (2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos lambda).le
    _ < 2 * (2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6) :=
      mul_lt_mul_of_pos_right hexp hprofilePos
    _ < 2 * (1 / 250000 : ℝ) :=
      mul_lt_mul_of_pos_left hprofile (by norm_num)
    _ = 1 / 125000 := by ring

theorem abs_oddCleanSinhMoment1_lt :
    |oddCleanSinhMoment1| < (1 / 8 : ℝ) := by
  have hsq := oddCleanSinhMoment1_sq_lt
  have habs0 := abs_nonneg oddCleanSinhMoment1
  rw [← sq_abs] at hsq
  nlinarith

theorem abs_oddCleanSinhMoment3_lt :
    |oddCleanSinhMoment3| < (1 / 4000 : ℝ) := by
  have hsq := oddCleanSinhMoment3_sq_lt
  have habs0 := abs_nonneg oddCleanSinhMoment3
  rw [← sq_abs] at hsq
  nlinarith

theorem abs_oddP5_hyperbolicCross15_lt :
    |2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddP5CleanSinhMoment| <
      (1 / 1000000 : ℝ) := by
  have hA : 2 * yoshidaEndpointA ≤ 1 := by
    linarith [endpointA_coarse_bounds.2]
  have h1 := abs_oddCleanSinhMoment1_lt
  have h5 := oddP5CleanSinhMoment_lt
  have h50 := oddP5CleanSinhMoment_nonneg
  have hprod :
      (2 * yoshidaEndpointA) * |oddCleanSinhMoment1| ≤ (1 / 8 : ℝ) := by
    calc
      (2 * yoshidaEndpointA) * |oddCleanSinhMoment1| ≤
          1 * |oddCleanSinhMoment1| :=
        mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ ≤ 1 / 8 := by linarith
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg yoshidaEndpointA_pos.le, abs_of_nonneg h50]
  calc
    (2 * yoshidaEndpointA) * |oddCleanSinhMoment1| * oddP5CleanSinhMoment ≤
        (1 / 8 : ℝ) * oddP5CleanSinhMoment :=
      mul_le_mul_of_nonneg_right hprod h50
    _ < (1 / 8 : ℝ) * (1 / 125000 : ℝ) :=
      mul_lt_mul_of_pos_left h5 (by norm_num)
    _ = 1 / 1000000 := by ring

theorem abs_oddP5_hyperbolicCross35_lt :
    |2 * yoshidaEndpointA * oddCleanSinhMoment3 * oddP5CleanSinhMoment| <
      (1 / 500000000 : ℝ) := by
  have hA : 2 * yoshidaEndpointA ≤ 1 := by
    linarith [endpointA_coarse_bounds.2]
  have h3 := abs_oddCleanSinhMoment3_lt
  have h5 := oddP5CleanSinhMoment_lt
  have h50 := oddP5CleanSinhMoment_nonneg
  have hprod :
      (2 * yoshidaEndpointA) * |oddCleanSinhMoment3| ≤
        (1 / 4000 : ℝ) := by
    calc
      (2 * yoshidaEndpointA) * |oddCleanSinhMoment3| ≤
          1 * |oddCleanSinhMoment3| :=
        mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ ≤ 1 / 4000 := by linarith
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg yoshidaEndpointA_pos.le, abs_of_nonneg h50]
  calc
    (2 * yoshidaEndpointA) * |oddCleanSinhMoment3| * oddP5CleanSinhMoment ≤
        (1 / 4000 : ℝ) * oddP5CleanSinhMoment :=
      mul_le_mul_of_nonneg_right hprod h50
    _ < (1 / 4000 : ℝ) * (1 / 125000 : ℝ) :=
      mul_lt_mul_of_pos_left h5 (by norm_num)
    _ = 1 / 500000000 := by ring

/-! ## Clean cross assembly -/

theorem oddP5CleanRegularPolynomial15_bounds :
    0 ≤ oddP5CleanRegularPolynomial15 ∧
      oddP5CleanRegularPolynomial15 < (1 / 8000000 : ℝ) := by
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hA := endpointA_coarse_bounds.2
  have hA3 := pow_lt_pow_left₀ hA hA0 (by norm_num : (3 : ℕ) ≠ 0)
  have hA5 := pow_lt_pow_left₀ hA hA0 (by norm_num : (5 : ℕ) ≠ 0)
  have hA6 := pow_lt_pow_left₀ hA hA0 (by norm_num : (6 : ℕ) ≠ 0)
  constructor
  · unfold oddP5CleanRegularPolynomial15
    positivity
  · unfold oddP5CleanRegularPolynomial15
    norm_num at hA3 hA5 hA6 ⊢
    nlinarith

theorem neg_oddP5CleanRegularPolynomial35_bounds :
    (1 / 25000 : ℝ) < -oddP5CleanRegularPolynomial35 ∧
      -oddP5CleanRegularPolynomial35 < (1 / 23000 : ℝ) := by
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hAlo := endpointA_coarse_bounds.1
  have hAhi := endpointA_coarse_bounds.2
  have hA3 := pow_lt_pow_left₀ hAhi hA0 (by norm_num : (3 : ℕ) ≠ 0)
  have hA5 := pow_lt_pow_left₀ hAhi hA0 (by norm_num : (5 : ℕ) ≠ 0)
  have hA3nonneg : 0 ≤ yoshidaEndpointA ^ 3 := pow_nonneg hA0 3
  have hA5nonneg : 0 ≤ yoshidaEndpointA ^ 5 := pow_nonneg hA0 5
  unfold oddP5CleanRegularPolynomial35
  constructor
  · have hloRat :
        (1 / 25000 : ℝ) < (693 / 2000 : ℝ) / 8316 := by
      norm_num
    nlinarith
  · norm_num at hA3 hA5 ⊢
    nlinarith

private theorem centeredRawLogBilinear_p1_p5_eq_zero :
    centeredRawLogBilinear centeredP1 factorTwoCenteredP5 = 0 := by
  have h := centeredRawLogBilinear_fixedOddLowProfile_tail_eq_zero
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2 1 0
  have hp : factorTwoOddStructuralLowProfile 1 0 = centeredP1 := by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring
  rwa [hp] at h

private theorem centeredRawLogBilinear_p3_p5_eq_zero :
    centeredRawLogBilinear centeredP3 factorTwoCenteredP5 = 0 := by
  have h := centeredRawLogBilinear_fixedOddLowProfile_tail_eq_zero
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2 0 1
  have hp : factorTwoOddStructuralLowProfile 0 1 = centeredP3 := by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring
  rwa [hp] at h

private theorem integral_centeredP1_mul_P5_eq_zero :
    (∫ x : ℝ in -1..1, centeredP1 x * factorTwoCenteredP5 x) = 0 := by
  have h := integral_fixedOddLowProfile_mul_tail_eq_zero
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2 1 0
  simpa [factorTwoOddStructuralLowProfile] using h

private theorem integral_centeredP3_mul_P5_eq_zero :
    (∫ x : ℝ in -1..1, centeredP3 x * factorTwoCenteredP5 x) = 0 := by
  have h := integral_fixedOddLowProfile_mul_tail_eq_zero
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2 0 1
  simpa [factorTwoOddStructuralLowProfile] using h

private theorem yoshidaEndpointCoshMoment_eq_centeredCoshMoment
    (w : ℝ → ℝ) :
    yoshidaEndpointCoshMoment w =
      centeredCoshMoment w (yoshidaEndpointA / 2) := by
  unfold centeredCoshMoment yoshidaEndpointCoshMoment
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem yoshidaEndpointCoshMoment_centeredP1_eq_zero :
    yoshidaEndpointCoshMoment centeredP1 = 0 := by
  have h := centeredCoshMoment_eq_zero_of_odd
    (w := centeredP1) (by intro x; unfold centeredP1; ring)
    (yoshidaEndpointA / 2)
  rw [yoshidaEndpointCoshMoment_eq_centeredCoshMoment]
  exact h

private theorem yoshidaEndpointCoshMoment_centeredP3_eq_zero :
    yoshidaEndpointCoshMoment centeredP3 = 0 := by
  have h := centeredCoshMoment_eq_zero_of_odd
    (w := centeredP3) (by intro x; unfold centeredP3; ring)
    (yoshidaEndpointA / 2)
  rw [yoshidaEndpointCoshMoment_eq_centeredCoshMoment]
  exact h

private theorem yoshidaEndpointCoshMoment_P5_eq_zero :
    yoshidaEndpointCoshMoment factorTwoCenteredP5 = 0 := by
  have h := centeredCoshMoment_eq_zero_of_odd odd_factorTwoCenteredP5
    (yoshidaEndpointA / 2)
  rw [yoshidaEndpointCoshMoment_eq_centeredCoshMoment]
  exact h

/-- Exact structural decomposition of the clean `P1`--`P5` cross. -/
theorem cleanBilinear_p1_p5_eq :
    yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 =
      (1 / 14 : ℝ) -
        yoshidaEndpointA * (oddP5CleanRegularPolynomial15 +
          oddP5CleanRegularEnvelopeError15) -
        2 * yoshidaEndpointA * oddCleanSinhMoment1 *
          oddP5CleanSinhMoment := by
  unfold yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_p1_p5_eq_zero,
    integral_endpointPotential_mul_centeredP1_mul_P5,
    integral_centeredP1_mul_P5_eq_zero,
    re_regularBilinear_p1_p5_eq,
    yoshidaEndpointCoshMoment_centeredP1_eq_zero,
    yoshidaEndpointCoshMoment_P5_eq_zero]
  unfold oddCleanSinhMoment1 oddP5CleanSinhMoment
  ring

/-- Exact structural decomposition of the clean `P3`--`P5` cross. -/
theorem cleanBilinear_p3_p5_eq :
    yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 =
      (1 / 9 : ℝ) -
        yoshidaEndpointA * (oddP5CleanRegularPolynomial35 +
          oddP5CleanRegularEnvelopeError35) -
        2 * yoshidaEndpointA * oddCleanSinhMoment3 *
          oddP5CleanSinhMoment := by
  unfold yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_p3_p5_eq_zero,
    integral_endpointPotential_mul_centeredP3_mul_P5,
    integral_centeredP3_mul_P5_eq_zero,
    re_regularBilinear_p3_p5_eq,
    yoshidaEndpointCoshMoment_centeredP3_eq_zero,
    yoshidaEndpointCoshMoment_P5_eq_zero]
  unfold oddCleanSinhMoment3 oddP5CleanSinhMoment
  ring

/-- Sharp rational box for the complete clean `P1`--`P5` cross. -/
theorem cleanBilinear_p1_p5_bounds :
    (71427 / 1000000 : ℝ) <
        yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 ∧
      yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 <
        (71429 / 1000000 : ℝ) := by
  have hdecomp := cleanBilinear_p1_p5_eq
  have hmodel := oddP5CleanRegularPolynomial15_bounds
  have hA := endpointA_coarse_bounds.2
  have hAModel :
      yoshidaEndpointA * oddP5CleanRegularPolynomial15 <
        (7 / 20 : ℝ) * (1 / 8000000 : ℝ) := by
    calc
      yoshidaEndpointA * oddP5CleanRegularPolynomial15 ≤
          (7 / 20 : ℝ) * oddP5CleanRegularPolynomial15 :=
        mul_le_mul_of_nonneg_right hA.le hmodel.1
      _ < (7 / 20 : ℝ) * (1 / 8000000 : ℝ) :=
        mul_lt_mul_of_pos_left hmodel.2 (by norm_num)
  have herr := abs_oddP5CleanRegularEnvelopeError15_lt
  have hAError :
      |yoshidaEndpointA * oddP5CleanRegularEnvelopeError15| <
        (7 / 20 : ℝ) * (1 / 3000000 : ℝ) := by
    rw [abs_mul, abs_of_pos yoshidaEndpointA_pos]
    calc
      yoshidaEndpointA * |oddP5CleanRegularEnvelopeError15| ≤
          (7 / 20 : ℝ) * |oddP5CleanRegularEnvelopeError15| :=
        mul_le_mul_of_nonneg_right hA.le (abs_nonneg _)
      _ < (7 / 20 : ℝ) * (1 / 3000000 : ℝ) :=
        mul_lt_mul_of_pos_left herr (by norm_num)
  have hhyper := abs_oddP5_hyperbolicCross15_lt
  have hhyperNonneg :
      0 ≤ 2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddP5CleanSinhMoment := by
    have h1 : 0 < oddCleanSinhMoment1 :=
      (show (0 : ℝ) < 11587142 / 100000000 by norm_num).trans
        oddCleanSinhMoment1_gt
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le) h1.le)
      oddP5CleanSinhMoment_nonneg
  constructor
  · nlinarith [neg_abs_le
      (yoshidaEndpointA * oddP5CleanRegularEnvelopeError15),
      le_abs_self (yoshidaEndpointA * oddP5CleanRegularEnvelopeError15),
      neg_abs_le
        (2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddP5CleanSinhMoment),
      le_abs_self
        (2 * yoshidaEndpointA * oddCleanSinhMoment1 * oddP5CleanSinhMoment)]
  · nlinarith [neg_abs_le
      (yoshidaEndpointA * oddP5CleanRegularEnvelopeError15),
      mul_nonneg yoshidaEndpointA_pos.le hmodel.1]

/-- Sharp rational box for the complete clean `P3`--`P5` cross. -/
theorem cleanBilinear_p3_p5_bounds :
    (111124 / 1000000 : ℝ) <
        yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 ∧
      yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 <
        (111127 / 1000000 : ℝ) := by
  have hdecomp := cleanBilinear_p3_p5_eq
  have hmodel := neg_oddP5CleanRegularPolynomial35_bounds
  have hAlo := endpointA_coarse_bounds.1
  have hAhi := endpointA_coarse_bounds.2
  have hmodelPos : 0 < -oddP5CleanRegularPolynomial35 :=
    (show (0 : ℝ) < 1 / 25000 by norm_num).trans hmodel.1
  have hAModelLower :
      (693 / 2000 : ℝ) * (1 / 25000 : ℝ) <
        yoshidaEndpointA * (-oddP5CleanRegularPolynomial35) := by
    calc
      (693 / 2000 : ℝ) * (1 / 25000 : ℝ) <
          yoshidaEndpointA * (1 / 25000 : ℝ) :=
        mul_lt_mul_of_pos_right hAlo (by norm_num)
      _ < yoshidaEndpointA * (-oddP5CleanRegularPolynomial35) :=
        mul_lt_mul_of_pos_left hmodel.1 yoshidaEndpointA_pos
  have hAModelUpper :
      yoshidaEndpointA * (-oddP5CleanRegularPolynomial35) <
        (7 / 20 : ℝ) * (1 / 23000 : ℝ) := by
    calc
      yoshidaEndpointA * (-oddP5CleanRegularPolynomial35) ≤
          (7 / 20 : ℝ) * (-oddP5CleanRegularPolynomial35) :=
        mul_le_mul_of_nonneg_right hAhi.le hmodelPos.le
      _ < (7 / 20 : ℝ) * (1 / 23000 : ℝ) :=
        mul_lt_mul_of_pos_left hmodel.2 (by norm_num)
  have herr := abs_oddP5CleanRegularEnvelopeError35_lt
  have hAError :
      |yoshidaEndpointA * oddP5CleanRegularEnvelopeError35| <
        (7 / 20 : ℝ) * (1 / 2800000 : ℝ) := by
    rw [abs_mul, abs_of_pos yoshidaEndpointA_pos]
    calc
      yoshidaEndpointA * |oddP5CleanRegularEnvelopeError35| ≤
          (7 / 20 : ℝ) * |oddP5CleanRegularEnvelopeError35| :=
        mul_le_mul_of_nonneg_right hAhi.le (abs_nonneg _)
      _ < (7 / 20 : ℝ) * (1 / 2800000 : ℝ) :=
        mul_lt_mul_of_pos_left herr (by norm_num)
  have hhyper := abs_oddP5_hyperbolicCross35_lt
  constructor
  · nlinarith [neg_abs_le
      (yoshidaEndpointA * oddP5CleanRegularEnvelopeError35),
      le_abs_self (yoshidaEndpointA * oddP5CleanRegularEnvelopeError35),
      neg_abs_le
        (2 * yoshidaEndpointA * oddCleanSinhMoment3 * oddP5CleanSinhMoment),
      le_abs_self
        (2 * yoshidaEndpointA * oddCleanSinhMoment3 * oddP5CleanSinhMoment)]
  · nlinarith [neg_abs_le
      (yoshidaEndpointA * oddP5CleanRegularEnvelopeError35),
      le_abs_self (yoshidaEndpointA * oddP5CleanRegularEnvelopeError35),
      neg_abs_le
        (2 * yoshidaEndpointA * oddCleanSinhMoment3 * oddP5CleanSinhMoment),
      le_abs_self
        (2 * yoshidaEndpointA * oddCleanSinhMoment3 * oddP5CleanSinhMoment)]

theorem cleanBilinear_oddP5_cross_bounds :
    ((71427 / 1000000 : ℝ) <
        yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 ∧
      yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 <
        (71429 / 1000000 : ℝ)) ∧
    ((111124 / 1000000 : ℝ) <
        yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 ∧
      yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 <
        (111127 / 1000000 : ℝ)) :=
  ⟨cleanBilinear_p1_p5_bounds, cleanBilinear_p3_p5_bounds⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
