import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.ShiftedLegendreLogEigen
import ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross
import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailReserve
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailReserve
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open UnitIntervalLogEnergyAffine
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointPullbackLipschitz
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur
open ShiftedLegendreLogEigen
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open ShiftedLegendreLogKernel
open TwoByTwoSchur
open YoshidaEndpointWeightedCauchy

noncomputable section

/-- The regular-kernel Riesz representer of a real low profile on the
centered endpoint interval. -/
def yoshidaEndpointEvenRegularRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in Icc (-1) 1,
    yoshidaRegularKernel (yoshidaEndpointA * |x - y|) * p y

theorem integrable_regular_pairing
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    Integrable
      (fun z : ℝ × ℝ ↦
        yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
          p z.2 * r z.1)
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → ℝ := fun z ↦
    yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|)
  let G : ℝ × ℝ → ℝ := fun z ↦ K z * p z.2 * r z.1
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0) <;> fun_prop
  have hKMeas : Measurable K := by
    dsimp only [K]
    fun_prop
  have hpInt : Integrable p μ :=
    hp.continuousOn.integrableOn_compact isCompact_Icc
  have hrInt : Integrable r μ :=
    hr.continuousOn.integrableOn_compact isCompact_Icc
  have hprodNorm : Integrable
      (fun z : ℝ × ℝ ↦ ‖p z.2‖ * ‖r z.1‖) (μ.prod μ) := by
    simpa only [mul_comm] using hrInt.norm.mul_prod hpInt.norm
  have hdomInt : Integrable
      (fun z : ℝ × ℝ ↦ (1 / 4 : ℝ) * (‖p z.2‖ * ‖r z.1‖))
      (μ.prod μ) := hprodNorm.const_mul (1 / 4 : ℝ)
  have hzMem : ∀ᵐ z ∂μ.prod μ, z ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hKBound : ∀ᵐ z ∂μ.prod μ, ‖K z‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hzMem] with z hz
    have habs : |z.1 - z.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |z.1 - z.2| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have harg2 : yoshidaEndpointA * |z.1 - z.2| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left habs
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hreg := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [K]
    rw [Real.norm_eq_abs, abs_of_nonneg hreg.1]
    exact hreg.2
  have hGMeas : AEStronglyMeasurable G (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G]
    fun_prop
  have hGInt : Integrable G (μ.prod μ) := by
    refine hdomInt.mono' hGMeas ?_
    filter_upwards [hKBound] with z hz
    dsimp only [G]
    rw [norm_mul, norm_mul]
    have hnonneg : 0 ≤ ‖p z.2‖ * ‖r z.1‖ :=
      mul_nonneg (norm_nonneg (p z.2)) (norm_nonneg (r z.1))
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hz hnonneg
  simpa only [I, μ, K, G] using hGInt

theorem yoshidaEndpointRegularRealBilinear_eq_integral_representer
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    (yoshidaEndpointRegularRealBilinear p r +
      yoshidaEndpointRegularRealBilinear r p).re =
      2 * ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter p x * r x := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : (ℝ → ℝ) → (ℝ → ℝ) → ℝ × ℝ → ℝ := fun u v z ↦
    yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
      u z.2 * v z.1
  have hpr : Integrable (G p r) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regular_pairing p r hp hr
  have hrp : Integrable (G r p) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regular_pairing r p hr hp
  have hswap : (∫ z, G r p z ∂μ.prod μ) = ∫ z, G p r z ∂μ.prod μ := by
    calc
      (∫ z, G r p z ∂μ.prod μ) =
          ∫ z, G r p z.swap ∂μ.prod μ :=
        (MeasureTheory.integral_prod_swap _).symm
      _ = ∫ z, G p r z ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rcases z with ⟨x, y⟩
        dsimp only [G, Prod.swap_prod_mk]
        rw [abs_sub_comm]
        ring
  have hreal (u v : ℝ → ℝ) :
      yoshidaEndpointRegularRealBilinear u v =
        ((∫ z, G u v z ∂μ.prod μ : ℝ) : ℂ) := by
    unfold yoshidaEndpointRegularRealBilinear
    dsimp only [μ, G]
    calc
      (∫ z : ℝ × ℝ,
          (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (u z.2 : ℂ) * star (v z.1 : ℂ)
          ∂(volume.restrict (Icc (-1) 1)).prod
            (volume.restrict (Icc (-1) 1))) =
          ∫ z : ℝ × ℝ,
            ((yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
              u z.2 * v z.1 : ℝ) : ℂ)
            ∂(volume.restrict (Icc (-1) 1)).prod
              (volume.restrict (Icc (-1) 1)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        push_cast
        simp
      _ = ((∫ z : ℝ × ℝ,
          yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
            u z.2 * v z.1
          ∂(volume.restrict (Icc (-1) 1)).prod
            (volume.restrict (Icc (-1) 1)) : ℝ) : ℂ) :=
        integral_ofReal (𝕜 := ℂ)
  rw [hreal p r, hreal r p, hswap]
  simp only [add_re, ofReal_re]
  rw [show (∫ z, G p r z ∂μ.prod μ) =
      ∫ x, ∫ y, G p r (x, y) ∂μ ∂μ by
        exact MeasureTheory.integral_prod _ hpr]
  have hiter : (∫ x, ∫ y, G p r (x, y) ∂μ ∂μ) =
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter p x * r x := by
    calc
      (∫ x, ∫ y, G p r (x, y) ∂μ ∂μ) =
          ∫ x : ℝ in Icc (-1) 1,
            yoshidaEndpointEvenRegularRepresenter p x * r x := by
        apply integral_congr_ae
        filter_upwards [] with x
        unfold yoshidaEndpointEvenRegularRepresenter
        dsimp only [G, μ]
        rw [integral_mul_const]
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [hiter]
  ring

/-- Polarization of the centered raw logarithmic difference energy. -/
def centeredRawLogBilinear (u v : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
    ((u x - u y) * (v x - v y)) / |x - y|

private theorem eval_shiftedLegendreReal_two (t : ℝ) :
    (shiftedLegendreReal 2).eval t = 1 - 6 * t + 6 * t ^ 2 := by
  calc
    (shiftedLegendreReal 2).eval t =
        (shiftedLegendreReal 2).eval (((2 * t - 1) + 1) / 2) := by
      congr 1
      ring
    _ = (centeredShiftedLegendreReal 2).eval (2 * t - 1) :=
      (eval_centeredShiftedLegendreReal 2 (2 * t - 1)).symm
    _ = (3 * (2 * t - 1) ^ 2 - 1) / 2 :=
      eval_centeredShiftedLegendreReal_two (2 * t - 1)
    _ = _ := by ring

theorem centeredRawLogBilinear_centeredEvenP2_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (htwo : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0) :
    centeredRawLogBilinear centeredEvenP2 r = 0 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let p : ℝ[X] := shiftedLegendreReal 2
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    exact hr.comp (by fun_prop)
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hpair : (∫ t : unitInterval,
      f t * (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [show shiftedLogKernel p = Polynomial.C 3 * p by
      dsimp only [p]
      rw [shiftedLogKernel_shiftedLegendreReal]
      norm_num [harmonic]]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (∫ t : unitInterval, f t * (3 * p.eval (t : ℝ))) =
        3 * ∫ t : unitInterval, f t * p.eval (t : ℝ) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring]
    have hpull : (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * centeredEvenP2 x := by
      calc
        (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
            ∫ t : ℝ in 0..1, centeredPullback r t * p.eval t := by
          change (∫ t : unitInterval,
              (fun s : ℝ ↦ centeredPullback r s * p.eval s) (t : ℝ)) = _
          exact integral_unitInterval_eq_intervalIntegral
            (fun s : ℝ ↦ centeredPullback r s * p.eval s)
        _ =
            ∫ t : ℝ in 0..1,
              centeredPullback r t * (1 - 6 * t + 6 * t ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [f, p]
          rw [eval_shiftedLegendreReal_two]
        _ = ∫ t : ℝ in 0..1,
            (fun x : ℝ ↦ r x * centeredEvenP2 x) (2 * t - 1) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          unfold centeredPullback centeredEvenP2
          ring
        _ = _ := integral_comp_two_mul_sub_one
          (fun x : ℝ ↦ r x * centeredEvenP2 x)
    rw [hpull, htwo]
    ring
  rw [hpair] at hcross
  norm_num at hcross
  have hUzero : (∫ z, U z) = 0 := by
    simpa only [U] using hcross
  have hiter : (∫ z, U z) =
      ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          (((shiftedLegendreReal 2).eval s -
            (shiftedLegendreReal 2).eval t) / |s - t|) := by
    calc
      (∫ z, U z) = ∫ s : unitInterval, ∫ t : unitInterval, U (s, t) :=
        MeasureTheory.integral_prod _ hUInt
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          (centeredPullback r (s : ℝ) - centeredPullback r t) *
            (((shiftedLegendreReal 2).eval (s : ℝ) -
              (shiftedLegendreReal 2).eval t) / |(s : ℝ) - t|) := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = _ := by
        rw [← integral_unitInterval_eq_intervalIntegral]
  rw [hiter] at hUzero
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          (((shiftedLegendreReal 2).eval s -
            (shiftedLegendreReal 2).eval t) / |s - t|) =
        2 * (((centeredEvenP2 (2 * s - 1) -
            centeredEvenP2 (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    rw [eval_shiftedLegendreReal_two, eval_shiftedLegendreReal_two]
    unfold centeredPullback centeredEvenP2
    rw [show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
      ring
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          (((shiftedLegendreReal 2).eval s -
            (shiftedLegendreReal 2).eval t) / |s - t|)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear centeredEvenP2 r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((centeredEvenP2 x - centeredEvenP2 y) * (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hscaled] at hUzero
  linarith

theorem centeredRawLogEnergy_low_tail
    (r : ℝ → ℝ) (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (htwo : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0)
    (c b : ℝ) :
    centeredRawLogEnergy
        (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) =
      b ^ 2 * centeredRawLogEnergy centeredEvenP2 +
        centeredRawLogEnergy r := by
  let w : ℝ → ℝ := fun x ↦
    c * centeredEvenP0 x + b * centeredEvenP2 x + r x
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let pfun : unitInterval → ℝ := fun t ↦
    centeredPullback centeredEvenP2 (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let p : ℝ[X] := shiftedLegendreReal 2
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hlocal
  have hfEnergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hfcont : Continuous f := by
    simpa only [f] using hLip.continuous
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpPoint (t : unitInterval) : pfun t = p.eval (t : ℝ) := by
    dsimp only [pfun, p, centeredPullback]
    rw [eval_shiftedLegendreReal_two]
    unfold centeredEvenP2
    ring
  have hpEq : pfun = fun t : unitInterval ↦ p.eval (t : ℝ) := by
    funext t
    exact hpPoint t
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    rw [hpEq]
    exact integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcrossEq :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hpair : (∫ t : unitInterval,
      f t * (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [show shiftedLogKernel p = Polynomial.C 3 * p by
      dsimp only [p]
      rw [shiftedLogKernel_shiftedLegendreReal]
      norm_num [harmonic]]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (∫ t : unitInterval, f t * (3 * p.eval (t : ℝ))) =
        3 * ∫ t : unitInterval, f t * p.eval (t : ℝ) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring]
    have hpull : (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * centeredEvenP2 x := by
      calc
        (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
            ∫ t : ℝ in 0..1, centeredPullback r t * p.eval t := by
          change (∫ t : unitInterval,
              (fun s : ℝ ↦ centeredPullback r s * p.eval s) (t : ℝ)) = _
          exact integral_unitInterval_eq_intervalIntegral
            (fun s : ℝ ↦ centeredPullback r s * p.eval s)
        _ = ∫ t : ℝ in 0..1,
            centeredPullback r t * (1 - 6 * t + 6 * t ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [p]
          rw [eval_shiftedLegendreReal_two]
        _ = ∫ t : ℝ in 0..1,
            (fun x : ℝ ↦ r x * centeredEvenP2 x) (2 * t - 1) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          unfold centeredPullback centeredEvenP2
          ring
        _ = _ := integral_comp_two_mul_sub_one
          (fun x : ℝ ↦ r x * centeredEvenP2 x)
    rw [hpull, htwo]
    ring
  rw [hpair] at hcrossEq
  norm_num at hcrossEq
  have hUzero : (∫ z, U z) = 0 := by
    simpa only [U] using hcrossEq
  have hgPoint (t : unitInterval) : g t = c + b * pfun t + f t := by
    dsimp only [g, w, pfun, f, centeredPullback, centeredEvenP0]
    ring
  have hpoint (z : unitInterval × unitInterval) :
      unitIntervalRawLogEnergyIntegrand g z =
        b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * b * U z := by
    unfold unitIntervalRawLogEnergyIntegrand U
      unitIntervalRawPolynomialLogKernel
    rw [hgPoint z.1, hgPoint z.2, hpPoint z.1, hpPoint z.2]
    ring
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z +
        unitIntervalRawLogEnergyIntegrand f z + 2 * b * U z) :=
    ((hpEnergy.const_mul (b ^ 2)).add hfEnergy).add
      (hUInt.const_mul (2 * b))
  have hgEnergy : Integrable (unitIntervalRawLogEnergyIntegrand g) := by
    apply hcombo.congr
    filter_upwards [] with z
    exact (hpoint z).symm
  have hIntegralExpand :
      (∫ z, b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * b * U z) =
        b ^ 2 * (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) +
          (∫ z, unitIntervalRawLogEnergyIntegrand f z) +
          2 * b * (∫ z, U z) := by
    calc
      _ = (∫ z, b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z +
            unitIntervalRawLogEnergyIntegrand f z) +
          ∫ z, 2 * b * U z := by
        exact integral_add ((hpEnergy.const_mul (b ^ 2)).add hfEnergy)
          (hUInt.const_mul (2 * b))
      _ = ((∫ z, b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z) +
            ∫ z, unitIntervalRawLogEnergyIntegrand f z) +
          ∫ z, 2 * b * U z := by
        rw [integral_add (hpEnergy.const_mul (b ^ 2)) hfEnergy]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
  have hunitExpand : unitIntervalLogEnergy g =
      b ^ 2 * unitIntervalLogEnergy pfun + unitIntervalLogEnergy f := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand g z) =
        ∫ z, b ^ 2 * unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * b * U z by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z,
      hIntegralExpand, hUzero]
    ring
  have hbridgeW : unitIntervalLogEnergy g =
      (1 / 4 : ℝ) * centeredRawLogEnergy w := by
    simpa only [g] using unitIntervalLogEnergy_centeredPullback w hgEnergy
  have hbridgeP : unitIntervalLogEnergy pfun =
      (1 / 4 : ℝ) * centeredRawLogEnergy centeredEvenP2 := by
    simpa only [pfun] using
      unitIntervalLogEnergy_centeredPullback centeredEvenP2 hpEnergy
  have hbridgeR : unitIntervalLogEnergy f =
      (1 / 4 : ℝ) * centeredRawLogEnergy r := by
    simpa only [f] using unitIntervalLogEnergy_centeredPullback r hfEnergy
  rw [hbridgeW, hbridgeP, hbridgeR] at hunitExpand
  simpa only [w] using (show centeredRawLogEnergy w =
      b ^ 2 * centeredRawLogEnergy centeredEvenP2 +
        centeredRawLogEnergy r by linarith)

theorem centeredRawLogBilinear_centeredEvenP0_eq_zero (r : ℝ → ℝ) :
    centeredRawLogBilinear centeredEvenP0 r = 0 := by
  unfold centeredRawLogBilinear centeredEvenP0
  simp

theorem intervalIntegrable_endpointPotential_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * u x * v x)
      volume (-1) 1 := by
  have hplus := intervalIntegrable_endpointPotential_mul_sq
    (fun x ↦ u x + v x) (hu.add hv)
  have hminus := intervalIntegrable_endpointPotential_mul_sq
    (fun x ↦ u x - v x) (hu.sub hv)
  have hcomb := (hplus.sub hminus).const_mul (1 / 4 : ℝ)
  apply hcomb.congr
  intro x _hx
  ring

theorem intervalIntegrable_regularRepresenter_mul
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenter p x * r x)
      volume (-1) 1 := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : ℝ × ℝ → ℝ := fun z ↦
    yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
      p z.2 * r z.1
  have hG : Integrable G (μ.prod μ) := by
    simpa only [G, μ] using integrable_regular_pairing p r hp hr
  have houter := hG.integral_prod_left
  have hset : Integrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenter p x * r x) μ := by
    apply houter.congr
    filter_upwards [] with x
    unfold yoshidaEndpointEvenRegularRepresenter
    dsimp only [G, μ]
    rw [integral_mul_const]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  dsimp only [μ] at hset ⊢
  exact hset.mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self (le_refl volume))

/-- The odd real hyperbolic moment used only to state the exact polarization
of the clean endpoint quadratic. -/
def yoshidaEndpointSinhMoment (u : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, Real.sinh (yoshidaEndpointA * x / 2) * u x

theorem yoshidaEndpointSinhMoment_eq_zero_of_even
    (u : ℝ → ℝ) (hu : Function.Even u) :
    yoshidaEndpointSinhMoment u = 0 := by
  let S : ℝ → ℝ := fun x ↦
    Real.sinh (yoshidaEndpointA * x / 2) * u x
  have hodd : Function.Odd S := by
    intro x
    dsimp only [S]
    rw [show yoshidaEndpointA * -x / 2 =
      -(yoshidaEndpointA * x / 2) by ring, Real.sinh_neg, hu x]
    ring
  have hchange : (∫ x : ℝ in -1..1, S (-x)) =
      ∫ x : ℝ in -1..1, S x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := S)
        (a := (-1 : ℝ)) (b := 1))
  have hneg : (∫ x : ℝ in -1..1, S (-x)) =
      -(∫ x : ℝ in -1..1, S x) := by
    rw [show (fun x : ℝ ↦ S (-x)) = fun x ↦ -S x by
      funext x
      exact hodd x,
      intervalIntegral.integral_neg]
  unfold yoshidaEndpointSinhMoment
  dsimp only [S] at hchange hneg ⊢
  rw [hneg] at hchange
  linarith

/-- The symmetric real bilinear form whose diagonal is the clean endpoint
quadratic. -/
def yoshidaEndpointEvenCleanBilinear (u v : ℝ → ℝ) : ℝ :=
  centeredRawLogBilinear u v / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x * v x) -
    yoshidaEndpointScalarMassLoss *
      (∫ x : ℝ in -1..1, u x * v x) -
    (yoshidaEndpointA / 2) *
      (yoshidaEndpointRegularRealBilinear u v +
        yoshidaEndpointRegularRealBilinear v u).re +
    2 * yoshidaEndpointA *
      (yoshidaEndpointCoshMoment u * yoshidaEndpointCoshMoment v -
        yoshidaEndpointSinhMoment u * yoshidaEndpointSinhMoment v)

theorem yoshidaEndpointEvenCleanBilinear_self
    (w : ℝ → ℝ) :
    yoshidaEndpointEvenCleanBilinear w w =
      yoshidaEndpointOddCleanQuadratic w := by
  have hraw : centeredRawLogBilinear w w = centeredRawLogEnergy w := by
    unfold centeredRawLogBilinear centeredRawLogEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    apply intervalIntegral.integral_congr
    intro y _hy
    ring
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x * w x) =
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hmass : (∫ x : ℝ in -1..1, w x * w x) =
      ∫ x : ℝ in -1..1, w x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hregular :
      yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ)) =
        yoshidaEndpointRegularRealBilinear w w := by
    unfold yoshidaEndpointRegularQuadratic
      yoshidaEndpointRegularRealBilinear yoshidaEndpointA
    rfl
  have hcosh :
      (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
          (yoshidaEndpointCoshMoment w : ℂ) := by
    unfold yoshidaEndpointCoshMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hsinh :
      (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
          (yoshidaEndpointSinhMoment w : ℂ) := by
    unfold yoshidaEndpointSinhMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hhyper :
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) =
        2 * yoshidaEndpointA *
          (yoshidaEndpointCoshMoment w ^ 2 -
            yoshidaEndpointSinhMoment w ^ 2) := by
    unfold yoshidaEndpointHyperbolicQuadratic
    rw [hcosh, hsinh]
    simp only [Complex.normSq_ofReal]
    ring
  unfold yoshidaEndpointEvenCleanBilinear
    yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [hraw, hpotential, hmass, hregular, hhyper]
  simp only [add_re]
  ring

/-- Fixed entries of the clean `P₀/P₂` low Gram matrix. -/
def yoshidaEndpointEvenLowGram00 : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP0 centeredEvenP0

def yoshidaEndpointEvenLowGram02 : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP0 centeredEvenP2

def yoshidaEndpointEvenLowGram22 : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP2 centeredEvenP2

theorem yoshidaEndpointEvenLowGram00_eq :
    yoshidaEndpointEvenLowGram00 =
      yoshidaEndpointOddCleanQuadratic centeredEvenP0 := by
  exact yoshidaEndpointEvenCleanBilinear_self centeredEvenP0

theorem yoshidaEndpointEvenLowGram22_eq :
    yoshidaEndpointEvenLowGram22 =
      yoshidaEndpointOddCleanQuadratic centeredEvenP2 := by
  exact yoshidaEndpointEvenCleanBilinear_self centeredEvenP2

/-- The pointwise representer of the clean low-to-even-tail functional.
The mass and raw-log terms vanish on a `P₀/P₂`-orthogonal tail. -/
def yoshidaEndpointEvenTailRepresenter (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * p x -
    yoshidaEndpointA * yoshidaEndpointEvenRegularRepresenter p x +
    2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p *
      Real.cosh (yoshidaEndpointA * x / 2)

def yoshidaEndpointEvenTailRepresenter0 : ℝ → ℝ :=
  yoshidaEndpointEvenTailRepresenter centeredEvenP0

def yoshidaEndpointEvenTailRepresenter2 : ℝ → ℝ :=
  yoshidaEndpointEvenTailRepresenter centeredEvenP2

/-- A representative of the same tail functional after subtracting an
arbitrary element of the annihilated `P₀/P₂` dual span.  This subtraction is
essential: the raw representers contain large low-mode components which do
not act on a zero-two tail. -/
def yoshidaEndpointEvenProjectedTailRepresenter
    (p : ℝ → ℝ) (s0 s2 : ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointEvenTailRepresenter p x -
    s0 * centeredEvenP0 x - s2 * centeredEvenP2 x

def yoshidaEndpointEvenProjectedTailRepresenter0
    (s0 s2 : ℝ) : ℝ → ℝ :=
  yoshidaEndpointEvenProjectedTailRepresenter centeredEvenP0 s0 s2

def yoshidaEndpointEvenProjectedTailRepresenter2
    (s0 s2 : ℝ) : ℝ → ℝ :=
  yoshidaEndpointEvenProjectedTailRepresenter centeredEvenP2 s0 s2

theorem intervalIntegrable_projectedTailRepresenter_mul
    (p r : ℝ → ℝ) (hr : Continuous r) (s0 s2 : ℝ)
    (hF : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter p x * r x)
      volume (-1) 1) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenProjectedTailRepresenter p s0 s2 x * r x)
      volume (-1) 1 := by
  have h0 : IntervalIntegrable
      (fun x ↦ r x * centeredEvenP0 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP0; fun_prop)).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x ↦ r x * centeredEvenP2 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP2; fun_prop)).intervalIntegrable (-1) 1
  apply (hF.sub (h0.const_mul s0)).sub (h2.const_mul s2) |>.congr
  intro x _hx
  unfold yoshidaEndpointEvenProjectedTailRepresenter
  ring

/-- Subtracting `P₀/P₂` from a representer does not change its pairing with a
tail orthogonal to those two modes. -/
theorem integral_projectedTailRepresenter_mul_eq
    (p r : ℝ → ℝ) (hr : Continuous r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (s0 s2 : ℝ)
    (hF : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter p x * r x)
      volume (-1) 1) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenProjectedTailRepresenter p s0 s2 x * r x) =
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailRepresenter p x * r x := by
  have h0 : IntervalIntegrable
      (fun x ↦ r x * centeredEvenP0 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP0; fun_prop)).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x ↦ r x * centeredEvenP2 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP2; fun_prop)).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenProjectedTailRepresenter p s0 s2 x * r x) =
      fun x ↦ yoshidaEndpointEvenTailRepresenter p x * r x -
        s0 * (r x * centeredEvenP0 x) -
        s2 * (r x * centeredEvenP2 x) by
    funext x
    unfold yoshidaEndpointEvenProjectedTailRepresenter
    ring,
    intervalIntegral.integral_sub (hF.sub (h0.const_mul s0))
      (h2.const_mul s2),
    intervalIntegral.integral_sub hF (h0.const_mul s0),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_mul_centeredEvenP0_eq,
    integral_mul_centeredEvenP2_eq,
    hzero, htwo]
  ring

private theorem integral_tailRepresenter_mul
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailRepresenter p x * r x) =
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * p x * r x) -
      yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter p x * r x) +
      2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p *
        yoshidaEndpointCoshMoment r := by
  have hV := intervalIntegrable_endpointPotential_mul p r hp hr
  have hR := intervalIntegrable_regularRepresenter_mul p r hp hr
  have hC : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  unfold yoshidaEndpointEvenTailRepresenter
  rw [show (fun x : ℝ ↦
      (yoshidaEndpointPotential x * p x -
          yoshidaEndpointA * yoshidaEndpointEvenRegularRepresenter p x +
        2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p *
          Real.cosh (yoshidaEndpointA * x / 2)) * r x) =
      fun x ↦ yoshidaEndpointPotential x * p x * r x -
        yoshidaEndpointA *
          (yoshidaEndpointEvenRegularRepresenter p x * r x) +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p) *
          (Real.cosh (yoshidaEndpointA * x / 2) * r x) by
    funext x
    ring]
  rw [intervalIntegral.integral_add
      (hV.sub (hR.const_mul yoshidaEndpointA))
      (hC.const_mul (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p)),
    intervalIntegral.integral_sub hV (hR.const_mul yoshidaEndpointA),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold yoshidaEndpointCoshMoment
  ring

theorem yoshidaEndpointEvenLowTailCross_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hmean : (∫ x : ℝ in -1..1, r x) = 0) :
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 r =
      ∫ x : ℝ in -1..1, yoshidaEndpointEvenTailRepresenter0 x * r x := by
  have hraw := centeredRawLogBilinear_centeredEvenP0_eq_zero r
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 r (by unfold centeredEvenP0; fun_prop) hr
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even r hre
  have hF := integral_tailRepresenter_mul centeredEvenP0 r
    (by unfold centeredEvenP0; fun_prop) hr
  unfold yoshidaEndpointEvenCleanBilinear
  unfold yoshidaEndpointEvenTailRepresenter0
  simp only [centeredEvenP0, one_mul]
  rw [hraw, hmean, hreg, hsinh, hF]
  simp only [centeredEvenP0]
  ring

theorem yoshidaEndpointEvenLowTailCross_two
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (htwo : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0) :
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 r =
      ∫ x : ℝ in -1..1, yoshidaEndpointEvenTailRepresenter2 x * r x := by
  have hraw := centeredRawLogBilinear_centeredEvenP2_tail_eq_zero r hr htwo
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP2 r (by unfold centeredEvenP2; fun_prop) hr
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even r hre
  have hF := integral_tailRepresenter_mul centeredEvenP2 r
    (by unfold centeredEvenP2; fun_prop) hr
  have hmass : (∫ x : ℝ in -1..1, centeredEvenP2 x * r x) = 0 := by
    rw [show (fun x : ℝ ↦ centeredEvenP2 x * r x) =
      fun x ↦ r x * centeredEvenP2 x by
        funext x
        ring,
      htwo]
  unfold yoshidaEndpointEvenCleanBilinear
  unfold yoshidaEndpointEvenTailRepresenter2
  rw [hraw, hmass, hreg, hsinh, hF]
  ring

/-- The positive weight retained by the exact even tail reserve. -/
def yoshidaEndpointEvenTailWeight (x : ℝ) : ℝ :=
  (41 / 60 : ℝ) + yoshidaEndpointPotential x

theorem weighted_low_tail_adjugate_le
    (r g0 g2 : ℝ → ℝ) (q00 q02 q22 : ℝ)
    (hq00 : 0 < q00) (hdet : 0 < q00 * q22 - q02 ^ 2)
    (hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * g0 x + b * g2 x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)))
    (hprimal : MemLp (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x) 2
        (volume.restrict (Ioc (-1) 1)))
    (hcross0 : IntervalIntegrable
      (fun x ↦ g0 x * r x)
      volume (-1) 1)
    (hcross2 : IntervalIntegrable
      (fun x ↦ g2 x * r x)
      volume (-1) 1)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * g0 x + b * g2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2) :
    q22 * (∫ x : ℝ in -1..1,
        g0 x * r x) ^ 2 -
      2 * q02 *
        (∫ x : ℝ in -1..1,
          g0 x * r x) *
        (∫ x : ℝ in -1..1,
          g2 x * r x) +
      q00 * (∫ x : ℝ in -1..1,
        g2 x * r x) ^ 2 ≤
      (q00 * q22 - q02 ^ 2) *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailWeight x * r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1) 1)
  let W : ℝ → ℝ := yoshidaEndpointEvenTailWeight
  let F0 : ℝ → ℝ := g0
  let F2 : ℝ → ℝ := g2
  let ell0 : ℝ := ∫ x : ℝ in -1..1, F0 x * r x
  let ell2 : ℝ := ∫ x : ℝ in -1..1, F2 x * r x
  let T : ℝ := ∫ x : ℝ in -1..1, W x * r x ^ 2
  let det : ℝ := q00 * q22 - q02 ^ 2
  let A : ℝ := q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 +
    q00 * ell2 ^ 2
  let ca : ℝ := q22 * ell0 - q02 * ell2
  let ba : ℝ := q00 * ell2 - q02 * ell0
  let G : ℝ → ℝ := fun x ↦ ca * F0 x + ba * F2 x
  have hW : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hV := yoshidaEndpointPotential_nonneg_on_Icc
      (show x ∈ Icc (-1) 1 from ⟨hx.1.le, hx.2⟩)
    dsimp only [W, yoshidaEndpointEvenTailWeight]
    linarith
  have hmeasureIntegral (g : ℝ → ℝ) :
      (∫ x, g x ∂μ) = ∫ x : ℝ in -1..1, g x := by
    dsimp only [μ]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hGcross : (∫ x : ℝ in -1..1, G x * r x) =
      ca * ell0 + ba * ell2 := by
    rw [show (fun x : ℝ ↦ G x * r x) =
        fun x ↦ ca * (F0 x * r x) + ba * (F2 x * r x) by
      funext x
      dsimp only [G]
      ring,
      intervalIntegral.integral_add
        (hcross0.const_mul ca) (hcross2.const_mul ba),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hcauchy := sq_integral_mul_le_weighted μ W G r hW
    (by simpa only [G, W, F0, F2] using hdualLp ca ba)
    (by simpa only [W] using hprimal)
  rw [hmeasureIntegral (fun x ↦ G x * r x),
    hmeasureIntegral (fun x ↦ G x ^ 2 / W x),
    hmeasureIntegral (fun x ↦ W x * r x ^ 2), hGcross] at hcauchy
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    have hV := yoshidaEndpointPotential_nonneg_on_Icc hxIcc
    exact mul_nonneg (by
      dsimp only [W, yoshidaEndpointEvenTailWeight]
      linarith) (sq_nonneg _)
  have hdual := hdualGram ca ba
  have hdualScaled := mul_le_mul_of_nonneg_right hdual hT0
  have hbound : (ca * ell0 + ba * ell2) ^ 2 ≤
      (q00 * ca ^ 2 + 2 * q02 * ca * ba + q22 * ba ^ 2) * T := by
    exact hcauchy.trans hdualScaled
  have hcombine : ca * ell0 + ba * ell2 = A := by
    dsimp only [ca, ba, A]
    ring
  have hlowAdj :
      q00 * ca ^ 2 + 2 * q02 * ca * ba + q22 * ba ^ 2 = det * A := by
    dsimp only [ca, ba, det, A]
    ring
  rw [hcombine, hlowAdj] at hbound
  have hA0 : 0 ≤ A := by
    have hid : q00 * A =
        (q00 * ell2 - q02 * ell0) ^ 2 + det * ell0 ^ 2 := by
      dsimp only [A, det]
      ring
    have hright : 0 ≤
        (q00 * ell2 - q02 * ell0) ^ 2 + det * ell0 ^ 2 := by
      exact add_nonneg (sq_nonneg _)
        (mul_nonneg hdet.le (sq_nonneg _))
    have hscaled : 0 ≤ q00 * A := by rw [hid]; exact hright
    exact nonneg_of_mul_nonneg_right hscaled hq00
  have hschur : A ≤ det * T := by
    rcases hA0.eq_or_lt with hAzero | hApos
    · rw [← hAzero]
      exact mul_nonneg hdet.le hT0
    · apply le_of_mul_le_mul_left (a := A) (b := A) (c := det * T) _ hApos
      calc
        A * A = A ^ 2 := by ring
        _ ≤ det * A * T := hbound
        _ = A * (det * T) := by ring
  simpa only [A, det, T, ell0, ell2, W, F0, F2] using hschur

theorem weighted_tail_mass_le_cleanQuadratic
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailWeight x * r x ^ 2) ≤
        yoshidaEndpointOddCleanQuadratic r := by
  have hreserve :=
    yoshidaEndpointOddCleanQuadratic_tail_reserve_of_zero_two_of_locallyLipschitzOn
      r hr hre hzero htwo hlocal
  have hhyper := yoshidaEndpointHyperbolicQuadratic_nonneg_of_even r hre
  have hrSq : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (-1) 1 := (hr.pow 2).intervalIntegrable (-1) 1
  have hV := intervalIntegrable_endpointPotential_mul_sq r hr
  have hweight :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailWeight x * r x ^ 2) =
      (41 / 60 : ℝ) * (∫ x : ℝ in -1..1, r x ^ 2) +
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2 := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointEvenTailWeight x * r x ^ 2) =
        fun x ↦ (41 / 60 : ℝ) * r x ^ 2 +
          yoshidaEndpointPotential x * r x ^ 2 by
      funext x
      unfold yoshidaEndpointEvenTailWeight
      ring,
      intervalIntegral.integral_add (hrSq.const_mul (41 / 60 : ℝ)) hV,
      intervalIntegral.integral_const_mul]
  rw [hweight]
  linarith

theorem low_tail_schur_sum_nonneg
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (g0 g2 : ℝ → ℝ)
    (q00 q02 q22 c b : ℝ)
    (hq00 : 0 < q00) (hdet : 0 < q00 * q22 - q02 ^ 2)
    (hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * g0 x + b * g2 x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)))
    (hprimal : MemLp (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x) 2
        (volume.restrict (Ioc (-1) 1)))
    (hcross0 : IntervalIntegrable
      (fun x ↦ g0 x * r x)
      volume (-1) 1)
    (hcross2 : IntervalIntegrable
      (fun x ↦ g2 x * r x)
      volume (-1) 1)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * g0 x + b * g2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2) :
    0 ≤ q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2 +
      2 * c * (∫ x : ℝ in -1..1,
        g0 x * r x) +
      2 * b * (∫ x : ℝ in -1..1,
        g2 x * r x) +
      yoshidaEndpointOddCleanQuadratic r := by
  have hadj := weighted_low_tail_adjugate_le r g0 g2 q00 q02 q22
    hq00 hdet hdualLp hprimal hcross0 hcross2 hdualGram
  have htail := weighted_tail_mass_le_cleanQuadratic
    r hr hre hzero htwo hlocal
  have hscaledTail := mul_le_mul_of_nonneg_left htail hdet.le
  have hschur := hadj.trans hscaledTail
  exact quadratic_add_tail_nonneg
    q00 q02 q22
    (∫ x : ℝ in -1..1, g0 x * r x)
    (∫ x : ℝ in -1..1, g2 x * r x)
    (yoshidaEndpointOddCleanQuadratic r) c b hq00 hdet hschur

/-- Exact conditional reduction of full even clean positivity to the fixed
low Gram matrix and a weighted inequality for representers projected modulo
the annihilated `P₀/P₂` span.

The four projection coefficients are arbitrary.  The zero-two hypotheses
prove that subtracting the corresponding low profiles leaves both tail
pairings unchanged.  The uniform `hdualGram` premise is intentionally
visible and concerns these projected representers.  The analogous premise
for the raw representers is false because of their large, irrelevant low-mode
components.  This theorem is conditional, not an unconditional positivity
result.  `hformPolarization` is the exact form-domain expansion. -/
theorem cleanQuadratic_nonneg_of_fixed_lowGram_of_projected_weighted_dual
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (c b : ℝ)
    (s00 s02 s20 s22 : ℝ)
    (hq00 : 0 < yoshidaEndpointEvenLowGram00)
    (hdet : 0 < yoshidaEndpointEvenLowGram00 *
        yoshidaEndpointEvenLowGram22 - yoshidaEndpointEvenLowGram02 ^ 2)
    (hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * yoshidaEndpointEvenProjectedTailRepresenter0 s00 s02 x +
          b * yoshidaEndpointEvenProjectedTailRepresenter2 s20 s22 x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)))
    (hprimal : MemLp (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x) 2
        (volume.restrict (Ioc (-1) 1)))
    (hcross0 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter0 x * r x)
      volume (-1) 1)
    (hcross2 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter2 x * r x)
      volume (-1) 1)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * yoshidaEndpointEvenProjectedTailRepresenter0 s00 s02 x +
          b * yoshidaEndpointEvenProjectedTailRepresenter2 s20 s22 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2)
    (hformPolarization :
      yoshidaEndpointOddCleanQuadratic
          (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2 +
          2 * c * (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailRepresenter0 x * r x) +
          2 * b * (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailRepresenter2 x * r x) +
          yoshidaEndpointOddCleanQuadratic r) :
    0 ≤ yoshidaEndpointOddCleanQuadratic
      (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) := by
  have hprojected0 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenProjectedTailRepresenter0 s00 s02 x * r x)
      volume (-1) 1 := by
    simpa only [yoshidaEndpointEvenProjectedTailRepresenter0,
      yoshidaEndpointEvenTailRepresenter0] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP0 r hr s00 s02 hcross0
  have hprojected2 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenProjectedTailRepresenter2 s20 s22 x * r x)
      volume (-1) 1 := by
    simpa only [yoshidaEndpointEvenProjectedTailRepresenter2,
      yoshidaEndpointEvenTailRepresenter2] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP2 r hr s20 s22 hcross2
  have hpair0 :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenProjectedTailRepresenter0 s00 s02 x * r x) =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter0 x * r x := by
    simpa only [yoshidaEndpointEvenProjectedTailRepresenter0,
      yoshidaEndpointEvenTailRepresenter0] using
      integral_projectedTailRepresenter_mul_eq
        centeredEvenP0 r hr hzero htwo s00 s02 hcross0
  have hpair2 :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenProjectedTailRepresenter2 s20 s22 x * r x) =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter2 x * r x := by
    simpa only [yoshidaEndpointEvenProjectedTailRepresenter2,
      yoshidaEndpointEvenTailRepresenter2] using
      integral_projectedTailRepresenter_mul_eq
        centeredEvenP2 r hr hzero htwo s20 s22 hcross2
  rw [hformPolarization]
  rw [← hpair0, ← hpair2]
  exact low_tail_schur_sum_nonneg r hr hre hzero htwo hlocal
    (yoshidaEndpointEvenProjectedTailRepresenter0 s00 s02)
    (yoshidaEndpointEvenProjectedTailRepresenter2 s20 s22)
    yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
    yoshidaEndpointEvenLowGram22 c b hq00 hdet hdualLp hprimal
    hprojected0 hprojected2 hdualGram

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
