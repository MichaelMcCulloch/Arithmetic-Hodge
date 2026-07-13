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
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open UnitIntervalLogEnergyAffine
open UnitIntervalIntegralBridge
open YoshidaRegularKernelBound
open ShiftedLegendreLogEigen
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open ShiftedLegendreLogKernel

noncomputable section

/-- The regular-kernel Riesz representer of a real low profile on the
centered endpoint interval. -/
def yoshidaEndpointEvenRegularRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in Icc (-1) 1,
    yoshidaRegularKernel (yoshidaEndpointA * |x - y|) * p y

private theorem integrable_regular_pairing
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
    fun_prop
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

theorem centeredRawLogBilinear_centeredEvenP0_eq_zero (r : ℝ → ℝ) :
    centeredRawLogBilinear centeredEvenP0 r = 0 := by
  unfold centeredRawLogBilinear centeredEvenP0
  simp

private theorem intervalIntegrable_endpointPotential_mul
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

private theorem intervalIntegrable_regularRepresenter_mul
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

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
