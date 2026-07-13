import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross
import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailReserve
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointHyperbolicBound
open YoshidaRegularKernelBound

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
      2 * ∫ x : ℝ in Icc (-1) 1,
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
      ∫ x : ℝ in Icc (-1) 1,
        yoshidaEndpointEvenRegularRepresenter p x * r x := by
    apply integral_congr_ae
    filter_upwards [] with x
    unfold yoshidaEndpointEvenRegularRepresenter
    dsimp only [G, μ]
    rw [integral_mul_const]
  rw [hiter]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
