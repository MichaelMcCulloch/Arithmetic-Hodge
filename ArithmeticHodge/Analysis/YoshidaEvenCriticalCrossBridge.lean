import ArithmeticHodge.Analysis.YoshidaEvenDistributionReduction
import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate Convolution FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaEvenCriticalCrossBridge

noncomputable section

open ArithmeticHodge.Analysis
open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaClippedEvenMomentBridge
open YoshidaClippedMomentBridge
open YoshidaEvenDistributionReduction
open YoshidaEvenIntervalCertificate
open YoshidaOddGramPrefix
open YoshidaOddCorrelationIntegrability
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries

local notation "FT" => FourierTransform.fourier

/-!
# Endpoint-compatible even critical-cross bridge

The clipped even modes jump at the endpoints of their zero extensions.  This
module therefore uses measurable Fourier convolution, rather than the
continuous-input wrapper used by the odd block.  The digamma series is passed
through the integral by dominated convergence of its finite partial sums.  Its
partial sums are uniformly trapped between a fixed bounded initial term and
the full local critical kernel, so ordinary `O(v^-2)` spectral-product decay is
enough; no false weighted second moment is assumed.
-/

private theorem measurable_clippedEvenUnifiedRealMode (n : ℕ) :
    Measurable (clippedEvenUnifiedRealMode n) := by
  by_cases hn : n = 0
  · simp only [clippedEvenUnifiedRealMode, if_pos hn]
    unfold clippedEvenZeroRealMode
    fun_prop
  · simp only [clippedEvenUnifiedRealMode, if_neg hn]
    unfold clippedEvenRealMode
    fun_prop

theorem measurable_evenModeFunction (n : ℕ) :
    Measurable (evenModeFunction n) := by
  rw [show evenModeFunction n =
      Set.piecewise (Set.Icc (-yoshidaHalfLength) yoshidaHalfLength)
        (fun x ↦ (clippedEvenUnifiedRealMode n x : ℂ)) 0 by
    funext x
    rw [evenModeFunction_apply_all]
    rfl]
  exact Measurable.piecewise measurableSet_Icc
    (Complex.measurable_ofReal.comp (measurable_clippedEvenUnifiedRealMode n))
    measurable_const

theorem continuous_clippedEvenUnifiedCorrelation (n m : ℕ) :
    Continuous (clippedEvenUnifiedCorrelation n m) := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      rw [show clippedEvenUnifiedCorrelation 0 0 =
          fun u ↦ (yoshidaLength - u) / yoshidaLength by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_pos rfl, if_pos rfl,
          clippedEvenZeroCorrelation_half]]
      fun_prop
    · rw [show clippedEvenUnifiedCorrelation 0 m =
          fun u ↦ 2 * (-1 : ℝ) ^ (m + 1) * Real.sin (yoshidaKappa m * u) /
            (yoshidaLength * Real.sqrt 2 * yoshidaKappa m) by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_pos rfl, if_neg hm,
          clippedEvenZeroPositiveCorrelation_half hm]]
      fun_prop
  · by_cases hm : m = 0
    · subst m
      rw [show clippedEvenUnifiedCorrelation n 0 =
          fun u ↦ 2 * (-1 : ℝ) ^ (n + 1) * Real.sin (yoshidaKappa n * u) /
            (yoshidaLength * Real.sqrt 2 * yoshidaKappa n) by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_neg hn, if_pos rfl,
          clippedEvenPositiveZeroCorrelation_half hn]]
      fun_prop
    · by_cases hnm : n = m
      · subst m
        rw [show clippedEvenUnifiedCorrelation n n =
            fun u ↦ ((yoshidaLength - u) * Real.cos (yoshidaKappa n * u) -
              Real.sin (yoshidaKappa n * u) / yoshidaKappa n) /
                yoshidaLength by
          funext u
          rw [clippedEvenUnifiedCorrelation, if_neg hn, if_neg hn,
            clippedEvenCorrelation_half_diag hn]]
        fun_prop
      · rw [show clippedEvenUnifiedCorrelation n m =
            fun u ↦ (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
              (yoshidaKappa m * Real.sin (yoshidaKappa m * u) -
                yoshidaKappa n * Real.sin (yoshidaKappa n * u)) /
              (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) by
          funext u
          rw [clippedEvenUnifiedCorrelation, if_neg hn, if_neg hm,
            clippedEvenCorrelation_half_offdiag hn hm hnm]]
        fun_prop

theorem clippedEvenUnifiedCorrelation_length (n m : ℕ) :
    clippedEvenUnifiedCorrelation n m yoshidaLength = 0 := by
  rw [clippedEvenUnifiedCorrelation_eq_realIntegral]
  rw [show yoshidaHalfLength - yoshidaLength = -yoshidaHalfLength by
    rw [yoshidaHalfLength]
    ring]
  simp

private def evenCorrelationExtension (n m : ℕ) (u : ℝ) : ℂ :=
  if |u| ≤ yoshidaLength then
    (clippedEvenUnifiedCorrelation n m |u| : ℂ)
  else 0

private theorem continuous_evenCorrelationExtension (n m : ℕ) :
    Continuous (evenCorrelationExtension n m) := by
  unfold evenCorrelationExtension
  apply Continuous.if_le
    ((Complex.continuous_ofReal.comp
      (continuous_clippedEvenUnifiedCorrelation n m)).comp continuous_abs)
    continuous_const continuous_abs continuous_const
  intro u hu
  simp only [Function.comp_apply]
  rw [hu, clippedEvenUnifiedCorrelation_length]
  simp

private theorem evenCrossCorrelation_eq_extension (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) =
      evenCorrelationExtension n m := by
  funext u
  by_cases hu : 0 ≤ u
  · rw [evenCorrelationExtension, abs_of_nonneg hu]
    by_cases huL : u ≤ yoshidaLength
    · rw [if_pos huL,
        evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation hu huL]
    · rw [if_neg huL,
        evenCrossCorrelation_eq_zero_of_length_lt (lt_of_not_ge huL)]
  · have hneg : 0 ≤ -u := by linarith
    have habs : |u| = -u := abs_of_neg (lt_of_not_ge hu)
    rw [evenCorrelationExtension, habs]
    rw [← evenCrossCorrelation_even n m u]
    by_cases huL : -u ≤ yoshidaLength
    · rw [if_pos huL,
        evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation hneg huL]
    · rw [if_neg huL,
        evenCrossCorrelation_eq_zero_of_length_lt (lt_of_not_ge huL)]

theorem continuous_evenCrossCorrelation (n m : ℕ) :
    Continuous (crossCorrelation (evenModeFunction n) (evenModeFunction m)) := by
  rw [evenCrossCorrelation_eq_extension]
  exact continuous_evenCorrelationExtension n m

/-! ## Fourier convolution without endpoint continuity -/

private theorem integrable_prod_sub_of_measurable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfm : Measurable f) (hgm : Measurable g) :
    Integrable (fun p : ℝ × ℝ ↦
      ‖ContinuousLinearMap.mul ℂ ℂ‖ *
        (‖f (p.1 - p.2)‖ * ‖g p.2‖)) (volume.prod volume) := by
  apply Integrable.const_mul
  rw [integrable_prod_iff' ?_]
  · constructor
    · filter_upwards with x
      exact (hf.comp_sub_right x).norm.mul_const _
    · have hmajor : Integrable (fun x : ℝ ↦
          (∫ y : ℝ, ‖f y‖) * ‖g x‖) := by
        apply hg.norm.bdd_mul (by fun_prop)
          (c := ‖(∫ y : ℝ, ‖f y‖)‖)
        filter_upwards with x
        rfl
      convert hmajor using 1
      ext x
      simp_rw [norm_mul, norm_norm]
      rw [integral_mul_const]
      congr 1
      convert integral_sub_right_eq_self (fun y : ℝ ↦ ‖f y‖) x
        (μ := volume)
  · exact (((hfm.comp (measurable_fst.sub measurable_snd)).norm).mul
      ((hgm.comp measurable_snd).norm)).aestronglyMeasurable

private theorem fourier_mul_convolution_eq_of_measurable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfm : Measurable f) (hgm : Measurable g) (w : ℝ) :
    FT (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) w = FT f w * FT g w := by
  calc
    FT (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) w =
        FT (g ⋆[(ContinuousLinearMap.mul ℂ ℂ).flip] f) w := by
      rw [MeasureTheory.convolution_flip]
    _ = ∫ x : ℝ, (Real.fourierChar (-inner ℝ x w)) •
          ∫ y : ℝ, ContinuousLinearMap.mul ℂ ℂ (f (x - y)) (g y) := by
      rfl
    _ = ∫ x : ℝ, ∫ y : ℝ,
          (Real.fourierChar (-inner ℝ x w)) •
            ContinuousLinearMap.mul ℂ ℂ (f (x - y)) (g y) := by
      congr
      ext x
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ y : ℝ, ∫ x : ℝ,
          (Real.fourierChar (-inner ℝ x w)) •
            ContinuousLinearMap.mul ℂ ℂ (f (x - y)) (g y) := by
      refine integral_integral_swap ?_
      apply (integrable_prod_sub_of_measurable
        hf hg hfm hgm).mono (by measurability)
      filter_upwards with p
      rcases p with ⟨x, y⟩
      simp [norm_mul]
    _ = ∫ y : ℝ, ∫ x : ℝ,
          (Real.fourierChar (-inner ℝ (y + x) w)) •
            ContinuousLinearMap.mul ℂ ℂ (f x) (g y) := by
      congr
      ext y
      convert integral_sub_right_eq_self _ y (μ := volume)
      congr
      simp
    _ = ∫ y : ℝ, ∫ x : ℝ,
          (Real.fourierChar (-inner ℝ y w)) •
            (Real.fourierChar (-inner ℝ x w)) •
              ContinuousLinearMap.mul ℂ ℂ (f x) (g y) := by
      congr
      ext y
      congr
      ext x
      rw [smul_smul, ← AddChar.map_add_eq_mul, inner_add_left]
      congr
      grind
    _ = ∫ y : ℝ,
          (∫ x : ℝ, ContinuousLinearMap.mul ℂ ℂ
            ((Real.fourierChar (-inner ℝ x w)) • f x))
            ((Real.fourierChar (-inner ℝ y w)) • g y) := by
      congr
      ext y
      simp_rw [Circle.smul_def, map_smul, MeasureTheory.integral_smul]
      congr
      have hmajor : Integrable (fun x : ℝ ↦
          ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖f x‖) :=
        hf.norm.const_mul _
      have hphi : Integrable (fun x : ℝ ↦
          (Real.fourierChar (-inner ℝ x w)) •
            ContinuousLinearMap.mul ℂ ℂ (f x)) := by
        apply hmajor.mono (by measurability)
        filter_upwards with x
        simp
      calc
        (∫ a : ℝ, (Real.fourierChar (-inner ℝ a w) : ℂ) •
            ContinuousLinearMap.mul ℂ ℂ (f a) (g y)) =
            ∫ a : ℝ, ((Real.fourierChar (-inner ℝ a w)) •
              ContinuousLinearMap.mul ℂ ℂ (f a)) (g y) := by
          apply integral_congr_ae
          filter_upwards [] with a
          simp [Circle.smul_def]
        _ = (∫ x : ℝ, (Real.fourierChar (-inner ℝ x w)) •
              ContinuousLinearMap.mul ℂ ℂ (f x)) (g y) :=
          (ContinuousLinearMap.integral_apply hphi (g y)).symm
    _ = ContinuousLinearMap.mul ℂ ℂ
          (∫ x : ℝ, (Real.fourierChar (-inner ℝ x w)) • f x)
          (∫ y : ℝ, (Real.fourierChar (-inner ℝ y w)) • g y) := by
      rw [← ContinuousLinearMap.integral_comp_comm _ (by simpa using hg),
        ← ContinuousLinearMap.integral_comp_comm _ (by simpa using hf)]
    _ = FT f w * FT g w := rfl

private theorem measurable_starReflection_evenModeFunction (n : ℕ) :
    Measurable (starReflection (evenModeFunction n)) := by
  unfold starReflection
  exact Complex.continuous_conj.measurable.comp
    ((measurable_evenModeFunction n).comp measurable_neg)

theorem fourier_evenCrossCorrelation (n m : ℕ) (w : ℝ) :
    FT (crossCorrelation (evenModeFunction n) (evenModeFunction m)) w =
      star (FT (evenModeFunction n) w) * FT (evenModeFunction m) w := by
  rw [crossCorrelation,
    fourier_mul_convolution_eq_of_measurable
      (by
        have hneg : Integrable (fun x : ℝ ↦ evenModeFunction n (-x)) :=
          (evenModeFunction_integrable n).comp_neg
        simpa only [starReflection, RCLike.star_def] using
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg)
      (evenModeFunction_integrable m)
      (measurable_starReflection_evenModeFunction n)
      (measurable_evenModeFunction m)]
  rw [fourier_starReflection]

/-! ## Endpoint-compatible Cauchy evaluations -/

theorem angularFourier_evenModeFunction_eq_criticalSample
    (n : ℕ) (v : ℝ) :
    angularFourier (evenModeFunction n) v =
      yoshidaCriticalSampleLinear yoshidaHalfLength yoshidaHalfLength_pos v
        (clippedEvenUnifiedMode n) := by
  exact (yoshidaCriticalSample_eq_fourier
    yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)).symm

theorem evenFourierProduct_integrable (n m : ℕ) :
    Integrable (fun w : ℝ ↦
      star (FT (evenModeFunction n) w) * FT (evenModeFunction m) w) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hscaled :=
    (evenAngularSpectralProduct_integrable n m).comp_mul_left' (R := c) hc
  apply hscaled.congr
  filter_upwards [] with w
  unfold evenAngularSpectralProduct evenModeFunction
  rw [yoshidaCriticalSample_eq_fourier,
    yoshidaCriticalSample_eq_fourier]
  congr 4 <;> dsimp [c] <;> field_simp [Real.pi_ne_zero]

/-- The real-space Cauchy value for a unified even mode pair. -/
def evenCauchyCorrelationValue (n m k : ℕ) : ℂ :=
  ∫ u : ℝ,
    (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u

theorem normalized_bombieriDigammaKernel_evenSpectralProduct
    (n m k : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        evenAngularSpectralProduct n m v) =
      evenCauchyCorrelationValue n m k := by
  let H : ℝ → ℂ :=
    crossCorrelation (evenModeFunction n) (evenModeFunction m)
  let b : ℝ := 2 * (k : ℝ) + 1 / 2
  have hb : 0 < b := by positivity
  have hH : Integrable H := by
    simpa only [H] using evenCrossCorrelation_integrable n m
  have hHcont : Continuous H := by
    simpa only [H] using continuous_evenCrossCorrelation n m
  have hFH : Integrable (FT H) := by
    apply (evenFourierProduct_integrable n m).congr
    filter_upwards [] with w
    simpa only [H] using (fourier_evenCrossCorrelation n m w).symm
  have hcauchy := angular_cauchy_fourier_pairing
    hH hFH hHcont b hb
  have hangular (v : ℝ) :
      angularFourier H v = evenAngularSpectralProduct n m v := by
    rw [angularFourier]
    rw [show FT H (v / (2 * Real.pi)) =
        star (FT (evenModeFunction n) (v / (2 * Real.pi))) *
          FT (evenModeFunction m) (v / (2 * Real.pi)) by
      simpa only [H] using
        fourier_evenCrossCorrelation n m (v / (2 * Real.pi))]
    rw [evenAngularSpectralProduct]
    rw [yoshidaCriticalSample_eq_fourier,
      yoshidaCriticalSample_eq_fourier]
    rfl
  have hkernel (v : ℝ) :
      (bombieriDigammaKernel k v : ℂ) =
        (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    unfold bombieriDigammaKernel
    dsimp [b]
    push_cast
    ring
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
          evenAngularSpectralProduct n m v) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              angularFourier H v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hkernel, hangular]
    _ = ∫ u : ℝ, laplaceKernel b u * H u := hcauchy
    _ = evenCauchyCorrelationValue n m k := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [laplaceKernel]
      calc
        Complex.exp (-(b : ℂ) * (↑|u| : ℂ)) * H u =
            (Real.exp (-b * |u|) : ℝ) * H u := by
          rw [show -(b : ℂ) * (↑|u| : ℂ) =
              ((-b * |u| : ℝ) : ℂ) by
            push_cast
            ring,
            (Complex.ofReal_exp _).symm]
        _ = _ := rfl

theorem normalized_integral_evenSpectralProduct_eq_correlation_zero
    (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, evenAngularSpectralProduct n m v) =
      crossCorrelation (evenModeFunction n) (evenModeFunction m) 0 := by
  let H : ℝ → ℂ :=
    crossCorrelation (evenModeFunction n) (evenModeFunction m)
  have hH : Integrable H := by
    simpa only [H] using evenCrossCorrelation_integrable n m
  have hHcont : Continuous H := by
    simpa only [H] using continuous_evenCrossCorrelation n m
  have hFH : Integrable (FT H) := by
    apply (evenFourierProduct_integrable n m).congr
    filter_upwards [] with w
    simpa only [H] using (fourier_evenCrossCorrelation n m w).symm
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier H) 0 = H 0 :=
    hH.fourierInv_fourier_eq hFH hHcont.continuousAt
  have hzero : (∫ w : ℝ, FT H w) = H 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hscale := Measure.integral_comp_mul_left
    (evenAngularSpectralProduct n m) c
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, evenAngularSpectralProduct n m v) =
        |c⁻¹| • ∫ v : ℝ, evenAngularSpectralProduct n m v := by
      rw [Complex.real_smul]
      congr 1
      dsimp [c]
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, evenAngularSpectralProduct n m (c * w) := hscale.symm
    _ = ∫ w : ℝ,
        star (FT (evenModeFunction n) w) * FT (evenModeFunction m) w := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold evenAngularSpectralProduct evenModeFunction
      rw [yoshidaCriticalSample_eq_fourier,
        yoshidaCriticalSample_eq_fourier]
      congr 4 <;> dsimp [c] <;> field_simp [Real.pi_ne_zero]
    _ = ∫ w : ℝ, FT H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      simpa only [H] using (fourier_evenCrossCorrelation n m w).symm
    _ = H 0 := hzero
    _ = crossCorrelation (evenModeFunction n) (evenModeFunction m) 0 := rfl

theorem exp_abs_mul_evenCrossCorrelation_integrable
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    Integrable (fun u : ℝ ↦
      ((Real.exp (-a * |u|) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u) := by
  have hcoeff : Continuous (fun u : ℝ ↦
      ((Real.exp (-a * |u|) : ℝ) : ℂ)) := by fun_prop
  refine (evenCrossCorrelation_integrable n m).bdd_mul (c := 1)
    hcoeff.aestronglyMeasurable ?_
  filter_upwards [] with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff).2 (mul_nonpos_of_nonpos_of_nonneg
    (by linarith : -a ≤ 0) (abs_nonneg u))

theorem exp_abs_mul_evenCrossCorrelation_eq_two_integral_length
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    (∫ u : ℝ,
      ((Real.exp (-a * |u|) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u) =
      2 * ∫ u : ℝ in 0..yoshidaLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m u : ℂ) := by
  let F : ℝ → ℂ := fun u ↦
    ((Real.exp (-a * |u|) : ℝ) : ℂ) *
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u
  have hFint : Integrable F := by
    simpa only [F] using exp_abs_mul_evenCrossCorrelation_integrable ha n m
  have hFeven : Function.Even F := by
    intro u
    dsimp only [F]
    rw [abs_neg, evenCrossCorrelation_even]
  have hleft : (∫ u : ℝ in Set.Iic 0, F u) =
      ∫ u : ℝ in Set.Ioi 0, F u := by
    calc
      (∫ u : ℝ in Set.Iic 0, F u) =
          ∫ u : ℝ in Set.Iic 0, F (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (hFeven u).symm
      _ = ∫ u : ℝ in Set.Ioi 0, F u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 F
  have hwhole : (∫ u : ℝ, F u) =
      2 * ∫ u : ℝ in Set.Ioi 0, F u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hFint.integrableOn hFint.integrableOn,
      hleft]
    ring
  have hpositive : (∫ u : ℝ in Set.Ioi 0, F u) =
      ∫ u : ℝ in 0..yoshidaLength, F u := by
    rw [intervalIntegral.integral_of_le yoshidaLength_pos.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    intro u hu
    have huLt : yoshidaLength < u := by
      rcases hu with ⟨hu0, huNot⟩
      simp only [mem_Ioi] at hu0
      simp only [mem_Ioc, not_and, not_le] at huNot
      exact huNot hu0
    dsimp only [F]
    rw [evenCrossCorrelation_eq_zero_of_length_lt huLt, mul_zero]
  have hinterval : (∫ u : ℝ in 0..yoshidaLength, F u) =
      ∫ u : ℝ in 0..yoshidaLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m u : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) yoshidaLength := by
      simpa only [uIcc_of_le yoshidaLength_pos.le] using hu
    dsimp only [F]
    rw [abs_of_nonneg hu'.1,
      evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation hu'.1 hu'.2]
  change (∫ u : ℝ, F u) = _
  rw [hwhole, hpositive, hinterval]

theorem evenCauchyCorrelationValue_eq_geometricIntegralTerm
    (n m k : ℕ) :
    evenCauchyCorrelationValue n m k =
      (geometricIntegralTerm yoshidaLength
        (clippedEvenUnifiedCorrelation n m) k : ℂ) := by
  have h := exp_abs_mul_evenCrossCorrelation_eq_two_integral_length
    (a := 2 * (k : ℝ) + 1 / 2) (by positivity) n m
  rw [evenCauchyCorrelationValue]
  calc
    (∫ u : ℝ,
        (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
          crossCorrelation (evenModeFunction n) (evenModeFunction m) u) =
        2 * ∫ u : ℝ in 0..yoshidaLength,
          ((Real.exp (-(2 * (k : ℝ) + 1 / 2) * u) : ℝ) : ℂ) *
            (clippedEvenUnifiedCorrelation n m u : ℂ) := h
    _ = (geometricIntegralTerm yoshidaLength
          (clippedEvenUnifiedCorrelation n m) k : ℂ) := by
      rw [geometricIntegralTerm]
      push_cast
      rw [← intervalIntegral.integral_ofReal]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      simp only [oddRate]
      push_cast
      rfl

theorem evenCrossCorrelation_zero_eq_unified (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) 0 =
      (clippedEvenUnifiedCorrelation n m 0 : ℂ) := by
  exact evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation
    (le_refl 0) yoshidaLength_pos.le n m

/-! ## Removable real-space geometric series -/

def evenCorrelationRemovableD (n m : ℕ) : ℝ → ℝ :=
  dslope (clippedEvenUnifiedCorrelation n m) 0

private theorem differentiable_clippedEvenUnifiedCorrelation (n m : ℕ) :
    Differentiable ℝ (clippedEvenUnifiedCorrelation n m) := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      rw [show clippedEvenUnifiedCorrelation 0 0 =
          fun u ↦ (yoshidaLength - u) / yoshidaLength by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_pos rfl, if_pos rfl,
          clippedEvenZeroCorrelation_half]]
      fun_prop
    · rw [show clippedEvenUnifiedCorrelation 0 m =
          fun u ↦ 2 * (-1 : ℝ) ^ (m + 1) * Real.sin (yoshidaKappa m * u) /
            (yoshidaLength * Real.sqrt 2 * yoshidaKappa m) by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_pos rfl, if_neg hm,
          clippedEvenZeroPositiveCorrelation_half hm]]
      fun_prop
  · by_cases hm : m = 0
    · subst m
      rw [show clippedEvenUnifiedCorrelation n 0 =
          fun u ↦ 2 * (-1 : ℝ) ^ (n + 1) * Real.sin (yoshidaKappa n * u) /
            (yoshidaLength * Real.sqrt 2 * yoshidaKappa n) by
        funext u
        rw [clippedEvenUnifiedCorrelation, if_neg hn, if_pos rfl,
          clippedEvenPositiveZeroCorrelation_half hn]]
      fun_prop
    · by_cases hnm : n = m
      · subst m
        rw [show clippedEvenUnifiedCorrelation n n =
            fun u ↦ ((yoshidaLength - u) * Real.cos (yoshidaKappa n * u) -
              Real.sin (yoshidaKappa n * u) / yoshidaKappa n) /
                yoshidaLength by
          funext u
          rw [clippedEvenUnifiedCorrelation, if_neg hn, if_neg hn,
            clippedEvenCorrelation_half_diag hn]]
        fun_prop
      · rw [show clippedEvenUnifiedCorrelation n m =
            fun u ↦ (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
              (yoshidaKappa m * Real.sin (yoshidaKappa m * u) -
                yoshidaKappa n * Real.sin (yoshidaKappa n * u)) /
              (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) by
          funext u
          rw [clippedEvenUnifiedCorrelation, if_neg hn, if_neg hm,
            clippedEvenCorrelation_half_offdiag hn hm hnm]]
        fun_prop

theorem continuous_evenCorrelationRemovableD (n m : ℕ) :
    Continuous (evenCorrelationRemovableD n m) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [evenCorrelationRemovableD]
  by_cases hu : u = 0
  · subst u
    rw [continuousAt_dslope_same]
    exact (differentiable_clippedEvenUnifiedCorrelation n m).differentiableAt
  · rw [continuousAt_dslope_of_ne hu]
    exact (continuous_clippedEvenUnifiedCorrelation n m).continuousAt

theorem clippedEvenUnifiedCorrelation_removable (n m : ℕ) (u : ℝ) :
    clippedEvenUnifiedCorrelation n m u =
      clippedEvenUnifiedCorrelation n m 0 +
        u * evenCorrelationRemovableD n m u := by
  have h := sub_smul_dslope (clippedEvenUnifiedCorrelation n m) 0 u
  simp only [sub_zero, smul_eq_mul,
    evenCorrelationRemovableD] at h ⊢
  linarith

theorem even_pairedIntegralInterchange (n m : ℕ) :
    PairedIntegralInterchange yoshidaLength
      (clippedEvenUnifiedCorrelation n m 0)
      (clippedEvenUnifiedCorrelation n m) := by
  apply pairedIntegralInterchange_of_removable yoshidaLength_pos
    (continuous_clippedEvenUnifiedCorrelation n m)
  · intro u _hu
    exact clippedEvenUnifiedCorrelation_removable n m u
  · exact removableMajorantLimit_intervalIntegrable
      (continuous_evenCorrelationRemovableD n m)
      (clippedEvenUnifiedCorrelation n m 0) yoshidaLength

theorem even_stableGeometricIntegrand_intervalIntegrable (n m : ℕ) :
    IntervalIntegrable
      (stableGeometricIntegrand (clippedEvenUnifiedCorrelation n m 0)
        (clippedEvenUnifiedCorrelation n m)) volume 0 yoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    (continuous_evenCorrelationRemovableD n m)
    (clippedEvenUnifiedCorrelation n m 0) yoshidaLength
    (clippedEvenUnifiedCorrelation_removable n m)

/-! ## Digamma finite sums under ordinary `O(v⁻²)` decay -/

/-- The nonnegative harmonic-subtracted correction in the quarter-line
digamma series. -/
def evenDigammaCorrection (j : ℕ) (v : ℝ) : ℝ :=
  ((j + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (j + 1) v

theorem evenDigammaCorrection_nonneg (j : ℕ) (v : ℝ) :
    0 ≤ evenDigammaCorrection j v := by
  rw [evenDigammaCorrection]
  apply sub_nonneg.mpr
  simp only [bombieriDigammaKernel, Nat.cast_add, Nat.cast_one]
  let q : ℝ := j + 1
  change (4 * q + 1) / ((2 * q + 1 / 2) ^ 2 + v ^ 2) ≤ q⁻¹
  have hq : 1 ≤ q := by simp [q]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hden : 0 < (2 * q + 1 / 2) ^ 2 + v ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith [sq_nonneg v]

theorem summable_evenDigammaCorrection (v : ℝ) :
    Summable (fun j : ℕ ↦ evenDigammaCorrection j v) := by
  have hp : Summable (fun j : ℕ ↦
      (1 + v ^ 2) / (((j + 1 : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun j : ℕ ↦
        1 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa only [one_div] using
        (summable_nat_add_iff 1).2
          (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    refine (hbase.mul_left (1 + v ^ 2)).congr ?_
    intro j
    simp only [div_eq_mul_inv]
    ring
  apply hp.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (evenDigammaCorrection_nonneg j v)]
  have h := abs_bombieriDigammaKernel_sub_inv_le j v
  rw [abs_sub_comm] at h
  change |evenDigammaCorrection j v| ≤
    (1 + v ^ 2) / (((j + 1 : ℕ) : ℝ) ^ 2) at h
  rw [abs_of_nonneg (evenDigammaCorrection_nonneg j v)] at h
  exact h

/-- The bounded initial part of the local critical kernel. -/
def evenDigammaBase (v : ℝ) : ℝ :=
  -bombieriDigammaKernel 0 v - Real.eulerMascheroniConstant -
    Real.log Real.pi

/-- Finite monotone approximation to the complete local critical kernel. -/
def evenDigammaPartialKernel (N : ℕ) (v : ℝ) : ℝ :=
  evenDigammaBase v +
    ∑ j ∈ Finset.range N, evenDigammaCorrection j v

theorem continuous_evenDigammaBase : Continuous evenDigammaBase := by
  have hK : Continuous (fun v : ℝ ↦ bombieriDigammaKernel 0 v) := by
    unfold bombieriDigammaKernel
    exact continuous_const.div
      ((continuous_const.pow 2).add (continuous_id.pow 2))
      (fun v ↦ by positivity)
  exact (hK.neg.sub continuous_const).sub continuous_const

theorem continuous_evenDigammaPartialKernel (N : ℕ) :
    Continuous (evenDigammaPartialKernel N) := by
  unfold evenDigammaPartialKernel evenDigammaCorrection
  apply continuous_evenDigammaBase.add
  apply continuous_finset_sum
  intro j _hj
  apply continuous_const.sub
  unfold bombieriDigammaKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2))
    (fun v ↦ by positivity)

theorem evenDigammaBase_le_partial (N : ℕ) (v : ℝ) :
    evenDigammaBase v ≤ evenDigammaPartialKernel N v := by
  rw [evenDigammaPartialKernel]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ ↦ evenDigammaCorrection_nonneg j v)

theorem evenDigammaPartial_le_localKernel (N : ℕ) (v : ℝ) :
    evenDigammaPartialKernel N v ≤
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi := by
  have hsum := (summable_evenDigammaCorrection v).sum_le_tsum
    (Finset.range N) (fun j _ ↦ evenDigammaCorrection_nonneg j v)
  rw [evenDigammaPartialKernel]
  have hfull :
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi =
        evenDigammaBase v + ∑' j : ℕ, evenDigammaCorrection j v := by
    rw [digamma_quarter_vertical_re_eq]
    rw [show (∑' j : ℕ,
        (bombieriDigammaKernel (j + 1) v - ((j : ℝ) + 1)⁻¹)) =
        -(∑' j : ℕ, evenDigammaCorrection j v) by
      rw [← tsum_neg]
      apply tsum_congr
      intro j
      rw [evenDigammaCorrection]
      push_cast
      ring]
    rw [evenDigammaBase]
    ring
  rw [hfull]
  simpa only [add_comm] using add_le_add_left hsum (evenDigammaBase v)

theorem abs_evenDigammaPartialKernel_le (N : ℕ) (v : ℝ) :
    |evenDigammaPartialKernel N v| ≤
      |evenDigammaBase v| +
        |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi| := by
  have hlo := evenDigammaBase_le_partial N v
  have hhi := evenDigammaPartial_le_localKernel N v
  rw [abs_le]
  constructor
  · calc
      -(|evenDigammaBase v| +
          |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi|) ≤ -|evenDigammaBase v| := by
        linarith [abs_nonneg
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi)]
      _ ≤ evenDigammaBase v := neg_abs_le _
      _ ≤ evenDigammaPartialKernel N v := hlo
  · calc
      evenDigammaPartialKernel N v ≤
          (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi := hhi
      _ ≤ |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi| := le_abs_self _
      _ ≤ |evenDigammaBase v| +
          |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi| := le_add_of_nonneg_left (abs_nonneg _)

private theorem bombieriDigammaKernel_zero_norm_le_four (v : ℝ) :
    ‖(bombieriDigammaKernel 0 v : ℂ)‖ ≤ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold bombieriDigammaKernel
  norm_num
  have hden : 0 < (1 / 4 : ℝ) + v ^ 2 := by positivity
  rw [abs_of_pos hden]
  rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 4)]
  nlinarith [sq_nonneg v]

theorem evenDigammaBase_mul_spectralProduct_integrable (n m : ℕ) :
    Integrable (fun v : ℝ ↦
      (evenDigammaBase v : ℂ) * evenAngularSpectralProduct n m v) := by
  let C : ℝ := 4 + |Real.eulerMascheroniConstant| + |Real.log Real.pi|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (evenAngularSpectralProduct_integrable n m).bdd_mul
    (c := C) (Complex.continuous_ofReal.comp continuous_evenDigammaBase
      |>.aestronglyMeasurable)
  filter_upwards [] with v
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |evenDigammaBase v| ≤
        |bombieriDigammaKernel 0 v| +
          |Real.eulerMascheroniConstant| + |Real.log Real.pi| := by
      rw [evenDigammaBase]
      have houter := abs_sub_le
        (-bombieriDigammaKernel 0 v - Real.eulerMascheroniConstant)
        0 (Real.log Real.pi)
      have hinner := abs_sub_le (-bombieriDigammaKernel 0 v)
        0 Real.eulerMascheroniConstant
      simp only [sub_zero, zero_sub, abs_neg] at houter hinner
      linarith
    _ ≤ C := by
      have hk := bombieriDigammaKernel_zero_norm_le_four v
      rw [Complex.norm_real, Real.norm_eq_abs] at hk
      dsimp [C]
      linarith

def evenDigammaPartialIntegrand (n m N : ℕ) (v : ℝ) : ℂ :=
  (evenDigammaPartialKernel N v : ℂ) *
    evenAngularSpectralProduct n m v

theorem evenDigammaPartialIntegrand_integrable (n m N : ℕ) :
    Integrable (evenDigammaPartialIntegrand n m N) := by
  let bound : ℝ → ℝ := fun v ↦
    ‖(evenDigammaBase v : ℂ) * evenAngularSpectralProduct n m v‖ +
      ‖yoshidaClippedCriticalCrossIntegrand
        yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v‖
  have hbound : Integrable bound := by
    exact (evenDigammaBase_mul_spectralProduct_integrable n m).norm.add
      (yoshidaClippedCriticalCrossIntegrand_integrable
        yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m)).norm
  apply hbound.mono'
  · exact ((Complex.continuous_ofReal.comp
      (continuous_evenDigammaPartialKernel N)).mul
        (continuous_evenAngularSpectralProduct n m)).aestronglyMeasurable
  · filter_upwards [] with v
    rw [evenDigammaPartialIntegrand]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs := abs_evenDigammaPartialKernel_le N v
    have hnorm := mul_le_mul_of_nonneg_right habs
      (norm_nonneg (evenAngularSpectralProduct n m v))
    calc
      |evenDigammaPartialKernel N v| *
          ‖evenAngularSpectralProduct n m v‖ ≤
          (|evenDigammaBase v| +
            |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
              Real.log Real.pi|) *
            ‖evenAngularSpectralProduct n m v‖ := hnorm
      _ = bound v := by
        simp only [bound, yoshidaClippedCriticalCrossIntegrand,
          MultiplicativeWeil.bombieriLocalCriticalKernel,
          evenAngularSpectralProduct, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        ring

theorem tendsto_integral_evenDigammaPartialIntegrand (n m : ℕ) :
    Tendsto (fun N : ℕ ↦
      ∫ v : ℝ, evenDigammaPartialIntegrand n m N v) atTop
      (𝓝 (∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v)) := by
  let bound : ℝ → ℝ := fun v ↦
    ‖(evenDigammaBase v : ℂ) * evenAngularSpectralProduct n m v‖ +
      ‖yoshidaClippedCriticalCrossIntegrand
        yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v‖
  have hbound : Integrable bound := by
    exact (evenDigammaBase_mul_spectralProduct_integrable n m).norm.add
      (yoshidaClippedCriticalCrossIntegrand_integrable
        yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m)).norm
  apply tendsto_integral_of_dominated_convergence bound
  · intro N
    exact (evenDigammaPartialIntegrand_integrable n m N).aestronglyMeasurable
  · exact hbound
  · intro N
    filter_upwards [] with v
    rw [evenDigammaPartialIntegrand]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs := abs_evenDigammaPartialKernel_le N v
    have hnorm := mul_le_mul_of_nonneg_right habs
      (norm_nonneg (evenAngularSpectralProduct n m v))
    calc
      |evenDigammaPartialKernel N v| *
          ‖evenAngularSpectralProduct n m v‖ ≤
          (|evenDigammaBase v| +
            |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
              Real.log Real.pi|) *
            ‖evenAngularSpectralProduct n m v‖ := hnorm
      _ = bound v := by
        simp only [bound, yoshidaClippedCriticalCrossIntegrand,
          MultiplicativeWeil.bombieriLocalCriticalKernel,
          evenAngularSpectralProduct, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        ring
  · filter_upwards [] with v
    have hsum := (summable_evenDigammaCorrection v).hasSum.tendsto_sum_nat
    have hkernel : Tendsto (fun N : ℕ ↦ evenDigammaPartialKernel N v)
        atTop (𝓝 ((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi)) := by
      rw [show (Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi =
          evenDigammaBase v + ∑' j : ℕ, evenDigammaCorrection j v by
        rw [digamma_quarter_vertical_re_eq]
        rw [show (∑' j : ℕ,
            (bombieriDigammaKernel (j + 1) v - ((j : ℝ) + 1)⁻¹)) =
            -(∑' j : ℕ, evenDigammaCorrection j v) by
          rw [← tsum_neg]
          apply tsum_congr
          intro j
          rw [evenDigammaCorrection]
          push_cast
          ring]
        rw [evenDigammaBase]
        ring]
      exact tendsto_const_nhds.add hsum
    have hkernelC : Tendsto
        (fun N : ℕ ↦ (evenDigammaPartialKernel N v : ℂ)) atTop
        (𝓝 (((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hkernel
    have hmul := hkernelC.mul
      (tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ evenAngularSpectralProduct n m v) atTop
        (𝓝 (evenAngularSpectralProduct n m v)))
    simpa only [evenDigammaPartialIntegrand,
      yoshidaClippedCriticalCrossIntegrand,
      MultiplicativeWeil.bombieriLocalCriticalKernel,
      evenAngularSpectralProduct, mul_assoc] using hmul

/-! ## Evaluation of every finite partial integral -/

private theorem continuous_bombieriDigammaKernel (k : ℕ) :
    Continuous (fun v : ℝ ↦ bombieriDigammaKernel k v) := by
  unfold bombieriDigammaKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2))
    (fun v ↦ by positivity)

private theorem bombieriDigammaKernel_nonneg (k : ℕ) (v : ℝ) :
    0 ≤ bombieriDigammaKernel k v := by
  unfold bombieriDigammaKernel
  positivity

theorem evenDigammaCorrection_le_inv (j : ℕ) (v : ℝ) :
    evenDigammaCorrection j v ≤ ((j + 1 : ℕ) : ℝ)⁻¹ := by
  rw [evenDigammaCorrection]
  linarith [bombieriDigammaKernel_nonneg (j + 1) v]

theorem evenDigammaCorrection_mul_spectralProduct_integrable
    (n m j : ℕ) :
    Integrable (fun v : ℝ ↦
      (evenDigammaCorrection j v : ℂ) *
        evenAngularSpectralProduct n m v) := by
  let c : ℝ := ((j + 1 : ℕ) : ℝ)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply (evenAngularSpectralProduct_integrable n m).bdd_mul (c := c)
    ((Complex.continuous_ofReal.comp (by
      unfold evenDigammaCorrection
      exact continuous_const.sub (continuous_bombieriDigammaKernel (j + 1))))
      |>.aestronglyMeasurable)
  filter_upwards [] with v
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (evenDigammaCorrection_nonneg j v)]
  exact evenDigammaCorrection_le_inv j v

theorem bombieriDigammaKernel_mul_evenSpectralProduct_integrable
    (n m k : ℕ) :
    Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel k v : ℂ) *
        evenAngularSpectralProduct n m v) := by
  by_cases hk : k = 0
  · subst k
    apply (evenAngularSpectralProduct_integrable n m).bdd_mul (c := 4)
      ((Complex.continuous_ofReal.comp
        (continuous_bombieriDigammaKernel 0)).aestronglyMeasurable)
    filter_upwards [] with v
    exact bombieriDigammaKernel_zero_norm_le_four v
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    let r : ℂ := ((((j + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)
    have hrM : Integrable (fun v : ℝ ↦
        r * evenAngularSpectralProduct n m v) :=
      (evenAngularSpectralProduct_integrable n m).const_mul r
    have hq := evenDigammaCorrection_mul_spectralProduct_integrable n m j
    apply (hrM.sub hq).congr
    filter_upwards [] with v
    simp only [Pi.sub_apply, r, evenDigammaCorrection]
    push_cast
    ring

theorem normalized_integral_evenDigammaCorrection_mul
    (n m j : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (evenDigammaCorrection j v : ℂ) *
        evenAngularSpectralProduct n m v) =
      ((((j + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
        evenCauchyCorrelationValue n m (j + 1) := by
  let r : ℂ := ((((j + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)
  let M : ℝ → ℂ := evenAngularSpectralProduct n m
  have hM : Integrable M := by
    simpa only [M] using evenAngularSpectralProduct_integrable n m
  have hrM : Integrable (fun v : ℝ ↦ r * M v) := hM.const_mul r
  have hK : Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel (j + 1) v : ℂ) * M v) := by
    simpa only [M] using
      bombieriDigammaKernel_mul_evenSpectralProduct_integrable n m (j + 1)
  have hsplit :
      (∫ v : ℝ, (evenDigammaCorrection j v : ℂ) * M v) =
        r * (∫ v : ℝ, M v) -
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v := by
    calc
      (∫ v : ℝ, (evenDigammaCorrection j v : ℂ) * M v) =
          ∫ v : ℝ, r * M v -
            (bombieriDigammaKernel (j + 1) v : ℂ) * M v := by
        apply integral_congr_ae
        filter_upwards [] with v
        simp only [evenDigammaCorrection, r]
        push_cast
        ring
      _ = (∫ v : ℝ, r * M v) -
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v :=
        MeasureTheory.integral_sub hrM hK
      _ = r * (∫ v : ℝ, M v) -
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v := by
        congr 1
        simpa using MeasureTheory.integral_const_mul r M
  rw [hsplit]
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (r * (∫ v : ℝ, M v) -
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v)) =
        r * ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, M v)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v) := by
      ring
    _ = r * (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
        evenCauchyCorrelationValue n m (j + 1) := by
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, M v) =
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) by
        rw [show M = evenAngularSpectralProduct n m by rfl,
          normalized_integral_evenSpectralProduct_eq_correlation_zero,
          evenCrossCorrelation_zero_eq_unified],
        show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel (j + 1) v : ℂ) * M v) =
          evenCauchyCorrelationValue n m (j + 1) by
        rw [show M = evenAngularSpectralProduct n m by rfl]
        exact normalized_bombieriDigammaKernel_evenSpectralProduct n m (j + 1)]
    _ = _ := rfl

theorem normalized_integral_evenDigammaBase_mul
    (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (evenDigammaBase v : ℂ) *
        evenAngularSpectralProduct n m v) =
      -evenCauchyCorrelationValue n m 0 -
        (Real.eulerMascheroniConstant : ℂ) *
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
        (Real.log Real.pi : ℂ) *
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) := by
  let M : ℝ → ℂ := evenAngularSpectralProduct n m
  let γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  let p : ℂ := (Real.log Real.pi : ℂ)
  have hM : Integrable M := by
    simpa only [M] using evenAngularSpectralProduct_integrable n m
  have hK : Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel 0 v : ℂ) * M v) := by
    simpa only [M] using
      bombieriDigammaKernel_mul_evenSpectralProduct_integrable n m 0
  have hγ : Integrable (fun v : ℝ ↦ γ * M v) := hM.const_mul γ
  have hp : Integrable (fun v : ℝ ↦ p * M v) := hM.const_mul p
  have hγint : (∫ v : ℝ, γ * M v) = γ * ∫ v : ℝ, M v := by
    simpa using MeasureTheory.integral_const_mul γ M
  have hpint : (∫ v : ℝ, p * M v) = p * ∫ v : ℝ, M v := by
    simpa using MeasureTheory.integral_const_mul p M
  have hsplit :
      (∫ v : ℝ, (evenDigammaBase v : ℂ) * M v) =
        -(∫ v : ℝ, (bombieriDigammaKernel 0 v : ℂ) * M v) -
          γ * (∫ v : ℝ, M v) - p * (∫ v : ℝ, M v) := by
    calc
      (∫ v : ℝ, (evenDigammaBase v : ℂ) * M v) =
          ∫ v : ℝ,
            -((bombieriDigammaKernel 0 v : ℂ) * M v) -
              γ * M v - p * M v := by
        apply integral_congr_ae
        filter_upwards [] with v
        simp only [evenDigammaBase, γ, p]
        push_cast
        ring
      _ = (∫ v : ℝ, -((bombieriDigammaKernel 0 v : ℂ) * M v) -
            γ * M v) - ∫ v : ℝ, p * M v :=
        MeasureTheory.integral_sub (hK.neg.sub hγ) hp
      _ = ((∫ v : ℝ, -((bombieriDigammaKernel 0 v : ℂ) * M v)) -
            ∫ v : ℝ, γ * M v) - ∫ v : ℝ, p * M v := by
        congr 1
        exact MeasureTheory.integral_sub hK.neg hγ
      _ = _ := by
        rw [MeasureTheory.integral_neg, hγint, hpint]
  rw [hsplit]
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (-(∫ v : ℝ, (bombieriDigammaKernel 0 v : ℂ) * M v) -
          γ * (∫ v : ℝ, M v) - p * (∫ v : ℝ, M v))) =
        -((((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ v : ℝ, (bombieriDigammaKernel 0 v : ℂ) * M v)) -
          γ * ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, M v)) -
          p * ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, M v)) := by
      ring
    _ = -evenCauchyCorrelationValue n m 0 -
        γ * (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
        p * (clippedEvenUnifiedCorrelation n m 0 : ℂ) := by
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel 0 v : ℂ) * M v) =
          evenCauchyCorrelationValue n m 0 by
        rw [show M = evenAngularSpectralProduct n m by rfl]
        exact normalized_bombieriDigammaKernel_evenSpectralProduct n m 0,
        show (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, M v) =
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) by
        rw [show M = evenAngularSpectralProduct n m by rfl,
          normalized_integral_evenSpectralProduct_eq_correlation_zero,
          evenCrossCorrelation_zero_eq_unified]]
    _ = _ := rfl

theorem normalized_integral_evenDigammaPartialIntegrand
    (n m N : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, evenDigammaPartialIntegrand n m N v) =
      (-evenCauchyCorrelationValue n m 0 -
        (Real.eulerMascheroniConstant : ℂ) *
          (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
        (Real.log Real.pi : ℂ) *
          (clippedEvenUnifiedCorrelation n m 0 : ℂ)) +
        ∑ j ∈ Finset.range N,
          (((((j + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
              (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
            evenCauchyCorrelationValue n m (j + 1)) := by
  let B : ℝ → ℂ := fun v ↦
    (evenDigammaBase v : ℂ) * evenAngularSpectralProduct n m v
  let Q : ℕ → ℝ → ℂ := fun j v ↦
    (evenDigammaCorrection j v : ℂ) * evenAngularSpectralProduct n m v
  have hB : Integrable B := by
    simpa only [B] using evenDigammaBase_mul_spectralProduct_integrable n m
  have hQ (j : ℕ) : Integrable (Q j) := by
    simpa only [Q] using
      evenDigammaCorrection_mul_spectralProduct_integrable n m j
  have hQsum : Integrable (fun v : ℝ ↦
      ∑ j ∈ Finset.range N, Q j v) := by
    apply integrable_finset_sum
    intro j hj
    exact hQ j
  have hsplit :
      (∫ v : ℝ, evenDigammaPartialIntegrand n m N v) =
        (∫ v : ℝ, B v) + ∑ j ∈ Finset.range N, ∫ v : ℝ, Q j v := by
    calc
      (∫ v : ℝ, evenDigammaPartialIntegrand n m N v) =
          ∫ v : ℝ, B v + ∑ j ∈ Finset.range N, Q j v := by
        apply integral_congr_ae
        filter_upwards [] with v
        simp only [evenDigammaPartialIntegrand, evenDigammaPartialKernel,
          B, Q]
        push_cast
        rw [add_mul, Finset.sum_mul]
      _ = (∫ v : ℝ, B v) +
          ∫ v : ℝ, ∑ j ∈ Finset.range N, Q j v :=
        MeasureTheory.integral_add hB hQsum
      _ = _ := by
        rw [MeasureTheory.integral_finset_sum]
        intro i hi
        exact hQ i
  rw [hsplit]
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ v : ℝ, B v) +
          ∑ j ∈ Finset.range N, ∫ v : ℝ, Q j v)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, B v) +
          ∑ j ∈ Finset.range N,
            (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, Q j v) := by
      rw [mul_add, Finset.mul_sum]
    _ = _ := by
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, B v) =
          -evenCauchyCorrelationValue n m 0 -
            (Real.eulerMascheroniConstant : ℂ) *
              (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
            (Real.log Real.pi : ℂ) *
              (clippedEvenUnifiedCorrelation n m 0 : ℂ) by
        simpa only [B] using normalized_integral_evenDigammaBase_mul n m]
      apply congrArg (fun z : ℂ ↦
        (-evenCauchyCorrelationValue n m 0 -
          (Real.eulerMascheroniConstant : ℂ) *
            (clippedEvenUnifiedCorrelation n m 0 : ℂ) -
          (Real.log Real.pi : ℂ) *
            (clippedEvenUnifiedCorrelation n m 0 : ℂ)) + z)
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Q] using normalized_integral_evenDigammaCorrection_mul n m j

/-! ## Identification of the real geometric limit -/

def evenRealDigammaGeometricValue (n m : ℕ) : ℝ :=
  -(geometricIntegralTerm yoshidaLength
        (clippedEvenUnifiedCorrelation n m) 0 +
      Real.eulerMascheroniConstant *
        clippedEvenUnifiedCorrelation n m 0 +
      ∑' j : ℕ,
        (geometricIntegralTerm yoshidaLength
            (clippedEvenUnifiedCorrelation n m) (j + 1) -
          ((j + 1 : ℕ) : ℝ)⁻¹ *
            clippedEvenUnifiedCorrelation n m 0)) -
    Real.log Real.pi * clippedEvenUnifiedCorrelation n m 0

theorem evenRealDigammaGeometricValue_eq_negatedKernel (n m : ℕ) :
    evenRealDigammaGeometricValue n m =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * clippedEvenUnifiedCorrelation n m u +
          clippedEvenUnifiedCorrelation n m 0 / u) -
      (Real.log yoshidaLength + Real.eulerMascheroniConstant +
        Real.log 2 + Real.log Real.pi) *
          clippedEvenUnifiedCorrelation n m 0 := by
  let C : ℝ → ℝ := clippedEvenUnifiedCorrelation n m
  let C0 : ℝ := clippedEvenUnifiedCorrelation n m 0
  have hren : HasSum (renormalizedTerm yoshidaLength C0 C)
      ((∫ u in 0..yoshidaLength, stableGeometricIntegrand C0 C u) +
        (Real.log yoshidaLength + Real.log 2) * C0) :=
    renormalizedSeries_hasSum_stable yoshidaLength_pos
      (continuous_clippedEvenUnifiedCorrelation n m)
      (even_pairedIntegralInterchange n m)
      (even_stableGeometricIntegrand_intervalIntegrable n m)
      (referenceRegularized_intervalIntegrable yoshidaLength)
  have hindex :
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
            C0 / (j + 1 : ℕ)) =
        ∑' j : ℕ, renormalizedTerm yoshidaLength C0 C j := by
    calc
      geometricIntegralTerm yoshidaLength C 0 +
            ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
              C0 / (j + 1 : ℕ)) =
          (∫ u in 0..yoshidaLength, stableGeometricIntegrand C0 C u) +
            (Real.log yoshidaLength + Real.log 2) * C0 :=
        geometricIntegralTerm_zero_add_tsum_shifted_eq hren
      _ = ∑' j : ℕ, renormalizedTerm yoshidaLength C0 C j :=
        hren.tsum_eq.symm
  have hneg := negated_geometric_identity yoshidaLength_pos
    (continuous_clippedEvenUnifiedCorrelation n m)
    (even_pairedIntegralInterchange n m)
    (even_stableGeometricIntegrand_intervalIntegrable n m)
    (referenceRegularized_intervalIntegrable yoshidaLength)
  change _ = _ at hneg
  rw [evenRealDigammaGeometricValue]
  change
    -(geometricIntegralTerm yoshidaLength C 0 +
        Real.eulerMascheroniConstant * C0 +
        ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
          ((j + 1 : ℕ) : ℝ)⁻¹ * C0)) - Real.log Real.pi * C0 = _
  have hindex' :
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
            ((j + 1 : ℕ) : ℝ)⁻¹ * C0) =
        ∑' j : ℕ, renormalizedTerm yoshidaLength C0 C j := by
    simpa only [div_eq_mul_inv, mul_comm] using hindex
  rw [show geometricIntegralTerm yoshidaLength C 0 +
      Real.eulerMascheroniConstant * C0 +
      ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
        ((j + 1 : ℕ) : ℝ)⁻¹ * C0) =
      Real.eulerMascheroniConstant * C0 +
        (geometricIntegralTerm yoshidaLength C 0 +
          ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
            ((j + 1 : ℕ) : ℝ)⁻¹ * C0)) by ring,
    hindex']
  dsimp only [C, C0] at hneg ⊢
  linarith

theorem evenRealDigammaGeometricValue_eq_distribution (n m : ℕ) :
    evenRealDigammaGeometricValue n m =
      clippedEvenRealDigammaDistributionValue n m := by
  let C : ℝ → ℝ := clippedEvenUnifiedCorrelation n m
  let C0 : ℝ := clippedEvenUnifiedCorrelation n m 0
  let N : ℝ → ℝ := fun u ↦ -oddKernel u * C u + C0 / u
  let P : ℝ → ℝ := fun u ↦
    2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * C u
  have hN : IntervalIntegrable N volume 0 yoshidaLength := by
    apply (even_stableGeometricIntegrand_intervalIntegrable n m).neg.congr
    intro u _hu
    simp only [Pi.neg_apply]
    unfold N C C0 stableGeometricIntegrand
    ring
  have hP : IntervalIntegrable P volume 0 yoshidaLength := by
    apply Continuous.intervalIntegrable
    unfold P C
    exact (show Continuous (fun u : ℝ ↦
      2 * (Real.exp (u / 2) + Real.exp (-u / 2))) by fun_prop).mul
        (continuous_clippedEvenUnifiedCorrelation n m)
  have hstable :
      (∫ u in 0..yoshidaLength,
        clippedEvenStableCorrelationIntegrand n m u) =
      (∫ u in 0..yoshidaLength, N u) +
        ∫ u in 0..yoshidaLength, P u := by
    rw [← intervalIntegral.integral_add hN hP]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _hu
    have hpoint := clippedEvenStable_sub_polar_eq_negatedGeometric_of_ne_zero
      n m hu
    dsimp only [N, P, C, C0]
    linarith
  have hpolar : clippedEvenRealPolarCorrelationValue n m =
      ∫ u in 0..yoshidaLength, P u := by
    rw [clippedEvenRealPolarCorrelationValue,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [P, C]
    ring
  rw [evenRealDigammaGeometricValue_eq_negatedKernel]
  rw [clippedEvenRealDigammaDistributionValue,
    clippedEvenAdmissibleRealSpaceGram]
  dsimp only [N, C, C0] at hstable ⊢
  rw [hstable, hpolar]
  ring

def evenDigammaPartialRealValue (n m N : ℕ) : ℝ :=
  -geometricIntegralTerm yoshidaLength
      (clippedEvenUnifiedCorrelation n m) 0 -
    Real.eulerMascheroniConstant * clippedEvenUnifiedCorrelation n m 0 -
    Real.log Real.pi * clippedEvenUnifiedCorrelation n m 0 +
    ∑ j ∈ Finset.range N,
      (((j + 1 : ℕ) : ℝ)⁻¹ * clippedEvenUnifiedCorrelation n m 0 -
        geometricIntegralTerm yoshidaLength
          (clippedEvenUnifiedCorrelation n m) (j + 1))

theorem normalized_integral_evenDigammaPartialIntegrand_eq_ofReal
    (n m N : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, evenDigammaPartialIntegrand n m N v) =
      (evenDigammaPartialRealValue n m N : ℂ) := by
  rw [normalized_integral_evenDigammaPartialIntegrand]
  simp_rw [evenCauchyCorrelationValue_eq_geometricIntegralTerm]
  rw [evenDigammaPartialRealValue]
  push_cast
  ring

theorem tendsto_evenDigammaPartialRealValue (n m : ℕ) :
    Tendsto (evenDigammaPartialRealValue n m) atTop
      (𝓝 (evenRealDigammaGeometricValue n m)) := by
  let C : ℝ → ℝ := clippedEvenUnifiedCorrelation n m
  let C0 : ℝ := clippedEvenUnifiedCorrelation n m 0
  let S : ℝ :=
    (∫ u in 0..yoshidaLength, stableGeometricIntegrand C0 C u) +
      (Real.log yoshidaLength + Real.log 2) * C0
  have hren : HasSum (renormalizedTerm yoshidaLength C0 C) S := by
    simpa only [S] using
      renormalizedSeries_hasSum_stable yoshidaLength_pos
        (continuous_clippedEvenUnifiedCorrelation n m)
        (even_pairedIntegralInterchange n m)
        (even_stableGeometricIntegrand_intervalIntegrable n m)
        (referenceRegularized_intervalIntegrable yoshidaLength)
  have hshift : HasSum
      (fun j : ℕ ↦ geometricIntegralTerm yoshidaLength C (j + 1) -
        C0 / (j + 1 : ℕ))
      (S - geometricIntegralTerm yoshidaLength C 0) :=
    hasSum_shifted_geometric_of_hasSum_renormalized hren
  have hneg : HasSum
      (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)⁻¹ * C0 -
        geometricIntegralTerm yoshidaLength C (j + 1))
      (-(S - geometricIntegralTerm yoshidaLength C 0)) := by
    apply HasSum.congr_fun hshift.neg
    intro j
    simp only [div_eq_mul_inv]
    ring
  let B : ℝ := -geometricIntegralTerm yoshidaLength C 0 -
    Real.eulerMascheroniConstant * C0 - Real.log Real.pi * C0
  have hconst : Tendsto (fun _N : ℕ ↦ B) atTop (𝓝 B) :=
    tendsto_const_nhds
  have ht := hconst.add hneg.tendsto_sum_nat
  have hvalue :
      evenRealDigammaGeometricValue n m =
        B +
          (-(S - geometricIntegralTerm yoshidaLength C 0)) := by
    rw [evenRealDigammaGeometricValue]
    change
      -(geometricIntegralTerm yoshidaLength C 0 +
          Real.eulerMascheroniConstant * C0 +
          ∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
            ((j + 1 : ℕ) : ℝ)⁻¹ * C0)) - Real.log Real.pi * C0 = _
    have htsum :
        (∑' j : ℕ, (geometricIntegralTerm yoshidaLength C (j + 1) -
          ((j + 1 : ℕ) : ℝ)⁻¹ * C0)) =
        S - geometricIntegralTerm yoshidaLength C 0 := by
      simpa only [div_eq_mul_inv, mul_comm] using hshift.tsum_eq
    rw [htsum]
    dsimp only [B]
    ring
  rw [hvalue]
  apply ht.congr'
  filter_upwards [] with N
  rw [evenDigammaPartialRealValue]

theorem normalized_evenCriticalCross_eq_distribution (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v) =
      (clippedEvenRealDigammaDistributionValue n m : ℂ) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hleft : Tendsto (fun N : ℕ ↦
      c * ∫ v : ℝ, evenDigammaPartialIntegrand n m N v) atTop
      (𝓝 (c * ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v)) :=
    Tendsto.const_mul c (tendsto_integral_evenDigammaPartialIntegrand n m)
  have hreal := tendsto_evenDigammaPartialRealValue n m
  have hcast : Tendsto
      (fun N : ℕ ↦ (evenDigammaPartialRealValue n m N : ℂ)) atTop
      (𝓝 (evenRealDigammaGeometricValue n m : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hreal
  have hright : Tendsto (fun N : ℕ ↦
      c * ∫ v : ℝ, evenDigammaPartialIntegrand n m N v) atTop
      (𝓝 (evenRealDigammaGeometricValue n m : ℂ)) := by
    apply hcast.congr'
    filter_upwards [] with N
    exact (normalized_integral_evenDigammaPartialIntegrand_eq_ofReal
      n m N).symm
  have hlimit := tendsto_nhds_unique hleft hright
  rw [show c = ((1 / (2 * Real.pi) : ℝ) : ℂ) by rfl] at hlimit
  rw [evenRealDigammaGeometricValue_eq_distribution] at hlimit
  exact hlimit

/-- The endpoint-jump-compatible critical-cross proposition required by the
even moment bridge is unconditional. -/
theorem clippedEvenCriticalCrossDistributionBridge :
    ClippedEvenCriticalCrossDistributionBridge := by
  intro n m
  exact normalized_evenCriticalCross_eq_distribution n m

/-- The production 40,000-entry admissible-distribution bridge follows with
no remaining premise. -/
theorem clippedEvenFullAdmissibleDistributionBridge :
    ClippedEvenFullAdmissibleDistributionBridge :=
  clippedEvenFullAdmissibleDistributionBridge_of_criticalCrossBridge
    clippedEvenCriticalCrossDistributionBridge

/-- The actual clipped even Gram matrix is the explicit moment-model Gram. -/
theorem clippedEvenFullMomentBridge : ClippedEvenFullMomentBridge :=
  clippedEvenFullMomentBridge_of_criticalCrossBridge
    clippedEvenCriticalCrossDistributionBridge

end

end ArithmeticHodge.Analysis.YoshidaEvenCriticalCrossBridge
