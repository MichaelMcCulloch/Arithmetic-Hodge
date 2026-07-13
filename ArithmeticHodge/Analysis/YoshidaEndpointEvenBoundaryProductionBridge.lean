import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.YoshidaEndpointClippedPolarBridge
import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross
import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionPositive
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate Convolution FourierTransform
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge

open ArithmeticHodge.Analysis
open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaClippedEndpointContinuous
open YoshidaEndpointClippedPolarBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenConstantDiagonal
open YoshidaEndpointEvenResidualProduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseParityCore
open YoshidaRenormalizedGeometricKernel
open YoshidaSectionSixAnalytic
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability

noncomputable section

local notation "FT" => FourierTransform.fourier

/-!
# The even endpoint-boundary production bridge

This file treats the endpoint jump analytically.  It does not expand a source
in finitely many modes.  Finite partial sums of the quarter-line digamma
series are dominated by the already-integrable production cross integrand,
so ordinary `O(v⁻²)` product decay is enough.
-/

private def boundarySpectralProduct {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) (v : ℝ) : ℂ :=
  star (yoshidaCriticalSampleLinear a ha v f) *
    yoshidaCriticalSampleLinear a ha v g

private theorem continuous_boundarySpectralProduct {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) :
    Continuous (boundarySpectralProduct ha f g) := by
  exact (continuous_yoshidaCriticalSample ha f).star.mul
    (continuous_yoshidaCriticalSample ha g)

/-- Ordinary integrability of a clipped spectral product.  This is the exact
decay available when endpoint jumps are present. -/
private theorem boundarySpectralProduct_integrable {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) :
    Integrable (boundarySpectralProduct ha f g) := by
  let Cf : ℝ := yoshidaCriticalDecayConstant a f
  let Cg : ℝ := yoshidaCriticalDecayConstant a g
  let K : ℝ := 2 * Cf * Cg
  let q : ℝ → ℝ := fun v ↦ (1 + v ^ 2)⁻¹
  let S : Set ℝ := Icc (-1 : ℝ) 1
  have hcompact : IntegrableOn (boundarySpectralProduct ha f g) S :=
    (continuous_boundarySpectralProduct ha f g).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hCf : 0 ≤ Cf := yoshidaCriticalDecayConstant_nonneg ha f
  have hCg : 0 ≤ Cg := yoshidaCriticalDecayConstant_nonneg ha g
  have hmajor : Integrable (fun v ↦ K * q v) :=
    integrable_inv_one_add_sq.const_mul K
  have htail : IntegrableOn (boundarySpectralProduct ha f g) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact (continuous_boundarySpectralProduct ha f g)
        |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have habs : 1 < |v| := by
        by_contra h
        apply hv
        exact abs_le.mp (le_of_not_gt h)
      have hvne : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
      have hf := yoshidaCriticalSample_norm_le_inv_abs ha v hvne f
      have hg := yoshidaCriticalSample_norm_le_inv_abs ha v hvne g
      have hrecip : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
        have hsq : 1 < v ^ 2 := by
          rw [← sq_abs]
          nlinarith
        rw [div_le_div_iff₀ (by positivity : 0 < v ^ 2)
          (by positivity : 0 < 1 + v ^ 2)]
        nlinarith
      calc
        ‖boundarySpectralProduct ha f g v‖ =
            ‖yoshidaCriticalSampleLinear a ha v f‖ *
              ‖yoshidaCriticalSampleLinear a ha v g‖ := by
          simp [boundarySpectralProduct]
        _ ≤ (Cf / |v|) * (Cg / |v|) := by
          exact mul_le_mul hf hg (norm_nonneg _) (by positivity)
        _ = Cf * Cg * (1 / v ^ 2) := by
          field_simp [hvne, abs_ne_zero.mpr hvne]
          rw [sq_abs]
          ring
        _ ≤ Cf * Cg * (2 / (1 + v ^ 2)) :=
          mul_le_mul_of_nonneg_left hrecip (mul_nonneg hCf hCg)
        _ = K * q v := by
          dsimp only [K, q]
          ring
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

private theorem clipped_integrable {a : ℝ} (f : YoshidaClippedSmooth a) :
    Integrable (f : ℝ → ℂ) :=
  f.property.1.continuousOn.integrableOn_Icc
    |>.integrable_of_forall_notMem_eq_zero
      (fun _ hx ↦ yoshidaClippedSmooth_eq_zero_outside f hx)

private theorem clipped_hasCompactSupport {a : ℝ}
    (f : YoshidaClippedSmooth a) :
    HasCompactSupport (f : ℝ → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (yoshidaClippedSmooth_eq_zero_outside f hmem)

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
      apply (integrable_prod_sub_of_measurable hf hg hfm hgm).mono
        (by measurability)
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
        (∫ x : ℝ, (Real.fourierChar (-inner ℝ x w) : ℂ) •
            ContinuousLinearMap.mul ℂ ℂ (f x) (g y)) =
            ∫ x : ℝ, ((Real.fourierChar (-inner ℝ x w)) •
              ContinuousLinearMap.mul ℂ ℂ (f x)) (g y) := by
          apply integral_congr_ae
          filter_upwards [] with x
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

private theorem measurable_starReflection {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (starReflection f) := by
  unfold starReflection
  exact Complex.continuous_conj.measurable.comp (hf.comp measurable_neg)

private theorem fourier_crossCorrelation_of_measurable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfm : Measurable f) (hgm : Measurable g) (w : ℝ) :
    FT (crossCorrelation f g) w = star (FT f w) * FT g w := by
  rw [crossCorrelation,
    fourier_mul_convolution_eq_of_measurable
      (by
        have hneg : Integrable (fun x : ℝ ↦ f (-x)) := hf.comp_neg
        simpa only [starReflection, RCLike.star_def] using
          Complex.conjCLE.toContinuousLinearMap.integrable_comp hneg)
      hg (measurable_starReflection hfm) hgm]
  rw [fourier_starReflection]

private theorem boundaryFourierProduct_integrable {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) :
    Integrable (fun w : ℝ ↦
      star (FT (f : ℝ → ℂ) w) * FT (g : ℝ → ℂ) w) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hscaled :=
    (boundarySpectralProduct_integrable ha f g).comp_mul_left' (R := c) hc
  apply hscaled.congr
  filter_upwards [] with w
  rw [show boundarySpectralProduct ha f g (c * w) =
      star (FT (f : ℝ → ℂ) w) * FT (g : ℝ → ℂ) w by
    unfold boundarySpectralProduct
    rw [yoshidaCriticalSample_eq_fourier,
      yoshidaCriticalSample_eq_fourier]
    congr 4 <;> dsimp only [c] <;> field_simp [Real.pi_ne_zero]]

private theorem crossCorrelation_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (crossCorrelation f g) := by
  have hstar : Integrable (starReflection f) := by
    have hneg : Integrable (fun x : ℝ ↦ f (-x)) := hf.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hneg
  exact hstar.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hg

private theorem normalized_bombieriKernel_boundarySpectralProduct
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    (hfm : Measurable (f : ℝ → ℂ)) (hgm : Measurable (g : ℝ → ℂ))
    (hHcont : Continuous (crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ)))
    (k : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        boundarySpectralProduct ha f g v) =
      ∫ u : ℝ,
        (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
          crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) u := by
  let H : ℝ → ℂ := crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ)
  let b : ℝ := 2 * (k : ℝ) + 1 / 2
  have hb : 0 < b := by positivity
  have hH : Integrable H := by
    exact crossCorrelation_integrable (clipped_integrable f) (clipped_integrable g)
  have hFH : Integrable (FT H) := by
    apply (boundaryFourierProduct_integrable ha f g).congr
    filter_upwards [] with w
    simpa only [H] using (fourier_crossCorrelation_of_measurable
      (clipped_integrable f) (clipped_integrable g) hfm hgm w).symm
  have hcauchy := angular_cauchy_fourier_pairing hH hFH
    (by simpa only [H] using hHcont) b hb
  have hangular (v : ℝ) :
      angularFourier H v = boundarySpectralProduct ha f g v := by
    rw [angularFourier]
    rw [show FT H (v / (2 * Real.pi)) =
        star (FT (f : ℝ → ℂ) (v / (2 * Real.pi))) *
          FT (g : ℝ → ℂ) (v / (2 * Real.pi)) by
      simpa only [H] using fourier_crossCorrelation_of_measurable
        (clipped_integrable f) (clipped_integrable g) hfm hgm
          (v / (2 * Real.pi))]
    unfold boundarySpectralProduct
    rw [yoshidaCriticalSample_eq_fourier,
      yoshidaCriticalSample_eq_fourier]
  have hkernel (v : ℝ) :
      (bombieriDigammaKernel k v : ℂ) =
        (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    unfold bombieriDigammaKernel
    dsimp only [b]
    push_cast
    ring
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
          boundarySpectralProduct ha f g v) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              angularFourier H v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hkernel, hangular]
    _ = ∫ u : ℝ, laplaceKernel b u * H u := hcauchy
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [laplaceKernel]
      change Complex.exp (-(b : ℂ) * (↑|u| : ℂ)) * H u =
        (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) * H u
      rw [show -(b : ℂ) * (↑|u| : ℂ) =
          ((-(2 * (k : ℝ) + 1 / 2) * |u| : ℝ) : ℂ) by
        dsimp only [b]
        push_cast
        ring,
        (Complex.ofReal_exp _).symm]

private theorem normalized_integral_boundarySpectralProduct
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    (hfm : Measurable (f : ℝ → ℂ)) (hgm : Measurable (g : ℝ → ℂ))
    (hHcont : Continuous (crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ))) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, boundarySpectralProduct ha f g v) =
      crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) 0 := by
  let H : ℝ → ℂ := crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ)
  have hH : Integrable H :=
    crossCorrelation_integrable (clipped_integrable f) (clipped_integrable g)
  have hFH : Integrable (FT H) := by
    apply (boundaryFourierProduct_integrable ha f g).congr
    filter_upwards [] with w
    simpa only [H] using (fourier_crossCorrelation_of_measurable
      (clipped_integrable f) (clipped_integrable g) hfm hgm w).symm
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier H) 0 = H 0 :=
    hH.fourierInv_fourier_eq hFH
      (by simpa only [H] using hHcont.continuousAt)
  have hzero : (∫ w : ℝ, FT H w) = H 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  let c : ℝ := 2 * Real.pi
  have hscale := Measure.integral_comp_mul_left
    (boundarySpectralProduct ha f g) c
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, boundarySpectralProduct ha f g v) =
        |c⁻¹| • ∫ v : ℝ, boundarySpectralProduct ha f g v := by
      rw [Complex.real_smul]
      congr 1
      dsimp only [c]
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, boundarySpectralProduct ha f g (c * w) := hscale.symm
    _ = ∫ w : ℝ,
        star (FT (f : ℝ → ℂ) w) * FT (g : ℝ → ℂ) w := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold boundarySpectralProduct
      rw [yoshidaCriticalSample_eq_fourier,
        yoshidaCriticalSample_eq_fourier]
      congr 4 <;> dsimp only [c] <;> field_simp [Real.pi_ne_zero]
    _ = ∫ w : ℝ, FT H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      simpa only [H] using (fourier_crossCorrelation_of_measurable
        (clipped_integrable f) (clipped_integrable g) hfm hgm w).symm
    _ = H 0 := hzero
    _ = _ := rfl

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
