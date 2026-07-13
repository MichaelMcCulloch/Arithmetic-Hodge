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

/-! ## Digamma finite sums under ordinary product decay -/

private def boundaryDigammaCorrection (j : ℕ) (v : ℝ) : ℝ :=
  ((j + 1 : ℕ) : ℝ)⁻¹ - bombieriDigammaKernel (j + 1) v

private theorem boundaryDigammaCorrection_nonneg (j : ℕ) (v : ℝ) :
    0 ≤ boundaryDigammaCorrection j v := by
  rw [boundaryDigammaCorrection]
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

private theorem summable_boundaryDigammaCorrection (v : ℝ) :
    Summable (fun j : ℕ ↦ boundaryDigammaCorrection j v) := by
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
  rw [Real.norm_eq_abs,
    abs_of_nonneg (boundaryDigammaCorrection_nonneg j v)]
  have h := abs_bombieriDigammaKernel_sub_inv_le j v
  rw [abs_sub_comm] at h
  change |boundaryDigammaCorrection j v| ≤
    (1 + v ^ 2) / (((j + 1 : ℕ) : ℝ) ^ 2) at h
  rw [abs_of_nonneg (boundaryDigammaCorrection_nonneg j v)] at h
  exact h

private def boundaryDigammaBase (v : ℝ) : ℝ :=
  -bombieriDigammaKernel 0 v - Real.eulerMascheroniConstant -
    Real.log Real.pi

private def boundaryDigammaPartialKernel (N : ℕ) (v : ℝ) : ℝ :=
  boundaryDigammaBase v +
    ∑ j ∈ Finset.range N, boundaryDigammaCorrection j v

private theorem continuous_bombieriDigammaKernel (k : ℕ) :
    Continuous (fun v : ℝ ↦ bombieriDigammaKernel k v) := by
  unfold bombieriDigammaKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2))
    (fun v ↦ by positivity)

private theorem continuous_boundaryDigammaBase :
    Continuous boundaryDigammaBase := by
  exact ((continuous_bombieriDigammaKernel 0).neg.sub continuous_const).sub
    continuous_const

private theorem continuous_boundaryDigammaPartialKernel (N : ℕ) :
    Continuous (boundaryDigammaPartialKernel N) := by
  unfold boundaryDigammaPartialKernel boundaryDigammaCorrection
  apply continuous_boundaryDigammaBase.add
  apply continuous_finset_sum
  intro j _hj
  exact continuous_const.sub (continuous_bombieriDigammaKernel (j + 1))

private theorem boundaryDigammaBase_le_partial (N : ℕ) (v : ℝ) :
    boundaryDigammaBase v ≤ boundaryDigammaPartialKernel N v := by
  rw [boundaryDigammaPartialKernel]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ ↦ boundaryDigammaCorrection_nonneg j v)

private theorem boundaryDigammaPartial_le_localKernel (N : ℕ) (v : ℝ) :
    boundaryDigammaPartialKernel N v ≤
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi := by
  have hsum := (summable_boundaryDigammaCorrection v).sum_le_tsum
    (Finset.range N) (fun j _ ↦ boundaryDigammaCorrection_nonneg j v)
  rw [boundaryDigammaPartialKernel]
  have hfull :
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi =
        boundaryDigammaBase v + ∑' j : ℕ, boundaryDigammaCorrection j v := by
    rw [digamma_quarter_vertical_re_eq]
    rw [show (∑' j : ℕ,
        (bombieriDigammaKernel (j + 1) v - ((j : ℝ) + 1)⁻¹)) =
        -(∑' j : ℕ, boundaryDigammaCorrection j v) by
      rw [← tsum_neg]
      apply tsum_congr
      intro j
      rw [boundaryDigammaCorrection]
      push_cast
      ring]
    rw [boundaryDigammaBase]
    ring
  rw [hfull]
  simpa only [add_comm] using
    add_le_add_left hsum (boundaryDigammaBase v)

private theorem abs_boundaryDigammaPartialKernel_le (N : ℕ) (v : ℝ) :
    |boundaryDigammaPartialKernel N v| ≤
      |boundaryDigammaBase v| +
        |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
          Real.log Real.pi| := by
  have hlo := boundaryDigammaBase_le_partial N v
  have hhi := boundaryDigammaPartial_le_localKernel N v
  rw [abs_le]
  constructor
  · calc
      -(|boundaryDigammaBase v| +
          |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi|) ≤ -|boundaryDigammaBase v| := by
        linarith [abs_nonneg
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi)]
      _ ≤ boundaryDigammaBase v := neg_abs_le _
      _ ≤ boundaryDigammaPartialKernel N v := hlo
  · calc
      boundaryDigammaPartialKernel N v ≤
          (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi := hhi
      _ ≤ |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi| := le_abs_self _
      _ ≤ |boundaryDigammaBase v| +
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

private theorem boundaryDigammaBase_mul_integrable
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    Integrable (fun v : ℝ ↦
      (boundaryDigammaBase v : ℂ) * boundarySpectralProduct ha f g v) := by
  let C : ℝ := 4 + |Real.eulerMascheroniConstant| + |Real.log Real.pi|
  apply (boundarySpectralProduct_integrable ha f g).bdd_mul
    (c := C) (Complex.continuous_ofReal.comp continuous_boundaryDigammaBase
      |>.aestronglyMeasurable)
  filter_upwards [] with v
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |boundaryDigammaBase v| ≤
        |bombieriDigammaKernel 0 v| +
          |Real.eulerMascheroniConstant| + |Real.log Real.pi| := by
      rw [boundaryDigammaBase]
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
      dsimp only [C]
      linarith

private def boundaryDigammaPartialIntegrand
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    (N : ℕ) (v : ℝ) : ℂ :=
  (boundaryDigammaPartialKernel N v : ℂ) *
    boundarySpectralProduct ha f g v

private theorem boundaryDigammaPartialIntegrand_integrable
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) (N : ℕ) :
    Integrable (boundaryDigammaPartialIntegrand ha f g N) := by
  let bound : ℝ → ℝ := fun v ↦
    ‖(boundaryDigammaBase v : ℂ) * boundarySpectralProduct ha f g v‖ +
      ‖yoshidaClippedCriticalCrossIntegrand a ha f g v‖
  have hbound : Integrable bound :=
    (boundaryDigammaBase_mul_integrable ha f g).norm.add
      (yoshidaClippedCriticalCrossIntegrand_integrable ha f g).norm
  apply hbound.mono'
  · exact ((Complex.continuous_ofReal.comp
      (continuous_boundaryDigammaPartialKernel N)).mul
        (continuous_boundarySpectralProduct ha f g)).aestronglyMeasurable
  · filter_upwards [] with v
    rw [boundaryDigammaPartialIntegrand]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs := abs_boundaryDigammaPartialKernel_le N v
    have hnorm := mul_le_mul_of_nonneg_right habs
      (norm_nonneg (boundarySpectralProduct ha f g v))
    calc
      |boundaryDigammaPartialKernel N v| *
          ‖boundarySpectralProduct ha f g v‖ ≤
          (|boundaryDigammaBase v| +
            |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
              Real.log Real.pi|) *
            ‖boundarySpectralProduct ha f g v‖ := hnorm
      _ = bound v := by
        simp only [bound, yoshidaClippedCriticalCrossIntegrand,
          MultiplicativeWeil.bombieriLocalCriticalKernel,
          boundarySpectralProduct, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        ring

private theorem tendsto_integral_boundaryDigammaPartialIntegrand
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    Tendsto (fun N : ℕ ↦
      ∫ v : ℝ, boundaryDigammaPartialIntegrand ha f g N v) atTop
      (𝓝 (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v)) := by
  let bound : ℝ → ℝ := fun v ↦
    ‖(boundaryDigammaBase v : ℂ) * boundarySpectralProduct ha f g v‖ +
      ‖yoshidaClippedCriticalCrossIntegrand a ha f g v‖
  have hbound : Integrable bound :=
    (boundaryDigammaBase_mul_integrable ha f g).norm.add
      (yoshidaClippedCriticalCrossIntegrand_integrable ha f g).norm
  apply tendsto_integral_of_dominated_convergence bound
  · intro N
    exact (boundaryDigammaPartialIntegrand_integrable ha f g N)
      |>.aestronglyMeasurable
  · exact hbound
  · intro N
    filter_upwards [] with v
    rw [boundaryDigammaPartialIntegrand]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs := abs_boundaryDigammaPartialKernel_le N v
    have hnorm := mul_le_mul_of_nonneg_right habs
      (norm_nonneg (boundarySpectralProduct ha f g v))
    calc
      |boundaryDigammaPartialKernel N v| *
          ‖boundarySpectralProduct ha f g v‖ ≤
          (|boundaryDigammaBase v| +
            |(Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
              Real.log Real.pi|) *
            ‖boundarySpectralProduct ha f g v‖ := hnorm
      _ = bound v := by
        simp only [bound, yoshidaClippedCriticalCrossIntegrand,
          MultiplicativeWeil.bombieriLocalCriticalKernel,
          boundarySpectralProduct, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        ring
  · filter_upwards [] with v
    have hsum := (summable_boundaryDigammaCorrection v).hasSum.tendsto_sum_nat
    have hkernel : Tendsto
        (fun N : ℕ ↦ boundaryDigammaPartialKernel N v) atTop
        (𝓝 ((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi)) := by
      rw [show (Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi =
          boundaryDigammaBase v +
            ∑' j : ℕ, boundaryDigammaCorrection j v by
        rw [digamma_quarter_vertical_re_eq]
        rw [show (∑' j : ℕ,
            (bombieriDigammaKernel (j + 1) v - ((j : ℝ) + 1)⁻¹)) =
            -(∑' j : ℕ, boundaryDigammaCorrection j v) by
          rw [← tsum_neg]
          apply tsum_congr
          intro j
          rw [boundaryDigammaCorrection]
          push_cast
          ring]
        rw [boundaryDigammaBase]
        ring]
      exact tendsto_const_nhds.add hsum
    have hkernelC : Tendsto
        (fun N : ℕ ↦ (boundaryDigammaPartialKernel N v : ℂ)) atTop
        (𝓝 (((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * I)).re - Real.log Real.pi : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hkernel
    have hmul := hkernelC.mul
      (tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ boundarySpectralProduct ha f g v) atTop
        (𝓝 (boundarySpectralProduct ha f g v)))
    simpa only [boundaryDigammaPartialIntegrand,
      yoshidaClippedCriticalCrossIntegrand,
      MultiplicativeWeil.bombieriLocalCriticalKernel,
      boundarySpectralProduct, mul_assoc] using hmul

private theorem bombieriDigammaKernel_nonneg (k : ℕ) (v : ℝ) :
    0 ≤ bombieriDigammaKernel k v := by
  unfold bombieriDigammaKernel
  positivity

private theorem boundaryDigammaCorrection_le_inv (j : ℕ) (v : ℝ) :
    boundaryDigammaCorrection j v ≤ ((j + 1 : ℕ) : ℝ)⁻¹ := by
  rw [boundaryDigammaCorrection]
  linarith [bombieriDigammaKernel_nonneg (j + 1) v]

private theorem boundaryDigammaCorrection_mul_integrable
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) (j : ℕ) :
    Integrable (fun v : ℝ ↦
      (boundaryDigammaCorrection j v : ℂ) *
        boundarySpectralProduct ha f g v) := by
  let c : ℝ := ((j + 1 : ℕ) : ℝ)⁻¹
  apply (boundarySpectralProduct_integrable ha f g).bdd_mul (c := c)
    ((Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_bombieriDigammaKernel (j + 1))))
      |>.aestronglyMeasurable)
  filter_upwards [] with v
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |boundaryDigammaCorrection j v| ≤ c
  rw [
    abs_of_nonneg (boundaryDigammaCorrection_nonneg j v)]
  exact boundaryDigammaCorrection_le_inv j v

private theorem bombieriDigammaKernel_mul_integrable
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) (k : ℕ) :
    Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel k v : ℂ) *
        boundarySpectralProduct ha f g v) := by
  by_cases hk : k = 0
  · subst k
    apply (boundarySpectralProduct_integrable ha f g).bdd_mul (c := 4)
      ((Complex.continuous_ofReal.comp
        (continuous_bombieriDigammaKernel 0)).aestronglyMeasurable)
    filter_upwards [] with v
    exact bombieriDigammaKernel_zero_norm_le_four v
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    let r : ℂ := ((((j + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)
    have hrM : Integrable (fun v : ℝ ↦
        r * boundarySpectralProduct ha f g v) :=
      (boundarySpectralProduct_integrable ha f g).const_mul r
    have hq := boundaryDigammaCorrection_mul_integrable ha f g j
    apply (hrM.sub hq).congr
    filter_upwards [] with v
    simp only [Pi.sub_apply, r, boundaryDigammaCorrection]
    push_cast
    ring

/-- Endpoint-jump-compatible digamma distribution.  Unlike the weighted
interface, this theorem uses only ordinary product decay and the actual
integrability of the production critical-cross integrand. -/
private theorem normalized_boundaryCriticalCross_eq_cauchySeries
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    (A : ℕ → ℂ) (H0 : ℂ)
    (hA : ∀ k : ℕ,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
            boundarySpectralProduct ha f g v = A k)
    (hH0 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, boundarySpectralProduct ha f g v = H0)
    (hs : Summable (fun j : ℕ ↦
      A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v) =
      -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          ∑' j : ℕ,
            (A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) -
        (Real.log Real.pi : ℂ) * H0 := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let B : ℂ := -A 0 - (Real.eulerMascheroniConstant : ℂ) * H0 -
    (Real.log Real.pi : ℂ) * H0
  let Q : ℕ → ℂ := fun j ↦
    (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0 - A (j + 1)
  have hQ : Summable Q := by
    apply hs.neg.congr
    intro j
    dsimp only [Q]
    ring
  have hfinite (N : ℕ) :
      c * ∫ v : ℝ, boundaryDigammaPartialIntegrand ha f g N v =
        B + ∑ j ∈ Finset.range N, Q j := by
    let M : ℝ → ℂ := boundarySpectralProduct ha f g
    let Base : ℝ → ℂ := fun v ↦ (boundaryDigammaBase v : ℂ) * M v
    let Corr : ℕ → ℝ → ℂ := fun j v ↦
      (boundaryDigammaCorrection j v : ℂ) * M v
    have hM : Integrable M := boundarySpectralProduct_integrable ha f g
    have hBase : Integrable Base := by
      simpa only [Base, M] using boundaryDigammaBase_mul_integrable ha f g
    have hCorr (j : ℕ) : Integrable (Corr j) := by
      simpa only [Corr, M] using
        boundaryDigammaCorrection_mul_integrable ha f g j
    have hCorrSum : Integrable (fun v : ℝ ↦
        ∑ j ∈ Finset.range N, Corr j v) := by
      apply integrable_finset_sum
      intro j hj
      exact hCorr j
    have hsplit :
        (∫ v : ℝ, boundaryDigammaPartialIntegrand ha f g N v) =
          (∫ v : ℝ, Base v) +
            ∑ j ∈ Finset.range N, ∫ v : ℝ, Corr j v := by
      calc
        _ = ∫ v : ℝ, Base v + ∑ j ∈ Finset.range N, Corr j v := by
          apply integral_congr_ae
          filter_upwards [] with v
          simp only [boundaryDigammaPartialIntegrand,
            boundaryDigammaPartialKernel, Base, Corr, M]
          push_cast
          rw [add_mul, Finset.sum_mul]
        _ = (∫ v : ℝ, Base v) +
            ∫ v : ℝ, ∑ j ∈ Finset.range N, Corr j v :=
          MeasureTheory.integral_add hBase hCorrSum
        _ = _ := by
          rw [MeasureTheory.integral_finset_sum]
          intro j hj
          exact hCorr j
    have hBaseValue : c * ∫ v : ℝ, Base v = B := by
      let K0 : ℝ → ℂ := fun v ↦
        (bombieriDigammaKernel 0 v : ℂ) * M v
      let γM : ℝ → ℂ := fun v ↦
        (Real.eulerMascheroniConstant : ℂ) * M v
      let pM : ℝ → ℂ := fun v ↦ (Real.log Real.pi : ℂ) * M v
      have hK0 : Integrable K0 := by
        simpa only [K0, M] using bombieriDigammaKernel_mul_integrable ha f g 0
      have hγM : Integrable γM := hM.const_mul _
      have hpM : Integrable pM := hM.const_mul _
      have hinner : (∫ v : ℝ, -K0 v - γM v) =
          (∫ v : ℝ, -K0 v) - ∫ v : ℝ, γM v := by
        exact MeasureTheory.integral_sub hK0.neg hγM
      have hdecomp : (∫ v : ℝ, Base v) =
          -(∫ v : ℝ, K0 v) -
            (Real.eulerMascheroniConstant : ℂ) * (∫ v : ℝ, M v) -
            (Real.log Real.pi : ℂ) * (∫ v : ℝ, M v) := by
        calc
          _ = ∫ v : ℝ,
              -K0 v - γM v - pM v := by
            apply integral_congr_ae
            filter_upwards [] with v
            simp only [Base, K0, γM, pM, M, boundaryDigammaBase]
            push_cast
            ring
          _ = ((∫ v : ℝ, -K0 v) - ∫ v : ℝ, γM v) -
              ∫ v : ℝ, pM v := by
            calc
              (∫ v : ℝ, -K0 v - γM v - pM v) =
                  (∫ v : ℝ, -K0 v - γM v) -
                    ∫ v : ℝ, pM v :=
                MeasureTheory.integral_sub (hK0.neg.sub hγM) hpM
              _ = _ := by
                rw [hinner]
          _ = _ := by
            rw [MeasureTheory.integral_neg,
              show (∫ v : ℝ, γM v) =
                  (Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v by
                simpa only [γM] using MeasureTheory.integral_const_mul
                  (Real.eulerMascheroniConstant : ℂ) M,
              show (∫ v : ℝ, pM v) =
                  (Real.log Real.pi : ℂ) * ∫ v : ℝ, M v by
                simpa only [pM] using MeasureTheory.integral_const_mul
                  (Real.log Real.pi : ℂ) M]
      rw [hdecomp]
      have hK0Value : c * ∫ v : ℝ, K0 v = A 0 := by
        simpa only [c, K0, M] using hA 0
      have hMValue : c * ∫ v : ℝ, M v = H0 := by
        simpa only [c, M] using hH0
      calc
        c * ((-(∫ v : ℝ, K0 v) -
              (Real.eulerMascheroniConstant : ℂ) * (∫ v : ℝ, M v)) -
            (Real.log Real.pi : ℂ) * (∫ v : ℝ, M v)) =
            -(c * ∫ v : ℝ, K0 v) -
              (Real.eulerMascheroniConstant : ℂ) *
                (c * ∫ v : ℝ, M v) -
              (Real.log Real.pi : ℂ) *
                (c * ∫ v : ℝ, M v) := by ring
        _ = B := by
          rw [hK0Value, hMValue]
    have hCorrValue (j : ℕ) :
        c * ∫ v : ℝ, Corr j v = Q j := by
      let r : ℂ := (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ)
      let K : ℝ → ℂ := fun v ↦
        (bombieriDigammaKernel (j + 1) v : ℂ) * M v
      have hrM : Integrable (fun v : ℝ ↦ r * M v) := hM.const_mul r
      have hK : Integrable K := by
        simpa only [K, M] using
          bombieriDigammaKernel_mul_integrable ha f g (j + 1)
      have hdecomp : (∫ v : ℝ, Corr j v) =
          r * (∫ v : ℝ, M v) - ∫ v : ℝ, K v := by
        calc
          _ = ∫ v : ℝ, r * M v - K v := by
            apply integral_congr_ae
            filter_upwards [] with v
            simp only [Corr, r, K, M, boundaryDigammaCorrection]
            push_cast
            ring
          _ = (∫ v : ℝ, r * M v) - ∫ v : ℝ, K v :=
            MeasureTheory.integral_sub hrM hK
          _ = _ := by
            congr 1
            simpa using MeasureTheory.integral_const_mul r M
      rw [hdecomp]
      have hMValue : c * ∫ v : ℝ, M v = H0 := by
        simpa only [c, M] using hH0
      have hKValue : c * ∫ v : ℝ, K v = A (j + 1) := by
        simpa only [c, K, M] using hA (j + 1)
      calc
        c * (r * (∫ v : ℝ, M v) - ∫ v : ℝ, K v) =
            r * (c * ∫ v : ℝ, M v) -
              (c * ∫ v : ℝ, K v) := by ring
        _ = Q j := by
          rw [hMValue, hKValue]
    rw [hsplit]
    calc
      c * ((∫ v : ℝ, Base v) +
          ∑ j ∈ Finset.range N, ∫ v : ℝ, Corr j v) =
          c * (∫ v : ℝ, Base v) +
            ∑ j ∈ Finset.range N,
              c * ∫ v : ℝ, Corr j v := by
        rw [mul_add, Finset.mul_sum]
      _ = _ := by
        rw [hBaseValue]
        apply congrArg (fun z : ℂ ↦ B + z)
        apply Finset.sum_congr rfl
        intro j hj
        exact hCorrValue j
  have hleft : Tendsto (fun N : ℕ ↦
      c * ∫ v : ℝ, boundaryDigammaPartialIntegrand ha f g N v) atTop
      (𝓝 (c * ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand a ha f g v)) :=
    Tendsto.const_mul c
      (tendsto_integral_boundaryDigammaPartialIntegrand ha f g)
  have hright : Tendsto (fun N : ℕ ↦
      B + ∑ j ∈ Finset.range N, Q j) atTop
      (𝓝 (B + ∑' j : ℕ, Q j)) :=
    tendsto_const_nhds.add hQ.hasSum.tendsto_sum_nat
  have hsame : Tendsto (fun N : ℕ ↦
      c * ∫ v : ℝ, boundaryDigammaPartialIntegrand ha f g N v) atTop
      (𝓝 (B + ∑' j : ℕ, Q j)) := by
    apply hright.congr'
    filter_upwards [] with N
    exact (hfinite N).symm
  have hlimit := tendsto_nhds_unique hleft hsame
  rw [show c = ((1 / (2 * Real.pi) : ℝ) : ℂ) by rfl] at hlimit
  rw [show B + ∑' j : ℕ, Q j =
      -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          ∑' j : ℕ,
            (A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) -
        (Real.log Real.pi : ℂ) * H0 by
    dsimp only [B, Q]
    rw [show (∑' j : ℕ,
        ((((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0 - A (j + 1))) =
      -(∑' j : ℕ,
        (A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) by
      rw [← tsum_neg]
      apply tsum_congr
      intro j
      ring]
    ring] at hlimit
  exact hlimit

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
