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
open YoshidaRegularKernelBound
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

/-! ## Real positive-half geometric evaluation -/

def boundaryArchCorrelation (L : ℝ) (C : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ in 0..L,
      (C 0 - C u) / u - 2 * yoshidaRegularKernel u * C u) -
    (Real.log L + Real.eulerMascheroniConstant + Real.log 2 +
      Real.log Real.pi) * C 0

private theorem neg_oddKernel_eq_defect_sub_regular
    (C0 : ℝ) (C : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    -oddKernel u * C u + C0 / u =
      (C0 - C u) / u - 2 * yoshidaRegularKernel u * C u := by
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    have : u = -u := Real.exp_injective heq
    exact hu (by linarith)
  rw [oddKernel, yoshidaRegularKernel, if_neg hu, Real.sinh_eq]
  field_simp [hu, hden]
  ring

private theorem boundaryDigammaGeometricValue
    {L : ℝ} (hL : 0 < L) (C D : ℝ → ℝ)
    (hC : Continuous C) (hD : Continuous D)
    (hrem : ∀ u : ℝ, C u = C 0 + u * D u) :
    Summable (fun k : ℕ ↦
      geometricIntegralTerm L C (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * C 0)) ∧
    (-(geometricIntegralTerm L C 0 +
        Real.eulerMascheroniConstant * C 0 +
        ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
          (((k + 1 : ℕ) : ℝ)⁻¹ * C 0))) -
      Real.log Real.pi * C 0 = boundaryArchCorrelation L C) := by
  have hinterchange : PairedIntegralInterchange L (C 0) C := by
    apply pairedIntegralInterchange_of_removable hL hC
    · intro u _hu
      exact hrem u
    · exact removableMajorantLimit_intervalIntegrable hD (C 0) L
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand (C 0) C) volume 0 L :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (C 0) L hrem
  have href : IntervalIntegrable referenceRegularized volume 0 L :=
    referenceRegularized_intervalIntegrable L
  have hren : HasSum (renormalizedTerm L (C 0) C)
      ((∫ u : ℝ in 0..L, stableGeometricIntegrand (C 0) C u) +
        (Real.log L + Real.log 2) * C 0) :=
    renormalizedSeries_hasSum_stable hL hC hinterchange hstable href
  have hindex :
      geometricIntegralTerm L C 0 +
          ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
            C 0 / (k + 1 : ℕ)) =
        ∑' k : ℕ, renormalizedTerm L (C 0) C k := by
    calc
      _ = (∫ u : ℝ in 0..L,
            stableGeometricIntegrand (C 0) C u) +
          (Real.log L + Real.log 2) * C 0 :=
        geometricIntegralTerm_zero_add_tsum_shifted_eq hren
      _ = _ := hren.tsum_eq.symm
  have hneg := negated_geometric_identity hL hC hinterchange hstable href
  have hs : Summable (fun k : ℕ ↦
      geometricIntegralTerm L C (k + 1) - C 0 / (k + 1 : ℕ)) :=
    (hasSum_shifted_geometric_of_hasSum_renormalized hren).summable
  have hintegral :
      (∫ u : ℝ in 0..L, -oddKernel u * C u + C 0 / u) =
        ∫ u : ℝ in 0..L,
          (C 0 - C u) / u - 2 * yoshidaRegularKernel u * C u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _hu
    exact neg_oddKernel_eq_defect_sub_regular (C 0) C hu
  rw [hintegral] at hneg
  have hindex' :
      geometricIntegralTerm L C 0 +
          ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
            (((k + 1 : ℕ) : ℝ)⁻¹ * C 0)) =
        ∑' k : ℕ, renormalizedTerm L (C 0) C k := by
    simpa only [div_eq_mul_inv, mul_comm] using hindex
  have hs' : Summable (fun k : ℕ ↦
      geometricIntegralTerm L C (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * C 0)) := by
    simpa only [div_eq_mul_inv, mul_comm] using hs
  refine ⟨hs', ?_⟩
  rw [show geometricIntegralTerm L C 0 +
      Real.eulerMascheroniConstant * C 0 +
      ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * C 0)) =
      Real.eulerMascheroniConstant * C 0 +
        (geometricIntegralTerm L C 0 +
          ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
            (((k + 1 : ℕ) : ℝ)⁻¹ * C 0))) by ring,
    hindex']
  unfold boundaryArchCorrelation
  linarith

private theorem exp_abs_mul_crossCorrelation_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℝ ↦
      ((Real.exp (-b * |u|) : ℝ) : ℂ) * crossCorrelation f g u) := by
  have hcoeff : Continuous (fun u : ℝ ↦
      ((Real.exp (-b * |u|) : ℝ) : ℂ)) := by fun_prop
  refine (crossCorrelation_integrable hf hg).bdd_mul (c := 1)
    hcoeff.aestronglyMeasurable ?_
  filter_upwards [] with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff).2 (mul_nonpos_of_nonpos_of_nonneg
    (by linarith : -b ≤ 0) (abs_nonneg u))

private theorem integral_exp_abs_crossCorrelation_eq_geometric
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {L b : ℝ} (hL : 0 < L) (hb : 0 < b)
    (C : ℝ → ℝ)
    (hEven : Function.Even (crossCorrelation f g))
    (hzero : ∀ u : ℝ, L < u → crossCorrelation f g u = 0)
    (hmatch : ∀ u ∈ Icc (0 : ℝ) L,
      crossCorrelation f g u = (C u : ℂ)) :
    (∫ u : ℝ,
      ((Real.exp (-b * |u|) : ℝ) : ℂ) * crossCorrelation f g u) =
      2 * ∫ u : ℝ in 0..L,
        ((Real.exp (-b * u) : ℝ) : ℂ) * (C u : ℂ) := by
  let F : ℝ → ℂ := fun u ↦
    ((Real.exp (-b * |u|) : ℝ) : ℂ) * crossCorrelation f g u
  have hFint : Integrable F := by
    simpa only [F] using exp_abs_mul_crossCorrelation_integrable hf hg hb
  have hFeven : Function.Even F := by
    intro u
    dsimp only [F]
    rw [abs_neg, hEven]
  have hleft : (∫ u : ℝ in Iic 0, F u) =
      ∫ u : ℝ in Ioi 0, F u := by
    calc
      (∫ u : ℝ in Iic 0, F u) =
          ∫ u : ℝ in Iic 0, F (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _hu
        exact (hFeven u).symm
      _ = ∫ u : ℝ in Ioi 0, F u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 F
  have hwhole : (∫ u : ℝ, F u) =
      2 * ∫ u : ℝ in Ioi 0, F u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hFint.integrableOn hFint.integrableOn,
      hleft]
    ring
  have hpositive : (∫ u : ℝ in Ioi 0, F u) =
      ∫ u : ℝ in 0..L, F u := by
    rw [intervalIntegral.integral_of_le hL.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self
    intro u hu
    have huLt : L < u := by
      rcases hu with ⟨hu0, huNot⟩
      simp only [mem_Ioi] at hu0
      simp only [mem_Ioc, not_and, not_le] at huNot
      exact huNot hu0
    dsimp only [F]
    rw [hzero u huLt, mul_zero]
  have hinterval : (∫ u : ℝ in 0..L, F u) =
      ∫ u : ℝ in 0..L,
        ((Real.exp (-b * u) : ℝ) : ℂ) * (C u : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) L := by
      simpa only [uIcc_of_le hL.le] using hu
    dsimp only [F]
    rw [abs_of_nonneg hu'.1, hmatch u hu']
  change (∫ u : ℝ, F u) = _
  rw [hwhole, hpositive, hinterval]

private theorem normalized_boundaryCriticalCross_eq_archCorrelation
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a)
    {L : ℝ} (hL : 0 < L) (C D : ℝ → ℝ)
    (hC : Continuous C) (hD : Continuous D)
    (hrem : ∀ u : ℝ, C u = C 0 + u * D u)
    (hA : ∀ k : ℕ,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
            boundarySpectralProduct ha f g v =
        (geometricIntegralTerm L C k : ℂ))
    (hH0 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, boundarySpectralProduct ha f g v = (C 0 : ℂ)) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v =
      (boundaryArchCorrelation L C : ℂ) := by
  have hgeo := boundaryDigammaGeometricValue hL C D hC hD hrem
  obtain ⟨hsReal, hvalue⟩ := hgeo
  let A : ℕ → ℂ := fun k ↦ (geometricIntegralTerm L C k : ℂ)
  let H0 : ℂ := (C 0 : ℂ)
  have hsComplex : Summable (fun j : ℕ ↦
      A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0) := by
    have hcast := Complex.ofRealCLM.summable hsReal
    apply hcast.congr
    intro j
    dsimp only [A, H0]
    rw [Complex.ofRealCLM_apply]
    push_cast
    ring
  have hdist := normalized_boundaryCriticalCross_eq_cauchySeries
    ha f g A H0 (by intro k; simpa only [A] using hA k)
      (by simpa only [H0] using hH0) hsComplex
  have htsum :
      (∑' j : ℕ,
        (A (j + 1) - (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) =
      (((∑' j : ℕ,
        (geometricIntegralTerm L C (j + 1) -
          (((j + 1 : ℕ) : ℝ)⁻¹ * C 0))) : ℝ) : ℂ) := by
    calc
      _ = ∑' j : ℕ, Complex.ofRealCLM
          (geometricIntegralTerm L C (j + 1) -
            (((j + 1 : ℕ) : ℝ)⁻¹ * C 0)) := by
        apply tsum_congr
        intro j
        dsimp only [A, H0]
        rw [Complex.ofRealCLM_apply]
        push_cast
        ring
      _ = Complex.ofRealCLM (∑' j : ℕ,
          (geometricIntegralTerm L C (j + 1) -
            (((j + 1 : ℕ) : ℝ)⁻¹ * C 0))) :=
        Complex.ofRealCLM.map_tsum hsReal |>.symm
      _ = _ := Complex.ofRealCLM_apply _
  rw [htsum] at hdist
  have hrhs :
      -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          (((∑' j : ℕ,
            (geometricIntegralTerm L C (j + 1) -
              (((j + 1 : ℕ) : ℝ)⁻¹ * C 0))) : ℝ) : ℂ)) -
        (Real.log Real.pi : ℂ) * H0 =
      (boundaryArchCorrelation L C : ℂ) := by
    dsimp only [A, H0]
    rw [← hvalue]
    push_cast
    ring
  rw [hrhs] at hdist
  exact hdist

/-! ## Constant and constant--zero-trace correlations -/

private theorem measurable_yoshidaClippedOne (a : ℝ) :
    Measurable ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ) := by
  change Measurable (fun x : ℝ ↦
    if x ∈ Icc (-a) a then (1 : ℂ) else 0)
  exact Measurable.ite measurableSet_Icc measurable_const measurable_const

private theorem yoshidaClippedOne_real (a x : ℝ) :
    star ((yoshidaClippedOne a : YoshidaClippedSmooth a) x) =
      (yoshidaClippedOne a : YoshidaClippedSmooth a) x := by
  change star (if x ∈ Icc (-a) a then (1 : ℂ) else 0) =
    if x ∈ Icc (-a) a then (1 : ℂ) else 0
  split <;> simp

private theorem crossCorrelation_even_of_real_even
    {f g : ℝ → ℂ}
    (hfReal : ∀ x : ℝ, star (f x) = f x)
    (hfEven : Function.Even f) (hgEven : Function.Even g) :
    Function.Even (crossCorrelation f g) := by
  intro u
  rw [crossCorrelation]
  apply convolution_neg_of_neg_eq
  · filter_upwards [] with x
    unfold starReflection
    rw [hfEven, hfReal]
  · filter_upwards [] with x
    exact hgEven x

private theorem crossCorrelation_eq_zero_of_two_mul_a_lt
    {a u : ℝ} (hu : 2 * a < u)
    (f g : YoshidaClippedSmooth a) :
    crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) u = 0 := by
  rw [crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-a) a
  · have hux : u + x ∉ Icc (-a) a := by
      intro hmem
      linarith [hx.1, hmem.2]
    rw [yoshidaClippedSmooth_eq_zero_outside g hux, mul_zero]
    simp
  · rw [yoshidaClippedSmooth_eq_zero_outside f hx, star_zero, zero_mul]
    simp

private theorem crossCorrelation_eq_real_overlap
    {a u : ℝ} (f g : YoshidaClippedSmooth a)
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (hg_real : ∀ x ∈ Icc (-a) a, g x = ((g x).re : ℂ))
    (hu0 : 0 ≤ u) (huL : u ≤ 2 * a) :
    crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) u =
      ((∫ x : ℝ in -a..a - u,
        (f x).re * (g (u + x)).re : ℝ) : ℂ) := by
  rw [crossCorrelation_apply]
  have hle : -a ≤ a - u := by linarith
  have hsupport :
      (∫ x : ℝ, star (f x) * g (u + x)) =
        ∫ x : ℝ in -a..a - u, star (f x) * g (u + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxf : x ∈ Icc (-a) a
      · have hxgt : a - u < x := by
          by_contra hnot
          exact hx ⟨hxf.1, le_of_not_gt hnot⟩
        have hux : u + x ∉ Icc (-a) a := by
          intro hmem
          linarith [hmem.2]
        rw [yoshidaClippedSmooth_eq_zero_outside g hux, mul_zero]
      · rw [yoshidaClippedSmooth_eq_zero_outside f hxf,
          star_zero, zero_mul])).symm
  rw [hsupport, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (-a) (a - u) := by
    simpa only [uIcc_of_le hle] using hx
  have hxf : x ∈ Icc (-a) a := ⟨hx'.1, by linarith [hx'.2, hu0]⟩
  have hux : u + x ∈ Icc (-a) a := by
    constructor <;> linarith [hx'.1, hx'.2, hu0]
  change star (f x) * g (u + x) =
    (((f x).re * (g (u + x)).re : ℝ) : ℂ)
  rw [hf_real x hxf, hg_real (u + x) hux]
  simp

def constantEndpointCorrelation (a : ℝ) (u : ℝ) : ℝ :=
  2 * a - u

private theorem continuous_constantEndpointCorrelation (a : ℝ) :
    Continuous (constantEndpointCorrelation a) := by
  unfold constantEndpointCorrelation
  fun_prop

private theorem constantEndpointCorrelation_removable (a u : ℝ) :
    constantEndpointCorrelation a u =
      constantEndpointCorrelation a 0 + u * (-1) := by
  unfold constantEndpointCorrelation
  ring

private theorem crossCorrelation_one_one_match
    {a u : ℝ} (hu : u ∈ Icc (0 : ℝ) (2 * a)) :
    crossCorrelation
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ) u =
      (constantEndpointCorrelation a u : ℂ) := by
  rw [crossCorrelation_eq_real_overlap
    (yoshidaClippedOne a) (yoshidaClippedOne a)
    (fun x hx ↦ by rw [show
      (yoshidaClippedOne a : YoshidaClippedSmooth a) x = 1 by
        change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
        rw [if_pos hx]]; simp)
    (fun x hx ↦ by rw [show
      (yoshidaClippedOne a : YoshidaClippedSmooth a) x = 1 by
        change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
        rw [if_pos hx]]; simp)
    hu.1 hu.2]
  have hle : -a ≤ a - u := by linarith [hu.2]
  have hreal :
      (∫ x : ℝ in -a..a - u,
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) x).re *
          ((yoshidaClippedOne a : YoshidaClippedSmooth a) (u + x)).re) =
        constantEndpointCorrelation a u := by
    calc
      _ = ∫ _x : ℝ in -a..a - u, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (-a) (a - u) := by
          simpa only [uIcc_of_le hle] using hx
        have hxf : x ∈ Icc (-a) a :=
          ⟨hx'.1, by linarith [hx'.2, hu.1]⟩
        have hux : u + x ∈ Icc (-a) a := by
          constructor <;> linarith [hx'.1, hx'.2, hu.1]
        change
          ((yoshidaClippedOne a : YoshidaClippedSmooth a) x).re *
            ((yoshidaClippedOne a : YoshidaClippedSmooth a) (u + x)).re = 1
        rw [show (yoshidaClippedOne a : YoshidaClippedSmooth a) x = 1 by
          change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
          rw [if_pos hxf],
          show (yoshidaClippedOne a : YoshidaClippedSmooth a) (u + x) = 1 by
          change (if u + x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
          rw [if_pos hux]]
        norm_num
      _ = constantEndpointCorrelation a u := by
        unfold constantEndpointCorrelation
        norm_num
        ring
  exact congrArg Complex.ofReal hreal

private def constantCorrelationExtension (a : ℝ) (u : ℝ) : ℝ :=
  if |u| ≤ 2 * a then 2 * a - |u| else 0

private theorem continuous_constantCorrelationExtension (a : ℝ) :
    Continuous (constantCorrelationExtension a) := by
  unfold constantCorrelationExtension
  apply Continuous.if_le
    ((continuous_const.sub continuous_abs)) continuous_const
    continuous_abs continuous_const
  intro u hu
  rw [hu]
  ring

private theorem crossCorrelation_one_one_even (a : ℝ) : Function.Even
    (crossCorrelation
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)) :=
  crossCorrelation_even_of_real_even
    (yoshidaClippedOne_real a) (periodicCoreOne_even a)
      (periodicCoreOne_even a)

private theorem crossCorrelation_one_one_eq_extension (a : ℝ) :
    crossCorrelation
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ) =
      fun u ↦ (constantCorrelationExtension a u : ℂ) := by
  funext u
  by_cases hu : 0 ≤ u
  · rw [constantCorrelationExtension, abs_of_nonneg hu]
    by_cases huL : u ≤ 2 * a
    · rw [if_pos huL]
      exact crossCorrelation_one_one_match ⟨hu, huL⟩
    · rw [if_neg huL,
        crossCorrelation_eq_zero_of_two_mul_a_lt
          (lt_of_not_ge huL) (yoshidaClippedOne a) (yoshidaClippedOne a)]
      norm_num
  · have hneg : 0 ≤ -u := by linarith
    have habs : |u| = -u := abs_of_neg (lt_of_not_ge hu)
    rw [constantCorrelationExtension, habs,
      ← crossCorrelation_one_one_even a u]
    by_cases huL : -u ≤ 2 * a
    · rw [if_pos huL]
      exact crossCorrelation_one_one_match ⟨hneg, huL⟩
    · rw [if_neg huL,
        crossCorrelation_eq_zero_of_two_mul_a_lt
          (lt_of_not_ge huL) (yoshidaClippedOne a) (yoshidaClippedOne a)]
      norm_num

private theorem continuous_crossCorrelation_one_one (a : ℝ) :
    Continuous (crossCorrelation
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  rw [crossCorrelation_one_one_eq_extension a]
  exact Complex.continuous_ofReal.comp
    (continuous_constantCorrelationExtension a)

def residualEndpointCorrelation {a : ℝ}
    (r : YoshidaClippedSmooth a) (u : ℝ) : ℝ :=
  ∫ x : ℝ in -a..a - u, (r x).re

private theorem continuous_residualEndpointCorrelation
    {a : ℝ} (r : YoshidaClippedSmooth a)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    Continuous (residualEndpointCorrelation r) := by
  have hg : Continuous (fun x : ℝ ↦ (r x).re) :=
    Complex.continuous_re.comp hrcont
  rw [continuous_iff_continuousAt]
  intro u
  have hFTC := intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable (-a) (a - u))
    hg.stronglyMeasurable.stronglyMeasurableAtFilter
    hg.continuousAt
  have hinner : Tendsto (fun v : ℝ ↦ a - v) (𝓝 u) (𝓝 (a - u)) := by
    exact continuousAt_const.sub continuousAt_id
  exact (hFTC.continuousAt.comp hinner)

private theorem contDiff_one_residualEndpointCorrelation
    {a : ℝ} (r : YoshidaClippedSmooth a)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    ContDiff ℝ 1 (residualEndpointCorrelation r) := by
  let g : ℝ → ℝ := fun x ↦ (r x).re
  have hg : Continuous g := Complex.continuous_re.comp hrcont
  have hderiv (u : ℝ) : HasDerivAt (residualEndpointCorrelation r)
      (-g (a - u)) u := by
    have hFTC := intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (-a) (a - u))
      hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
    have hinner : HasDerivAt (fun v : ℝ ↦ a - v) (-1) u := by
      convert (hasDerivAt_const u a).sub (hasDerivAt_id u) using 1
      all_goals simp
    convert hFTC.comp u hinner using 1
    all_goals simp [g]
  rw [contDiff_one_iff_deriv]
  constructor
  · intro u
    exact (hderiv u).differentiableAt
  · rw [show deriv (residualEndpointCorrelation r) =
        fun u ↦ -g (a - u) by
      funext u
      exact (hderiv u).deriv]
    fun_prop

private theorem exists_continuous_residualEndpointSlope
    {a : ℝ} (r : YoshidaClippedSmooth a)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    ∃ D : ℝ → ℝ, Continuous D ∧
      ∀ u : ℝ, residualEndpointCorrelation r u =
        residualEndpointCorrelation r 0 + u * D u := by
  let C : ℝ → ℝ := residualEndpointCorrelation r
  have hC : ContDiff ℝ 1 C :=
    contDiff_one_residualEndpointCorrelation r hrcont
  let Q : ℝ → ℝ := fun u ↦ (C u - C 0) / u
  let D : ℝ → ℝ := Function.update Q 0 (deriv C 0)
  have hderiv : HasDerivAt C (deriv C 0) 0 :=
    (hC.differentiable (by norm_num) 0).hasDerivAt
  have hQzero : Tendsto Q (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (deriv C 0)) := by
    have h := hderiv.tendsto_slope_zero
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [Q]
    simp only [zero_add, smul_eq_mul, div_eq_inv_mul]
  have hD : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = 0
    · subst u
      rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_same]
      exact hQzero
    · rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_of_ne hu]
      exact ((hC.continuous.continuousAt.sub continuousAt_const).div
        continuousAt_id hu)
  refine ⟨D, hD, ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    simp
  · rw [show D u = Q u by simp [D, hu]]
    dsimp only [Q]
    field_simp [hu]
    ring

private theorem continuous_crossCorrelation_one_residual
    {a : ℝ} (r : YoshidaClippedSmooth a)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    Continuous (crossCorrelation
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
      (r : ℝ → ℂ)) := by
  rw [crossCorrelation]
  have honeInt : Integrable
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ) :=
    clipped_integrable (yoshidaClippedOne a)
  have hstarInt : Integrable (starReflection
      ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)) := by
    have hneg : Integrable (fun x : ℝ ↦
        (yoshidaClippedOne a : YoshidaClippedSmooth a) (-x)) :=
      honeInt.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hneg
  exact (clipped_hasCompactSupport r).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ) hstarInt.locallyIntegrable hrcont

private theorem crossCorrelation_one_residual_even
    {a : ℝ} (r : YoshidaClippedSmooth a)
    (hrEven : Function.Even (r : ℝ → ℂ)) : Function.Even
      (crossCorrelation
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
        (r : ℝ → ℂ)) :=
  crossCorrelation_even_of_real_even
    (yoshidaClippedOne_real a) (periodicCoreOne_even a) hrEven

private theorem crossCorrelation_one_residual_match
    {a u : ℝ} (r : YoshidaClippedSmooth a)
    (hr_real : ∀ x ∈ Icc (-a) a, r x = ((r x).re : ℂ))
    (hrEven : Function.Even (r : ℝ → ℂ))
    (hu : u ∈ Icc (0 : ℝ) (2 * a)) :
    crossCorrelation
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) : ℝ → ℂ)
        (r : ℝ → ℂ) u = (residualEndpointCorrelation r u : ℂ) := by
  rw [crossCorrelation_eq_real_overlap
    (yoshidaClippedOne a) r
    (fun x hx ↦ by
      change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) =
        (((if x ∈ Icc (-a) a then (1 : ℂ) else 0)).re : ℂ)
      rw [if_pos hx]
      simp)
    hr_real hu.1 hu.2]
  have hle : -a ≤ a - u := by linarith [hu.2]
  let q : ℝ → ℝ := fun x ↦ (r x).re
  have hfirst :
      (∫ x : ℝ in -a..a - u,
        ((yoshidaClippedOne a : YoshidaClippedSmooth a) x).re *
          (r (u + x)).re) =
        ∫ x : ℝ in -a..a - u, q (u + x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-a) (a - u) := by
      simpa only [uIcc_of_le hle] using hx
    have hxf : x ∈ Icc (-a) a :=
      ⟨hx'.1, by linarith [hx'.2, hu.1]⟩
    change ((yoshidaClippedOne a : YoshidaClippedSmooth a) x).re *
        (r (u + x)).re = q (u + x)
    rw [show (yoshidaClippedOne a : YoshidaClippedSmooth a) x = 1 by
      change (if x ∈ Icc (-a) a then (1 : ℂ) else 0) = 1
      rw [if_pos hxf]]
    simp [q]
  have hshift :
      (∫ x : ℝ in -a..a - u, q (u + x)) =
        ∫ x : ℝ in -a + u..a, q x := by
    rw [show (fun x : ℝ ↦ q (u + x)) = fun x ↦ q (x + u) by
      funext x
      rw [add_comm]]
    rw [intervalIntegral.integral_comp_add_right]
    congr 1
    all_goals ring
  have hneg :
      (∫ x : ℝ in -a + u..a, q x) =
        ∫ x : ℝ in -a..a - u, q (-x) := by
    rw [intervalIntegral.integral_comp_neg]
    congr 1
    all_goals ring
  have heven :
      (∫ x : ℝ in -a..a - u, q (-x)) =
        ∫ x : ℝ in -a..a - u, q x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [q]
    exact congrArg Complex.re (hrEven x)
  rw [hfirst, hshift, hneg, heven]
  rfl

/-- Structural endpoint-jump archimedean evaluation on the clipped constant.
No mode expansion or weighted second moment is used. -/
theorem normalized_arch_periodicCoreOne_eq_boundaryArch :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand
          yoshidaEndpointA yoshidaEndpointA_pos
          (yoshidaClippedOne yoshidaEndpointA)
          (yoshidaClippedOne yoshidaEndpointA) v =
      (boundaryArchCorrelation (2 * yoshidaEndpointA)
        (constantEndpointCorrelation yoshidaEndpointA) : ℂ) := by
  let one : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaClippedOne yoshidaEndpointA
  let C : ℝ → ℝ := constantEndpointCorrelation yoshidaEndpointA
  let D : ℝ → ℝ := fun _ ↦ -1
  have hA (k : ℕ) :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
            boundarySpectralProduct yoshidaEndpointA_pos one one v =
        (geometricIntegralTerm (2 * yoshidaEndpointA) C k : ℂ) := by
    rw [normalized_bombieriKernel_boundarySpectralProduct
      yoshidaEndpointA_pos one one
      (measurable_yoshidaClippedOne yoshidaEndpointA)
      (measurable_yoshidaClippedOne yoshidaEndpointA)
      (by simpa only [one] using
        continuous_crossCorrelation_one_one yoshidaEndpointA)]
    have hfold := integral_exp_abs_crossCorrelation_eq_geometric
      (clipped_integrable one) (clipped_integrable one)
      (L := 2 * yoshidaEndpointA)
      (b := 2 * (k : ℝ) + 1 / 2)
      (mul_pos (by norm_num) yoshidaEndpointA_pos) (by positivity) C
      (by simpa only [one] using
        crossCorrelation_one_one_even yoshidaEndpointA)
      (fun u hu ↦ by
        simpa only [one] using crossCorrelation_eq_zero_of_two_mul_a_lt
          hu one one)
      (fun u hu ↦ by
        simpa only [one, C] using crossCorrelation_one_one_match hu)
    rw [hfold, geometricIntegralTerm]
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [oddRate]
    push_cast
    rfl
  have hH0 :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, boundarySpectralProduct yoshidaEndpointA_pos one one v =
        (C 0 : ℂ) := by
    rw [normalized_integral_boundarySpectralProduct
      yoshidaEndpointA_pos one one
      (measurable_yoshidaClippedOne yoshidaEndpointA)
      (measurable_yoshidaClippedOne yoshidaEndpointA)
      (by simpa only [one] using
        continuous_crossCorrelation_one_one yoshidaEndpointA)]
    simpa only [one, C] using
      crossCorrelation_one_one_match
        (show (0 : ℝ) ∈ Icc 0 (2 * yoshidaEndpointA) by
          exact ⟨le_rfl,
            (mul_pos (by norm_num) yoshidaEndpointA_pos).le⟩)
  simpa only [one, C] using
    normalized_boundaryCriticalCross_eq_archCorrelation
      yoshidaEndpointA_pos one one (L := 2 * yoshidaEndpointA)
      (mul_pos (by norm_num) yoshidaEndpointA_pos) C D
      (continuous_constantEndpointCorrelation yoshidaEndpointA)
      continuous_const
      (fun u ↦ by simpa only [C, D] using
        constantEndpointCorrelation_removable yoshidaEndpointA u)
      hA hH0

/-- Ordered constant--residual archimedean evaluation for an arbitrary real,
even, globally continuous endpoint-zero residual. -/
theorem normalized_arch_periodicCoreOne_residual_eq_boundaryArch
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ))
    (hr_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      r x = ((r x).re : ℂ))
    (hrEven : Function.Even (r : ℝ → ℂ)) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand
          yoshidaEndpointA yoshidaEndpointA_pos
          (yoshidaClippedOne yoshidaEndpointA) r v =
      (boundaryArchCorrelation (2 * yoshidaEndpointA)
        (residualEndpointCorrelation r) : ℂ) := by
  let one : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaClippedOne yoshidaEndpointA
  let C : ℝ → ℝ := residualEndpointCorrelation r
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_residualEndpointSlope r hrcont
  have hHcont : Continuous
      (crossCorrelation (one : ℝ → ℂ) (r : ℝ → ℂ)) := by
    simpa only [one] using continuous_crossCorrelation_one_residual r hrcont
  have hA (k : ℕ) :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
            boundarySpectralProduct yoshidaEndpointA_pos one r v =
        (geometricIntegralTerm (2 * yoshidaEndpointA) C k : ℂ) := by
    rw [normalized_bombieriKernel_boundarySpectralProduct
      yoshidaEndpointA_pos one r
      (by simpa only [one] using
        measurable_yoshidaClippedOne yoshidaEndpointA)
      hrcont.measurable hHcont]
    have hfold := integral_exp_abs_crossCorrelation_eq_geometric
      (clipped_integrable one) (clipped_integrable r)
      (L := 2 * yoshidaEndpointA)
      (b := 2 * (k : ℝ) + 1 / 2)
      (mul_pos (by norm_num) yoshidaEndpointA_pos) (by positivity) C
      (by simpa only [one] using
        crossCorrelation_one_residual_even r hrEven)
      (fun u hu ↦ crossCorrelation_eq_zero_of_two_mul_a_lt hu one r)
      (fun u hu ↦ by
        simpa only [one, C] using
          crossCorrelation_one_residual_match r hr_real hrEven hu)
    rw [hfold, geometricIntegralTerm]
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [oddRate]
    push_cast
    rfl
  have hH0 :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, boundarySpectralProduct yoshidaEndpointA_pos one r v =
        (C 0 : ℂ) := by
    rw [normalized_integral_boundarySpectralProduct
      yoshidaEndpointA_pos one r
      (by simpa only [one] using
        measurable_yoshidaClippedOne yoshidaEndpointA)
      hrcont.measurable hHcont]
    simpa only [one, C] using
      crossCorrelation_one_residual_match r hr_real hrEven
        (show (0 : ℝ) ∈ Icc 0 (2 * yoshidaEndpointA) by
          exact ⟨le_rfl,
            (mul_pos (by norm_num) yoshidaEndpointA_pos).le⟩)
  simpa only [one, C] using
    normalized_boundaryCriticalCross_eq_archCorrelation
      yoshidaEndpointA_pos one r (L := 2 * yoshidaEndpointA)
      (mul_pos (by norm_num) yoshidaEndpointA_pos) C D
      (continuous_residualEndpointCorrelation r hrcont) hD hrem hA hH0

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
