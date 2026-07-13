import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaClippedEnergyStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRealQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRegularScaling
import ArithmeticHodge.Analysis.YoshidaPointwiseOddPeriodicCore
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate Convolution FourierTransform
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge

open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaDigammaDistribution
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointRegularCorrelation
open YoshidaEndpointScaledCorrelation
open YoshidaRegularKernelBound
open YoshidaPointwiseOddPeriodicCore
open YoshidaRenormalizedGeometricKernel
open YoshidaSectionSixAnalytic
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability

noncomputable section

private theorem exists_continuous_removable_slope
    (C : ℝ → ℝ) (hC : ContDiff ℝ 1 C) :
    ∃ D : ℝ → ℝ, Continuous D ∧
      ∀ u : ℝ, C u = C 0 + u * D u := by
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
  · rw [show D u = Q u by
      simp [D, hu]]
    dsimp only [Q]
    field_simp [hu]
    ring

private def clippedDerivative
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a :=
  ⟨fun x ↦ if x ∈ Icc (-a) a then yoshidaClippedDeriv a f x else 0, by
    constructor
    · have hderiv : ContDiffOn ℝ ∞ (yoshidaClippedDeriv a f)
          (Icc (-a) a) := by
        exact f.property.1.derivWithin
          (uniqueDiffOn_Icc (by linarith)) (by simp)
      exact hderiv.congr fun x hx ↦ by simp [hx]
    · intro x hx
      change (if x ∈ Icc (-a) a then yoshidaClippedDeriv a f x else 0) = 0
      rw [if_neg hx]⟩

@[simp] private theorem clippedDerivative_apply_of_mem
    {a x : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hx : x ∈ Icc (-a) a) :
    clippedDerivative ha f x = yoshidaClippedDeriv a f x := by
  change (if x ∈ Icc (-a) a then yoshidaClippedDeriv a f x else 0) = _
  rw [if_pos hx]

private theorem continuous_clipped_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hneg : f (-a) = 0) (hpos : f a = 0) :
    Continuous (f : ℝ → ℂ) := by
  let S : Set ℝ := Icc (-a) a
  have hfront : ∀ x ∈ frontier S, (f : ℝ → ℂ) x = 0 := by
    intro x hx
    have hx' : x ∈ ({-a, a} : Set ℝ) := by
      simpa only [S, frontier_Icc (by linarith : -a ≤ a)] using hx
    rcases hx' with (rfl | rfl)
    · exact hneg
    · exact hpos
  have hpiece : Continuous (S.piecewise (f : ℝ → ℂ) 0) := by
    apply continuous_piecewise hfront
    · simpa only [S, isClosed_Icc.closure_eq] using
        f.property.1.continuousOn
    · exact continuousOn_const
  have heq : (f : ℝ → ℂ) = S.piecewise (f : ℝ → ℂ) 0 := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.piecewise, hx]
    · rw [yoshidaClippedSmooth_eq_zero_outside f (by simpa only [S] using hx)]
      simp [Set.piecewise, hx]
  rw [heq]
  exact hpiece

private theorem hasCompactSupport_clipped
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    HasCompactSupport (f : ℝ → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (yoshidaClippedSmooth_eq_zero_outside f hmem)

private theorem integrable_clipped
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    Integrable (f : ℝ → ℂ) :=
  f.property.1.continuousOn.integrableOn_Icc
    |>.integrable_of_forall_notMem_eq_zero
      (fun _ hx ↦ yoshidaClippedSmooth_eq_zero_outside f hx)

private theorem criticalSample_norm_le_inv_sq_of_endpoints_zero
    {a v : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hneg : f (-a) = 0) (hpos : f a = 0) (hv : v ≠ 0) :
    ‖yoshidaCriticalSampleLinear a ha v f‖ ≤
      yoshidaCriticalDecayConstant a (clippedDerivative ha f) / |v| ^ 2 := by
  have habs : 0 < |v| := abs_pos.mpr hv
  have hformula :=
    yoshidaCriticalSample_mul_neg_mul_I_eq_boundary_sub_derivIntegral
      ha v f
  rw [hneg, hpos] at hformula
  simp only [zero_mul, neg_zero, zero_sub] at hformula
  have hderivSample :
      (∫ x : ℝ in -a..a,
          yoshidaClippedDeriv a f x *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))) =
        yoshidaCriticalSampleLinear a ha v (clippedDerivative ha f) := by
    rw [yoshidaCriticalSampleLinear, yoshidaCenteredLaplaceLinear_apply]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-a) a := by
      simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx
    change yoshidaClippedDeriv a f x * _ =
      _ * (if x ∈ Icc (-a) a then yoshidaClippedDeriv a f x else 0)
    rw [if_pos hx']
    ring
  rw [hderivSample] at hformula
  have hnorm := congrArg norm hformula
  have hleft :
      ‖yoshidaCriticalSampleLinear a ha v f * (-((v : ℂ) * Complex.I))‖ =
        ‖yoshidaCriticalSampleLinear a ha v f‖ * |v| := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_I, mul_one]
  rw [hleft, norm_neg] at hnorm
  have hfirst := yoshidaCriticalSample_norm_le_inv_abs ha v hv
    (clippedDerivative ha f)
  apply (le_div_iff₀ (sq_pos_of_pos habs)).2
  calc
    ‖yoshidaCriticalSampleLinear a ha v f‖ * |v| ^ 2 =
        (‖yoshidaCriticalSampleLinear a ha v f‖ * |v|) * |v| := by ring
    _ = ‖yoshidaCriticalSampleLinear a ha v (clippedDerivative ha f)‖ *
        |v| := by rw [hnorm]
    _ ≤ (yoshidaCriticalDecayConstant a (clippedDerivative ha f) / |v|) *
        |v| := mul_le_mul_of_nonneg_right hfirst habs.le
    _ = yoshidaCriticalDecayConstant a (clippedDerivative ha f) := by
      field_simp [habs.ne']

private theorem integrable_weighted_normSq_criticalSample_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hneg : f (-a) = 0) (hpos : f a = 0) :
    Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
  let D : ℝ := yoshidaCriticalDecayConstant a (clippedDerivative ha f)
  let K : ℝ := 4 * D ^ 2
  let q : ℝ → ℝ := fun v ↦ (1 + v ^ 2)⁻¹
  let S : Set ℝ := Icc (-1 : ℝ) 1
  have hD : 0 ≤ D := yoshidaCriticalDecayConstant_nonneg ha _
  have hcont : Continuous (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
    exact (continuous_const.add (continuous_id.pow 2)).mul
      (Complex.continuous_normSq.comp (continuous_yoshidaCriticalSample ha f))
  have hcompact : IntegrableOn (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) S :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_inv_one_add_sq
  have hmajor : Integrable (fun v ↦ K * q v) := hq.const_mul K
  have htail : IntegrableOn (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have habs : 1 < |v| := by
        by_contra h
        apply hv
        exact abs_le.mp (le_of_not_gt h)
      have hv0 : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
      have hs := criticalSample_norm_le_inv_sq_of_endpoints_zero
        ha f hneg hpos hv0
      have hsSq :
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            D ^ 2 / v ^ 4 := by
        rw [Complex.normSq_eq_norm_sq]
        have hright : 0 ≤ D / |v| ^ 2 := div_nonneg hD (sq_nonneg _)
        have hsq := sq_le_sq₀ (norm_nonneg _) hright |>.2 hs
        calc
          ‖yoshidaCriticalSampleLinear a ha v f‖ ^ 2 ≤
              (yoshidaCriticalDecayConstant a (clippedDerivative ha f) /
                |v| ^ 2) ^ 2 := hsq
          _ = D ^ 2 / v ^ 4 := by
            dsimp only [D]
            rw [div_pow, show (|v| ^ 2) ^ 2 = v ^ 4 by
              rw [sq_abs]
              ring]
      have hvSq : 1 < v ^ 2 := by
        rw [← sq_abs]
        nlinarith
      have hweighted :
          (1 + v ^ 2) *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            K * q v := by
        calc
          (1 + v ^ 2) *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
              (1 + v ^ 2) * (D ^ 2 / v ^ 4) :=
            mul_le_mul_of_nonneg_left hsSq (by positivity)
          _ ≤ K * q v := by
            dsimp only [K, q]
            have hv2 : 0 < v ^ 2 := lt_trans (by norm_num) hvSq
            have hone : 0 < 1 + v ^ 2 := by positivity
            rw [inv_eq_one_div]
            rw [show 4 * D ^ 2 * (1 / (1 + v ^ 2)) =
              (4 * D ^ 2) / (1 + v ^ 2) by ring]
            apply (le_div_iff₀ hone).2
            have hv4 : 0 < v ^ 4 := by positivity
            have hpoly : (1 + v ^ 2) ^ 2 ≤ 4 * v ^ 4 := by
              nlinarith [sq_nonneg (v ^ 2 - 1)]
            calc
              (1 + v ^ 2) * (D ^ 2 / v ^ 4) * (1 + v ^ 2) =
                  (1 + v ^ 2) ^ 2 * D ^ 2 / v ^ 4 := by ring
              _ ≤ (4 * v ^ 4) * D ^ 2 / v ^ 4 := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hpoly (sq_nonneg D)) hv4.le
              _ = 4 * D ^ 2 := by field_simp [hv0]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (Complex.normSq_nonneg _))]
      exact hweighted
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

private theorem contDiff_one_re_crossCorrelation
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hfcont : Continuous (f : ℝ → ℂ))
    (hweighted : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f))) :
    ContDiff ℝ 1
      (fun u : ℝ ↦ (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re) := by
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  let c : ℝ := 2 * Real.pi
  let M : ℝ → ℂ := fun w ↦
    (Complex.normSq (FourierTransform.fourier g w) : ℂ)
  let H : ℝ → ℂ := crossCorrelation g g
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hcSq : 1 ≤ c ^ 2 := by
    dsimp only [c]
    nlinarith [Real.pi_gt_three]
  have hgInt : Integrable g := by
    simpa only [g] using integrable_clipped f
  have hgCompact : HasCompactSupport g := by
    simpa only [g] using hasCompactSupport_clipped f
  have hstarInt : Integrable (starReflection g) := by
    have hneg : Integrable (fun x : ℝ ↦ g (-x)) := hgInt.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg
  have hHInt : Integrable H := by
    exact hstarInt.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hgInt
  have hHCont : Continuous H := by
    exact hgCompact.continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ) hstarInt.locallyIntegrable
      (by simpa only [g] using hfcont)
  have hFourierSq : Integrable (fun w : ℝ ↦
      Complex.normSq (FourierTransform.fourier g w)) := by
    have hscaled :=
      (integrable_normSq_yoshidaCriticalSample ha f).comp_mul_left'
        (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    dsimp only [g]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w) f, harg]
  have hMInt : Integrable M := by
    simpa only [M] using hFourierSq.ofReal
  have hscaledWeighted : Integrable (fun w : ℝ ↦
      (1 + (c * w) ^ 2) *
        Complex.normSq (FourierTransform.fourier g w)) := by
    have hscaled := hweighted.comp_mul_left' (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    dsimp only [g]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w) f, harg]
  have hweightedFourier : Integrable (fun w : ℝ ↦
      (1 + w ^ 2) *
        Complex.normSq (FourierTransform.fourier g w)) := by
    apply hscaledWeighted.mono'
    · exact ((continuous_const.add (continuous_id.pow 2)).mul
        (Complex.continuous_normSq.comp
          (VectorFourier.fourierIntegral_continuous
            Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgInt)))
          |>.aestronglyMeasurable
    · filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (Complex.normSq_nonneg _))]
      have hweight : 1 + w ^ 2 ≤ 1 + (c * w) ^ 2 := by
        nlinarith [sq_nonneg w,
          mul_le_mul_of_nonneg_right hcSq (sq_nonneg w)]
      exact mul_le_mul_of_nonneg_right hweight (Complex.normSq_nonneg _)
  have hFT (w : ℝ) : FourierTransform.fourier H w = M w := by
    dsimp only [H, M]
    rw [fourier_crossCorrelation hgInt hgInt
      (by simpa only [g] using hfcont) (by simpa only [g] using hfcont)]
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self
        (z := FourierTransform.fourier g w)).symm
  have hFTHInt : Integrable (FourierTransform.fourier H) := by
    exact hMInt.congr (by filter_upwards [] with w; exact (hFT w).symm)
  have hinversion (u : ℝ) : FourierTransform.fourierInv M u = H u := by
    have h : FourierTransform.fourierInv (FourierTransform.fourier H) u = H u :=
      hHInt.fourierInv_fourier_eq hFTHInt hHCont.continuousAt
    rw [show FourierTransform.fourier H = M by funext w; exact hFT w] at h
    exact h
  have hMCont : Continuous M := by
    exact Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp
        (VectorFourier.fourierIntegral_continuous
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgInt))
  have hfourier : ContDiff ℝ 1 (FourierTransform.fourier M) := by
    apply Real.contDiff_fourier
    intro n hn
    have hnNat : n ≤ 1 := by exact_mod_cast hn
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hnNat) with rfl | rfl
    · simpa only [pow_zero, one_mul] using hMInt.norm
    · apply hweightedFourier.mono'
      · exact ((continuous_norm.pow 1).mul
          (continuous_norm.comp hMCont))
          |>.aestronglyMeasurable
      · filter_upwards [] with w
        simp only [pow_one, M, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Complex.normSq_nonneg _)]
        rw [abs_of_nonneg
          (mul_nonneg (abs_nonneg _) (Complex.normSq_nonneg _))]
        exact mul_le_mul_of_nonneg_right
          (by
            have habssq : |w| ^ 2 = w ^ 2 := sq_abs w
            nlinarith [sq_nonneg (|w| - 1)])
          (Complex.normSq_nonneg _)
  have hcomp : ContDiff ℝ 1
      (fun u : ℝ ↦ FourierTransform.fourier M (-u)) := by
    exact hfourier.comp (by fun_prop)
  have hre : ContDiff ℝ 1
      (fun u : ℝ ↦ (FourierTransform.fourier M (-u)).re) := by
    exact (Complex.reCLM.contDiff (n := (1 : WithTop ℕ∞))).comp hcomp
  have heq :
      (fun u : ℝ ↦
        (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re) =
      (fun u : ℝ ↦ (FourierTransform.fourier M (-u)).re) := by
    funext u
    rw [← Real.fourierInv_eq_fourier_neg M u, hinversion]
  rw [heq]
  exact hre

private theorem crossCorrelation_self_neg
    (g : ℝ → ℂ) (u : ℝ) :
    crossCorrelation g g (-u) = star (crossCorrelation g g u) := by
  rw [crossCorrelation_apply, crossCorrelation_apply]
  let G : ℝ → ℂ := fun y ↦ star (g (y + u)) * g y
  calc
    (∫ x : ℝ, star (g x) * g (-u + x)) =
        ∫ x : ℝ, G (x + (-u)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      congr 2 <;> ring_nf
    _ = ∫ y : ℝ, G y := MeasureTheory.integral_add_right_eq_self G (-u)
    _ = ∫ y : ℝ, star (star (g y) * g (u + y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [G]
      change conj (g (y + u)) * g y =
        conj (conj (g y) * g (u + y))
      rw [map_mul, conj_conj, add_comm y u, mul_comm]
    _ = star (∫ y : ℝ, star (g y) * g (u + y)) := by
      simpa only [RCLike.star_def] using
        (integral_conj (f := fun y : ℝ ↦ star (g y) * g (u + y)))

private theorem re_crossCorrelation_self_even (g : ℝ → ℂ) :
    Function.Even (fun u : ℝ ↦ (crossCorrelation g g u).re) := by
  intro u
  change (crossCorrelation g g (-u)).re = (crossCorrelation g g u).re
  rw [crossCorrelation_self_neg]
  simp

private theorem crossCorrelation_eq_zero_of_two_mul_a_lt
    {a u : ℝ} (hu : 2 * a < u) (f : YoshidaClippedSmooth a) :
    crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u = 0 := by
  rw [crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-a) a
  · have hux : u + x ∉ Icc (-a) a := by
      intro hmem
      linarith [hx.1, hmem.2]
    rw [yoshidaClippedSmooth_eq_zero_outside f hux, mul_zero]
    simp
  · rw [yoshidaClippedSmooth_eq_zero_outside f hx, star_zero, zero_mul]
    simp

private theorem re_crossCorrelation_eq_realEndpointCorrelation
    {a u : ℝ} (f : YoshidaClippedSmooth a)
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (hu0 : 0 ≤ u) (huL : u ≤ 2 * a) :
    (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re =
      realEndpointCorrelation a (fun x ↦ (f x).re) u := by
  rw [crossCorrelation_apply]
  have hle : -a ≤ a - u := by linarith
  have hsupport :
      (∫ x : ℝ, star (f x) * f (u + x)) =
        ∫ x : ℝ in -a..a - u, star (f x) * f (u + x) := by
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
        rw [yoshidaClippedSmooth_eq_zero_outside f hux, mul_zero]
      · rw [yoshidaClippedSmooth_eq_zero_outside f hxf,
          star_zero, zero_mul])).symm
  rw [hsupport]
  have hrealIntegral :
      (∫ x : ℝ in -a..a - u, star (f x) * f (u + x)) =
        ((∫ x : ℝ in -a..a - u,
          (f (u + x)).re * (f x).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-a) (a - u) := by
      simpa only [uIcc_of_le hle] using hx
    have hxf : x ∈ Icc (-a) a := ⟨hx'.1, by linarith [hx'.2, hu0]⟩
    have hux : u + x ∈ Icc (-a) a := by
      constructor <;> linarith [hx'.1, hx'.2, hu0]
    change star (f x) * f (u + x) =
      (((f (u + x)).re * (f x).re : ℝ) : ℂ)
    rw [hf_real x hxf, hf_real (u + x) hux]
    simp
    ring
  rw [hrealIntegral]
  unfold realEndpointCorrelation
  rfl

private theorem integral_exp_re_crossCorrelation_eq_physical
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : YoshidaClippedSmooth a)
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ)) :
    (∫ u : ℝ, Real.exp (-b * |u|) *
        (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re) =
      2 * ∫ u : ℝ in 0..2 * a,
        Real.exp (-b * u) *
          realEndpointCorrelation a (fun x ↦ (f x).re) u := by
  let C : ℝ → ℝ := fun u ↦
    (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re
  let W : ℝ → ℝ := fun u ↦ Real.exp (-b * |u|) * C u
  have hfInt : Integrable (f : ℝ → ℂ) := integrable_clipped f
  have hstarInt : Integrable (starReflection (f : ℝ → ℂ)) := by
    have hneg : Integrable (fun x : ℝ ↦ f (-x)) := hfInt.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg
  have hCInt : Integrable C := by
    have hcorr := hstarInt.integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) hfInt
    simpa only [C] using hcorr.re
  have hWInt : Integrable W := by
    have hweight : Continuous (fun u : ℝ ↦ Real.exp (-b * |u|)) := by
      fun_prop
    have hbounded : ∀ u : ℝ, ‖Real.exp (-b * |u|)‖ ≤ 1 := by
      intro u
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg u))
    have h := hCInt.bdd_mul hweight.aestronglyMeasurable
      (Filter.Eventually.of_forall hbounded)
    apply h.congr
    filter_upwards [] with u
    dsimp only [W, C]
  have hWeven : Function.Even W := by
    intro u
    dsimp only [W, C]
    change Real.exp (-b * |-u|) *
        (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) (-u)).re =
      Real.exp (-b * |u|) *
        (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u).re
    rw [crossCorrelation_self_neg]
    rw [abs_neg]
    change Real.exp (-b * |u|) *
        (conj (crossCorrelation (f : ℝ → ℂ) (f : ℝ → ℂ) u)).re = _
    rw [conj_re]
  have hleft : (∫ u : ℝ in Iic 0, W u) = ∫ u : ℝ in Ioi 0, W u := by
    calc
      (∫ u : ℝ in Iic 0, W u) = ∫ u : ℝ in Iic 0, W (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (hWeven u).symm
      _ = ∫ u : ℝ in Ioi 0, W u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 W
  have hwhole : (∫ u : ℝ, W u) = 2 * ∫ u : ℝ in Ioi 0, W u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
      hWInt.integrableOn hWInt.integrableOn, hleft]
    ring
  have hpositive : (∫ u : ℝ in Ioi 0, W u) =
      ∫ u : ℝ in 0..2 * a,
        Real.exp (-b * u) *
          realEndpointCorrelation a (fun x ↦ (f x).re) u := by
    rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * a)]
    calc
      (∫ u : ℝ in Ioi 0, W u) = ∫ u : ℝ in Ioc 0 (2 * a), W u := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
          Ioc_subset_Ioi_self
        intro u hu
        have huL : 2 * a < u := by
          exact lt_of_not_ge (fun hle ↦ hu.2 ⟨hu.1, hle⟩)
        dsimp only [W, C]
        rw [crossCorrelation_eq_zero_of_two_mul_a_lt huL f]
        simp
      _ = ∫ u : ℝ in Ioc 0 (2 * a),
          Real.exp (-b * u) *
            realEndpointCorrelation a (fun x ↦ (f x).re) u := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        dsimp only [W, C]
        rw [abs_of_pos hu.1,
          re_crossCorrelation_eq_realEndpointCorrelation f hf_real
            hu.1.le hu.2]
  dsimp only [W] at hwhole
  rw [hwhole, hpositive]

private theorem normalized_cauchy_normSq_eq_geometricIntegralTerm
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hfcont : Continuous (f : ℝ → ℂ))
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (k : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
          (Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℂ)) =
      (geometricIntegralTerm (2 * a)
        (realEndpointCorrelation a (fun x ↦ (f x).re)) k : ℂ) := by
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  let b : ℝ := oddRate k
  let c : ℝ := 2 * Real.pi
  have hb : 0 < b := oddRate_pos k
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hgInt : Integrable g := by
    simpa only [g] using integrable_clipped f
  have hgCompact : HasCompactSupport g := by
    simpa only [g] using hasCompactSupport_clipped f
  have hFourierSq : Integrable (fun w : ℝ ↦
      Complex.normSq (FourierTransform.fourier g w)) := by
    have hscaled :=
      (integrable_normSq_yoshidaCriticalSample ha f).comp_mul_left'
        (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    dsimp only [g]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w) f, harg]
  have hprod : Integrable (fun w : ℝ ↦
      star (FourierTransform.fourier g w) *
        FourierTransform.fourier g w) := by
    have hcomplex : Integrable (fun w : ℝ ↦
        (Complex.normSq (FourierTransform.fourier g w) : ℂ)) :=
      hFourierSq.ofReal
    apply hcomplex.congr
    filter_upwards [] with w
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self
        (z := FourierTransform.fourier g w))
  have hcauchy := angular_cauchy_crossCorrelation_pairing
    hgInt hgInt (by simpa only [g] using hfcont)
      (by simpa only [g] using hfcont) hgCompact hprod b hb
  have hkernel (v : ℝ) :
      (bombieriDigammaKernel k v : ℂ) =
        (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    unfold bombieriDigammaKernel
    dsimp only [b, oddRate]
    push_cast
    ring
  have hspectral :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
            (Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℂ)) =
        ∫ u : ℝ, (Real.exp (-b * |u|) : ℝ) *
          crossCorrelation g g u := by
    calc
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              (star (angularFourier g v) * angularFourier g v)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with v
        rw [hkernel]
        have hs : yoshidaCriticalSampleLinear a ha v f =
            angularFourier g v := by
          exact yoshidaCriticalSample_eq_fourier ha v f
        rw [hs]
        rw [Complex.normSq_eq_conj_mul_self]
        simp only [starRingEnd_apply]
      _ = _ := hcauchy
  have hglobalReal (x : ℝ) : f x = ((f x).re : ℂ) := by
    by_cases hx : x ∈ Icc (-a) a
    · exact hf_real x hx
    · rw [yoshidaClippedSmooth_eq_zero_outside f hx]
      simp
  have hcorrReal (u : ℝ) :
      crossCorrelation g g u =
        (((crossCorrelation g g u).re : ℝ) : ℂ) := by
    let R : ℝ := ∫ x : ℝ, (f x).re * (f (u + x)).re
    have hval : crossCorrelation g g u = (R : ℂ) := by
      rw [crossCorrelation_apply]
      calc
        (∫ x : ℝ, star (g x) * g (u + x)) =
            ∫ x : ℝ, (((f x).re * (f (u + x)).re : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp only [g]
          rw [hglobalReal x, hglobalReal (u + x)]
          simp
        _ = (R : ℂ) := by
          exact integral_complex_ofReal
    rw [hval]
    simp
  rw [hspectral]
  calc
    (∫ u : ℝ, (Real.exp (-b * |u|) : ℝ) * crossCorrelation g g u) =
        ∫ u : ℝ,
          (((Real.exp (-b * |u|) * (crossCorrelation g g u).re : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hcorrReal]
      push_cast
      rfl
    _ = (((∫ u : ℝ,
          Real.exp (-b * |u|) * (crossCorrelation g g u).re) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = ((2 * ∫ u : ℝ in 0..2 * a,
        Real.exp (-b * u) *
          realEndpointCorrelation a (fun x ↦ (f x).re) u : ℝ) : ℂ) := by
      rw [integral_exp_re_crossCorrelation_eq_physical ha hb f hf_real]
    _ = (geometricIntegralTerm (2 * a)
        (realEndpointCorrelation a (fun x ↦ (f x).re)) k : ℂ) := by
      rfl

private theorem normalized_integral_normSq_eq_correlation_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hfcont : Continuous (f : ℝ → ℂ))
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ)) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℂ)) =
      (realEndpointCorrelation a (fun x ↦ (f x).re) 0 : ℂ) := by
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  let c : ℝ := 2 * Real.pi
  let q : ℝ → ℂ := fun v ↦
    (Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℂ)
  let H : ℝ → ℂ := crossCorrelation g g
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hgInt : Integrable g := by
    simpa only [g] using integrable_clipped f
  have hgCompact : HasCompactSupport g := by
    simpa only [g] using hasCompactSupport_clipped f
  have hstarInt : Integrable (starReflection g) := by
    have hneg : Integrable (fun x : ℝ ↦ g (-x)) := hgInt.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg
  have hHInt : Integrable H := by
    exact hstarInt.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hgInt
  have hHCont : Continuous H := by
    exact hgCompact.continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ) hstarInt.locallyIntegrable
      (by simpa only [g] using hfcont)
  have hFourierSq : Integrable (fun w : ℝ ↦
      Complex.normSq (FourierTransform.fourier g w)) := by
    have hscaled :=
      (integrable_normSq_yoshidaCriticalSample ha f).comp_mul_left'
        (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    dsimp only [g]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w) f, harg]
  have hprod : Integrable (fun w : ℝ ↦
      star (FourierTransform.fourier g w) *
        FourierTransform.fourier g w) := by
    have hcomplex : Integrable (fun w : ℝ ↦
        (Complex.normSq (FourierTransform.fourier g w) : ℂ)) :=
      hFourierSq.ofReal
    apply hcomplex.congr
    filter_upwards [] with w
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self
        (z := FourierTransform.fourier g w))
  have hFTHInt : Integrable (FourierTransform.fourier H) := by
    apply hprod.congr
    filter_upwards [] with w
    exact (fourier_crossCorrelation hgInt hgInt
      (by simpa only [g] using hfcont) (by simpa only [g] using hfcont) w).symm
  have hzero : (∫ w : ℝ, FourierTransform.fourier H w) = H 0 := by
    have hinv : FourierTransform.fourierInv
        (FourierTransform.fourier H) 0 = H 0 :=
      hHInt.fourierInv_fourier_eq hFTHInt hHCont.continuousAt
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  have hPlancherel :
      (∫ w : ℝ,
          (Complex.normSq (FourierTransform.fourier g w) : ℂ)) = H 0 := by
    calc
      _ = ∫ w : ℝ,
          star (FourierTransform.fourier g w) *
            FourierTransform.fourier g w := by
        apply integral_congr_ae
        filter_upwards [] with w
        simpa only [starRingEnd_apply] using
          (Complex.normSq_eq_conj_mul_self
            (z := FourierTransform.fourier g w))
      _ = ∫ w : ℝ, FourierTransform.fourier H w := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact (fourier_crossCorrelation hgInt hgInt
          (by simpa only [g] using hfcont) (by simpa only [g] using hfcont) w).symm
      _ = H 0 := hzero
  have hglobalReal (x : ℝ) : f x = ((f x).re : ℂ) := by
    by_cases hx : x ∈ Icc (-a) a
    · exact hf_real x hx
    · rw [yoshidaClippedSmooth_eq_zero_outside f hx]
      simp
  have hHzero : H 0 =
      (realEndpointCorrelation a (fun x ↦ (f x).re) 0 : ℂ) := by
    dsimp only [H]
    rw [crossCorrelation_apply]
    unfold realEndpointCorrelation
    simp only [zero_add, sub_zero]
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
      ← integral_Icc_eq_integral_Ioc]
    calc
      (∫ x : ℝ, star (g x) * g x) =
          ∫ x : ℝ in Icc (-a) a, star (g x) * g x := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        dsimp only [g]
        rw [yoshidaClippedSmooth_eq_zero_outside f hx, star_zero, zero_mul]
      _ = ∫ x : ℝ in Icc (-a) a,
          (((f x).re ^ 2 : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only [g]
        rw [hglobalReal x]
        simp
        ring
      _ = ((∫ x : ℝ in Icc (-a) a, (f x).re ^ 2 : ℝ) : ℂ) :=
        integral_complex_ofReal
      _ = ((∫ x : ℝ in Icc (-a) a,
          (f x).re * (f x).re : ℝ) : ℂ) := by
        simp only [pow_two]
  have hscale := Measure.integral_comp_mul_left q c
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ,
        (Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℂ)) =
        |c⁻¹| • ∫ v : ℝ, q v := by
      rw [Complex.real_smul]
      rw [abs_of_pos (inv_pos.mpr (by dsimp only [c]; positivity))]
      dsimp only [c, q]
      rw [one_div]
    _ = ∫ w : ℝ, q (c * w) := hscale.symm
    _ = ∫ w : ℝ,
        (Complex.normSq (FourierTransform.fourier g w) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with w
      have harg : c * w / (2 * Real.pi) = w := by
        dsimp only [c]
        field_simp [Real.pi_ne_zero]
      dsimp only [q, g]
      rw [yoshidaCriticalSample_eq_fourier ha (c * w) f, harg]
    _ = H 0 := hPlancherel
    _ = _ := hHzero

private theorem neg_oddKernel_eq_defect_sub_regular
    (C0 : ℝ) (C : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    -oddKernel u * C u + C0 / u =
      (C0 - C u) / u - 2 * yoshidaRegularKernel u * C u := by
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    have : u = -u := Real.exp_injective heq
    apply hu
    linarith
  rw [oddKernel, yoshidaRegularKernel, if_neg hu, Real.sinh_eq]
  field_simp [hu, hden]
  ring

private theorem intervalIntegrable_physical_defect_and_regular
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hfcont : Continuous (f : ℝ → ℂ))
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (hweighted : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f))) :
    (let P := realEndpointCorrelation a (fun x ↦ (f x).re)
    IntervalIntegrable (fun u ↦ (P 0 - P u) / u) volume 0 (2 * a) ∧
      IntervalIntegrable
        (fun u ↦ yoshidaRegularKernel u * P u) volume 0 (2 * a)) := by
  dsimp only
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  let C : ℝ → ℝ := fun u ↦ (crossCorrelation g g u).re
  let P : ℝ → ℝ := realEndpointCorrelation a (fun x ↦ (f x).re)
  have hL : 0 < 2 * a := by positivity
  have hCdiff : ContDiff ℝ 1 C := by
    simpa only [C, g] using
      contDiff_one_re_crossCorrelation ha f hfcont hweighted
  obtain ⟨D, hD, hrem⟩ := exists_continuous_removable_slope C hCdiff
  have hCP {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ 2 * a) : C u = P u := by
    dsimp only [C, P, g]
    exact re_crossCorrelation_eq_realEndpointCorrelation
      f hf_real hu0 huL
  have hdefect : IntervalIntegrable
      (fun u ↦ (P 0 - P u) / u) volume 0 (2 * a) := by
    apply (hD.neg.intervalIntegrable 0 (2 * a)).congr
    intro u hu
    rw [uIoc_of_le hL.le] at hu
    change -D u = (P 0 - P u) / u
    rw [← hCP (u := 0) le_rfl hL.le,
      ← hCP (u := u) hu.1.le hu.2, hrem u]
    field_simp [hu.1.ne']
    ring
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand (C 0) C) volume 0 (2 * a) := by
    exact stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (C 0) (2 * a) hrem
  have hcombinedC : IntervalIntegrable
      (fun u ↦ -oddKernel u * C u + C 0 / u) volume 0 (2 * a) := by
    apply hstable.neg.congr
    intro u _hu
    change -(oddKernel u * C u - C 0 / u) =
      -oddKernel u * C u + C 0 / u
    ring
  have hcombinedP : IntervalIntegrable
      (fun u ↦ (P 0 - P u) / u -
        2 * yoshidaRegularKernel u * P u) volume 0 (2 * a) := by
    apply hcombinedC.congr
    intro u hu
    rw [uIoc_of_le hL.le] at hu
    change -oddKernel u * C u + C 0 / u =
      (P 0 - P u) / u - 2 * yoshidaRegularKernel u * P u
    rw [hCP (u := u) hu.1.le hu.2, hCP (u := 0) le_rfl hL.le]
    exact neg_oddKernel_eq_defect_sub_regular (P 0) P hu.1.ne'
  have htwice : IntervalIntegrable
      (fun u ↦ 2 * yoshidaRegularKernel u * P u) volume 0 (2 * a) := by
    apply (hdefect.sub hcombinedP).congr
    intro u _hu
    ring
  have hregular : IntervalIntegrable
      (fun u ↦ yoshidaRegularKernel u * P u) volume 0 (2 * a) := by
    apply (htwice.const_mul (1 / 2 : ℝ)).congr
    intro u _hu
    ring
  exact ⟨hdefect, hregular⟩

private theorem digammaGeometricValue_eq_endpointClippedArchCorrelation
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hfcont : Continuous (f : ℝ → ℂ))
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (hweighted : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f))) :
    (let P := realEndpointCorrelation a (fun x ↦ (f x).re);
    Summable (fun k : ℕ ↦
      geometricIntegralTerm (2 * a) P (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * P 0)) ∧
    (-(geometricIntegralTerm (2 * a) P 0 +
        Real.eulerMascheroniConstant * P 0 +
        ∑' k : ℕ, (geometricIntegralTerm (2 * a) P (k + 1) -
          (((k + 1 : ℕ) : ℝ)⁻¹ * P 0))) -
      Real.log Real.pi * P 0 =
    (∫ u : ℝ in 0..2 * a,
        (P 0 - P u) / u - 2 * yoshidaRegularKernel u * P u) -
      (Real.log (2 * a) + Real.eulerMascheroniConstant +
        Real.log 2 + Real.log Real.pi) * P 0)) := by
  dsimp only
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  let C : ℝ → ℝ := fun u ↦ (crossCorrelation g g u).re
  let C0 : ℝ := C 0
  let P : ℝ → ℝ := realEndpointCorrelation a (fun x ↦ (f x).re)
  have hL : 0 < 2 * a := by positivity
  have hCdiff : ContDiff ℝ 1 C := by
    simpa only [C, g] using
      contDiff_one_re_crossCorrelation ha f hfcont hweighted
  obtain ⟨D, hD, hrem⟩ := exists_continuous_removable_slope C hCdiff
  have hinterchange : PairedIntegralInterchange (2 * a) C0 C := by
    apply pairedIntegralInterchange_of_removable hL hCdiff.continuous
    · intro u _hu
      simpa only [C0] using hrem u
    · exact removableMajorantLimit_intervalIntegrable hD C0 (2 * a)
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand C0 C) volume 0 (2 * a) := by
    exact stableGeometricIntegrand_intervalIntegrable_of_removable
      hD C0 (2 * a) (by intro u; simpa only [C0] using hrem u)
  have href : IntervalIntegrable referenceRegularized volume 0 (2 * a) :=
    referenceRegularized_intervalIntegrable (2 * a)
  have hren : HasSum (renormalizedTerm (2 * a) C0 C)
      ((∫ u : ℝ in 0..2 * a, stableGeometricIntegrand C0 C u) +
        (Real.log (2 * a) + Real.log 2) * C0) :=
    renormalizedSeries_hasSum_stable hL hCdiff.continuous
      hinterchange hstable href
  have hindex :
      geometricIntegralTerm (2 * a) C 0 +
          ∑' k : ℕ, (geometricIntegralTerm (2 * a) C (k + 1) -
            C0 / (k + 1 : ℕ)) =
        ∑' k : ℕ, renormalizedTerm (2 * a) C0 C k := by
    calc
      _ = (∫ u : ℝ in 0..2 * a, stableGeometricIntegrand C0 C u) +
          (Real.log (2 * a) + Real.log 2) * C0 :=
        geometricIntegralTerm_zero_add_tsum_shifted_eq hren
      _ = _ := hren.tsum_eq.symm
  have hneg := negated_geometric_identity hL hCdiff.continuous
    hinterchange hstable href
  have hCP {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ 2 * a) : C u = P u := by
    dsimp only [C, P, g]
    exact re_crossCorrelation_eq_realEndpointCorrelation
      f hf_real hu0 huL
  have hC0 : C0 = P 0 := by
    dsimp only [C0]
    exact hCP le_rfl hL.le
  have hgeom (k : ℕ) :
      geometricIntegralTerm (2 * a) C k =
        geometricIntegralTerm (2 * a) P k := by
    unfold geometricIntegralTerm
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) (2 * a) := by
      simpa only [uIcc_of_le hL.le] using hu
    change Real.exp (-oddRate k * u) * C u =
      Real.exp (-oddRate k * u) * P u
    rw [hCP hu'.1 hu'.2]
  have hindexP :
      geometricIntegralTerm (2 * a) P 0 +
          ∑' k : ℕ, (geometricIntegralTerm (2 * a) P (k + 1) -
            (((k + 1 : ℕ) : ℝ)⁻¹ * P 0)) =
        ∑' k : ℕ, renormalizedTerm (2 * a) C0 C k := by
    calc
      _ = geometricIntegralTerm (2 * a) C 0 +
          ∑' k : ℕ, (geometricIntegralTerm (2 * a) C (k + 1) -
            C0 / (k + 1 : ℕ)) := by
        rw [hgeom 0, hC0]
        congr 1
        apply tsum_congr
        intro k
        rw [hgeom (k + 1)]
        push_cast
        ring
      _ = _ := hindex
  have hsC : Summable (fun k : ℕ ↦
      geometricIntegralTerm (2 * a) C (k + 1) -
        C0 / (k + 1 : ℕ)) :=
    (hasSum_shifted_geometric_of_hasSum_renormalized hren).summable
  have hsP : Summable (fun k : ℕ ↦
      geometricIntegralTerm (2 * a) P (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * P 0)) := by
    apply hsC.congr
    intro k
    rw [hgeom (k + 1), hC0]
    push_cast
    ring
  have hintegral :
      (∫ u : ℝ in 0..2 * a, -oddKernel u * C u + C0 / u) =
        ∫ u : ℝ in 0..2 * a,
          (P 0 - P u) / u - 2 * yoshidaRegularKernel u * P u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro huIcc
    rw [uIoc_of_le hL.le] at huIcc
    have hu' : u ∈ Icc (0 : ℝ) (2 * a) := by
      exact ⟨huIcc.1.le, huIcc.2⟩
    rw [hCP hu'.1 hu'.2, hC0]
    exact neg_oddKernel_eq_defect_sub_regular (P 0) P hu
  rw [hintegral, hC0] at hneg
  rw [hC0] at hindexP
  refine ⟨hsP, ?_⟩
  change _ = _
  rw [show geometricIntegralTerm (2 * a) P 0 +
      Real.eulerMascheroniConstant * P 0 +
      ∑' k : ℕ, (geometricIntegralTerm (2 * a) P (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * P 0)) =
      Real.eulerMascheroniConstant * P 0 +
        (geometricIntegralTerm (2 * a) P 0 +
          ∑' k : ℕ, (geometricIntegralTerm (2 * a) P (k + 1) -
            (((k + 1 : ℕ) : ℝ)⁻¹ * P 0))) by ring,
    hindexP]
  linarith

/-- The physical endpoint correlation expression produced by the digamma
distribution, before adding the polar term. -/
def endpointClippedArchCorrelation (g : ℝ → ℝ) : ℝ :=
  let C := realEndpointCorrelation yoshidaEndpointA g
  (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      (C 0 - C u) / u - 2 * yoshidaRegularKernel u * C u) -
    (Real.log (2 * yoshidaEndpointA) + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) * C 0

/-- Test-first statement of the generic clipped archimedean bridge. -/
theorem clippedArchEnergy_eq_endpointClippedArchCorrelation
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hf_odd : Function.Odd
      (((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA) =
      endpointClippedArchCorrelation
        (fun x ↦ ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (f : YoshidaClippedSmooth yoshidaEndpointA)
  let fo : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA :=
    ⟨f, hf_odd⟩
  obtain ⟨hpos, hneg⟩ :=
    pointwiseOddPeriodicCore_endpoints_zero yoshidaEndpointA_pos fo
  have hpos' : fs yoshidaEndpointA = 0 := by
    simpa only [fs, fo] using hpos
  have hneg' : fs (-yoshidaEndpointA) = 0 := by
    simpa only [fs, fo] using hneg
  have hfreal : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      fs x = ((fs x).re : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp
    · simpa only [ofReal_im] using hf_real x hx
  have hfcont : Continuous (fs : ℝ → ℂ) :=
    continuous_clipped_of_endpoints_zero yoshidaEndpointA_pos fs hneg' hpos'
  have hweighted : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq
          (yoshidaCriticalSampleLinear yoshidaEndpointA yoshidaEndpointA_pos v fs)) :=
    integrable_weighted_normSq_criticalSample_of_endpoints_zero
      yoshidaEndpointA_pos fs hneg' hpos'
  let P : ℝ → ℝ :=
    realEndpointCorrelation yoshidaEndpointA (fun x ↦ (fs x).re)
  let M : ℝ → ℂ := fun v ↦
    (Complex.normSq
      (yoshidaCriticalSampleLinear yoshidaEndpointA yoshidaEndpointA_pos v fs) : ℂ)
  let A : ℕ → ℂ := fun k ↦
    (geometricIntegralTerm (2 * yoshidaEndpointA) P k : ℂ)
  let H0 : ℂ := (P 0 : ℂ)
  let B : ℕ → ℝ := fun k ↦
    geometricIntegralTerm (2 * yoshidaEndpointA) P (k + 1) -
      (((k + 1 : ℕ) : ℝ)⁻¹ * P 0)
  have hM : Integrable M := by
    simpa only [M] using
      (integrable_normSq_yoshidaCriticalSample yoshidaEndpointA_pos fs).ofReal
  have hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖) := by
    apply hweighted.congr
    filter_upwards [] with v
    dsimp only [M]
    rw [norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  have hA (k : ℕ) :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) * M v) = A k := by
    simpa only [M, A, P] using
      normalized_cauchy_normSq_eq_geometricIntegralTerm
        yoshidaEndpointA_pos fs hfcont hfreal k
  have hH0 :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, M v) = H0 := by
    simpa only [M, H0, P] using
      normalized_integral_normSq_eq_correlation_zero
        yoshidaEndpointA_pos fs hfcont hfreal
  have hdist := localCriticalKernel_integral_eq_cauchySeries
    M hM hW A H0 hA hH0
  have hgeo := digammaGeometricValue_eq_endpointClippedArchCorrelation
    yoshidaEndpointA_pos fs hfcont hfreal hweighted
  change Summable B ∧ _ at hgeo
  obtain ⟨hsB, hvalue⟩ := hgeo
  have hterm (k : ℕ) :
      A (k + 1) - (((k + 1 : ℕ) : ℝ)⁻¹ * H0) = (B k : ℂ) := by
    dsimp only [A, H0, B]
    push_cast
    ring
  have htsum :
      (∑' k : ℕ, (A (k + 1) -
        (((k + 1 : ℕ) : ℝ)⁻¹ * H0))) =
          Complex.ofReal ((∑' k : ℕ, B k) : ℝ) := by
    calc
      _ = ∑' k : ℕ, (B k : ℂ) := by
        apply tsum_congr
        exact hterm
      _ = Complex.ofReal ((∑' k : ℕ, B k) : ℝ) :=
        (Complex.ofRealCLM.map_tsum hsB).symm
  have hrhs :
      -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          ∑' k : ℕ, (A (k + 1) -
            (((k + 1 : ℕ) : ℝ)⁻¹ * H0))) -
        (Real.log Real.pi : ℂ) * H0 =
      ((-(geometricIntegralTerm (2 * yoshidaEndpointA) P 0 +
          Real.eulerMascheroniConstant * P 0 + ∑' k : ℕ, B k) -
        Real.log Real.pi * P 0 : ℝ) : ℂ) := by
    rw [htsum]
    dsimp only [A, H0]
    push_cast
    ring
  have harchCast :
      (clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos fs : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (((Complex.digamma
              ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
                Real.log Real.pi : ℝ) : ℂ) * M v) := by
    unfold clippedArchEnergy
    dsimp only [M]
    calc
      (((1 / (2 * Real.pi) : ℝ) *
          ∫ v : ℝ,
            ((Complex.digamma
              ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
                Real.log Real.pi) *
              Complex.normSq
                (yoshidaCriticalSampleLinear yoshidaEndpointA
                  yoshidaEndpointA_pos v fs) : ℝ) : ℂ) =
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (((∫ v : ℝ,
              ((Complex.digamma
                ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
                  Real.log Real.pi) *
                Complex.normSq
                  (yoshidaCriticalSampleLinear yoshidaEndpointA
                    yoshidaEndpointA_pos v fs)) : ℝ) : ℂ)) := by
        push_cast
        rfl
      _ = _ := by
        congr 1
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        filter_upwards [] with v
        push_cast
        rfl
  have harchValue :
      clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos fs =
        -(geometricIntegralTerm (2 * yoshidaEndpointA) P 0 +
          Real.eulerMascheroniConstant * P 0 + ∑' k : ℕ, B k) -
        Real.log Real.pi * P 0 := by
    apply Complex.ofReal_injective
    rw [harchCast, hdist]
    push_cast at hrhs ⊢
    exact hrhs
  rw [harchValue, hvalue]
  rfl

/-- For a real structural odd endpoint profile, both pieces of the physical
archimedean integral are separately interval-integrable.  Thus later uses of
the split singular-minus-regular formula do not rely on the totalized value
of a nonintegrable interval integral. -/
theorem endpointClippedArchCorrelation_terms_intervalIntegrable
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hf_odd : Function.Odd
      (((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    (let g : ℝ → ℝ := fun x ↦
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
    let C := realEndpointCorrelation yoshidaEndpointA g
    IntervalIntegrable (fun u ↦ (C 0 - C u) / u) volume
        0 (2 * yoshidaEndpointA) ∧
      IntervalIntegrable (fun u ↦ yoshidaRegularKernel u * C u) volume
        0 (2 * yoshidaEndpointA)) := by
  dsimp only
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (f : YoshidaClippedSmooth yoshidaEndpointA)
  let fo : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA :=
    ⟨f, hf_odd⟩
  obtain ⟨hpos, hneg⟩ :=
    pointwiseOddPeriodicCore_endpoints_zero yoshidaEndpointA_pos fo
  have hpos' : fs yoshidaEndpointA = 0 := by
    simpa only [fs, fo] using hpos
  have hneg' : fs (-yoshidaEndpointA) = 0 := by
    simpa only [fs, fo] using hneg
  have hfreal : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      fs x = ((fs x).re : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp
    · simpa only [ofReal_im] using hf_real x hx
  have hfcont : Continuous (fs : ℝ → ℂ) :=
    continuous_clipped_of_endpoints_zero yoshidaEndpointA_pos fs hneg' hpos'
  have hweighted : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        Complex.normSq
          (yoshidaCriticalSampleLinear yoshidaEndpointA
            yoshidaEndpointA_pos v fs)) :=
    integrable_weighted_normSq_criticalSample_of_endpoints_zero
      yoshidaEndpointA_pos fs hneg' hpos'
  simpa only [fs] using
    intervalIntegrable_physical_defect_and_regular
      yoshidaEndpointA_pos fs hfcont hfreal hweighted

/-- Exact split of the combined physical archimedean integrand. -/
theorem endpointClippedArchCorrelation_eq_split
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hf_odd : Function.Odd
      (((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    (let g : ℝ → ℝ := fun x ↦
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
    let C := realEndpointCorrelation yoshidaEndpointA g
    endpointClippedArchCorrelation g =
      (∫ u : ℝ in 0..2 * yoshidaEndpointA, (C 0 - C u) / u) -
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u * C u) -
      (Real.log (2 * yoshidaEndpointA) +
        Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi) *
        C 0) := by
  dsimp only
  let g : ℝ → ℝ := fun x ↦
    ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
  let C : ℝ → ℝ := realEndpointCorrelation yoshidaEndpointA g
  obtain ⟨hdefect, hregular⟩ :=
    endpointClippedArchCorrelation_terms_intervalIntegrable f hf_real hf_odd
  have htwice : IntervalIntegrable
      (fun u ↦ 2 * yoshidaRegularKernel u * C u) volume
        0 (2 * yoshidaEndpointA) := by
    apply (hregular.const_mul 2).congr
    intro u _hu
    ring
  have htwoIntegral :
      (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        2 * yoshidaRegularKernel u * C u) =
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u * C u) := by
    calc
      _ = ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          2 * (yoshidaRegularKernel u * C u) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  unfold endpointClippedArchCorrelation
  dsimp only
  rw [intervalIntegral.integral_sub hdefect htwice, htwoIntegral]

/-- Adding the raw physical polar product to the archimedean correlation is
exactly the named physical endpoint quadratic. -/
theorem endpointClippedArchCorrelation_add_polar_eq_physicalRealQuadratic
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hf_odd : Function.Odd
      (((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    (let g : ℝ → ℝ := fun x ↦
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
    endpointClippedArchCorrelation g +
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * g y) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * g y) =
      yoshidaEndpointPhysicalRealQuadratic g) := by
  dsimp only
  rw [endpointClippedArchCorrelation_eq_split f hf_real hf_odd]
  unfold yoshidaEndpointPhysicalRealQuadratic
  ring

/-- Direct production bridge: clipped archimedean energy plus the raw
physical polar product is the physical endpoint quadratic. -/
theorem clippedArchEnergy_add_polar_eq_physicalRealQuadratic
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hf_odd : Function.Odd
      (((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    (let g : ℝ → ℝ := fun x ↦
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
    clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA) +
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * g y) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * g y) =
      yoshidaEndpointPhysicalRealQuadratic g) := by
  dsimp only
  rw [clippedArchEnergy_eq_endpointClippedArchCorrelation f hf_real hf_odd,
    endpointClippedArchCorrelation_add_polar_eq_physicalRealQuadratic
      f hf_real hf_odd]

end

end ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
