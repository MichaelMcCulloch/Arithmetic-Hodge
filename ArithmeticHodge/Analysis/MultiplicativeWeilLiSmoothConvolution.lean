import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoff
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinBumpSequence
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothing a truncated Li kernel by multiplicative convolution

This file keeps the endpoint-discontinuous `liKernelCutoff` as the merely
locally integrable factor of an additive convolution in logarithmic
coordinates.  The other factor is a smooth compactly supported Bombieri test,
so Mathlib's convolution regularity theorem supplies all derivatives.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set TopologicalSpace Topology
open scoped ContDiff Convolution Distributions SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The closed interval containing the support of the truncated Li kernel. -/
def liCutoffSupport (epsilon : ℝ) : Set ℝ :=
  Icc epsilon 1

theorem liKernelCutoff_eq_zero_of_not_mem_support
    (n : ℕ) (epsilon : ℝ) {x : ℝ}
    (hx : x ∉ liCutoffSupport epsilon) :
    liKernelCutoff n epsilon x = 0 := by
  rw [liKernelCutoff]
  split_ifs with h
  · exact (hx ⟨h.1.le, h.2.le⟩).elim
  · rfl

theorem liKernelCutoff_hasCompactSupport (n : ℕ) (epsilon : ℝ) :
    HasCompactSupport (liKernelCutoff n epsilon) := by
  exact HasCompactSupport.intro isCompact_Icc fun _x hx ↦
    liKernelCutoff_eq_zero_of_not_mem_support n epsilon hx

/-- The truncated Li kernel in the logarithmic coordinate `x = exp (-u)`. -/
def liCutoffLog (n : ℕ) (epsilon u : ℝ) : ℂ :=
  liKernelCutoff n epsilon (Real.exp (-u))

private theorem liPolynomial_continuous (n : ℕ) :
    Continuous (liPolynomial n) := by
  unfold liPolynomial
  fun_prop

theorem liCutoffLog_locallyIntegrable (n : ℕ) (epsilon : ℝ) :
    LocallyIntegrable (liCutoffLog n epsilon) := by
  let S : Set ℝ := (fun u : ℝ ↦ Real.exp (-u)) ⁻¹' Ioo epsilon 1
  let P : ℝ → ℂ := fun u ↦ (liPolynomial n (Real.log (Real.exp (-u))) : ℝ)
  have hS : MeasurableSet S := by
    exact measurableSet_Ioo.preimage (by fun_prop)
  have hP : Continuous P := by
    have hneg : Continuous (fun u : ℝ ↦ -u) := by fun_prop
    have hreal : Continuous (fun u : ℝ ↦ liPolynomial n (-u)) :=
      (liPolynomial_continuous n).comp hneg
    have hcomplex : Continuous (fun u : ℝ ↦ (liPolynomial n (-u) : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hreal
    simpa only [P, Real.log_exp] using hcomplex
  have hindicator : LocallyIntegrable (S.indicator P) :=
    hP.locallyIntegrable.indicator hS
  have heq : liCutoffLog n epsilon = S.indicator P := by
    funext u
    by_cases hu : Real.exp (-u) ∈ Ioo epsilon 1
    · simp [liCutoffLog, liKernelCutoff, S, P, hu]
    · simp [liCutoffLog, liKernelCutoff, S, P, hu]
  rw [heq]
  exact hindicator

/-- The smooth Bombieri factor in the same logarithmic coordinate. -/
def bombieriLogFactor (eta : BombieriTest) (u : ℝ) : ℂ :=
  eta (Real.exp (-u))

theorem bombieriLogFactor_contDiff (eta : BombieriTest) :
    ContDiff ℝ ∞ (bombieriLogFactor eta) := by
  have heq : bombieriLogFactor eta =
      BombieriTest.logarithmicPullback 0 eta := by
    funext u
    simp [bombieriLogFactor, BombieriTest.logarithmicPullback]
  rw [heq]
  exact eta.logarithmicPullback_contDiff 0

theorem bombieriLogFactor_hasCompactSupport (eta : BombieriTest) :
    HasCompactSupport (bombieriLogFactor eta) := by
  have heq : bombieriLogFactor eta =
      BombieriTest.logarithmicPullback 0 eta := by
    funext u
    simp [bombieriLogFactor, BombieriTest.logarithmicPullback]
  rw [heq]
  exact eta.logarithmicPullback_hasCompactSupport 0

/-- Additive convolution of the smooth test with the locally integrable Li
cutoff after passing to logarithmic coordinates. -/
def liSmoothLogConvolution (n : ℕ) (epsilon : ℝ)
    (eta : BombieriTest) : ℝ → ℂ :=
  bombieriLogFactor eta ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
    liCutoffLog n epsilon

theorem liSmoothLogConvolution_contDiff (n : ℕ) (epsilon : ℝ)
    (eta : BombieriTest) :
    ContDiff ℝ ∞ (liSmoothLogConvolution n epsilon eta) := by
  exact (bombieriLogFactor_hasCompactSupport eta).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ)
    (bombieriLogFactor_contDiff eta)
    (liCutoffLog_locallyIntegrable n epsilon)

/-- A compact set containing the support after multiplicative smoothing. -/
def liSmoothConvolutionSupport (epsilon : ℝ)
    (eta : BombieriTest) : Set ℝ :=
  (fun p : ℝ × ℝ ↦ p.1 * p.2) ''
    (liCutoffSupport epsilon ×ˢ tsupport eta)

theorem liSmoothConvolutionSupport_isCompact (epsilon : ℝ)
    (eta : BombieriTest) :
    IsCompact (liSmoothConvolutionSupport epsilon eta) := by
  exact (isCompact_Icc.prod eta.hasCompactSupport.isCompact).image
    (continuous_fst.mul continuous_snd)

theorem liSmoothConvolutionSupport_subset_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (eta : BombieriTest) :
    liSmoothConvolutionSupport epsilon eta ⊆ Ioi 0 := by
  rintro _x ⟨p, hp, rfl⟩
  have hp1 : 0 < p.1 := hepsilon.trans_le hp.1.1
  have hp2 : 0 < p.2 := by
    simpa [positiveHalfLine] using eta.tsupport_subset hp.2
  exact mul_pos hp1 hp2

theorem liSmoothConvolution_eq_zero_of_not_mem_support
    (n : ℕ) (epsilon : ℝ) (eta : BombieriTest) {x : ℝ}
    (hx : x ∉ liSmoothConvolutionSupport epsilon eta) :
    convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ) x = 0 := by
  unfold convolution
  calc
    (∫ y : ℝ in Ioi 0,
        liKernelCutoff n epsilon (x / y) * eta y / y) =
        ∫ _y : ℝ in Ioi 0, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      by_cases heta : eta y = 0
      · simp [heta]
      by_cases hli : liKernelCutoff n epsilon (x / y) = 0
      · simp [hli]
      exfalso
      apply hx
      have hratio : x / y ∈ liCutoffSupport epsilon := by
        by_contra hnot
        exact hli (liKernelCutoff_eq_zero_of_not_mem_support n epsilon hnot)
      refine ⟨(x / y, y),
        ⟨hratio, subset_tsupport eta (Function.mem_support.mpr heta)⟩, ?_⟩
      exact div_mul_cancel₀ x hy.ne'
    _ = 0 := by simp

theorem liSmoothConvolution_hasCompactSupport
    (n : ℕ) (epsilon : ℝ) (eta : BombieriTest) :
    HasCompactSupport
      (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ)) := by
  exact HasCompactSupport.intro
    (liSmoothConvolutionSupport_isCompact epsilon eta)
    fun _x hx ↦ liSmoothConvolution_eq_zero_of_not_mem_support n epsilon eta hx

theorem liSmoothConvolution_tsupport_subset {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (eta : BombieriTest) :
    tsupport (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ))
      ⊆ Ioi 0 := by
  have hsupp : Function.support
      (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ)) ⊆
      liSmoothConvolutionSupport epsilon eta := by
    intro x hx
    by_contra hnot
    exact hx (liSmoothConvolution_eq_zero_of_not_mem_support
      n epsilon eta hnot)
  have hclosure : closure (Function.support
      (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ))) ⊆
      liSmoothConvolutionSupport epsilon eta :=
    (liSmoothConvolutionSupport_isCompact epsilon eta).isClosed
      |>.closure_subset_iff.mpr hsupp
  exact hclosure.trans (liSmoothConvolutionSupport_subset_pos hepsilon eta)

private theorem expNeg_deriv :
    ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun v : ℝ ↦ Real.exp (-v))
        (-Real.exp (-u)) univ u := by
  intro u _hu
  change HasDerivWithinAt (Real.exp ∘ Neg.neg) _ univ u
  exact mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u
      (hasDerivAt_neg u)).hasDerivWithinAt

private theorem expNeg_image_univ :
    (fun u : ℝ ↦ Real.exp (-u)) '' univ = Ioi 0 := by
  rw [show (fun u : ℝ ↦ Real.exp (-u)) = Real.exp ∘ Neg.neg by rfl,
    Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem expNeg_injOn_univ :
    Set.InjOn (fun u : ℝ ↦ Real.exp (-u)) univ :=
  Real.exp_injective.injOn.comp neg_injective.injOn
    (univ.mapsTo_univ _)

/-- Haar measure `dy / y` becomes Lebesgue measure under `y = exp (-u)`. -/
theorem integral_div_eq_integral_comp_expNeg (h : ℝ → ℂ) :
    (∫ y : ℝ in Ioi 0, h y / y) =
      ∫ u : ℝ, h (Real.exp (-u)) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ expNeg_deriv expNeg_injOn_univ
    (fun y : ℝ ↦ h y / y)
  rw [expNeg_image_univ] at hchange
  calc
    (∫ y : ℝ in Ioi 0, h y / y) =
        ∫ u : ℝ in univ,
          |-Real.exp (-u)| •
            (h (Real.exp (-u)) / Real.exp (-u)) := hchange
    _ = ∫ u : ℝ, h (Real.exp (-u)) := by
      rw [setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul]
      field_simp [Real.exp_ne_zero]

/-- On the positive half-line, multiplicative convolution is the additive
convolution above evaluated at `-log x`. -/
theorem liSmoothConvolution_eq_log
    (n : ℕ) (epsilon : ℝ) (eta : BombieriTest)
    {x : ℝ} (hx : 0 < x) :
    convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ) x =
      liSmoothLogConvolution n epsilon eta (-Real.log x) := by
  unfold convolution
  rw [integral_div_eq_integral_comp_expNeg
    (fun y : ℝ ↦ liKernelCutoff n epsilon (x / y) * eta y)]
  unfold liSmoothLogConvolution
  simp only [MeasureTheory.convolution_def, bombieriLogFactor, liCutoffLog,
    ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [] with u
  have hratio :
      x / Real.exp (-u) =
        Real.exp (-(-Real.log x - u)) := by
    calc
      x / Real.exp (-u) = x * Real.exp u := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        simp
      _ = Real.exp (Real.log x + u) := by
        rw [Real.exp_add, Real.exp_log hx]
      _ = Real.exp (-(-Real.log x - u)) := by ring_nf
  rw [hratio]
  ring

/-- Smoothing by any Bombieri test removes both endpoint discontinuities of
the truncated Li kernel. -/
theorem liSmoothConvolution_contDiff {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (eta : BombieriTest) :
    ContDiff ℝ ∞
      (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have harg : ContDiffAt ℝ ∞ (fun z : ℝ ↦ -Real.log z) x :=
      (Real.contDiffAt_log.2 hx.ne').neg
    have hsmooth : ContDiffAt ℝ ∞
        (fun z : ℝ ↦ liSmoothLogConvolution n epsilon eta (-Real.log z)) x :=
      (liSmoothLogConvolution_contDiff n epsilon eta).contDiffAt.comp x harg
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact liSmoothConvolution_eq_log n epsilon eta hz
  · have hxnot : x ∉ liSmoothConvolutionSupport epsilon eta := by
      intro hmem
      exact hx (liSmoothConvolutionSupport_subset_pos hepsilon eta hmem)
    have heq :
        convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ) =ᶠ[𝓝 x]
          fun _ : ℝ ↦ (0 : ℂ) := by
      filter_upwards [
        (liSmoothConvolutionSupport_isCompact epsilon eta).isClosed
          |>.compl_mem_nhds hxnot] with z hz
      exact liSmoothConvolution_eq_zero_of_not_mem_support
        n epsilon eta hz
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The multiplicatively smoothed cutoff bundled in Bombieri's test space. -/
def bombieriLiSmoothConvolution (n : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (eta : BombieriTest) : BombieriTest :=
  TestFunction.mk
    (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ))
    (liSmoothConvolution_contDiff hepsilon n eta)
    (liSmoothConvolution_hasCompactSupport n epsilon eta)
    (by simpa [positiveHalfLine] using
      liSmoothConvolution_tsupport_subset hepsilon n eta)

@[simp]
theorem bombieriLiSmoothConvolution_apply
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : BombieriTest) (x : ℝ) :
    bombieriLiSmoothConvolution n epsilon hepsilon eta x =
      convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ) x := rfl

/-! ## Mellin product formula -/

private def liConvolutionFubiniSupport (epsilon : ℝ)
    (eta : BombieriTest) : Set (ℝ × ℝ) :=
  (fun q : ℝ × ℝ ↦ (q.1 * q.2, q.2)) ''
    (liCutoffSupport epsilon ×ˢ tsupport eta)

private theorem liConvolutionFubiniSupport_isCompact (epsilon : ℝ)
    (eta : BombieriTest) :
    IsCompact (liConvolutionFubiniSupport epsilon eta) := by
  exact (isCompact_Icc.prod eta.hasCompactSupport.isCompact).image
    ((continuous_fst.mul continuous_snd).prodMk continuous_snd)

private theorem liConvolutionFubiniSupport_subset_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (eta : BombieriTest) :
    liConvolutionFubiniSupport epsilon eta ⊆ Ioi 0 ×ˢ Ioi 0 := by
  rintro _p ⟨q, hq, rfl⟩
  have hq1 : 0 < q.1 := hepsilon.trans_le hq.1.1
  have hq2 : 0 < q.2 := by
    simpa [positiveHalfLine] using eta.tsupport_subset hq.2
  exact ⟨mul_pos hq1 hq2, hq2⟩

private def liConvolutionContinuousKernel
    (n : ℕ) (eta : BombieriTest) (s : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  ((p.1 : ℂ) ^ (s - 1) *
      (liPolynomial n (Real.log (p.1 / p.2)) : ℝ)) *
    (eta p.2 / p.2)

private theorem liConvolutionContinuousKernel_continuousOn_pos
    (n : ℕ) (eta : BombieriTest) (s : ℂ) :
    ContinuousOn (liConvolutionContinuousKernel n eta s)
      (Ioi 0 ×ˢ Ioi 0) := by
  let U : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0
  have hpow : ContinuousOn (fun p : ℝ × ℝ ↦
      (p.1 : ℂ) ^ (s - 1)) U := by
    intro p hp
    exact (Complex.continuousAt_ofReal_cpow_const p.1 (s - 1)
      (Or.inr hp.1.ne')).comp_continuousWithinAt continuousWithinAt_fst
  have hratio : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 / p.2) U :=
    continuousOn_fst.div continuousOn_snd fun p hp ↦ hp.2.ne'
  have hlog : ContinuousOn (fun p : ℝ × ℝ ↦
      Real.log (p.1 / p.2)) U := by
    intro p hp
    have hratio_ne : p.1 / p.2 ≠ 0 :=
      div_ne_zero hp.1.ne' hp.2.ne'
    have hlogAt : ContinuousAt Real.log (p.1 / p.2) :=
      Real.continuousAt_log hratio_ne
    have hcomp : ContinuousWithinAt
        (Real.log ∘ fun q : ℝ × ℝ ↦ q.1 / q.2) U p :=
      ContinuousAt.comp_continuousWithinAt
        (f := fun q : ℝ × ℝ ↦ q.1 / q.2)
        hlogAt (hratio p hp)
    simpa only [Function.comp_apply] using hcomp
  have hpolyReal : ContinuousOn (fun p : ℝ × ℝ ↦
      liPolynomial n (Real.log (p.1 / p.2))) U :=
    (liPolynomial_continuous n).comp_continuousOn hlog
  have hpoly : ContinuousOn (fun p : ℝ × ℝ ↦
      (liPolynomial n (Real.log (p.1 / p.2)) : ℂ)) U :=
    Complex.ofRealCLM.continuous.comp_continuousOn hpolyReal
  have heta : ContinuousOn (fun p : ℝ × ℝ ↦ eta p.2) U :=
    eta.contDiff.continuous.comp_continuousOn continuousOn_snd
  have hdenom : ContinuousOn (fun p : ℝ × ℝ ↦ (p.2 : ℂ)) U := by
    fun_prop
  have hdenom_ne : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 := fun p hp ↦
    Complex.ofReal_ne_zero.mpr hp.2.ne'
  exact hpow.mul hpoly |>.mul (heta.div hdenom hdenom_ne)

private def liConvolutionRatioInterior (epsilon : ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ ↦ p.1 / p.2) ⁻¹' Ioo epsilon 1

private theorem liConvolutionRatioInterior_measurable (epsilon : ℝ) :
    MeasurableSet (liConvolutionRatioInterior epsilon) := by
  exact measurableSet_Ioo.preimage (by fun_prop)

private theorem convolutionMellinKernel_eq_indicator_on_pos
    (n : ℕ) (epsilon : ℝ) (eta : BombieriTest) (s : ℂ)
    (p : ℝ × ℝ) (_hp : p ∈ Ioi 0 ×ˢ Ioi 0) :
    convolutionMellinKernel (liKernelCutoff n epsilon)
        (eta : ℝ → ℂ) s p =
      (liConvolutionRatioInterior epsilon).indicator
        (liConvolutionContinuousKernel n eta s) p := by
  by_cases hratio : p.1 / p.2 ∈ Ioo epsilon 1
  · simp [convolutionMellinKernel, liKernelCutoff,
      liConvolutionRatioInterior, liConvolutionContinuousKernel, hratio]
  · simp [convolutionMellinKernel, liKernelCutoff,
      liConvolutionRatioInterior, hratio]

private theorem convolutionMellinKernel_eq_zero_of_pos_notMem
    (n : ℕ) (epsilon : ℝ) (eta : BombieriTest) (s : ℂ)
    (p : ℝ × ℝ) (hp : p ∈ Ioi 0 ×ˢ Ioi 0)
    (hnot : p ∉ liConvolutionFubiniSupport epsilon eta) :
    convolutionMellinKernel (liKernelCutoff n epsilon)
      (eta : ℝ → ℂ) s p = 0 := by
  by_cases hli : liKernelCutoff n epsilon (p.1 / p.2) = 0
  · simp [convolutionMellinKernel, hli]
  have heta : eta p.2 = 0 := by
    by_contra heta
    apply hnot
    have hratio : p.1 / p.2 ∈ liCutoffSupport epsilon := by
      by_contra hratio
      exact hli (liKernelCutoff_eq_zero_of_not_mem_support
        n epsilon hratio)
    refine ⟨(p.1 / p.2, p.2),
      ⟨hratio, subset_tsupport eta (Function.mem_support.mpr heta)⟩, ?_⟩
    apply Prod.ext
    · exact div_mul_cancel₀ p.1 hp.2.ne'
    · rfl
  simp [convolutionMellinKernel, heta]

/-- The Li-cutoff/Bombieri convolution satisfies the two-variable absolute
integrability condition at every Mellin argument. -/
theorem bombieriLiSmoothConvolution_fubiniAt {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (eta : BombieriTest) (s : ℂ) :
    ConvolutionFubiniAt (liKernelCutoff n epsilon)
      (eta : ℝ → ℂ) s := by
  unfold ConvolutionFubiniAt
  rw [Measure.prod_restrict]
  change IntegrableOn
    (convolutionMellinKernel (liKernelCutoff n epsilon)
      (eta : ℝ → ℂ) s)
    (Ioi 0 ×ˢ Ioi 0) (volume.prod volume)
  let K := liConvolutionFubiniSupport epsilon eta
  let H := liConvolutionContinuousKernel n eta s
  let S := liConvolutionRatioInterior epsilon
  have hK : IsCompact K := liConvolutionFubiniSupport_isCompact epsilon eta
  have hKD : K ⊆ Ioi 0 ×ˢ Ioi 0 :=
    liConvolutionFubiniSupport_subset_pos hepsilon eta
  have hH : ContinuousOn H K :=
    (liConvolutionContinuousKernel_continuousOn_pos n eta s).mono hKD
  have hHint : IntegrableOn H K (volume.prod volume) :=
    hH.integrableOn_compact hK
  have hSind : IntegrableOn (S.indicator H) K (volume.prod volume) :=
    hHint.indicator (liConvolutionRatioInterior_measurable epsilon)
  have hkernelK : IntegrableOn
      (convolutionMellinKernel (liKernelCutoff n epsilon)
        (eta : ℝ → ℂ) s) K (volume.prod volume) := by
    apply hSind.congr_fun
    · intro p hp
      exact (convolutionMellinKernel_eq_indicator_on_pos
        n epsilon eta s p (hKD hp)).symm
    · exact hK.measurableSet
  exact hkernelK.of_forall_diff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp ↦
      convolutionMellinKernel_eq_zero_of_pos_notMem
        n epsilon eta s p hp.1 hp.2

private def liCutoffMellinContinuousKernel (n : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * (liPolynomial n (Real.log x) : ℝ)

private theorem liCutoffMellinContinuousKernel_continuousOn_support
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ) (s : ℂ) :
    ContinuousOn (liCutoffMellinContinuousKernel n s)
      (liCutoffSupport epsilon) := by
  intro x hx
  have hxpos : 0 < x := hepsilon.trans_le hx.1
  have hpow : ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ (s - 1)) x :=
    Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr hxpos.ne')
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hxpos.ne'
  have hpolyReal : ContinuousAt (fun y : ℝ ↦
      liPolynomial n (Real.log y)) x :=
    ContinuousAt.comp (f := Real.log)
      (liPolynomial_continuous n).continuousAt hlog
  have hpoly : ContinuousAt (fun y : ℝ ↦
      (liPolynomial n (Real.log y) : ℂ)) x :=
    ContinuousAt.comp (f := fun y : ℝ ↦ liPolynomial n (Real.log y))
      Complex.ofRealCLM.continuous.continuousAt hpolyReal
  exact (hpow.mul hpoly).continuousWithinAt

/-- A positive truncation makes the Li cutoff Mellin-convergent at every
complex argument. -/
theorem liKernelCutoff_mellinConvergent {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (s : ℂ) :
    MellinConvergent (liKernelCutoff n epsilon) s := by
  change IntegrableOn (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liKernelCutoff n epsilon x) (Ioi 0)
  let K := liCutoffSupport epsilon
  let S : Set ℝ := Ioo epsilon 1
  let H := liCutoffMellinContinuousKernel n s
  have hH : ContinuousOn H K :=
    liCutoffMellinContinuousKernel_continuousOn_support hepsilon n s
  have hHint : IntegrableOn H K :=
    hH.integrableOn_compact isCompact_Icc
  have hSind : IntegrableOn (S.indicator H) K :=
    hHint.indicator measurableSet_Ioo
  have hcutK : IntegrableOn (fun x : ℝ ↦
      (x : ℂ) ^ (s - 1) * liKernelCutoff n epsilon x) K := by
    apply hSind.congr_fun
    · intro x hx
      by_cases hxi : x ∈ Ioo epsilon 1
      · simp [S, H, liCutoffMellinContinuousKernel,
          liKernelCutoff, hxi]
      · simp [S, H, liKernelCutoff, hxi]
    · exact measurableSet_Icc
  exact hcutK.of_forall_diff_eq_zero measurableSet_Ioi fun x hx ↦ by
    simp [liKernelCutoff_eq_zero_of_not_mem_support n epsilon hx.2]

/-- All hypotheses for the integrability-aware Mellin convolution theorem
are automatic for a positive cutoff and a Bombieri test. -/
theorem bombieriLiSmoothConvolution_mellinProductHypotheses
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (n : ℕ) (eta : BombieriTest) (s : ℂ) :
    MellinProductHypotheses (liKernelCutoff n epsilon)
      (eta : ℝ → ℂ) s :=
  ⟨liKernelCutoff_mellinConvergent hepsilon n s,
    eta.mellinConvergent s,
    bombieriLiSmoothConvolution_fubiniAt hepsilon n eta s⟩

/-- Mellin smoothing multiplies the truncated Li transform by the Mellin
transform of the Bombieri test, with Fubini discharged from support. -/
theorem mellin_bombieriLiSmoothConvolution {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (eta : BombieriTest) (s : ℂ) :
    mellin (bombieriLiSmoothConvolution n epsilon hepsilon eta : ℝ → ℂ) s =
      mellin (liKernelCutoff n epsilon) s * mellin (eta : ℝ → ℂ) s := by
  change mellin (convolution (liKernelCutoff n epsilon)
    (eta : ℝ → ℂ)) s = _
  exact mellin_convolution (liKernelCutoff n epsilon)
    (eta : ℝ → ℂ) s
    (bombieriLiSmoothConvolution_fubiniAt hepsilon n eta s)

/-- Integrability-aware version of the Mellin product formula. -/
theorem bombieriLiSmoothConvolution_hasMellin {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (n : ℕ) (eta : BombieriTest) (s : ℂ) :
    HasMellin
      (bombieriLiSmoothConvolution n epsilon hepsilon eta : ℝ → ℂ) s
      (mellin (liKernelCutoff n epsilon) s *
        mellin (eta : ℝ → ℂ) s) := by
  change HasMellin
    (convolution (liKernelCutoff n epsilon) (eta : ℝ → ℂ)) s _
  exact hasMellin_convolution (liKernelCutoff n epsilon)
    (eta : ℝ → ℂ) s
    (bombieriLiSmoothConvolution_mellinProductHypotheses
      hepsilon n eta s)

/-! ## The production shrinking bump sequence -/

/-- The truncated Li kernel smoothed by the `k`th production Mellin bump. -/
def bombieriLiMellinBumpConvolution (n : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (k : ℕ) : BombieriTest :=
  bombieriLiSmoothConvolution n epsilon hepsilon (mellinBumpSequence k)

@[simp]
theorem bombieriLiMellinBumpConvolution_apply
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (k : ℕ) (x : ℝ) :
    bombieriLiMellinBumpConvolution n epsilon hepsilon k x =
      convolution (liKernelCutoff n epsilon)
        (mellinBumpSequence k : ℝ → ℂ) x := rfl

theorem mellin_bombieriLiMellinBumpConvolution
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (k : ℕ) (s : ℂ) :
    mellin (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ) s =
      mellin (liKernelCutoff n epsilon) s *
        mellin (mellinBumpSequence k : ℝ → ℂ) s := by
  exact mellin_bombieriLiSmoothConvolution hepsilon n
    (mellinBumpSequence k) s

/-- In Mellin space the smooth approximants converge pointwise back to the
truncated Li kernel. -/
theorem mellin_bombieriLiMellinBumpConvolution_tendsto
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) (s : ℂ) :
    Tendsto (fun k : ℕ ↦
      mellin (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ) s)
      atTop (nhds (mellin (liKernelCutoff n epsilon) s)) := by
  have h := (tendsto_const_nhds (x := mellin (liKernelCutoff n epsilon) s)).mul
    (mellin_mellinBumpSequence_tendsto_one s)
  simpa only [mellin_bombieriLiMellinBumpConvolution, mul_one] using h

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

