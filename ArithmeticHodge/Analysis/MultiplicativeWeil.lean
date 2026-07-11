/-
  Source-oriented multiplicative Weil and Bombieri infrastructure.

  Functions are represented on `ℝ`, while every integral is restricted to
  `(0, ∞)`.  This keeps the definitions compatible with Mathlib's Mellin API
  while retaining the multiplicative Haar density `dy / y`.

  The conventions follow Bombieri, *Remarks on Weil's quadratic functional
  in the theory of prime numbers, I* (2000), Theorems 1--2.  This module does
  not identify the resulting complex Mellin functional with the legacy real
  additive `weilFunctionalFull`.
-/

import ArithmeticHodge.Analysis.WeilDefs
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Multiplicative Weil criterion

Source-faithful Mellin, convolution, and conditional Bombieri positivity
infrastructure on `C_c^∞((0,∞))`.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Bombieri's linear transpose `f*(x) = x⁻¹ f(x⁻¹)`. -/
def transpose (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-1 : ℂ) * f x⁻¹

/-- The transpose conjugate `bar(f)*(x) = x⁻¹ conj(f(x⁻¹))`. -/
def transposeConjugate (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  transpose (fun y ↦ starRingEnd ℂ (f y)) x

/-- Conjugation of the coefficients of a complex-variable function. -/
def coefficientConjugate (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  starRingEnd ℂ (F (starRingEnd ℂ s))

/-- Multiplicative convolution with Haar density `dy / y`. -/
noncomputable def convolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, f (x / y) * g y / y

/-- The equivalent autocorrelation presentation used by Bombieri. -/
noncomputable def autocorrelation (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, g (x * y) * starRingEnd ℂ (g y)

/-- Kernel whose absolute integrability licenses the convolution Fubini step. -/
def convolutionMellinKernel (f g : ℝ → ℂ) (s : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  ((p.1 : ℂ) ^ (s - 1) * f (p.1 / p.2)) * (g p.2 / p.2)

/-- Explicit Fubini hypothesis for a Mellin transform of a convolution. -/
def ConvolutionFubiniAt (f g : ℝ → ℂ) (s : ℂ) : Prop :=
  Integrable (convolutionMellinKernel f g s)
    ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- All convergence assumptions carried by the integrability-aware Mellin
product theorem. -/
def MellinProductHypotheses (f g : ℝ → ℂ) (s : ℂ) : Prop :=
  MellinConvergent f s ∧ MellinConvergent g s ∧ ConvolutionFubiniAt f g s

/-- The quadratic factor `M g(s) * bar(M g)(1-s)`. -/
noncomputable def spectralTerm (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin g s * coefficientConjugate (mellin g) (1 - s)

theorem transpose_apply_of_pos (f : ℝ → ℂ) {x : ℝ} (_hx : 0 < x) :
    transpose f x = f x⁻¹ / x := by
  rw [transpose, Complex.cpow_neg_one, ← Complex.ofReal_inv]
  simp only [div_eq_mul_inv, Complex.ofReal_inv]
  ring_nf

theorem transposeConjugate_apply_of_pos (f : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    transposeConjugate f x = starRingEnd ℂ (f x⁻¹) / x := by
  rw [transposeConjugate, transpose_apply_of_pos _ hx]

theorem transpose_involutive_on_pos (f : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    transpose (transpose f) x = f x := by
  rw [transpose_apply_of_pos _ hx,
    transpose_apply_of_pos f (inv_pos.mpr hx), inv_inv]
  rw [Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

theorem transposeConjugate_involutive_on_pos (f : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    transposeConjugate (transposeConjugate f) x = f x := by
  rw [transposeConjugate_apply_of_pos _ hx,
    transposeConjugate_apply_of_pos f (inv_pos.mpr hx), inv_inv]
  simp only [map_div₀, Complex.conj_ofReal, starRingEnd_self_apply]
  rw [Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

/-- The source's two presentations of the quadratic convolution agree. -/
theorem convolution_transposeConjugate_eq_autocorrelation
    (g : ℝ → ℂ) (x : ℝ) :
    convolution g (transposeConjugate g) x = autocorrelation g x := by
  unfold convolution autocorrelation
  calc
    (∫ y : ℝ in Ioi 0,
        g (x / y) * transposeConjugate g y / y) =
      ∫ y : ℝ in Ioi 0,
        ((|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) : ℝ) •
          (g (x * y ^ (-1 : ℝ)) *
            starRingEnd ℂ (g (y ^ (-1 : ℝ)))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [transposeConjugate_apply_of_pos g hy, Real.rpow_neg_one]
      norm_num only [abs_neg, abs_one, one_mul, neg_sub]
      rw [Real.rpow_neg hy.le 2, Real.rpow_two, Complex.real_smul,
        Complex.ofReal_inv]
      have hcast : ((y ^ 2 : ℝ) : ℂ) = (y : ℂ) ^ 2 := by
        apply Complex.ext <;> simp
      have hinv : ((y : ℂ) ^ 2)⁻¹ = ((y ^ 2 : ℝ) : ℂ)⁻¹ :=
        congrArg Inv.inv hcast.symm
      calc
        g (x / y) * (starRingEnd ℂ (g y⁻¹) / y) / y =
            ((y : ℂ) ^ 2)⁻¹ *
              (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹)) := by
          rw [div_eq_mul_inv]
          ring_nf
        _ = ((y ^ 2 : ℝ) : ℂ)⁻¹ *
              (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹)) := by
          rw [hinv]
    _ = ∫ y : ℝ in Ioi 0,
        g (x * y) * starRingEnd ℂ (g y) :=
      integral_comp_rpow_Ioi
        (fun y : ℝ ↦ g (x * y) * starRingEnd ℂ (g y))
        (by norm_num : (-1 : ℝ) ≠ 0)

/-- The linear transpose reflects the Mellin variable about `1/2`. -/
theorem mellin_transpose (f : ℝ → ℂ) (s : ℂ) :
    mellin (transpose f) s = mellin f (1 - s) := by
  calc
    mellin (transpose f) s =
        mellin (fun x : ℝ ↦ f x⁻¹) (s + (-1 : ℂ)) := by
      simpa [transpose, smul_eq_mul] using
        (mellin_cpow_smul (fun x : ℝ ↦ f x⁻¹) s (-1 : ℂ))
    _ = mellin f (-(s + (-1 : ℂ))) := mellin_comp_inv f (s + (-1 : ℂ))
    _ = mellin f (1 - s) := by
      rw [show -(s + (-1 : ℂ)) = 1 - s by ring]

/-- Mellin convergence is reflected by the same operation. -/
theorem mellinConvergent_transpose (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (transpose f) s ↔ MellinConvergent f (1 - s) := by
  change MellinConvergent
      (fun x : ℝ ↦ (x : ℂ) ^ (-1 : ℂ) • f x⁻¹) s ↔ _
  rw [MellinConvergent.cpow_smul]
  simp_rw [← Real.rpow_neg_one]
  rw [MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
  rw [show (s + (-1 : ℂ)) / (-1 : ℂ) = 1 - s by ring]

/-- Integrability-aware transpose transform rule. -/
theorem hasMellin_transpose (f : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent f (1 - s)) :
    HasMellin (transpose f) s (mellin f (1 - s)) :=
  ⟨(mellinConvergent_transpose f s).2 hf, mellin_transpose f s⟩

/-- Mellin transform of pointwise complex conjugation. -/
theorem mellin_conjugate (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun x ↦ starRingEnd ℂ (f x)) s =
      coefficientConjugate (mellin f) s := by
  unfold mellin coefficientConjugate
  change (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * starRingEnd ℂ (f t)) =
    starRingEnd ℂ (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (starRingEnd ℂ s - 1) * f t)
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) * starRingEnd ℂ (f t)) =
      ∫ t : ℝ in Ioi 0, starRingEnd ℂ
        ((t : ℂ) ^ (starRingEnd ℂ s - 1) * f t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have harg : (x : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hx.le]
        exact Real.pi_ne_zero.symm
      have hcpow := Complex.cpow_conj (x : ℂ)
        (starRingEnd ℂ s - 1) harg
      simp only [map_sub, map_one, starRingEnd_self_apply,
        Complex.conj_ofReal] at hcpow
      rw [map_mul, hcpow]
    _ = starRingEnd ℂ (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (starRingEnd ℂ s - 1) * f t) := integral_conj

/-- Transform rule for the transpose conjugate. -/
theorem mellin_transposeConjugate (f : ℝ → ℂ) (s : ℂ) :
    mellin (transposeConjugate f) s =
      coefficientConjugate (mellin f) (1 - s) := by
  change mellin (transpose (fun y ↦ starRingEnd ℂ (f y))) s = _
  rw [mellin_transpose, mellin_conjugate]

/-- Integrability-aware transpose-conjugate transform rule. -/
theorem hasMellin_transposeConjugate (f : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent (fun y ↦ starRingEnd ℂ (f y)) (1 - s)) :
    HasMellin (transposeConjugate f) s
      (coefficientConjugate (mellin f) (1 - s)) :=
  ⟨(mellinConvergent_transpose
      (fun y ↦ starRingEnd ℂ (f y)) s).2 hf,
    mellin_transposeConjugate f s⟩

private theorem ofReal_inv_cpow_neg {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  have harg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg, inv_inv]

/-- Mellin turns multiplicative convolution into multiplication once the
two-variable kernel is absolutely integrable. -/
theorem mellin_convolution
    (f g : ℝ → ℂ) (s : ℂ) (hfg : ConvolutionFubiniAt f g s) :
    mellin (convolution f g) s = mellin f s * mellin g s := by
  unfold mellin convolution
  change (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
      (∫ y : ℝ in Ioi 0, f (x / y) * g y / y)) = _
  calc
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        (∫ y : ℝ in Ioi 0, f (x / y) * g y / y)) =
      ∫ x : ℝ in Ioi 0, ∫ y : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y) := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        (x : ℂ) ^ (s - 1) *
            (∫ y : ℝ in Ioi 0, f (x / y) * g y / y) =
          ∫ y : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
            (f (x / y) * g y / y) :=
          (integral_const_mul (μ := volume.restrict (Ioi 0))
            ((x : ℂ) ^ (s - 1))
            (fun y : ℝ ↦ f (x / y) * g y / y)).symm
        _ = ∫ y : ℝ in Ioi 0,
            convolutionMellinKernel f g s (x, y) := by
          apply integral_congr_ae
          filter_upwards with y
          simp only [convolutionMellinKernel]
          ring
    _ = ∫ y : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y) := integral_integral_swap hfg
    _ = ∫ y : ℝ in Ioi 0,
        mellin f s * ((y : ℂ) ^ (s - 1) * g y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      calc
        (∫ x : ℝ in Ioi 0,
            convolutionMellinKernel f g s (x, y)) =
          (∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) := by
          calc
            (∫ x : ℝ in Ioi 0,
                convolutionMellinKernel f g s (x, y)) =
              ∫ x : ℝ in Ioi 0,
                ((x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [convolutionMellinKernel]
            _ = (∫ x : ℝ in Ioi 0,
                (x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) :=
              integral_mul_const (g y / y) _
        _ = mellin f s * ((y : ℂ) ^ (s - 1) * g y) := by
          change mellin (fun x : ℝ ↦ f (x / y)) s * (g y / y) = _
          have hfun : (fun x : ℝ ↦ f (x / y)) =
              fun x : ℝ ↦ f (x * y⁻¹) := by
            funext x
            rw [div_eq_mul_inv]
          rw [hfun, mellin_comp_mul_right f s (inv_pos.mpr hy),
            ofReal_inv_cpow_neg hy]
          simp only [smul_eq_mul]
          have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
          rw [Complex.cpow_sub s 1 hyne, Complex.cpow_one]
          ring
    _ = mellin f s * mellin g s := by
      change (∫ y : ℝ in Ioi 0,
          mellin f s * ((y : ℂ) ^ (s - 1) * g y)) =
        mellin f s * (∫ y : ℝ in Ioi 0,
          (y : ℂ) ^ (s - 1) * g y)
      exact integral_const_mul _ _

/-- Absolute integrability of the two-variable kernel also proves convergence
of the convolution's Mellin transform. -/
theorem mellinConvergent_convolution
    (f g : ℝ → ℂ) (s : ℂ) (hfg : ConvolutionFubiniAt f g s) :
    MellinConvergent (convolution f g) s := by
  change Integrable (fun x : ℝ ↦
      (x : ℂ) ^ (s - 1) * convolution f g x)
    (volume.restrict (Ioi 0))
  change Integrable (convolutionMellinKernel f g s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) at hfg
  have houter := hfg.integral_prod_left
  refine houter.congr ?_
  filter_upwards with x
  unfold convolution
  calc
    (∫ y : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y)) =
      ∫ y : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        (f (x / y) * g y / y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [convolutionMellinKernel]
      ring
    _ = (x : ℂ) ^ (s - 1) *
        (∫ y : ℝ in Ioi 0, f (x / y) * g y / y) :=
      integral_const_mul (μ := volume.restrict (Ioi 0)) ((x : ℂ) ^ (s - 1))
        (fun y : ℝ ↦ f (x / y) * g y / y)

/-- Fully integrability-aware convolution product relation. -/
theorem hasMellin_convolution
    (f g : ℝ → ℂ) (s : ℂ)
    (h : MellinProductHypotheses f g s) :
    HasMellin (convolution f g) s (mellin f s * mellin g s) :=
  ⟨mellinConvergent_convolution f g s h.2.2,
    mellin_convolution f g s h.2.2⟩

/-- The quadratic convolution has Bombieri's Mellin factor. -/
theorem mellin_quadraticConvolution
    (g : ℝ → ℂ) (s : ℂ)
    (hg : ConvolutionFubiniAt g (transposeConjugate g) s) :
    mellin (convolution g (transposeConjugate g)) s = spectralTerm g s := by
  rw [mellin_convolution g (transposeConjugate g) s hg,
    mellin_transposeConjugate]
  rfl

/-- On the critical line the Bombieri spectral term is a squared norm. -/
theorem spectralTerm_eq_normSq_of_re_eq_half
    (g : ℝ → ℂ) {s : ℂ} (hs : s.re = 1 / 2) :
    spectralTerm g s = (Complex.normSq (mellin g s) : ℂ) := by
  have hreflect : 1 - starRingEnd ℂ s = s := by
    apply Complex.ext
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp
  unfold spectralTerm coefficientConjugate
  simp only [map_sub, map_one]
  rw [hreflect, Complex.normSq_eq_conj_mul_self]
  ring

/-- Finite spectral sums are nonnegative when all entries lie on the critical
line. -/
theorem finite_spectral_sum_re_nonneg
    {ι : Type*} (S : Finset ι) (zeros : ι → ℂ) (g : ℝ → ℂ)
    (hcrit : ∀ i ∈ S, (zeros i).re = 1 / 2) :
    0 ≤ (∑ i ∈ S, spectralTerm g (zeros i)).re := by
  change 0 ≤ Complex.reCLM (∑ i ∈ S, spectralTerm g (zeros i))
  rw [map_sum Complex.reCLM]
  exact Finset.sum_nonneg fun i hi ↦ by
    rw [spectralTerm_eq_normSq_of_re_eq_half g (hcrit i hi)]
    exact Complex.normSq_nonneg _

/-- The positive half-line as an open subset of `ℝ`. -/
def positiveHalfLine : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

/-- Bombieri's `C_c^∞((0,∞))`, using Mathlib's bundled test functions.
In particular, `tsupport f` is compact and contained in the positive
half-line, so it is bounded away from both zero and infinity. -/
abbrev BombieriTest := 𝓓(positiveHalfLine, ℂ)

namespace BombieriTest

/-- Every Bombieri test has a convergent Mellin transform at every complex
argument.  Compact topological support inside `(0,∞)` removes both endpoint
singularities. -/
theorem mellinConvergent (f : BombieriTest) (s : ℂ) :
    MellinConvergent (f : ℝ → ℂ) s := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) * f x
  have hF_cont : ContinuousOn F (tsupport f) := by
    intro x hx
    have hx_pos : 0 < x := f.tsupport_subset hx
    exact ((Complex.continuousAt_ofReal_cpow_const x (s - 1)
      (Or.inr hx_pos.ne')).mul f.contDiff.continuous.continuousAt).continuousWithinAt
  have hF_integrableOn : IntegrableOn F (tsupport f) :=
    hF_cont.integrableOn_compact f.hasCompactSupport
  have hF_support : Function.support F ⊆ tsupport f := by
    intro x hx
    apply subset_tsupport f
    apply Function.mem_support.mpr
    intro hfx
    apply hx
    simp [F, hfx]
  have hF_integrable : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset hF_support).mp hF_integrableOn
  change IntegrableOn F (Ioi 0)
  exact hF_integrable.integrableOn

/-- Pull a multiplicative test to the additive real line with a Mellin
weight. -/
def logarithmicPullback (σ : ℝ) (f : BombieriTest) (u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))

private theorem comp_exp_neg_hasCompactSupport (f : BombieriTest) :
    HasCompactSupport (fun u : ℝ ↦ f (Real.exp (-u))) := by
  let K : Set ℝ := (fun x : ℝ ↦ -Real.log x) '' tsupport f
  have hlog : ContinuousOn (fun x : ℝ ↦ -Real.log x) (tsupport f) := by
    exact Real.continuousOn_log.neg.mono fun x hx ↦
      (f.tsupport_subset hx).ne'
  have hK : IsCompact K := f.hasCompactSupport.image_of_continuousOn hlog
  refine HasCompactSupport.intro hK ?_
  intro u hu
  by_contra hne
  apply hu
  refine ⟨Real.exp (-u), ?_, ?_⟩
  · exact subset_tsupport f (Function.mem_support.mpr hne)
  · simp

/-- Every logarithmic pullback of a Bombieri test is compactly supported. -/
theorem logarithmicPullback_hasCompactSupport
    (f : BombieriTest) (σ : ℝ) :
    HasCompactSupport (logarithmicPullback σ f) := by
  have hcore := comp_exp_neg_hasCompactSupport f
  simpa only [logarithmicPullback, Pi.mul_apply] using
    hcore.mul_left (f := fun u : ℝ ↦ (Real.exp (-σ * u) : ℂ))

/-- The logarithmic pullback remains smooth. -/
theorem logarithmicPullback_contDiff
    (f : BombieriTest) (σ : ℝ) :
    ContDiff ℝ ∞ (logarithmicPullback σ f) := by
  unfold logarithmicPullback
  have hweightReal : ContDiff ℝ ∞ (fun u : ℝ ↦ Real.exp (-σ * u)) := by
    fun_prop
  have hweight : ContDiff ℝ ∞ (fun u : ℝ ↦ (Real.exp (-σ * u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hweightReal
  have hargument : ContDiff ℝ ∞ (fun u : ℝ ↦ Real.exp (-u)) := by
    fun_prop
  exact hweight.mul (f.contDiff.comp hargument)

/-- The logarithmic pullback bundled as a Schwartz function. -/
def logarithmicPullbackSchwartz
    (f : BombieriTest) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (f.logarithmicPullback_hasCompactSupport σ).toSchwartzMap
    (f.logarithmicPullback_contDiff σ)

@[simp]
theorem logarithmicPullbackSchwartz_apply
    (f : BombieriTest) (σ u : ℝ) :
    f.logarithmicPullbackSchwartz σ u = logarithmicPullback σ f u := rfl

end BombieriTest

/-- A bundled realization of the linear transpose on the Bombieri test
space.  `MultiplicativeWeilTranspose` constructs the canonical realization;
keeping the data explicit makes the conditional formula usable independently
of that downstream module. -/
structure TransposeData where
  toLinearMap : BombieriTest →ₗ[ℂ] BombieriTest
  apply_pos : ∀ (f : BombieriTest) {x : ℝ}, 0 < x →
    toLinearMap f x = transpose (f : ℝ → ℂ) x

/-- A bundled Bombieri test representing `g ⋆ bar(g)*`. -/
structure QuadraticTestData (g : BombieriTest) where
  test : BombieriTest
  convolution_eq : ∀ x : ℝ, test x =
    convolution (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) x

/-- An exhaustive nontrivial-zero sequence whose finite fibers record analytic
multiplicity. -/
structure ZetaZeroEnumeration where
  zero : ℕ → NontrivialZetaZero
  exhaustive : ∀ ρ : NontrivialZetaZero, ∃ n, zero n = ρ
  fiberFinite : ∀ ρ : NontrivialZetaZero,
    Set.Finite {n : ℕ | zero n = ρ}
  fiberCard : ∀ ρ : NontrivialZetaZero,
    Nat.card {n : ℕ // zero n = ρ} =
      analyticOrderNatAt riemannZeta ρ.val

/-- Source-oriented conditional form of Bombieri's explicit formula. -/
def BombieriExplicitFormula
    (T : BombieriTest →ₗ[ℂ] ℂ) (transposeData : TransposeData)
    (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ f : BombieriTest,
    Summable (fun n ↦ mellin (f : ℝ → ℂ) (zeros.zero n).val) ∧
      T f = T (transposeData.toLinearMap f) ∧
      T f = ∑' n, mellin (f : ℝ → ℂ) (zeros.zero n).val

/-- Under RH, the quadratic functional is exactly the sum of Mellin squared
norms. -/
theorem rh_bombieri_quadratic_eq_tsum_normSq
    (T : BombieriTest →ₗ[ℂ] ℂ) (transposeData : TransposeData)
    (zeros : ZetaZeroEnumeration)
    (hexplicit : BombieriExplicitFormula T transposeData zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest)
    (q : QuadraticTestData g)
    (hfubini : ∀ n,
      ConvolutionFubiniAt (g : ℝ → ℂ)
        (transposeConjugate (g : ℝ → ℂ)) (zeros.zero n).val) :
    T q.test = ∑' n,
      (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ) := by
  have hexpl := hexplicit q.test
  have hterm : ∀ n, mellin (q.test : ℝ → ℂ) (zeros.zero n).val =
      spectralTerm (g : ℝ → ℂ) (zeros.zero n).val := by
    intro n
    rw [show (q.test : ℝ → ℂ) =
        convolution (g : ℝ → ℂ)
          (transposeConjugate (g : ℝ → ℂ)) from
      funext q.convolution_eq]
    exact mellin_quadraticConvolution (g : ℝ → ℂ)
      (zeros.zero n).val (hfubini n)
  rw [hexpl.2.2]
  apply tsum_congr
  intro n
  rw [hterm n, spectralTerm_eq_normSq_of_re_eq_half]
  exact hRH (zeros.zero n).val (zeros.zero n).is_zero (by
      rintro ⟨k, hk⟩
      have hre := (zeros.zero n).re_pos
      rw [hk] at hre
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := Nat.cast_add_one_pos k
      norm_num at hre
      linarith) (by
        intro hone
        have : (zeros.zero n).val.re = 1 := by rw [hone]; simp
        linarith [(zeros.zero n).re_lt_one])

/-- Correctly oriented RH-forward positivity.  The equality above also shows
that the quadratic value is real. -/
theorem rh_implies_bombieri_nonneg
    (T : BombieriTest →ₗ[ℂ] ℂ) (transposeData : TransposeData)
    (zeros : ZetaZeroEnumeration)
    (hexplicit : BombieriExplicitFormula T transposeData zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest)
    (q : QuadraticTestData g)
    (hfubini : ∀ n,
      ConvolutionFubiniAt (g : ℝ → ℂ)
        (transposeConjugate (g : ℝ → ℂ)) (zeros.zero n).val) :
    (T q.test).im = 0 ∧ 0 ≤ (T q.test).re := by
  have heq := rh_bombieri_quadratic_eq_tsum_normSq
    T transposeData zeros hexplicit hRH g q hfubini
  rw [heq]
  have hterm : ∀ n, mellin (q.test : ℝ → ℂ) (zeros.zero n).val =
      (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ) := by
    intro n
    rw [show (q.test : ℝ → ℂ) =
        convolution (g : ℝ → ℂ)
          (transposeConjugate (g : ℝ → ℂ)) from
      funext q.convolution_eq,
      mellin_quadraticConvolution (g : ℝ → ℂ)
        (zeros.zero n).val (hfubini n),
      spectralTerm_eq_normSq_of_re_eq_half]
    exact hRH (zeros.zero n).val (zeros.zero n).is_zero (by
        rintro ⟨k, hk⟩
        have hre := (zeros.zero n).re_pos
        rw [hk] at hre
        have hkpos : (0 : ℝ) < (k : ℝ) + 1 := Nat.cast_add_one_pos k
        norm_num at hre
        linarith) (by
          intro hone
          have : (zeros.zero n).val.re = 1 := by rw [hone]; simp
          linarith [(zeros.zero n).re_lt_one])
  have hsumm : Summable (fun n ↦
      (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ)) :=
    (hexplicit q.test).1.congr hterm
  constructor
  · change Complex.imCLM (∑' n,
        (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ)) = 0
    rw [Complex.imCLM.map_tsum hsumm]
    simp
  · change 0 ≤ Complex.reCLM (∑' n,
        (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ))
    rw [Complex.reCLM.map_tsum hsumm]
    exact tsum_nonneg fun n ↦ Complex.normSq_nonneg _

/-!
## Remaining analytic boundary

The module does not hide the following RH-equivalent work:

* Fubini for the quadratic convolution at every zeta zero;
* an exhaustive analytic-multiplicity zero enumeration;
* the concrete prime/archimedean Bombieri functional and explicit formula;
* strict positivity for nonzero tests, using zero density versus Mellin
  exponential type;
* the Li-function truncation and smoothing argument for the converse.
-/

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
