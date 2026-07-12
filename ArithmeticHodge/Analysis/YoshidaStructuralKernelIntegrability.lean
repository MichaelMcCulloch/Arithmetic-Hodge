import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability

noncomputable section

open YoshidaRenormalizedGeometricKernel

/-!
# Structural integrability for the renormalized Yoshida kernel

These lemmas isolate the removable singularities of the odd and reference
kernels by holomorphic divided slopes.  They use no mode enumeration,
rational enclosure, or finite certificate.
-/

private theorem complex_dslope_zero_differentiable
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  intro z
  have hOn : DifferentiableOn ℂ (dslope f 0) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).2
      hf.differentiableOn
  exact hOn.differentiableAt (by simp)

private def complexExpTwoCore (z : ℂ) : ℂ := Complex.exp (2 * z) - 1

private def complexExpThreeHalfCore (z : ℂ) : ℂ :=
  Complex.exp ((3 / 2 : ℂ) * z) - 1

private def complexReferenceCore (z : ℂ) : ℂ :=
  Complex.exp (2 * z) - 1 - 2 * z

private theorem complexExpTwoCore_differentiable :
    Differentiable ℂ complexExpTwoCore := by
  unfold complexExpTwoCore
  fun_prop

private theorem complexExpThreeHalfCore_differentiable :
    Differentiable ℂ complexExpThreeHalfCore := by
  unfold complexExpThreeHalfCore
  fun_prop

private theorem complexReferenceCore_differentiable :
    Differentiable ℂ complexReferenceCore := by
  unfold complexReferenceCore
  fun_prop

private theorem complexExpTwoCore_deriv_zero :
    deriv complexExpTwoCore 0 = 2 := by
  have hlin : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul 2
  have h := hlin.cexp.sub_const 1
  change deriv (fun z : ℂ ↦ Complex.exp (2 * z) - 1) 0 = 2
  (convert h.deriv using 1; norm_num)

private theorem complexReferenceCore_deriv_zero :
    deriv complexReferenceCore 0 = 0 := by
  have hlin : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul 2
  have hexp := hlin.cexp
  have h := (hexp.sub_const 1).sub hlin
  change deriv (fun z : ℂ ↦ Complex.exp (2 * z) - 1 - 2 * z) 0 = 0
  (convert h.deriv using 1; norm_num)

private def complexExpTwoSlope : ℂ → ℂ := dslope complexExpTwoCore 0

private def complexExpThreeHalfSlope : ℂ → ℂ :=
  dslope complexExpThreeHalfCore 0

private def complexReferenceSecondSlope : ℂ → ℂ :=
  dslope (dslope complexReferenceCore 0) 0

private theorem complexExpTwoSlope_differentiable :
    Differentiable ℂ complexExpTwoSlope :=
  complex_dslope_zero_differentiable complexExpTwoCore_differentiable

private theorem complexExpThreeHalfSlope_differentiable :
    Differentiable ℂ complexExpThreeHalfSlope :=
  complex_dslope_zero_differentiable complexExpThreeHalfCore_differentiable

private theorem complexReferenceSecondSlope_differentiable :
    Differentiable ℂ complexReferenceSecondSlope :=
  complex_dslope_zero_differentiable
    (complex_dslope_zero_differentiable complexReferenceCore_differentiable)

private theorem complexExpTwoCore_ofReal (u : ℝ) :
    complexExpTwoCore (u : ℂ) = (Real.exp (2 * u) - 1 : ℝ) := by
  rw [complexExpTwoCore]
  have harg : (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

private theorem complexExpThreeHalfCore_ofReal (u : ℝ) :
    complexExpThreeHalfCore (u : ℂ) =
      (Real.exp ((3 / 2 : ℝ) * u) - 1 : ℝ) := by
  rw [complexExpThreeHalfCore]
  have harg : (3 / 2 : ℂ) * (u : ℂ) =
      (((3 / 2 : ℝ) * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

private theorem complexReferenceCore_ofReal (u : ℝ) :
    complexReferenceCore (u : ℂ) =
      (Real.exp (2 * u) - 1 - 2 * u : ℝ) := by
  rw [complexReferenceCore]
  have harg : (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

private theorem complexExpTwoSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexExpTwoSlope (u : ℂ) =
      ((Real.exp (2 * u) - 1) / u : ℝ) := by
  rw [complexExpTwoSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexExpTwoCore_ofReal]
  simp [complexExpTwoCore]
  rw [div_eq_mul_inv]
  ring

private theorem complexExpThreeHalfSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexExpThreeHalfSlope (u : ℂ) =
      ((Real.exp ((3 / 2 : ℝ) * u) - 1) / u : ℝ) := by
  rw [complexExpThreeHalfSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexExpThreeHalfCore_ofReal]
  simp [complexExpThreeHalfCore]
  rw [div_eq_mul_inv]
  ring

private theorem complexReferenceSecondSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexReferenceSecondSlope (u : ℂ) =
      ((Real.exp (2 * u) - 1 - 2 * u) / u ^ 2 : ℝ) := by
  rw [complexReferenceSecondSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [dslope_same, complexReferenceCore_deriv_zero]
  rw [dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexReferenceCore_ofReal]
  simp [complexReferenceCore]
  field_simp [hu]

private theorem complexExpTwoSlope_ofReal_ne (u : ℝ) :
    complexExpTwoSlope (u : ℂ) ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    change complexExpTwoSlope (0 : ℂ) ≠ 0
    rw [complexExpTwoSlope, dslope_same, complexExpTwoCore_deriv_zero]
    norm_num
  · rw [complexExpTwoSlope_ofReal hu]
    have hnum : Real.exp (2 * u) - 1 ≠ 0 := by
      intro h
      have heq : Real.exp (2 * u) = Real.exp 0 := by
        simpa only [sub_eq_zero, Real.exp_zero] using h
      have : 2 * u = 0 := Real.exp_injective heq
      exact hu (by linarith)
    exact_mod_cast div_ne_zero hnum hu

private theorem oddKernel_eq_alt {u : ℝ} (hu : u ≠ 0) :
    oddKernel u =
      2 * Real.exp ((3 / 2 : ℝ) * u) / (Real.exp (2 * u) - 1) := by
  have hden1 : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    exact hu (by linarith [Real.exp_injective heq])
  have hden2 : Real.exp (2 * u) - 1 ≠ 0 := by
    intro h
    have heq : Real.exp (2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using h
    exact hu (by linarith [Real.exp_injective heq])
  have hhalf : Real.exp ((3 / 2 : ℝ) * u) =
      Real.exp (u / 2) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htwo : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
  have hinv : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [oddKernel]
  field_simp [hden1, hden2]
  rw [show u * 3 / 2 = (3 / 2 : ℝ) * u by ring, hhalf, htwo]
  rw [← hinv]
  ring

private theorem referenceKernel_eq_alt {u : ℝ} (hu : u ≠ 0) :
    referenceKernel u = 2 / (Real.exp (2 * u) - 1) := by
  have hden1 : 1 - Real.exp (-2 * u) ≠ 0 := by
    intro h
    have heq : Real.exp (-2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using (sub_eq_zero.mp h).symm
    exact hu (by linarith [Real.exp_injective heq])
  have hden2 : Real.exp (2 * u) - 1 ≠ 0 := by
    intro h
    have heq : Real.exp (2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using h
    exact hu (by linarith [Real.exp_injective heq])
  have hinv : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [referenceKernel]
  apply (div_eq_div_iff hden1 hden2).2
  nlinarith

private theorem ofReal_div_re (a b : ℝ) :
    (((a : ℂ) / (b : ℂ)).re) = a / b := by
  rw [← Complex.ofReal_div]
  simp

private def uOddKernelSurrogate (u : ℝ) : ℝ :=
  (((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

private def kernelDifferenceSurrogate (u : ℝ) : ℝ :=
  (2 * complexExpThreeHalfSlope (u : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

private def referenceRegularizedSurrogate (u : ℝ) : ℝ :=
  (complexReferenceSecondSlope (u : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

private theorem continuous_uOddKernelSurrogate :
    Continuous uOddKernelSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      ((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ)) := by
    fun_prop
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      ((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

private theorem continuous_kernelDifferenceSurrogate :
    Continuous kernelDifferenceSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      2 * complexExpThreeHalfSlope (u : ℂ)) := by
    exact continuous_const.mul
      (complexExpThreeHalfSlope_differentiable.continuous.comp
        Complex.continuous_ofReal)
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      2 * complexExpThreeHalfSlope (u : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

private theorem continuous_referenceRegularizedSurrogate :
    Continuous referenceRegularizedSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      complexReferenceSecondSlope (u : ℂ)) :=
    complexReferenceSecondSlope_differentiable.continuous.comp
      Complex.continuous_ofReal
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      complexReferenceSecondSlope (u : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

private theorem exp_two_sub_one_ne {u : ℝ} (hu : u ≠ 0) :
    Real.exp (2 * u) - 1 ≠ 0 := by
  intro h
  have heq : Real.exp (2 * u) = Real.exp 0 := by
    simpa only [sub_eq_zero, Real.exp_zero] using h
  exact hu (by linarith [Real.exp_injective heq])

private theorem uOddKernelSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    uOddKernelSurrogate u = u * oddKernel u := by
  rw [uOddKernelSurrogate, complexExpTwoSlope_ofReal hu,
    ofReal_div_re, oddKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

private theorem kernelDifferenceSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    kernelDifferenceSurrogate u = oddKernel u - referenceKernel u := by
  rw [kernelDifferenceSurrogate,
    complexExpThreeHalfSlope_ofReal hu, complexExpTwoSlope_ofReal hu]
  rw [show (2 : ℂ) *
      (((Real.exp ((3 / 2 : ℝ) * u) - 1) / u : ℝ) : ℂ) =
      (((2 * ((Real.exp ((3 / 2 : ℝ) * u) - 1) / u) : ℝ) : ℂ)) by
    push_cast
    ring]
  rw [ofReal_div_re, oddKernel_eq_alt hu, referenceKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

private theorem referenceRegularizedSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    referenceRegularizedSurrogate u = referenceRegularized u := by
  rw [referenceRegularizedSurrogate,
    complexReferenceSecondSlope_ofReal hu, complexExpTwoSlope_ofReal hu,
    ofReal_div_re, referenceRegularized, referenceKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

private theorem ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  simp [ae_iff, measure_singleton]

theorem referenceRegularized_intervalIntegrable (L : ℝ) :
    IntervalIntegrable referenceRegularized volume 0 L := by
  have hsur : IntervalIntegrable referenceRegularizedSurrogate volume 0 L :=
    Continuous.intervalIntegrable continuous_referenceRegularizedSurrogate 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  exact referenceRegularizedSurrogate_eq hu

theorem kernelDifference_intervalIntegrable (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u - referenceKernel u)
      volume 0 L := by
  have hsur : IntervalIntegrable kernelDifferenceSurrogate volume 0 L :=
    Continuous.intervalIntegrable continuous_kernelDifferenceSurrogate 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  exact kernelDifferenceSurrogate_eq hu

theorem oddKernel_mul_u_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u * (u * D u)) volume 0 L := by
  have hsur : IntervalIntegrable
      (fun u : ℝ ↦ uOddKernelSurrogate u * D u) volume 0 L :=
    Continuous.intervalIntegrable (continuous_uOddKernelSurrogate.mul hD) 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  rw [uOddKernelSurrogate_eq hu]
  ring

theorem oddKernel_mul_u_abs_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u * (u * |D u|)) volume 0 L := by
  exact oddKernel_mul_u_intervalIntegrable hD.abs L

theorem removableMajorantLimit_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (C0 L : ℝ) :
    IntervalIntegrable (removableMajorantLimit C0 D) volume 0 L := by
  rw [show removableMajorantLimit C0 D = fun u : ℝ ↦
      oddKernel u * (u * |D u|) +
        |C0| * (oddKernel u - referenceKernel u) by rfl]
  exact (oddKernel_mul_u_abs_intervalIntegrable hD L).add
    ((kernelDifference_intervalIntegrable L).const_mul |C0|)

theorem stableGeometricIntegrand_intervalIntegrable_of_removable
    {C D : ℝ → ℝ} (hD : Continuous D) (C0 L : ℝ)
    (hrem : ∀ u : ℝ, C u = C0 + u * D u) :
    IntervalIntegrable (stableGeometricIntegrand C0 C) volume 0 L := by
  have hmain := oddKernel_mul_u_intervalIntegrable hD L
  have hcorr := (kernelDifference_intervalIntegrable L).sub
    (referenceRegularized_intervalIntegrable L)
  have hsum := hmain.add (hcorr.const_mul C0)
  apply hsum.congr
  intro u _hu
  unfold stableGeometricIntegrand referenceRegularized
  rw [hrem u]
  ring

end

end ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability
