import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false

open Complex Filter Topology Real MeasureTheory Nat

namespace ArithmeticHodge.Analysis

/-! ## The current local contour premises are vacuous -/

/-- The stated residue placeholder contains no contour information: it is
true for arbitrary proposed spectral and polar values. -/
theorem residue_placeholder_vacuous_scratch (spectral polar : ℝ) :
    ∃ rectIntegral : ℝ, spectral + polar = rectIntegral :=
  ⟨spectral + polar, rfl⟩

/-- Likewise, the prime/archimedean placeholder types are independent of
the terms they are intended to approximate. -/
theorem error_placeholder_vacuous_scratch (T : ℝ) (hT : 2 ≤ T) :
    ∃ epsilon : ℝ, |epsilon| ≤ 1 / T ∧ True := by
  refine ⟨0, ?_, trivial⟩
  simp
  positivity

/-! ## The documented algebra has the wrong polar sign -/

/-- The two equations documented in the assembly imply subtraction of the
polar contribution. -/
theorem contour_assembly_correct_polar_sign_scratch
    {spectral polar contour prime arch : ℝ}
    (hresidue : spectral + polar = contour)
    (hboundary : contour = prime + arch) :
    spectral = prime + arch - polar := by
  linarith

/-- A concrete counterexample to the documented jump from
`spectral + polar = contour = prime + arch` to a result that *adds* polar. -/
theorem contour_plus_polar_assembly_counterexample_scratch :
    ((0 : ℝ) + 1 = 1) ∧
      ((1 : ℝ) = 1 + 0) ∧
      ¬((0 : ℝ) = 1 + 0 + 1) := by
  norm_num

/-- A sound minimum limit interface for the final contour assembly.  Once
the residue equality, boundary decomposition, and all four limits are
actually supplied, the conclusion follows with the forced polar sign. -/
theorem contour_limit_assembly_scratch
    (spectral contour right left horizontal : ℕ → ℝ)
    (spectralLimit polar prime arch : ℝ)
    (hresidue : ∀ n, spectral n + polar = contour n)
    (hboundary : ∀ n, contour n = right n + left n + horizontal n)
    (hspectral : Tendsto spectral atTop (nhds spectralLimit))
    (hright : Tendsto right atTop (nhds prime))
    (hleft : Tendsto left atTop (nhds arch))
    (hhorizontal : Tendsto horizontal atTop (nhds 0)) :
    spectralLimit = prime + arch - polar := by
  have hpoint : ∀ n,
      spectral n = right n + left n + horizontal n - polar := by
    intro n
    linarith [hresidue n, hboundary n]
  have hcombined :
      Tendsto (fun n => right n + left n + horizontal n - polar)
        atTop (nhds (prime + arch + 0 - polar)) :=
    ((hright.add hleft).add hhorizontal).sub_const polar
  have hspectral' :
      Tendsto (fun n => right n + left n + horizontal n - polar)
        atTop (nhds spectralLimit) :=
    hspectral.congr' (Eventually.of_forall fun n => hpoint n)
  have hlimits := tendsto_nhds_unique hspectral' hcombined
  linarith

/-! ## The admitted test class does not support the claimed holomorphic step -/

/-- A continuous, quadratically decaying test function with a cusp at zero. -/
noncomputable def cuspWeilTest (x : ℝ) : ℝ :=
  |x| / (1 + x ^ 2) ^ 2

theorem continuous_cuspWeilTest_scratch : Continuous cuspWeilTest := by
  unfold cuspWeilTest
  apply Continuous.div continuous_abs
    ((continuous_const.add (continuous_id.pow 2)).pow 2)
  intro x
  exact pow_ne_zero 2 (ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2))

theorem cuspWeilTest_decay_scratch (x : ℝ) :
    ‖cuspWeilTest x‖ ≤ 1 / (1 + x ^ 2) := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  have habs : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  rw [cuspWeilTest, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg x) (sq_nonneg _))]
  calc
    |x| / (1 + x ^ 2) ^ 2 ≤ (1 + x ^ 2) / (1 + x ^ 2) ^ 2 := by
      exact div_le_div_of_nonneg_right habs (sq_nonneg _)
    _ = 1 / (1 + x ^ 2) := by field_simp

/-- The same test is not differentiable at zero, hence the theorem's stated
assumptions cannot justify treating `h` itself as the restriction of a
holomorphic contour test function. -/
theorem not_differentiableAt_cuspWeilTest_zero_scratch :
    ¬ DifferentiableAt ℝ cuspWeilTest 0 := by
  intro hdiff
  have hpoly : DifferentiableAt ℝ (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 := by
    fun_prop
  have hprod := hdiff.mul hpoly
  change DifferentiableAt ℝ (fun x : ℝ =>
    cuspWeilTest x * (1 + x ^ 2) ^ 2) 0 at hprod
  have heq :
      (fun x : ℝ => cuspWeilTest x * (1 + x ^ 2) ^ 2) = abs := by
    funext x
    rw [cuspWeilTest]
    field_simp
  rw [heq] at hprod
  exact not_differentiableAt_abs_zero hprod

/-! ## The implemented archimedean kernel is a log-Gamma value -/

/-- Contrary to its docstring, the current kernel is `log |Gamma| + log pi`,
not the real part of the digamma/logarithmic derivative. -/
theorem archimedeanKernel_eq_log_norm_Gamma_scratch (t : ℝ) :
    archimedeanKernel t =
      Real.log ‖Complex.Gamma (1 / 4 + Complex.I * t / 2)‖ + Real.log Real.pi := by
  rw [archimedeanKernel, Complex.log_re]

/-- The local factor's actual logarithmic-derivative kernel, in the current
normalization. -/
noncomputable def digammaArchimedeanKernel (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + Complex.I * t / 2)).re - Real.log Real.pi

theorem digammaArchimedeanKernel_algebra_scratch (t : ℝ) :
    digammaArchimedeanKernel t =
      2 * (-(Real.log Real.pi : ℂ) / 2 +
        Complex.digamma (1 / 4 + Complex.I * t / 2) / 2).re := by
  simp [digammaArchimedeanKernel]
  ring

#print axioms residue_placeholder_vacuous_scratch
#print axioms error_placeholder_vacuous_scratch
#print axioms contour_assembly_correct_polar_sign_scratch
#print axioms contour_limit_assembly_scratch
#print axioms continuous_cuspWeilTest_scratch
#print axioms cuspWeilTest_decay_scratch
#print axioms not_differentiableAt_cuspWeilTest_zero_scratch
#print axioms archimedeanKernel_eq_log_norm_Gamma_scratch
#print axioms digammaArchimedeanKernel_algebra_scratch

end ArithmeticHodge.Analysis
