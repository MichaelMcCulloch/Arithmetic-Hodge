import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoff

/-!
# Spectral limits of truncated Li kernels

Li cutoffs are real-valued, so coefficient conjugation turns their quadratic
spectral term into the direct/reflected Mellin product.  Pointwise at every
nontrivial zero, shrinking the cutoff recovers Bombieri's paired Li value.
The remaining cutoff problem is the uniform domination needed to exchange
this limit with the infinite zero sum.
-/

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Li cutoffs are real-valued. -/
theorem star_liKernelCutoff (n : ℕ) (epsilon x : ℝ) :
    starRingEnd ℂ (liKernelCutoff n epsilon x) =
      liKernelCutoff n epsilon x := by
  simp only [liKernelCutoff]
  split_ifs <;> simp

/-- Consequently coefficient conjugation fixes the Mellin transform of every
Li cutoff. -/
theorem coefficientConjugate_mellin_liKernelCutoff
    (n : ℕ) (epsilon : ℝ) (s : ℂ) :
    coefficientConjugate (mellin (liKernelCutoff n epsilon)) s =
      mellin (liKernelCutoff n epsilon) s := by
  rw [← mellin_conjugate]
  apply congrArg (fun f : ℝ → ℂ ↦ mellin f s)
  funext x
  exact star_liKernelCutoff n epsilon x

/-- The quadratic spectral term of a real Li cutoff is its direct/reflected
Mellin product. -/
theorem spectralTerm_liKernelCutoff
    (n : ℕ) (epsilon : ℝ) (s : ℂ) :
    spectralTerm (liKernelCutoff n epsilon) s =
      mellin (liKernelCutoff n epsilon) s *
        mellin (liKernelCutoff n epsilon) (1 - s) := by
  rw [spectralTerm,
    coefficientConjugate_mellin_liKernelCutoff]

/-- Pointwise form of Bombieri's cutoff limit: at every nontrivial zero, the
quadratic cutoff spectral term tends to the paired Li value. -/
theorem spectralTerm_liKernelCutoff_tendsto_li_pair
    (n : ℕ) (rho : NontrivialZetaZero)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ k, 0 ≤ epsilon k)
    (hepsilon0 : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto
      (fun k ↦ spectralTerm (liKernelCutoff n (epsilon k)) rho.val)
      atTop
      (𝓝 (liFunction n rho.val + liFunction n (1 - rho.val))) := by
  have hrho0 : rho.val ≠ 0 := by
    intro h
    have hp := rho.re_pos
    rw [h] at hp
    norm_num at hp
  have hrho1 : rho.val ≠ 1 := by
    intro h
    have hlt := rho.re_lt_one
    rw [h] at hlt
    norm_num at hlt
  have honeSubPos : 0 < (1 - rho.val).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [rho.re_lt_one]
  have hdirect := mellin_liKernelCutoff_tendsto_liFunction
    n rho.val rho.re_pos epsilon hepsilon hepsilon0
  have hreflected := mellin_liKernelCutoff_tendsto_liFunction
    n (1 - rho.val) honeSubPos epsilon hepsilon hepsilon0
  have hproduct := hdirect.mul hreflected
  rw [liFunction_mul_one_sub n rho.val hrho0 hrho1] at hproduct
  exact hproduct.congr'
    (Eventually.of_forall fun k ↦ by
      change mellin (liKernelCutoff n (epsilon k)) rho.val *
          mellin (liKernelCutoff n (epsilon k)) (1 - rho.val) =
        spectralTerm (liKernelCutoff n (epsilon k)) rho.val
      exact (spectralTerm_liKernelCutoff
        n (epsilon k) rho.val).symm)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
