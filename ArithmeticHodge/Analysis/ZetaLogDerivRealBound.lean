import ArithmeticHodge.Analysis.ZetaLogDerivPositivity
import ArithmeticHodge.Analysis.ZetaNearOneBound

set_option autoImplicit false

open Complex Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The digamma factor is uniformly bounded on the real interval traversed
by `s / 2` when `1 ≤ s ≤ 2`. -/
theorem exists_digamma_half_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ,
      1 ≤ sigma → sigma ≤ 2 →
        ‖Complex.digamma (sigma / 2)‖ ≤ C := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU_open : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hGamma_diff : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hzpos : 0 < z.re := hz
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGamma_ne : ∀ z ∈ U, Complex.Gamma z ≠ 0 := by
    intro z hz
    exact Complex.Gamma_ne_zero_of_re_pos hz
  have hdigamma_cont : ContinuousOn Complex.digamma U := by
    simpa only [Complex.digamma_def, logDeriv, Pi.div_apply] using
      (hGamma_diff.deriv hU_open).continuousOn.div
        hGamma_diff.continuousOn hGamma_ne
  let K : Set ℂ := Set.Icc (1 / 2 : ℝ) 1 ×ℂ Set.Icc 0 0
  have hK_compact : IsCompact K :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K ⊆ U := by
    intro z hz
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hz.1.1
  have hbounded : BddAbove ((fun z : ℂ => ‖Complex.digamma z‖) '' K) :=
    hK_compact.bddAbove_image ((hdigamma_cont.mono hK_sub).norm)
  rw [bddAbove_def] at hbounded
  obtain ⟨M, hM⟩ := hbounded
  refine ⟨|M| + 1, by positivity, fun sigma hsigma1 hsigma2 => ?_⟩
  have hzK : ((sigma / 2 : ℝ) : ℂ) ∈ K := by
    rw [show K = Set.Icc (1 / 2 : ℝ) 1 ×ℂ Set.Icc 0 0 by rfl,
      mem_reProdIm]
    constructor
    · simp only [Complex.ofReal_re, mem_Icc]
      constructor <;> linarith
    · simp only [Complex.ofReal_im, mem_Icc]
      exact ⟨le_rfl, le_rfl⟩
  have hMbound : ‖Complex.digamma ((sigma / 2 : ℝ) : ℂ)‖ ≤ M :=
    hM _ ⟨((sigma / 2 : ℝ) : ℂ), hzK, rfl⟩
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    hMbound.trans (by linarith [le_abs_self M])

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

