import ArithmeticHodge.Analysis.ZetaZeroCount

set_option autoImplicit false

open Complex Filter Topology

namespace ArithmeticHodge.Analysis

theorem nontrivial_zeta_zero_re_scratch (s : ℂ)
    (hs_zero : riemannZeta s = 0)
    (hs_not_trivial : ¬ ∃ n : ℕ, s = -2 * (↑n + 1))
    (_hs_ne_one : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    push_neg at h
    have hs_ne_zero : s ≠ 0 := by
      intro heq
      rw [heq] at hs_zero
      simp [riemannZeta_zero] at hs_zero
    have hGamma_ne : Gammaℝ s ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff]
      push_neg
      intro n
      by_cases hn : n = 0
      · simp [hn]
        exact hs_ne_zero
      · intro heq
        apply hs_not_trivial
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact ⟨m, by rw [heq]; push_cast; ring⟩
    have hLambda_zero : completedRiemannZeta s = 0 := by
      have hdef := riemannZeta_def_of_ne_zero hs_ne_zero
      rw [hs_zero] at hdef
      rw [eq_comm, div_eq_zero_iff] at hdef
      exact hdef.resolve_right hGamma_ne
    have hLambda_one_sub : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]
      exact hLambda_zero
    have hre_one_sub : 1 ≤ (1 - s).re := by
      simp [Complex.sub_re, Complex.one_re]
      linarith
    have h1s_ne_zero : (1 : ℂ) - s ≠ 0 := by
      intro heq
      have : (1 - s).re = 0 := by rw [heq]; simp
      linarith
    have hzeta_one_sub : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s_ne_zero, hLambda_one_sub, zero_div]
    exact absurd hzeta_one_sub (riemannZeta_ne_zero_of_one_le_re hre_one_sub)
  · by_contra h
    push_neg at h
    exact absurd hs_zero (riemannZeta_ne_zero_of_one_le_re h)

def XiDivisorOnCriticalLine_scratch : Prop :=
  ∀ z : ℂ, 0 < xiZeroMultiplicity z → z.re = 1 / 2

theorem xiDivisorOnCriticalLine_iff_RH_scratch :
    XiDivisorOnCriticalLine_scratch ↔ RiemannHypothesis := by
  constructor
  · intro hline s hs_zero hs_not_trivial hs_ne_one
    have hre := nontrivial_zeta_zero_re_scratch s hs_zero hs_not_trivial hs_ne_one
    apply hline s
    exact (xiZeroMultiplicity_pos_iff s).mpr
      ((xiFunction_zero_iff hre.1 hre.2).mpr hs_zero)
  · intro hRH z hmult
    have hxi := (xiZeroMultiplicity_pos_iff z).mp hmult
    have hre := xiFunction_zero_re hxi
    have hzeta := (xiFunction_zero_iff hre.1 hre.2).mp hxi
    apply hRH z hzeta
    · rintro ⟨n, hn⟩
      rw [hn] at hre
      have htriv_re : (-2 * ((n : ℂ) + 1)).re =
          -2 * ((n : ℝ) + 1) := by
        simp [Complex.add_re, Complex.mul_re, Complex.neg_re,
          Complex.one_re, Complex.one_im]
      rw [htriv_re] at hre
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hz_one
      rw [hz_one] at hre
      norm_num at hre

theorem not_RH_iff_exists_xiZero_off_critical_line_scratch :
    ¬ RiemannHypothesis ↔
      ∃ z : ℂ, 0 < xiZeroMultiplicity z ∧ z.re ≠ 1 / 2 := by
  rw [← xiDivisorOnCriticalLine_iff_RH_scratch]
  simp [XiDivisorOnCriticalLine_scratch]

#print axioms nontrivial_zeta_zero_re_scratch
#print axioms xiDivisorOnCriticalLine_iff_RH_scratch
#print axioms not_RH_iff_exists_xiZero_off_critical_line_scratch

end ArithmeticHodge.Analysis
