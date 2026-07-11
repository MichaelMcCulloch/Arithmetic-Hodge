import ArithmeticHodge.Analysis.ZetaProduct
import ArithmeticHodge.Analysis.ZetaLogDerivPositivity

/-!
# Hadamard-zero repulsion for the zeta logarithmic derivative

This file proves the partial-fraction half of the classical
de la Vallee-Poussin zero-repulsion argument.  It first verifies that the
chosen Hadamard sequence covers every nontrivial zeta zero, then isolates one
zero in the real part of the absolutely convergent zero sum.
-/

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Every nontrivial zeta zero occurs in the zero sequence selected by the
Hadamard factorization. -/
theorem nontrivialZetaZero_mem_hadamardZeros
    (rho : NontrivialZetaZero) :
    ∃ n : ℕ, hadamardZeros n = rho.val := by
  have hxi : xiFunction rho.val = 0 :=
    (xiFunction_zero_iff rho.re_pos rho.re_lt_one).2 rho.is_zero
  have hrho0 : rho.val ≠ 0 := by
    intro hzero
    have hrepos := rho.re_pos
    rw [hzero] at hrepos
    simp at hrepos
  by_contra hmem
  push_neg at hmem
  have hconv : Summable
      (fun n => (‖hadamardZeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
    convert hadamardZeros_summable_inv_sq using 1
    all_goals norm_num
  have hproduct :
      ∏' n, EntireFunction.weierstraßElementary 1
        (rho.val / hadamardZeros n) ≠ 0 := by
    apply EntireFunction.tprod_weierstraßElementary_ne_zero
      hadamardZeros 1 hconv rho.val
    intro n hdiv
    have heq : rho.val = hadamardZeros n :=
      (div_eq_one_iff_eq (hadamardZeros_ne_zero n)).mp hdiv
    exact hmem n heq.symm
  have hfactor_ne :
      rho.val ^ hadamardM *
          Complex.exp (hadamardA + hadamardB * rho.val) *
          ∏' n, EntireFunction.weierstraßElementary 1
            (rho.val / hadamardZeros n) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (pow_ne_zero hadamardM hrho0) (Complex.exp_ne_zero _))
      hproduct
  rw [xi_hadamard_product_eq rho.val] at hxi
  exact hfactor_ne hxi

/-- Every genus-one partial-fraction term has nonnegative real part to the
right of the critical strip. -/
theorem hadamardPartialFractionTerm_re_nonneg
    {sigma t : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ (1 / (((sigma : ℂ) + t * I) - hadamardZeros n) +
      1 / hadamardZeros n).re := by
  have hre := hadamardZeros_re n
  have hdiff : ((sigma : ℂ) + t * I) - hadamardZeros n ≠ 0 := by
    intro hzero
    have hzre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero, Complex.zero_re] at hzre
    linarith
  have hdiffNorm : 0 < Complex.normSq
      (((sigma : ℂ) + t * I) - hadamardZeros n) :=
    Complex.normSq_pos.mpr hdiff
  have hrhoNorm : 0 < Complex.normSq (hadamardZeros n) :=
    Complex.normSq_pos.mpr (hadamardZeros_ne_zero n)
  simp only [one_div, Complex.add_re, Complex.inv_re,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_self, add_zero]
  exact add_nonneg
    (div_nonneg (by linarith) hdiffNorm.le)
    (div_nonneg hre.1.le hrhoNorm.le)

/-- At the ordinate of a chosen zero, its own partial-fraction term contributes
at least the reciprocal horizontal gap. -/
theorem chosenZeroPartialFractionTerm_re_ge_inv_gap
    (rho : NontrivialZetaZero) {sigma : ℝ} (hsigma : 1 < sigma) :
    1 / (sigma - rho.val.re) ≤
      (1 / (((sigma : ℂ) + rho.val.im * I) - rho.val) +
        1 / rho.val).re := by
  have hgap : 0 < sigma - rho.val.re := by
    linarith [rho.re_lt_one]
  have hdiff :
      ((sigma : ℂ) + rho.val.im * I) - rho.val =
        ((sigma - rho.val.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hrho0 : rho.val ≠ 0 := by
    intro hzero
    have hrepos := rho.re_pos
    rw [hzero] at hrepos
    simp at hrepos
  have hrhoNorm : 0 < Complex.normSq rho.val :=
    Complex.normSq_pos.mpr hrho0
  have hinvNonneg : 0 ≤ (1 / rho.val).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg rho.re_pos.le hrhoNorm.le
  rw [hdiff, Complex.add_re]
  have hrealInv :
      (1 / (((sigma - rho.val.re : ℝ) : ℂ))).re =
        1 / (sigma - rho.val.re) := by
    rw [one_div, Complex.inv_re, Complex.normSq_ofReal]
    simp only [Complex.ofReal_re]
    field_simp [hgap.ne']
  rw [hrealInv]
  exact le_add_of_nonneg_right hinvNonneg

/-- The real part of the full absolutely convergent Hadamard zero sum is at
least the reciprocal gap contributed by any chosen nontrivial zero. -/
theorem hadamardZeroSum_re_ge_inv_gap
    (rho : NontrivialZetaZero) {sigma : ℝ} (hsigma : 1 < sigma) :
    1 / (sigma - rho.val.re) ≤
      (∑' n, (1 /
          (((sigma : ℂ) + rho.val.im * I) - hadamardZeros n) +
        1 / hadamardZeros n)).re := by
  let s : ℂ := (sigma : ℂ) + rho.val.im * I
  have hs0 : s ≠ 0 := by
    intro hzero
    have hzre := congrArg Complex.re hzero
    simp [s] at hzre
    linarith
  have hsep : ∀ n, s ≠ hadamardZeros n := by
    intro n heq
    have hreEq := congrArg Complex.re heq
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_self, add_zero] at hreEq
    linarith [(hadamardZeros_re n).2]
  obtain ⟨hsumm, _hxi⟩ := xi_logDeriv_expansion s hs0 hsep
  have hreSumm : Summable (fun n =>
      (1 / (s - hadamardZeros n) + 1 / hadamardZeros n).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  obtain ⟨k, hk⟩ := nontrivialZetaZero_mem_hadamardZeros rho
  have hfinite := hreSumm.sum_le_tsum {k} (fun n _hn => by
    exact hadamardPartialFractionTerm_re_nonneg hsigma n)
  rw [Complex.re_tsum hsumm]
  calc
    1 / (sigma - rho.val.re) ≤
        (1 / (((sigma : ℂ) + rho.val.im * I) - rho.val) +
          1 / rho.val).re :=
      chosenZeroPartialFractionTerm_re_ge_inv_gap rho hsigma
    _ = (1 / (s - hadamardZeros k) + 1 / hadamardZeros k).re := by
      rw [hk]
    _ = ∑ n ∈ ({k} : Finset ℕ),
        (1 / (s - hadamardZeros n) + 1 / hadamardZeros n).re := by simp
    _ ≤ ∑' n,
        (1 / (s - hadamardZeros n) + 1 / hadamardZeros n).re := hfinite

/-- Explicit chosen-zero repulsion inequality for the real part of
`-ζ'/ζ`.  The selected zero contributes `-1/(sigma - beta)`; every other
Hadamard term has the same favorable sign. -/
theorem negZetaLogDeriv_re_le_chosenZero
    (rho : NontrivialZetaZero) {sigma : ℝ} (hsigma : 1 < sigma) :
    (-(deriv riemannZeta
        ((sigma : ℂ) + rho.val.im * I) /
      riemannZeta ((sigma : ℂ) + rho.val.im * I))).re ≤
      (-(hadamardM : ℂ) /
          ((sigma : ℂ) + rho.val.im * I) - hadamardB +
        1 / ((sigma : ℂ) + rho.val.im * I) +
        1 / (((sigma : ℂ) + rho.val.im * I) - 1) -
        (Real.log Real.pi : ℂ) / 2 +
        Complex.digamma
          (((sigma : ℂ) + rho.val.im * I) / 2) / 2).re -
          1 / (sigma - rho.val.re) := by
  let s : ℂ := (sigma : ℂ) + rho.val.im * I
  let zeroSum : ℂ := ∑' n,
    (1 / (s - hadamardZeros n) + 1 / hadamardZeros n)
  let correction : ℂ :=
    -(hadamardM : ℂ) / s - hadamardB + 1 / s +
      1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
      Complex.digamma (s / 2) / 2
  have hsre : 1 < s.re := by simp [s]; exact hsigma
  have hs0 : s ≠ 0 := by
    intro hzero
    have hzre := congrArg Complex.re hzero
    simp [s] at hzre
    linarith
  have hs1 : s ≠ 1 := by
    intro hone
    have hzre := congrArg Complex.re hone
    simp [s] at hzre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsre
  have hsep : ∀ n, s ≠ hadamardZeros n := by
    intro n heq
    have hreEq := congrArg Complex.re heq
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_self, add_zero] at hreEq
    linarith [(hadamardZeros_re n).2]
  obtain ⟨_hsumm, hpf⟩ :=
    zeta_logDeriv_partial_fraction_explicit s hs1 hs0 hzeta hsep
  have hsumLower :
      1 / (sigma - rho.val.re) ≤ zeroSum.re := by
    simpa only [s, zeroSum] using
      hadamardZeroSum_re_ge_inv_gap rho hsigma
  have heq :
      -(deriv riemannZeta s / riemannZeta s) =
        correction - zeroSum := by
    rw [hpf]
    dsimp only [correction, zeroSum]
    ring
  have hreEq := congrArg Complex.re heq
  simp only [Complex.sub_re] at hreEq
  change (-(deriv riemannZeta s / riemannZeta s)).re ≤
    correction.re - 1 / (sigma - rho.val.re)
  linarith

/-- The classical `3-4-1` positivity inequality combined with the selected
Hadamard pole.  This is the repulsion half of the de la Vallee-Poussin
argument, with every constant and archimedean term still explicit. -/
theorem trig341_chosenZero_repulsion
    (rho : NontrivialZetaZero) {sigma : ℝ} (hsigma : 1 < sigma) :
    4 / (sigma - rho.val.re) ≤
      3 * (-(deriv riemannZeta (sigma : ℂ) /
        riemannZeta (sigma : ℂ))).re +
      4 * (-(hadamardM : ℂ) /
          ((sigma : ℂ) + rho.val.im * I) - hadamardB +
        1 / ((sigma : ℂ) + rho.val.im * I) +
        1 / (((sigma : ℂ) + rho.val.im * I) - 1) -
        (Real.log Real.pi : ℂ) / 2 +
        Complex.digamma
          (((sigma : ℂ) + rho.val.im * I) / 2) / 2).re +
      (-(deriv riemannZeta
          ((sigma : ℂ) + (2 * rho.val.im) * I) /
        riemannZeta
          ((sigma : ℂ) + (2 * rho.val.im) * I))).re := by
  have hpos := negZetaLogDeriv_trig_nonneg hsigma rho.val.im
  have hchosen := negZetaLogDeriv_re_le_chosenZero rho hsigma
  rw [show 4 / (sigma - rho.val.re) =
    4 * (1 / (sigma - rho.val.re)) by ring]
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

