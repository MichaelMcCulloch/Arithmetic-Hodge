import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma
import ArithmeticHodge.Analysis.ZetaFunctionalLogDerivative

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

private theorem digamma_conj_of_pos_re (s : ℂ) (hs : 0 < s.re) :
    Complex.digamma (starRingEnd ℂ s) =
      starRingEnd ℂ (Complex.digamma s) := by
  have hsconj : 0 < (starRingEnd ℂ s).re := by simpa using hs
  rw [digamma_eq_tsum_of_pos_re _ hsconj,
    digamma_eq_tsum_of_pos_re _ hs]
  simp only [one_div, map_neg, map_add, map_sub, map_inv₀,
    map_natCast, conj_ofReal, Complex.conj_tsum]

theorem bombieri_digamma_critical_pair_scratch (v : ℝ) :
    -(Real.log Real.pi : ℂ) +
        Complex.digamma (((1 / 2 : ℝ) + v * I) / 2) / 2 +
        Complex.digamma ((1 - ((1 / 2 : ℝ) + v * I)) / 2) / 2 =
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) := by
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * I
  have hzre : 0 < z.re := by simp [z]
  have hconj := digamma_conj_of_pos_re z hzre
  have hfirst : (((1 / 2 : ℝ) + v * I) / 2 : ℂ) = z := by
    simp only [z]
    push_cast
    ring
  have hvhalf : starRingEnd ℂ ((v : ℂ) / 2) =
      ((v / 2 : ℝ) : ℂ) := by
    rw [map_div₀, conj_ofReal, map_ofNat]
    push_cast
    rfl
  have hsecond : ((1 - ((1 / 2 : ℝ) + v * I)) / 2 : ℂ) =
      starRingEnd ℂ z := by
    rw [show starRingEnd ℂ z =
        ((1 / 4 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * I by
      simp only [z, map_add, map_mul, conj_ofReal, conj_I]
      rw [hvhalf]
      ring]
    push_cast
    ring
  change -(Real.log Real.pi : ℂ) +
        Complex.digamma (((1 / 2 : ℝ) + v * I) / 2) / 2 +
        Complex.digamma ((1 - ((1 / 2 : ℝ) + v * I)) / 2) / 2 =
      (((Complex.digamma z).re - Real.log Real.pi : ℝ) : ℂ)
  rw [hfirst, hsecond, hconj]
  apply Complex.ext <;> simp <;> ring

theorem bombieri_neg_zeta_logDeriv_critical_pair_scratch
    (v : ℝ)
    (hzeta : riemannZeta ((1 / 2 : ℝ) + v * I) ≠ 0)
    (hzetaOneSub :
      riemannZeta (1 - ((1 / 2 : ℝ) + v * I)) ≠ 0) :
    -(deriv riemannZeta ((1 / 2 : ℝ) + v * I) /
        riemannZeta ((1 / 2 : ℝ) + v * I)) -
      deriv riemannZeta (1 - ((1 / 2 : ℝ) + v * I)) /
        riemannZeta (1 - ((1 / 2 : ℝ) + v * I)) =
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) := by
  let s : ℂ := (1 / 2 : ℝ) + v * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  rw [show -(deriv riemannZeta s / riemannZeta s) -
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) =
        -(Real.log Real.pi : ℂ) + Complex.digamma (s / 2) / 2 +
          Complex.digamma ((1 - s) / 2) / 2 by
    exact ArithmeticHodge.Analysis.neg_zeta_logDeriv_functional_pair
      s hs0 hs1 hzeta hzetaOneSub]
  exact bombieri_digamma_critical_pair_scratch v

#print axioms bombieri_digamma_critical_pair_scratch
#print axioms bombieri_neg_zeta_logDeriv_critical_pair_scratch

end ArithmeticHodge.Analysis.MultiplicativeWeil
