/-
  The symmetric real-gamma factor on the critical line.

  Euler's convergent digamma series commutes with complex conjugation on the
  positive half-plane.  At `s = 1/2 + iv`, the two functional-equation gamma
  terms therefore combine to `Re psi(1/4 + iv/2) - log pi`, exactly the
  integrand evaluated by the Bombieri archimedean calculation.
-/

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

/-- On the critical line, the paired digamma correction in the zeta
functional equation is the real-part gamma kernel minus `log pi`. -/
theorem bombieri_digamma_critical_pair (v : ℝ) :
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

end ArithmeticHodge.Analysis.MultiplicativeWeil
