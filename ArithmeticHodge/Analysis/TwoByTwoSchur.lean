import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.TwoByTwoSchur

/-- Scalar low--tail Schur closure.  A nonnegative low block and tail block
remain nonnegative after adding their mixed term when the exact determinant
bound holds. -/
theorem scalar_low_tail_nonneg
    (low tail mixed : ℝ)
    (hlow : 0 ≤ low) (htail : 0 ≤ tail)
    (hschur : mixed ^ 2 ≤ low * tail) :
    0 ≤ low + 2 * mixed + tail := by
  by_cases hmixed : 0 ≤ mixed
  · positivity
  · have hmixedNeg : mixed < 0 := lt_of_not_ge hmixed
    have hright : 0 < low + tail - 2 * mixed := by linarith
    have hprod : 0 ≤
        (low + 2 * mixed + tail) * (low + tail - 2 * mixed) := by
      nlinarith [sq_nonneg (low - tail)]
    exact nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hprod) hright

/-- Two determinant bounds with the same nonnegative cross scaling may be
added without loss.  This is the scalar form of closure of positive
semidefinite `2 × 2` matrices under addition.  Keeping the common factor
`delta` explicit avoids introducing square roots when `delta = 1 - a^2` in
a disk--Schur argument. -/
theorem scaled_determinant_bound_add
    (delta e₁ o₁ j₁ e₂ o₂ j₂ : ℝ)
    (hdelta : 0 ≤ delta)
    (he₁ : 0 ≤ e₁) (ho₁ : 0 ≤ o₁)
    (he₂ : 0 ≤ e₂) (ho₂ : 0 ≤ o₂)
    (h₁ : delta * j₁ ^ 2 ≤ 4 * e₁ * o₁)
    (h₂ : delta * j₂ ^ 2 ≤ 4 * e₂ * o₂) :
    delta * (j₁ + j₂) ^ 2 ≤
      4 * (e₁ + e₂) * (o₁ + o₂) := by
  have hleft₁ : 0 ≤ delta * j₁ ^ 2 :=
    mul_nonneg hdelta (sq_nonneg j₁)
  have hleft₂ : 0 ≤ delta * j₂ ^ 2 :=
    mul_nonneg hdelta (sq_nonneg j₂)
  have hright₁ : 0 ≤ 4 * e₁ * o₁ := by positivity
  have hproduct := mul_le_mul h₁ h₂ hleft₂ hright₁
  have hcrossBase :
      4 * (e₁ * o₁ * e₂ * o₂) ≤
        (e₁ * o₂ + e₂ * o₁) ^ 2 := by
    nlinarith [sq_nonneg (e₁ * o₂ - e₂ * o₁)]
  have hcrossNonneg : 0 ≤ e₁ * o₂ + e₂ * o₁ := by
    positivity
  have hcrossSquare :
      (delta * j₁ * j₂) ^ 2 ≤
        (2 * (e₁ * o₂ + e₂ * o₁)) ^ 2 := by
    nlinarith
  have hcross :
      delta * j₁ * j₂ ≤
        2 * (e₁ * o₂ + e₂ * o₁) := by
    by_cases hsign : 0 ≤ delta * j₁ * j₂
    · nlinarith
    · have : delta * j₁ * j₂ < 0 := lt_of_not_ge hsign
      nlinarith
  nlinarith

/-- Unscaled determinant closure, obtained by taking the common cross
scaling to be one. -/
theorem determinant_bound_add
    (e₁ o₁ j₁ e₂ o₂ j₂ : ℝ)
    (he₁ : 0 ≤ e₁) (ho₁ : 0 ≤ o₁)
    (he₂ : 0 ≤ e₂) (ho₂ : 0 ≤ o₂)
    (h₁ : j₁ ^ 2 ≤ 4 * e₁ * o₁)
    (h₂ : j₂ ^ 2 ≤ 4 * e₂ * o₂) :
    (j₁ + j₂) ^ 2 ≤
      4 * (e₁ + e₂) * (o₁ + o₂) := by
  simpa only [one_mul] using scaled_determinant_bound_add
    1 e₁ o₁ j₁ e₂ o₂ j₂ (by norm_num)
      he₁ ho₁ he₂ ho₂ (by simpa using h₁) (by simpa using h₂)

/-- Complement-preserving determinant addition.  One mixed family may spend
the named reserves `x` and `y`; a second family may spend exactly the
remaining diagonal forms.  Adding the two determinant bounds then controls
their coupled sum without a triangle inequality or square roots. -/
theorem determinant_bound_add_complements
    (low tail x y z s : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hlow : 0 ≤ low - x) (htail : 0 ≤ tail - y)
    (hz : z ^ 2 ≤ x * y)
    (hs : s ^ 2 ≤ (low - x) * (tail - y)) :
    (z + s) ^ 2 ≤ low * tail := by
  have hz' : (2 * z) ^ 2 ≤ 4 * x * y := by nlinarith
  have hs' : (2 * s) ^ 2 ≤ 4 * (low - x) * (tail - y) := by
    nlinarith
  have hsum := determinant_bound_add
    x y (2 * z) (low - x) (tail - y) (2 * s)
    hx hy hlow htail hz' hs'
  nlinarith

/-- Strict complement-preserving determinant addition.  A positive
semidefinite first determinant allocation plus a strictly positive second
allocation gives a strict determinant bound for their coupled sum. -/
theorem determinant_bound_add_complements_lt
    (low tail x y z s : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hlow : 0 ≤ low - x) (htail : 0 ≤ tail - y)
    (hz : z ^ 2 ≤ x * y)
    (hs : s ^ 2 < (low - x) * (tail - y)) :
    (z + s) ^ 2 < low * tail := by
  let u := low - x
  let v := tail - y
  have hu : 0 ≤ u := by simpa only [u] using hlow
  have hv : 0 ≤ v := by simpa only [v] using htail
  have hs' : s ^ 2 < u * v := by simpa only [u, v] using hs
  have hsle : s ^ 2 ≤ u * v := hs'.le
  have hproduct : z ^ 2 * s ^ 2 ≤ (x * y) * (u * v) :=
    mul_le_mul hz hsle (sq_nonneg s) (mul_nonneg hx hy)
  have hcrossBase :
      4 * ((x * y) * (u * v)) ≤ (x * v + y * u) ^ 2 := by
    nlinarith [sq_nonneg (x * v - y * u)]
  have hcrossSquare :
      (2 * z * s) ^ 2 ≤ (x * v + y * u) ^ 2 := by
    nlinarith
  have hcrossNonneg : 0 ≤ x * v + y * u := by positivity
  have hcross : 2 * z * s ≤ x * v + y * u := by
    by_cases hzs : 0 ≤ 2 * z * s
    · nlinarith
    · have : 2 * z * s < 0 := lt_of_not_ge hzs
      linarith
  dsimp only [u, v] at hcross hs'
  nlinarith

/-- A positive `2 × 2` low block plus a tail stays nonnegative when the two
low-to-tail functionals satisfy the exact adjugate Schur bound. -/
theorem quadratic_add_tail_nonneg
    (q00 q02 q22 ell0 ell2 tail c b : ℝ)
    (hq00 : 0 < q00)
    (hdet : 0 < q00 * q22 - q02 ^ 2)
    (hschur :
      q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 + q00 * ell2 ^ 2 ≤
        (q00 * q22 - q02 ^ 2) * tail) :
    0 ≤ q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2 +
      2 * c * ell0 + 2 * b * ell2 + tail := by
  let det : ℝ := q00 * q22 - q02 ^ 2
  let Q : ℝ := q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2 +
    2 * c * ell0 + 2 * b * ell2 + tail
  have hdet' : 0 < det := by simpa only [det] using hdet
  have hrem : 0 ≤ det * tail -
      (q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 + q00 * ell2 ^ 2) := by
    dsimp only [det]
    linarith
  have hid :
      q00 * det * Q =
        det * (q00 * c + q02 * b + ell0) ^ 2 +
          (det * b + q00 * ell2 - q02 * ell0) ^ 2 +
          q00 * (det * tail -
            (q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 +
              q00 * ell2 ^ 2)) := by
    dsimp only [det, Q]
    ring
  have hscaled : 0 ≤ q00 * det * Q := by
    rw [hid]
    positivity
  have hfactor : 0 < q00 * det := mul_pos hq00 hdet'
  have hQ : 0 ≤ Q := nonneg_of_mul_nonneg_right hscaled hfactor
  simpa only [Q] using hQ

end ArithmeticHodge.Analysis.TwoByTwoSchur
