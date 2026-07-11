import ArithmeticHodge.Analysis.EntireFunction.GrowthBound

open Complex Filter Topology Real

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- One genuine zero, padded by zeros thereafter. -/
def paddedOneZero (n : ℕ) : ℂ := if n = 0 then 1 else 0

/-- The padded sequence satisfies the genus-one inverse-square summability
hypothesis used by `re_bound_of_factorization`. -/
theorem paddedOneZero_summable :
    Summable (fun n => (‖paddedOneZero n‖⁻¹) ^ (((1 : ℕ) : ℝ) + 1)) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [paddedOneZero, hn0]

/-- The corresponding infinite product has exactly its zeroth factor. -/
theorem tprod_paddedOneZero (z : ℂ) :
    ∏' n, weierstraßElementary 1 (z / paddedOneZero n) =
      weierstraßElementary 1 z := by
  calc
    ∏' n, weierstraßElementary 1 (z / paddedOneZero n) =
        weierstraßElementary 1 (z / paddedOneZero 0) := by
      apply tprod_eq_mulSingle 0
      intro n hn
      simp [paddedOneZero, hn, weierstraßElementary_zero]
    _ = weierstraßElementary 1 z := by simp [paddedOneZero]

/-- With genus one and exponential part `g z = -z`, the padded product is
exactly the linear entire function `1 - z`. -/
theorem one_sub_factorization (z : ℂ) :
    1 - z = z ^ (0 : ℕ) * Complex.exp (-z) *
      ∏' n, weierstraßElementary 1 (z / paddedOneZero n) := by
  rw [tprod_paddedOneZero]
  simp only [pow_zero, one_mul]
  rw [show weierstraßElementary 1 z = (1 - z) * Complex.exp z by
    simp [weierstraßElementary]]
  calc
    1 - z = (1 - z) * (Complex.exp (-z) * Complex.exp z) := by
      rw [← Complex.exp_add]
      simp
    _ = Complex.exp (-z) * ((1 - z) * Complex.exp z) := by ring

/-- The proposed real-part conclusion at exponent `1/2` is false for
`g z = -z`: a linear function cannot be bounded above by square-root growth. -/
theorem no_sqrt_growth_neg_id :
    ¬ ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ,
      (-z).re ≤ A * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
  rintro ⟨A, hA, hbound⟩
  let R : ℝ := (2 * A + 1) ^ 2
  have hR_nonneg : 0 ≤ R := by positivity
  have htest := hbound (-(R : ℂ))
  have hsqrt : (1 + R) ^ (1 / 2 : ℝ) = Real.sqrt (1 + R) := by
    rw [Real.sqrt_eq_rpow]
  have hsqrt_bound : Real.sqrt (1 + R) ≤ 2 * A + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · dsimp [R]
      nlinarith
  have hnorm : ‖(-(R : ℂ))‖ = R := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR_nonneg]
  have hre : (-(-((R : ℂ)))).re = R := by simp
  have hlinear : R ≤ A * Real.sqrt (1 + R) := by
    rw [hre, hnorm, hsqrt] at htest
    exact htest
  have hupper : A * Real.sqrt (1 + R) ≤ A * (2 * A + 2) := by
    exact mul_le_mul_of_nonneg_left hsqrt_bound hA.le
  dsimp [R] at hlinear hupper ⊢
  nlinarith

#print axioms paddedOneZero_summable
#print axioms tprod_paddedOneZero
#print axioms one_sub_factorization
#print axioms no_sqrt_growth_neg_id

end ArithmeticHodge.Analysis.EntireFunction
