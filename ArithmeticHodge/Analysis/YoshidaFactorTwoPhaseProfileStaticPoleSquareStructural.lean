import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSplit

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural

noncomputable section

/-!
# A Hadamard square for the profile-static reflected pole

The two profile-static phase branches have signs `sigma = ±1`.  After the
even and odd endpoint values are kept together, their reflected pairing is a
rank-one matrix of operator norm two.  The corresponding energy defect is
exactly a sum of three squares.  This is a profile-level identity: no basis,
cutoff, or entry enumeration occurs.
-/

/-- The reflected endpoint pairing in one static parity branch. -/
def factorTwoProfileStaticReflectedPair
    (e o : ℝ → ℝ) (sigma r x : ℝ) : ℝ :=
  sigma *
      (e (2 - r + x) * e x - o (2 - r + x) * o x) -
    (o (2 - r + x) * e x - e (2 - r + x) * o x)

/-- The energy defect obtained after subtracting the static reflected
pairing. -/
def factorTwoProfileStaticPoleDefectIntegrand
    (e o : ℝ → ℝ) (sigma r x : ℝ) : ℝ :=
  e (2 - r + x) ^ 2 + o (2 - r + x) ^ 2 +
      e x ^ 2 + o x ^ 2 -
    factorTwoProfileStaticReflectedPair e o sigma r x

/-- The exact three-square reserve left by the static reflected pairing. -/
def factorTwoProfileStaticPoleHadamardSquare
    (e o : ℝ → ℝ) (sigma r x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (e (2 - r + x) - sigma * o (2 - r + x) -
          (sigma * e x + o x)) ^ 2 +
    (1 / 2 : ℝ) *
      (e (2 - r + x) + sigma * o (2 - r + x)) ^ 2 +
    (1 / 2 : ℝ) * (e x - sigma * o x) ^ 2

/-- Scalar Hadamard completion underlying both static parity branches. -/
theorem static_reflected_pair_eq_hadamard_three_squares
    (sigma e0 o0 e1 o1 : ℝ) (hsigma : sigma ^ 2 = 1) :
    e1 ^ 2 + o1 ^ 2 + e0 ^ 2 + o0 ^ 2 -
        (sigma * (e1 * e0 - o1 * o0) -
          (o1 * e0 - e1 * o0)) =
      (1 / 2 : ℝ) *
          (e1 - sigma * o1 - (sigma * e0 + o0)) ^ 2 +
        (1 / 2 : ℝ) * (e1 + sigma * o1) ^ 2 +
        (1 / 2 : ℝ) * (e0 - sigma * o0) ^ 2 := by
  linear_combination
    -(o1 ^ 2 + (1 / 2 : ℝ) * e0 ^ 2 +
      (1 / 2 : ℝ) * o0 ^ 2 + o1 * e0) * hsigma

/-- Pointwise exact completion of the static reflected endpoint defect. -/
theorem factorTwoProfileStaticPoleDefectIntegrand_eq_hadamardSquare
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (r x : ℝ) :
    factorTwoProfileStaticPoleDefectIntegrand e o sigma r x =
      factorTwoProfileStaticPoleHadamardSquare e o sigma r x := by
  unfold factorTwoProfileStaticPoleDefectIntegrand
    factorTwoProfileStaticReflectedPair
    factorTwoProfileStaticPoleHadamardSquare
  exact static_reflected_pair_eq_hadamard_three_squares
    sigma (e x) (o x) (e (2 - r + x)) (o (2 - r + x)) hsigma

/-- The static reflected endpoint defect is pointwise nonnegative. -/
theorem factorTwoProfileStaticPoleDefectIntegrand_nonneg
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (r x : ℝ) :
    0 ≤ factorTwoProfileStaticPoleDefectIntegrand e o sigma r x := by
  rw [factorTwoProfileStaticPoleDefectIntegrand_eq_hadamardSquare
    e o sigma hsigma r x]
  unfold factorTwoProfileStaticPoleHadamardSquare
  positivity

/-- The endpoint interval integral before completing the static square. -/
def factorTwoProfileStaticPoleDefectNumerator
    (e o : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  ∫ x : ℝ in -1..-1 + r,
    factorTwoProfileStaticPoleDefectIntegrand e o sigma r x

/-- The same endpoint numerator expressed as its exact Hadamard-square
integral. -/
def factorTwoProfileStaticPoleSquareNumerator
    (e o : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  ∫ x : ℝ in -1..-1 + r,
    factorTwoProfileStaticPoleHadamardSquare e o sigma r x

/-- Exact integrated completion of one static reflected endpoint branch. -/
theorem factorTwoProfileStaticPoleDefectNumerator_eq_square
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (r : ℝ) :
    factorTwoProfileStaticPoleDefectNumerator e o sigma r =
      factorTwoProfileStaticPoleSquareNumerator e o sigma r := by
  unfold factorTwoProfileStaticPoleDefectNumerator
    factorTwoProfileStaticPoleSquareNumerator
  apply intervalIntegral.integral_congr
  intro x _hx
  exact factorTwoProfileStaticPoleDefectIntegrand_eq_hadamardSquare
    e o sigma hsigma r x

/-- Every nonnegative endpoint length gives a nonnegative completed static
pole numerator. -/
theorem factorTwoProfileStaticPoleDefectNumerator_nonneg
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ factorTwoProfileStaticPoleDefectNumerator e o sigma r := by
  rw [factorTwoProfileStaticPoleDefectNumerator_eq_square
    e o sigma hsigma r]
  unfold factorTwoProfileStaticPoleSquareNumerator
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x _hx
  unfold factorTwoProfileStaticPoleHadamardSquare
  positivity

/-- The logarithmically weighted endpoint contribution is nonnegative for
either static sign.  The exact three-square identity remains separately
available, so later arguments may spend only part of this reserve. -/
theorem integral_factorTwoProfileStaticPoleDefectNumerator_div_nonneg
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    0 ≤ ∫ r : ℝ in 0..2,
      factorTwoProfileStaticPoleDefectNumerator e o sigma r / r := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  exact div_nonneg
    (factorTwoProfileStaticPoleDefectNumerator_nonneg
      e o sigma hsigma r hr.1) hr.1

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural
