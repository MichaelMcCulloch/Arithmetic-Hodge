import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

noncomputable section

open Polynomial
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural half-line reduction for the remaining six-mode projective gates

The projective entries are genuine polynomials in `x`; the square-root
coordinate has already disappeared from every determinant.  This file
records that polynomial structure without sampling the half-line.  It also
packages the coefficient cone which turns a structural coefficient proof
into all three remaining gates at once.
-/

/-- A real polynomial lies in the strict nonnegative-coefficient cone when
its constant coefficient is positive and all of its coefficients are
nonnegative. -/
def StrictNonnegativeCoefficientCone (p : ℝ[X]) : Prop :=
  0 < p.coeff 0 ∧ ∀ n : ℕ, 0 ≤ p.coeff n

/-- The closed nonnegative-coefficient cone. -/
def NonnegativeCoefficientCone (p : ℝ[X]) : Prop :=
  ∀ n : ℕ, 0 ≤ p.coeff n

/-- A polynomial in the strict nonnegative-coefficient cone is positive on
the whole nonnegative half-line.  This is a support-sum argument, not a
pointwise search. -/
theorem eval_pos_of_mem_strictNonnegativeCoefficientCone
    (p : ℝ[X]) (hp : StrictNonnegativeCoefficientCone p)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_pos'
  · intro n hn
    exact mul_nonneg (hp.2 n) (pow_nonneg hx n)
  · refine ⟨0, ?_, ?_⟩
    · exact Polynomial.mem_support_iff.mpr hp.1.ne'
    · simpa using hp.1

theorem eval_nonneg_of_mem_nonnegativeCoefficientCone
    (p : ℝ[X]) (hp : NonnegativeCoefficientCone p)
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (hp n) (pow_nonneg hx n)

/-- A structurally satisfiable cone for an exceptional determinant.  Its
quadratic head is positive either coefficientwise or by a strict
discriminant inequality, while every higher term stays in one
nonnegative-coefficient tail. -/
def PositiveQuadraticHeadNonnegativeTailCone (p : ℝ[X]) : Prop :=
  ∃ c0 c1 c2 : ℝ, ∃ q : ℝ[X],
    p = C c0 + C c1 * X + C c2 * X ^ 2 + X ^ 3 * q ∧
      0 < c0 ∧ 0 < c2 ∧
      (0 ≤ c1 ∨ (c1 < 0 ∧ c1 ^ 2 < 4 * c0 * c2)) ∧
      NonnegativeCoefficientCone q

/-- The negative-linear branch is a literal square completion.  Hence this
cone is positive on the whole half-line, without a subdivision or search. -/
theorem eval_pos_of_mem_positiveQuadraticHeadNonnegativeTailCone
    (p : ℝ[X]) (hp : PositiveQuadraticHeadNonnegativeTailCone p)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  rcases hp with ⟨c0, c1, c2, q, rfl, hc0, hc2, hc1, hq⟩
  have hqeval : 0 ≤ q.eval x :=
    eval_nonneg_of_mem_nonnegativeCoefficientCone q hq x hx
  have htail : 0 ≤ x ^ 3 * q.eval x :=
    mul_nonneg (pow_nonneg hx 3) hqeval
  have hhead : 0 < c0 + c1 * x + c2 * x ^ 2 := by
    rcases hc1 with hc1 | hc1
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg hc0 (mul_nonneg hc1 hx))
        (mul_nonneg hc2.le (sq_nonneg x))
    · have hsos :
          4 * c2 * (c0 + c1 * x + c2 * x ^ 2) =
            (2 * c2 * x + c1) ^ 2 + (4 * c0 * c2 - c1 ^ 2) := by
        ring
      have hrhs : 0 <
          (2 * c2 * x + c1) ^ 2 + (4 * c0 * c2 - c1 ^ 2) :=
        add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hc1.2)
      nlinarith
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  nlinarith

/-! ## Exact polynomial realization of the projective entries -/

private def affineEndpointPolynomial (plus minus : ℝ) : ℝ[X] :=
  C plus + C minus * X

private def low00Polynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow00 (-1))

private def low02Polynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoStructuralPhaseLow02 (-1))

private def low22Polynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoStructuralPhaseLow22 (-1))

private def lowDetPolynomial : ℝ[X] :=
  low00Polynomial * low22Polynomial - low02Polynomial ^ 2

private def cross04Polynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoIntrinsicFourP45Cross04 (-1))

private def cross24Polynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicFourP45Cross24 (-1))

private def p4DiagonalPolynomial : ℝ[X] :=
  affineEndpointPolynomial
    (factorTwoIntrinsicSixP4Diagonal 1)
    (factorTwoIntrinsicSixP4Diagonal (-1))

private def oddEntryPolynomial (i j : Fin 3) : ℝ[X] :=
  match i, j with
  | 0, 0 => affineEndpointPolynomial
      (factorTwoIntrinsicOddPhaseLow11 1)
      (factorTwoIntrinsicOddPhaseLow11 (-1))
  | 0, 1 => affineEndpointPolynomial
      (factorTwoIntrinsicOddPhaseLow13 1)
      (factorTwoIntrinsicOddPhaseLow13 (-1))
  | 1, 0 => affineEndpointPolynomial
      (factorTwoIntrinsicOddPhaseLow13 1)
      (factorTwoIntrinsicOddPhaseLow13 (-1))
  | 0, 2 => affineEndpointPolynomial
      (factorTwoIntrinsicFourP45Cross15 1)
      (factorTwoIntrinsicFourP45Cross15 (-1))
  | 2, 0 => affineEndpointPolynomial
      (factorTwoIntrinsicFourP45Cross15 1)
      (factorTwoIntrinsicFourP45Cross15 (-1))
  | 1, 1 => affineEndpointPolynomial
      (factorTwoIntrinsicOddPhaseLow33 1)
      (factorTwoIntrinsicOddPhaseLow33 (-1))
  | 1, 2 => affineEndpointPolynomial
      (factorTwoIntrinsicFourP45Cross35 1)
      (factorTwoIntrinsicFourP45Cross35 (-1))
  | 2, 1 => affineEndpointPolynomial
      (factorTwoIntrinsicFourP45Cross35 1)
      (factorTwoIntrinsicFourP45Cross35 (-1))
  | 2, 2 => affineEndpointPolynomial
      (factorTwoIntrinsicSixP5Diagonal 1)
      (factorTwoIntrinsicSixP5Diagonal (-1))

private def lowAlternating0 : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicAlternating01
  | 1 => factorTwoIntrinsicAlternating03
  | 2 => factorTwoIntrinsicFourP45Cross05

private def lowAlternating2 : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicAlternating21
  | 1 => factorTwoIntrinsicAlternating23
  | 2 => factorTwoIntrinsicFourP45Cross25

private def p4Alternating : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicFourP45Cross41
  | 1 => factorTwoIntrinsicFourP45Cross43
  | 2 => factorTwoIntrinsicSixAlternating45

private def oddEntryValue (x : ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => factorTwoIntrinsicSixProjectiveOdd11 x
  | 0, 1 => factorTwoIntrinsicSixProjectiveOdd13 x
  | 1, 0 => factorTwoIntrinsicSixProjectiveOdd13 x
  | 0, 2 => factorTwoIntrinsicSixProjectiveOdd15 x
  | 2, 0 => factorTwoIntrinsicSixProjectiveOdd15 x
  | 1, 1 => factorTwoIntrinsicSixProjectiveOdd33 x
  | 1, 2 => factorTwoIntrinsicSixProjectiveOdd35 x
  | 2, 1 => factorTwoIntrinsicSixProjectiveOdd35 x
  | 2, 2 => factorTwoIntrinsicSixProjectiveP5Diagonal x

private theorem p4OddCross_eq_explicit (x : ℝ) (i : Fin 3) :
    factorTwoIntrinsicSixProjectiveP4OddCross x i =
      factorTwoIntrinsicSixProjectiveLowDet x * p4Alternating i -
        factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
          (lowAlternating0 i) (lowAlternating2 i) := by
  fin_cases i <;> rfl

private theorem p4Pivot_eq_explicit (x : ℝ) :
    factorTwoIntrinsicSixProjectiveP4Pivot x =
      factorTwoIntrinsicSixProjectiveLowDet x *
          factorTwoIntrinsicSixProjectiveP4Diagonal x -
        factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x) := by
  rfl

private theorem oddResidual_eq_explicit
    (x : ℝ) (i j : Fin 3) :
    factorTwoIntrinsicSixProjectiveOddResidual x i j =
      factorTwoIntrinsicSixProjectiveLowDet x * oddEntryValue x i j -
        x * factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (lowAlternating0 i) (lowAlternating2 i)
          (lowAlternating0 j) (lowAlternating2 j) := by
  fin_cases i <;> fin_cases j <;> rfl

private def adjugateTwoPolynomial
    (u0 u2 v0 v2 : ℝ[X]) : ℝ[X] :=
  low22Polynomial * u0 * v0 -
    low02Polynomial * (u0 * v2 + u2 * v0) +
    low00Polynomial * u2 * v2

private def p4PivotPolynomial : ℝ[X] :=
  lowDetPolynomial * p4DiagonalPolynomial -
    adjugateTwoPolynomial
      cross04Polynomial cross24Polynomial
      cross04Polynomial cross24Polynomial

private def p4OddCrossPolynomial (i : Fin 3) : ℝ[X] :=
  lowDetPolynomial * C (p4Alternating i) -
    adjugateTwoPolynomial
      cross04Polynomial cross24Polynomial
      (C (lowAlternating0 i)) (C (lowAlternating2 i))

private def oddResidualPolynomial (i j : Fin 3) : ℝ[X] :=
  lowDetPolynomial * oddEntryPolynomial i j -
    X * adjugateTwoPolynomial
      (C (lowAlternating0 i)) (C (lowAlternating2 i))
      (C (lowAlternating0 j)) (C (lowAlternating2 j))

/-- Polarized adjugate form of the raw projective even `P₀/P₂/P₄`
matrix, lifted to the polynomial ring. -/
private def adjugateThreePolynomial
    (u0 u2 u4 v0 v2 v4 : ℝ[X]) : ℝ[X] :=
  (low22Polynomial * p4DiagonalPolynomial - cross24Polynomial ^ 2) *
      u0 * v0 +
    (cross04Polynomial * cross24Polynomial -
        low02Polynomial * p4DiagonalPolynomial) *
      (u0 * v2 + u2 * v0) +
    (low02Polynomial * cross24Polynomial -
        cross04Polynomial * low22Polynomial) *
      (u0 * v4 + u4 * v0) +
    (low00Polynomial * p4DiagonalPolynomial - cross04Polynomial ^ 2) *
      u2 * v2 +
    (low02Polynomial * cross04Polynomial -
        low00Polynomial * cross24Polynomial) *
      (u2 * v4 + u4 * v2) +
    lowDetPolynomial * u4 * v4

/-- Raw `P₀/P₂/P₄/P₁` leading determinant before eliminating
the low plane. -/
def factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial : ℝ[X] :=
  p4PivotPolynomial * oddEntryPolynomial 0 0 -
    X * adjugateThreePolynomial
      (C factorTwoIntrinsicAlternating01)
      (C factorTwoIntrinsicAlternating21)
      (C factorTwoIntrinsicFourP45Cross41)
      (C factorTwoIntrinsicAlternating01)
      (C factorTwoIntrinsicAlternating21)
      (C factorTwoIntrinsicFourP45Cross41)

private def rawAlternating0 (i : Fin 3) : ℝ[X] :=
  C (lowAlternating0 i)

private def rawAlternating2 (i : Fin 3) : ℝ[X] :=
  C (lowAlternating2 i)

private def rawAlternating4 (i : Fin 3) : ℝ[X] :=
  C (p4Alternating i)

private def rawAdjugatePairPolynomial (i j : Fin 3) : ℝ[X] :=
  adjugateThreePolynomial
    (rawAlternating0 i) (rawAlternating2 i) (rawAlternating4 i)
    (rawAlternating0 j) (rawAlternating2 j) (rawAlternating4 j)

private def rawCross0 (i j : Fin 3) : ℝ[X] :=
  rawAlternating2 i * rawAlternating4 j -
    rawAlternating4 i * rawAlternating2 j

private def rawCross2 (i j : Fin 3) : ℝ[X] :=
  rawAlternating4 i * rawAlternating0 j -
    rawAlternating0 i * rawAlternating4 j

private def rawCross4 (i j : Fin 3) : ℝ[X] :=
  rawAlternating0 i * rawAlternating2 j -
    rawAlternating2 i * rawAlternating0 j

private def rawEvenEnergyPolynomial
    (u0 u2 u4 v0 v2 v4 : ℝ[X]) : ℝ[X] :=
  low00Polynomial * u0 * v0 +
    low02Polynomial * (u0 * v2 + u2 * v0) +
    cross04Polynomial * (u0 * v4 + u4 * v0) +
    low22Polynomial * u2 * v2 +
    cross24Polynomial * (u2 * v4 + u4 * v2) +
    p4DiagonalPolynomial * u4 * v4

/-- The `E`-energy of the cross product of two alternating columns.  The
three-dimensional Gram identity says this is the quotient of their
adjugate Gram determinant by `det E`, with no division in the displayed
formula. -/
private def rawAlternatingCrossEnergyPolynomial (i j : Fin 3) : ℝ[X] :=
  rawEvenEnergyPolynomial
    (rawCross0 i j) (rawCross2 i j) (rawCross4 i j)
    (rawCross0 i j) (rawCross2 i j) (rawCross4 i j)

/-- Oriented cross-product column complementary to an odd index. -/
private def rawCofactorVector0 : Fin 3 → ℝ[X]
  | 0 => rawCross0 1 2
  | 1 => rawCross0 2 0
  | 2 => rawCross0 0 1

private def rawCofactorVector2 : Fin 3 → ℝ[X]
  | 0 => rawCross2 1 2
  | 1 => rawCross2 2 0
  | 2 => rawCross2 0 1

private def rawCofactorVector4 : Fin 3 → ℝ[X]
  | 0 => rawCross4 1 2
  | 1 => rawCross4 2 0
  | 2 => rawCross4 0 1

/-- After dividing a `2 x 2` adjugate minor of the alternating Gram matrix
by `det E`, the quotient is this `E`-energy of oriented cross products. -/
private def rawAdjugateCofactorPolynomial (i j : Fin 3) : ℝ[X] :=
  rawEvenEnergyPolynomial
    (rawCofactorVector0 i) (rawCofactorVector2 i) (rawCofactorVector4 i)
    (rawCofactorVector0 j) (rawCofactorVector2 j) (rawCofactorVector4 j)

private def rawOddDeterminantPolynomial : ℝ[X] :=
  oddEntryPolynomial 0 0 *
      (oddEntryPolynomial 1 1 * oddEntryPolynomial 2 2 -
        oddEntryPolynomial 1 2 ^ 2) -
    oddEntryPolynomial 0 1 *
      (oddEntryPolynomial 0 1 * oddEntryPolynomial 2 2 -
        oddEntryPolynomial 0 2 * oddEntryPolynomial 1 2) +
    oddEntryPolynomial 0 2 *
      (oddEntryPolynomial 0 1 * oddEntryPolynomial 1 2 -
        oddEntryPolynomial 0 2 * oddEntryPolynomial 1 1)

/-- First mixed determinant coefficient `trace(adj(O) A)`. -/
private def rawMixedAdjugateOnePolynomial : ℝ[X] :=
  (oddEntryPolynomial 1 1 * oddEntryPolynomial 2 2 -
      oddEntryPolynomial 1 2 ^ 2) * rawAdjugatePairPolynomial 0 0 +
    2 * (oddEntryPolynomial 0 2 * oddEntryPolynomial 1 2 -
      oddEntryPolynomial 0 1 * oddEntryPolynomial 2 2) *
        rawAdjugatePairPolynomial 0 1 +
    2 * (oddEntryPolynomial 0 1 * oddEntryPolynomial 1 2 -
      oddEntryPolynomial 0 2 * oddEntryPolynomial 1 1) *
        rawAdjugatePairPolynomial 0 2 +
    (oddEntryPolynomial 0 0 * oddEntryPolynomial 2 2 -
      oddEntryPolynomial 0 2 ^ 2) * rawAdjugatePairPolynomial 1 1 +
    2 * (oddEntryPolynomial 0 1 * oddEntryPolynomial 0 2 -
      oddEntryPolynomial 0 0 * oddEntryPolynomial 1 2) *
        rawAdjugatePairPolynomial 1 2 +
    (oddEntryPolynomial 0 0 * oddEntryPolynomial 1 1 -
      oddEntryPolynomial 0 1 ^ 2) * rawAdjugatePairPolynomial 2 2

/-- Second mixed determinant coefficient `trace(adj(A) O) / det(E)`,
already expressed without division by cross-product energies. -/
private def rawMixedAdjugateTwoPolynomial : ℝ[X] :=
  oddEntryPolynomial 0 0 * rawAdjugateCofactorPolynomial 0 0 +
    2 * oddEntryPolynomial 0 1 * rawAdjugateCofactorPolynomial 0 1 +
    2 * oddEntryPolynomial 0 2 * rawAdjugateCofactorPolynomial 0 2 +
    oddEntryPolynomial 1 1 * rawAdjugateCofactorPolynomial 1 1 +
    2 * oddEntryPolynomial 1 2 * rawAdjugateCofactorPolynomial 1 2 +
    oddEntryPolynomial 2 2 * rawAdjugateCofactorPolynomial 2 2

private def rawAlternatingDeterminant : ℝ :=
  lowAlternating0 0 *
      (lowAlternating2 1 * p4Alternating 2 -
        p4Alternating 1 * lowAlternating2 2) -
    lowAlternating2 0 *
      (lowAlternating0 1 * p4Alternating 2 -
        p4Alternating 1 * lowAlternating0 2) +
    p4Alternating 0 *
      (lowAlternating0 1 * lowAlternating2 2 -
        lowAlternating2 1 * lowAlternating0 2)

/-- Raw `P₀/P₂/P₄/P₁/P₃` leading determinant.  Its last
term is the cross-product Gram square rather than a quotient by the even
determinant. -/
def factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial : ℝ[X] :=
  p4PivotPolynomial *
      (oddEntryPolynomial 0 0 * oddEntryPolynomial 1 1 -
        oddEntryPolynomial 0 1 ^ 2) -
    X * (oddEntryPolynomial 1 1 * rawAdjugatePairPolynomial 0 0 -
      2 * oddEntryPolynomial 0 1 * rawAdjugatePairPolynomial 0 1 +
      oddEntryPolynomial 0 0 * rawAdjugatePairPolynomial 1 1) +
    X ^ 2 * rawAlternatingCrossEnergyPolynomial 0 1

/-- Raw determinant of the complete six-mode projective matrix.  The cubic
alternating term is a literal determinant square. -/
def factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial : ℝ[X] :=
  p4PivotPolynomial * rawOddDeterminantPolynomial -
    X * rawMixedAdjugateOnePolynomial +
    X ^ 2 * rawMixedAdjugateTwoPolynomial -
    X ^ 3 * C (rawAlternatingDeterminant ^ 2)

private theorem eval_affineEndpointPolynomial
    (plus minus x : ℝ) :
    (affineEndpointPolynomial plus minus).eval x = plus + x * minus := by
  simp [affineEndpointPolynomial]
  ring

private theorem eval_lowDetPolynomial (x : ℝ) :
    lowDetPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveLowDet x := by
  unfold lowDetPolynomial factorTwoIntrinsicSixProjectiveLowDet
    low00Polynomial low02Polynomial low22Polynomial
  simp only [eval_sub, eval_mul, eval_pow,
    eval_affineEndpointPolynomial]
  unfold factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
  ring

/-- The projective low determinant is the quadratic homogenization of the
already-proved affine low determinant. -/
theorem factorTwoIntrinsicSixProjectiveLowDet_eq_homogeneous
    (x : ℝ) (hden : 1 + x ≠ 0) :
    factorTwoIntrinsicSixProjectiveLowDet x =
      (1 + x) ^ 2 * factorTwoIntrinsicEvenPhaseDet
        ((1 - x) / (1 + x)) := by
  unfold factorTwoIntrinsicSixProjectiveLowDet
    factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
    factorTwoIntrinsicEvenPhaseDet
    factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  field_simp [hden]
  ring

/-- The eliminated `P₀/P₂` determinant is strictly positive on the
whole projective half-line.  This uses convexity of positive endpoint
quadratics, rather than coefficient inspection. -/
theorem factorTwoIntrinsicSixProjectiveLowDet_pos
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicSixProjectiveLowDet x := by
  have hdenPos : 0 < 1 + x := by linarith
  let a := (1 - x) / (1 + x)
  have haLower : -1 ≤ a := by
    dsimp only [a]
    rw [le_div_iff₀ hdenPos]
    linarith
  have haUpper : a ≤ 1 := by
    dsimp only [a]
    rw [div_le_iff₀ hdenPos]
    linarith
  have hphase := factorTwoStructuralPhaseLow_pos_of_endpoints
    a haLower haUpper
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
  rw [factorTwoIntrinsicSixProjectiveLowDet_eq_homogeneous
    x hdenPos.ne']
  exact mul_pos (pow_pos hdenPos 2) hphase.2

private theorem eval_cross04Polynomial (x : ℝ) :
    cross04Polynomial.eval x =
      factorTwoIntrinsicSixProjectiveCross04 x := by
  unfold cross04Polynomial factorTwoIntrinsicSixProjectiveCross04
  rw [eval_affineEndpointPolynomial]

private theorem eval_cross24Polynomial (x : ℝ) :
    cross24Polynomial.eval x =
      factorTwoIntrinsicSixProjectiveCross24 x := by
  unfold cross24Polynomial factorTwoIntrinsicSixProjectiveCross24
  rw [eval_affineEndpointPolynomial]

private theorem eval_p4DiagonalPolynomial (x : ℝ) :
    p4DiagonalPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveP4Diagonal x := by
  unfold p4DiagonalPolynomial factorTwoIntrinsicSixProjectiveP4Diagonal
  rw [eval_affineEndpointPolynomial]

private theorem eval_oddEntryPolynomial
    (x : ℝ) (i j : Fin 3) :
    (oddEntryPolynomial i j).eval x =
      match i, j with
      | 0, 0 => factorTwoIntrinsicSixProjectiveOdd11 x
      | 0, 1 => factorTwoIntrinsicSixProjectiveOdd13 x
      | 1, 0 => factorTwoIntrinsicSixProjectiveOdd13 x
      | 0, 2 => factorTwoIntrinsicSixProjectiveOdd15 x
      | 2, 0 => factorTwoIntrinsicSixProjectiveOdd15 x
      | 1, 1 => factorTwoIntrinsicSixProjectiveOdd33 x
      | 1, 2 => factorTwoIntrinsicSixProjectiveOdd35 x
      | 2, 1 => factorTwoIntrinsicSixProjectiveOdd35 x
      | 2, 2 => factorTwoIntrinsicSixProjectiveP5Diagonal x := by
  fin_cases i <;> fin_cases j <;>
    simp [oddEntryPolynomial, eval_affineEndpointPolynomial,
      factorTwoIntrinsicSixProjectiveOdd11,
      factorTwoIntrinsicSixProjectiveOdd13,
      factorTwoIntrinsicSixProjectiveOdd33,
      factorTwoIntrinsicSixProjectiveOdd15,
      factorTwoIntrinsicSixProjectiveOdd35,
      factorTwoIntrinsicSixProjectiveP5Diagonal]

private theorem eval_adjugateTwoPolynomial
    (x : ℝ) (u0 u2 v0 v2 : ℝ[X]) :
    (adjugateTwoPolynomial u0 u2 v0 v2).eval x =
      factorTwoIntrinsicSixAdjugateBilinear
        (factorTwoIntrinsicSixProjectiveLow00 x)
        (factorTwoIntrinsicSixProjectiveLow02 x)
        (factorTwoIntrinsicSixProjectiveLow22 x)
        (u0.eval x) (u2.eval x) (v0.eval x) (v2.eval x) := by
  unfold adjugateTwoPolynomial factorTwoIntrinsicSixAdjugateBilinear
    low00Polynomial low02Polynomial low22Polynomial
  simp only [eval_sub, eval_add, eval_mul,
    eval_affineEndpointPolynomial]
  unfold factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
  ring

private theorem eval_p4PivotPolynomial (x : ℝ) :
    p4PivotPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveP4Pivot x := by
  rw [p4Pivot_eq_explicit]
  unfold p4PivotPolynomial
  simp only [eval_sub, eval_mul, eval_lowDetPolynomial,
    eval_p4DiagonalPolynomial, eval_adjugateTwoPolynomial,
    eval_cross04Polynomial, eval_cross24Polynomial]

private theorem eval_p4OddCrossPolynomial (x : ℝ) (i : Fin 3) :
    (p4OddCrossPolynomial i).eval x =
      factorTwoIntrinsicSixProjectiveP4OddCross x i := by
  rw [p4OddCross_eq_explicit]
  simp [p4OddCrossPolynomial, eval_lowDetPolynomial,
    eval_adjugateTwoPolynomial, eval_cross04Polynomial,
    eval_cross24Polynomial]

private theorem eval_oddResidualPolynomial
    (x : ℝ) (i j : Fin 3) :
    (oddResidualPolynomial i j).eval x =
      factorTwoIntrinsicSixProjectiveOddResidual x i j := by
  rw [oddResidual_eq_explicit]
  simp [oddResidualPolynomial, eval_lowDetPolynomial,
    eval_oddEntryPolynomial, eval_adjugateTwoPolynomial,
    oddEntryValue]

/-! ## The three gate polynomials -/

/-- Polynomial whose evaluation is the second projective pivot. -/
def factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial : ℝ[X] :=
  p4PivotPolynomial * oddResidualPolynomial 0 0 -
    X * p4OddCrossPolynomial 0 ^ 2

/-- Polynomial whose evaluation is the projective `3 x 3` base determinant. -/
def factorTwoIntrinsicSixProjectiveBaseDetPolynomial : ℝ[X] :=
  p4PivotPolynomial *
      (oddResidualPolynomial 0 0 * oddResidualPolynomial 1 1 -
        oddResidualPolynomial 0 1 ^ 2) -
    X * (oddResidualPolynomial 1 1 * p4OddCrossPolynomial 0 ^ 2 -
      2 * oddResidualPolynomial 0 1 *
        p4OddCrossPolynomial 0 * p4OddCrossPolynomial 1 +
      oddResidualPolynomial 0 0 * p4OddCrossPolynomial 1 ^ 2)

/-- The determinant gap in the final scalar `P₅` Schur step. -/
def factorTwoIntrinsicSixProjectiveP5GapPolynomial : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveBaseDetPolynomial *
      oddResidualPolynomial 2 2 -
    (X * (oddResidualPolynomial 0 0 * oddResidualPolynomial 1 1 -
          oddResidualPolynomial 0 1 ^ 2) * p4OddCrossPolynomial 2 ^ 2 +
      2 * X *
        (p4OddCrossPolynomial 1 * oddResidualPolynomial 0 1 -
          p4OddCrossPolynomial 0 * oddResidualPolynomial 1 1) *
        p4OddCrossPolynomial 2 * oddResidualPolynomial 0 2 +
      2 * X *
        (p4OddCrossPolynomial 0 * oddResidualPolynomial 0 1 -
          p4OddCrossPolynomial 1 * oddResidualPolynomial 0 0) *
        p4OddCrossPolynomial 2 * oddResidualPolynomial 1 2 +
      (p4PivotPolynomial * oddResidualPolynomial 1 1 -
          X * p4OddCrossPolynomial 1 ^ 2) *
        oddResidualPolynomial 0 2 ^ 2 +
      2 * (X * p4OddCrossPolynomial 0 * p4OddCrossPolynomial 1 -
          p4PivotPolynomial * oddResidualPolynomial 0 1) *
        oddResidualPolynomial 0 2 * oddResidualPolynomial 1 2 +
      (p4PivotPolynomial * oddResidualPolynomial 0 0 -
          X * p4OddCrossPolynomial 0 ^ 2) *
        oddResidualPolynomial 1 2 ^ 2)

/-- Exact division-free Schur factorization of the second projective pivot.
The low determinant occurs once, and the remaining factor is the raw `4 x 4`
leading determinant. -/
theorem factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial_factor :
    factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial =
      lowDetPolynomial *
        factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial
    factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial
    p4PivotPolynomial p4OddCrossPolynomial oddResidualPolynomial
    adjugateThreePolynomial adjugateTwoPolynomial
    lowDetPolynomial
  simp only [lowAlternating0, lowAlternating2, p4Alternating]
  ring

/-- Exact division-free Schur factorization of the `3 x 3` projective base
determinant.  Eliminating a two-dimensional low plane contributes precisely
the square of its determinant. -/
theorem factorTwoIntrinsicSixProjectiveBaseDetPolynomial_factor :
    factorTwoIntrinsicSixProjectiveBaseDetPolynomial =
      lowDetPolynomial ^ 2 *
        factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial := by
  unfold factorTwoIntrinsicSixProjectiveBaseDetPolynomial
    factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial
    p4PivotPolynomial p4OddCrossPolynomial oddResidualPolynomial
    rawAdjugatePairPolynomial rawAlternatingCrossEnergyPolynomial
    rawEvenEnergyPolynomial rawCross0 rawCross2 rawCross4
    rawAlternating0 rawAlternating2 rawAlternating4
    adjugateThreePolynomial adjugateTwoPolynomial lowDetPolynomial
  simp only [lowAlternating0, lowAlternating2, p4Alternating]
  ring

theorem eval_factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveBaseMinorTwoX x := by
  unfold factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial
    factorTwoIntrinsicSixProjectiveBaseMinorTwoX
  simp [eval_p4PivotPolynomial, eval_oddResidualPolynomial,
    eval_p4OddCrossPolynomial]

/-- Structural closure of the second pivot after factoring off the already
positive low determinant. -/
theorem factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos_of_raw_cone
    (x : ℝ) (hx : 0 ≤ x)
    (hRaw : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial) :
    0 < factorTwoIntrinsicSixProjectiveBaseMinorTwoX x := by
  rw [← eval_factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial,
    factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial_factor,
    eval_mul]
  exact mul_pos (by
      rw [eval_lowDetPolynomial]
      exact factorTwoIntrinsicSixProjectiveLowDet_pos x hx)
    (eval_pos_of_mem_strictNonnegativeCoefficientCone _ hRaw x hx)

theorem eval_factorTwoIntrinsicSixProjectiveBaseDetPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveBaseDetPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveBaseDetX x := by
  unfold factorTwoIntrinsicSixProjectiveBaseDetPolynomial
    factorTwoIntrinsicSixProjectiveBaseDetX
    factorTwoIntrinsicSixAdjugateBilinear
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
    eval_ofNat, eval_p4PivotPolynomial, eval_oddResidualPolynomial,
    eval_p4OddCrossPolynomial]
  ring

/-- Structural closure of the projective base determinant after factoring
off the square of the positive low determinant. -/
theorem factorTwoIntrinsicSixProjectiveBaseDetX_pos_of_raw_cone
    (x : ℝ) (hx : 0 ≤ x)
    (hRaw : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial) :
    0 < factorTwoIntrinsicSixProjectiveBaseDetX x := by
  rw [← eval_factorTwoIntrinsicSixProjectiveBaseDetPolynomial,
    factorTwoIntrinsicSixProjectiveBaseDetPolynomial_factor,
    eval_mul, eval_pow]
  exact mul_pos (pow_pos (by
      rw [eval_lowDetPolynomial]
      exact factorTwoIntrinsicSixProjectiveLowDet_pos x hx) 2)
    (eval_pos_of_mem_strictNonnegativeCoefficientCone _ hRaw x hx)

theorem eval_factorTwoIntrinsicSixProjectiveP5GapPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveP5GapPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveBaseDetX x *
          factorTwoIntrinsicSixProjectiveP5DiagonalResidual x -
        factorTwoIntrinsicSixProjectiveP5AdjugateX x := by
  unfold factorTwoIntrinsicSixProjectiveP5GapPolynomial
    factorTwoIntrinsicSixProjectiveP5DiagonalResidual
    factorTwoIntrinsicSixProjectiveP5AdjugateX
  dsimp only
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
    eval_ofNat, eval_factorTwoIntrinsicSixProjectiveBaseDetPolynomial,
    eval_p4PivotPolynomial, eval_oddResidualPolynomial,
    eval_p4OddCrossPolynomial]

/-! ## One structural coefficient-cone closure -/

/-- Membership of the three exact determinant polynomials in the positive
coefficient cone closes every `x`-gate on the half-line.  The first pivot is
left as a hypothesis because its endpoint proof is independent. -/
theorem factorTwoIntrinsicSixProjectiveXGates_of_quadratic_head_cone
    (x : ℝ) (hx : 0 ≤ x)
    (hPivot : 0 < factorTwoIntrinsicSixProjectiveP4Pivot x)
    (hMinor : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial)
    (hDet : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveBaseDetPolynomial)
    (hGap : PositiveQuadraticHeadNonnegativeTailCone
      factorTwoIntrinsicSixProjectiveP5GapPolynomial) :
    FactorTwoIntrinsicSixProjectiveXGates x := by
  refine ⟨hPivot, ?_, ?_, ?_⟩
  · rw [← eval_factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial]
    exact eval_pos_of_mem_strictNonnegativeCoefficientCone _ hMinor x hx
  · rw [← eval_factorTwoIntrinsicSixProjectiveBaseDetPolynomial]
    exact eval_pos_of_mem_strictNonnegativeCoefficientCone _ hDet x hx
  · have hgapPos :=
      eval_pos_of_mem_positiveQuadraticHeadNonnegativeTailCone _ hGap x hx
    rw [eval_factorTwoIntrinsicSixProjectiveP5GapPolynomial] at hgapPos
    linarith

/-- The simpler all-positive coefficient cone remains as a direct stronger
route when such coefficient bounds are available. -/
theorem factorTwoIntrinsicSixProjectiveXGates_of_coefficient_cones
    (x : ℝ) (hx : 0 ≤ x)
    (hPivot : 0 < factorTwoIntrinsicSixProjectiveP4Pivot x)
    (hMinor : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial)
    (hDet : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveBaseDetPolynomial)
    (hGap : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveP5GapPolynomial) :
    FactorTwoIntrinsicSixProjectiveXGates x := by
  refine ⟨hPivot, ?_, ?_, ?_⟩
  · rw [← eval_factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial]
    exact eval_pos_of_mem_strictNonnegativeCoefficientCone _ hMinor x hx
  · rw [← eval_factorTwoIntrinsicSixProjectiveBaseDetPolynomial]
    exact eval_pos_of_mem_strictNonnegativeCoefficientCone _ hDet x hx
  · have hgapPos :=
      eval_pos_of_mem_strictNonnegativeCoefficientCone _ hGap x hx
    rw [eval_factorTwoIntrinsicSixProjectiveP5GapPolynomial] at hgapPos
    linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
