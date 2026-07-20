import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEndpointPencilConvexity

noncomputable section

open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix

/-!
# Convex interpolation of the concrete endpoint pencils

The symmetric phase coordinate enters each concrete diagonal pencil affinely.
Consequently, positivity of the two endpoint matrices at `a = -1` and `a = 1`
is enough for every `a` in the closed unit interval.  This isolates the finite
matrix certificate from the subsequent scalar coupling estimate.
-/

/-- The concrete even pencil is the affine chord joining its two endpoint
values. -/
theorem factorTwoConcreteEvenPencilValue_eq_endpoint_chord
    (a : ℝ) (e : YoshidaEvenIndex → ℝ) :
    factorTwoConcreteEvenPencilValue a e =
      ((1 + a) / 2) * factorTwoConcreteEvenPencilValue 1 e +
        ((1 - a) / 2) * factorTwoConcreteEvenPencilValue (-1) e := by
  unfold factorTwoConcreteEvenPencilValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- The concrete odd pencil is the affine chord joining its two endpoint
values. -/
theorem factorTwoConcreteOddPencilValue_eq_endpoint_chord
    (a : ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteOddPencilValue a o =
      ((1 + a) / 2) * factorTwoConcreteOddPencilValue 1 o +
        ((1 - a) / 2) * factorTwoConcreteOddPencilValue (-1) o := by
  unfold factorTwoConcreteOddPencilValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- Endpoint nonnegativity of the concrete even pencil extends to the whole
phase interval. -/
theorem factorTwoConcreteEvenPencilValue_nonneg_of_endpoints
    (a : ℝ) (ha : a ^ 2 ≤ 1) (e : YoshidaEvenIndex → ℝ)
    (hplus : 0 ≤ factorTwoConcreteEvenPencilValue 1 e)
    (hminus : 0 ≤ factorTwoConcreteEvenPencilValue (-1) e) :
    0 ≤ factorTwoConcreteEvenPencilValue a e := by
  have haLower : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have haUpper : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  rw [factorTwoConcreteEvenPencilValue_eq_endpoint_chord]
  exact add_nonneg
    (mul_nonneg (by linarith) hplus)
    (mul_nonneg (by linarith) hminus)

/-- Endpoint nonnegativity of the concrete odd pencil extends to the whole
phase interval. -/
theorem factorTwoConcreteOddPencilValue_nonneg_of_endpoints
    (a : ℝ) (ha : a ^ 2 ≤ 1) (o : YoshidaOddIndex → ℝ)
    (hplus : 0 ≤ factorTwoConcreteOddPencilValue 1 o)
    (hminus : 0 ≤ factorTwoConcreteOddPencilValue (-1) o) :
    0 ≤ factorTwoConcreteOddPencilValue a o := by
  have haLower : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have haUpper : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  rw [factorTwoConcreteOddPencilValue_eq_endpoint_chord]
  exact add_nonneg
    (mul_nonneg (by linarith) hplus)
    (mul_nonneg (by linarith) hminus)

/-- Four endpoint quadratic certificates supply both diagonal hypotheses of
the uniform disk-Schur criterion. -/
theorem factorTwoConcretePencilValues_nonneg_of_endpoints
    (hEvenPlus : ∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue 1 e)
    (hEvenMinus : ∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue (-1) e)
    (hOddPlus : ∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue 1 o)
    (hOddMinus : ∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue (-1) o) :
    (∀ a : ℝ, a ^ 2 ≤ 1 → ∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue a e) ∧
    (∀ a : ℝ, a ^ 2 ≤ 1 → ∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue a o) := by
  constructor
  · intro a ha e
    exact factorTwoConcreteEvenPencilValue_nonneg_of_endpoints a ha e
      (hEvenPlus e) (hEvenMinus e)
  · intro a ha o
    exact factorTwoConcreteOddPencilValue_nonneg_of_endpoints a ha o
      (hOddPlus o) (hOddMinus o)

/-- After endpoint interpolation, the only remaining finite-low hypothesis is
the inverse-free scalar coupling inequality. -/
theorem factorTwoConcreteLowPhase_nonneg_of_endpoint_pencils_and_disk_schur
    (hEvenPlus : ∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue 1 e)
    (hEvenMinus : ∀ e : YoshidaEvenIndex → ℝ,
      0 ≤ factorTwoConcreteEvenPencilValue (-1) e)
    (hOddPlus : ∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue 1 o)
    (hOddMinus : ∀ o : YoshidaOddIndex → ℝ,
      0 ≤ factorTwoConcreteOddPencilValue (-1) o)
    (hSchur : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ),
        (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
          4 * factorTwoConcreteEvenPencilValue a e *
            factorTwoConcreteOddPencilValue a o)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ YoshidaFactorTwoPhaseFullProfile.factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  obtain ⟨hEven, hOdd⟩ := factorTwoConcretePencilValues_nonneg_of_endpoints
    hEvenPlus hEvenMinus hOddPlus hOddMinus
  exact factorTwoConcreteLowPhase_nonneg_of_uniform_disk_schur
    hEven hOdd hSchur e o a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEndpointPencilConvexity
