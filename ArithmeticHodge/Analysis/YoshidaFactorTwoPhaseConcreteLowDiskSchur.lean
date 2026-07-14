import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
import ArithmeticHodge.Analysis.TwoByTwoSchur

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur

noncomputable section

open ArithmeticHodge.Analysis
open TwoByTwoSchur
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

/-!
# Disk-uniform scalar Schur criterion for the concrete low phase

The fully concrete `200 + 10` low phase splits into an even diagonal pencil,
an odd diagonal pencil, and one alternating scalar cross term.  The disk
constraint pays for the phase coefficient on the cross term.  The resulting
criterion remains valid when either diagonal pencil is merely semidefinite,
because it uses the division-free scalar Schur lemma.
-/

/-- The endpoint-adapted even diagonal pencil evaluated on a coefficient
vector. -/
def factorTwoConcreteEvenPencilValue
    (a : ℝ) (e : YoshidaEvenIndex → ℝ) : ℝ :=
  e ⬝ᵥ ((factorTwoConcreteAdaptedEvenCleanMatrix +
    a • factorTwoConcreteEvenPerturbationMatrix) *ᵥ e)

/-- The canonical odd diagonal pencil evaluated on a coefficient vector. -/
def factorTwoConcreteOddPencilValue
    (a : ℝ) (o : YoshidaOddIndex → ℝ) : ℝ :=
  o ⬝ᵥ ((factorTwoConcreteOddCleanMatrix +
    a • factorTwoConcreteOddPerturbationMatrix) *ᵥ o)

/-- The unphased alternating even--odd cross value. -/
def factorTwoConcreteAlternatingValue
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) : ℝ :=
  ∑ i, ∑ j, e i * factorTwoConcreteAlternatingMatrix i j * o j

/-- Exact scalar-pencil expansion of the synthesized concrete low phase. -/
theorem factorTwoConcreteLowPhase_eq_pencils
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoAdaptedEvenLowSynthesis e)
        (factorTwoOddLowSynthesis o) a b =
      factorTwoConcreteEvenPencilValue a e +
        factorTwoConcreteOddPencilValue a o +
        b * factorTwoConcreteAlternatingValue e o := by
  rw [factorTwoConcreteLowPhaseMatrix_represents]
  rw [factorTwoConcreteLowPhaseMatrix,
    factorTwoFiniteLowPhaseMatrix_quadratic]
  unfold factorTwoConcreteEvenPencilValue
    factorTwoConcreteOddPencilValue factorTwoConcreteAlternatingValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- Division-free pointwise Schur closure on the phase disk.  The determinant
budget is independent of `b`; the disk inequality supplies
`b² ≤ 1 - a²`. -/
theorem factorTwoConcreteLowPhase_nonneg_of_disk_schur
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hEven : 0 ≤ factorTwoConcreteEvenPencilValue a e)
    (hOdd : 0 ≤ factorTwoConcreteOddPencilValue a o)
    (hSchur :
      (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
        4 * factorTwoConcreteEvenPencilValue a e *
          factorTwoConcreteOddPencilValue a o) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  have hb : b ^ 2 ≤ 1 - a ^ 2 := by
    linarith
  have hcross :
      b ^ 2 * factorTwoConcreteAlternatingValue e o ^ 2 ≤
        (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 :=
    mul_le_mul_of_nonneg_right hb
      (sq_nonneg (factorTwoConcreteAlternatingValue e o))
  have hmixed :
      (b * factorTwoConcreteAlternatingValue e o / 2) ^ 2 ≤
        factorTwoConcreteEvenPencilValue a e *
          factorTwoConcreteOddPencilValue a o := by
    nlinarith
  have hnonneg := scalar_low_tail_nonneg
    (factorTwoConcreteEvenPencilValue a e)
    (factorTwoConcreteOddPencilValue a o)
    (b * factorTwoConcreteAlternatingValue e o / 2)
    hEven hOdd hmixed
  rw [factorTwoConcreteLowPhase_eq_pencils]
  nlinarith

/-- A certificate quantified only by the symmetric phase coordinate `a`
and all coefficient vectors closes every `b` in the unit disk.  Thus `b`
does not occur in any diagonal or determinant certificate. -/
theorem factorTwoConcreteLowPhase_nonneg_of_uniform_disk_schur
    (hEven : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ e : YoshidaEvenIndex → ℝ,
        0 ≤ factorTwoConcreteEvenPencilValue a e)
    (hOdd : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ o : YoshidaOddIndex → ℝ,
        0 ≤ factorTwoConcreteOddPencilValue a o)
    (hSchur : ∀ a : ℝ, a ^ 2 ≤ 1 →
      ∀ (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ),
        (1 - a ^ 2) * factorTwoConcreteAlternatingValue e o ^ 2 ≤
          4 * factorTwoConcreteEvenPencilValue a e *
            factorTwoConcreteOddPencilValue a o)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  have ha : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  exact factorTwoConcreteLowPhase_nonneg_of_disk_schur
    e o a b hab (hEven a ha e) (hOdd a ha o) (hSchur a ha e o)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur
