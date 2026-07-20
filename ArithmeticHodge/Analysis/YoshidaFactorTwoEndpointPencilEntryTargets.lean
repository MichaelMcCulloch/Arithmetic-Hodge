import ArithmeticHodge.Analysis.YoshidaFactorTwoPerturbationEntryTargets
import ArithmeticHodge.Analysis.YoshidaFactorTwoScalarSchurBridgeStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilEntryTargets

noncomputable section

open RatInterval
open YoshidaFactorTwoCleanEntryTargets
open YoshidaFactorTwoPerturbationEntryTargets
open YoshidaFactorTwoScalarSchurBridgeStructural

/-!
# Rational entry targets for the four endpoint pencils

The interval formulas are evaluated only in a canonical index order.  This
makes the rational center matrices symmetric by construction while
Hermitian symmetry of the true real matrices transfers entrywise
containment to the reversed index order.
-/

/-! ## Ordered interval targets -/

/-- Evaluate an interval matrix only at the ordered pair
`(min i j, max i j)`. -/
def orderedIntervalTargetMatrix
    {n : Type*} [LinearOrder n]
    (targets : Matrix n n RatInterval) : Matrix n n RatInterval :=
  fun i j ↦ targets (min i j) (max i j)

/-- The rational midpoint matrix of an ordered interval target is symmetric
without any finite index computation. -/
theorem targetCenterMatrix_orderedIntervalTargetMatrix_isSymm
    {n : Type*} [LinearOrder n]
    (targets : Matrix n n RatInterval) :
    (targetCenterMatrix
      (orderedIntervalTargetMatrix targets)).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, targetCenterMatrix_apply,
    orderedIntervalTargetMatrix, min_comm, max_comm]

/-- If the raw targets contain every entry of a Hermitian real matrix, their
ordered version still contains every entry. -/
theorem orderedIntervalTargetMatrix_contains_of_isHermitian
    {n : Type*} [LinearOrder n]
    (A : Matrix n n ℝ) (targets : Matrix n n RatInterval)
    (hA : A.IsHermitian)
    (hcontains : ∀ i j, (targets i j).Contains (A i j)) :
    ∀ i j, (orderedIntervalTargetMatrix targets i j).Contains (A i j) := by
  intro i j
  rcases le_total i j with hij | hji
  · simp only [orderedIntervalTargetMatrix, min_eq_left hij,
      max_eq_right hij]
    exact hcontains i j
  · simp only [orderedIntervalTargetMatrix, min_eq_right hji,
      max_eq_left hji]
    have hcomm : A i j = A j i := by
      simpa only [star_trivial] using (hA.apply i j).symm
    rw [hcomm]
    exact hcontains j i

/-! ## Even endpoint targets -/

/-- Ordered interval target matrix for the endpoint-adapted even pencil at
`a = 1`. -/
def factorTwoConcreteEvenPlusPencilTargetMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=
  orderedIntervalTargetMatrix fun i j ↦
    factorTwoAdaptedEvenCleanTarget i j +
      factorTwoConcreteEvenPerturbationTarget i j

/-- Ordered interval target matrix for the endpoint-adapted even pencil at
`a = -1`. -/
def factorTwoConcreteEvenMinusPencilTargetMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=
  orderedIntervalTargetMatrix fun i j ↦
    factorTwoAdaptedEvenCleanTarget i j -
      factorTwoConcreteEvenPerturbationTarget i j

theorem factorTwoConcreteEvenPlusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoConcreteEvenPlusPencilTargetMatrix i j).Contains
        (factorTwoConcreteEvenPlusPencilMatrix i j) := by
  apply orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoConcreteEvenPlusPencilMatrix
    (fun i j ↦ factorTwoAdaptedEvenCleanTarget i j +
      factorTwoConcreteEvenPerturbationTarget i j)
    factorTwoConcreteEvenPlusPencilMatrix_isHermitian
  intro i j
  simpa [factorTwoConcreteEvenPlusPencilMatrix] using
    contains_add (factorTwoAdaptedEvenCleanTarget_contains i j)
      (factorTwoConcreteEvenPerturbationTarget_contains i j)

theorem factorTwoConcreteEvenMinusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoConcreteEvenMinusPencilTargetMatrix i j).Contains
        (factorTwoConcreteEvenMinusPencilMatrix i j) := by
  apply orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoConcreteEvenMinusPencilMatrix
    (fun i j ↦ factorTwoAdaptedEvenCleanTarget i j -
      factorTwoConcreteEvenPerturbationTarget i j)
    factorTwoConcreteEvenMinusPencilMatrix_isHermitian
  intro i j
  simpa [factorTwoConcreteEvenMinusPencilMatrix] using
    contains_sub (factorTwoAdaptedEvenCleanTarget_contains i j)
      (factorTwoConcreteEvenPerturbationTarget_contains i j)

theorem factorTwoConcreteEvenPlusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoConcreteEvenPlusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

theorem factorTwoConcreteEvenMinusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoConcreteEvenMinusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

/-! ## Odd endpoint targets -/

/-- Ordered interval target matrix for the canonical odd pencil at
`a = 1`. -/
def factorTwoConcreteOddPlusPencilTargetMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex RatInterval :=
  orderedIntervalTargetMatrix fun i j ↦
    factorTwoOddCleanTarget i j +
      factorTwoConcreteOddPerturbationTarget i j

/-- Ordered interval target matrix for the canonical odd pencil at
`a = -1`. -/
def factorTwoConcreteOddMinusPencilTargetMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex RatInterval :=
  orderedIntervalTargetMatrix fun i j ↦
    factorTwoOddCleanTarget i j -
      factorTwoConcreteOddPerturbationTarget i j

theorem factorTwoConcreteOddPlusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoConcreteOddPlusPencilTargetMatrix i j).Contains
        (factorTwoConcreteOddPlusPencilMatrix i j) := by
  apply orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoConcreteOddPlusPencilMatrix
    (fun i j ↦ factorTwoOddCleanTarget i j +
      factorTwoConcreteOddPerturbationTarget i j)
    factorTwoConcreteOddPlusPencilMatrix_isHermitian
  intro i j
  simpa [factorTwoConcreteOddPlusPencilMatrix] using
    contains_add (factorTwoOddCleanTarget_contains i j)
      (factorTwoConcreteOddPerturbationTarget_contains i j)

theorem factorTwoConcreteOddMinusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoConcreteOddMinusPencilTargetMatrix i j).Contains
        (factorTwoConcreteOddMinusPencilMatrix i j) := by
  apply orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoConcreteOddMinusPencilMatrix
    (fun i j ↦ factorTwoOddCleanTarget i j -
      factorTwoConcreteOddPerturbationTarget i j)
    factorTwoConcreteOddMinusPencilMatrix_isHermitian
  intro i j
  simpa [factorTwoConcreteOddMinusPencilMatrix] using
    contains_sub (factorTwoOddCleanTarget_contains i j)
      (factorTwoConcreteOddPerturbationTarget_contains i j)

theorem factorTwoConcreteOddPlusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoConcreteOddPlusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

theorem factorTwoConcreteOddMinusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoConcreteOddMinusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilEntryTargets
