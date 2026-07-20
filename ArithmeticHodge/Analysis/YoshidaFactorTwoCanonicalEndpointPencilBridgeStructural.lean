import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointPencilEntryTargets
import ArithmeticHodge.Analysis.YoshidaFactorTwoScalarSchurBridgeStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCanonicalEndpointPencilBridgeStructural

noncomputable section

open RatInterval
open YoshidaCoercivityNumerics
open YoshidaEvenIntervalCertificate
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCleanEntryTargets
open YoshidaFactorTwoEndpointPencilEntryTargets
open YoshidaFactorTwoPerturbationEntryTargets
open YoshidaFactorTwoScalarSchurBridgeStructural
open YoshidaOddGramPrefix
open YoshidaWeightedTailBounds

/-!
# Canonical endpoint pencils and the adaptation congruence

The endpoint-adapted `Fin 200` even basis is an injective pullback of the
canonical frequencies `0, ..., 200`.  Certifying the canonical endpoint
pencils therefore suffices for the production adapted endpoint matrices,
while preserving the scalar interval dependencies lost by a four-term
entrywise expansion.
-/

/-- The canonical endpoint index is the retained range together with the
single correction frequency. -/
abbrev FactorTwoCanonicalEndpointEvenIndex := YoshidaEvenIndex ⊕ Unit

/-- Map the split endpoint index to the canonical frequency range
`0, ..., 200`. -/
def factorTwoCanonicalEndpointIndex :
    FactorTwoCanonicalEndpointEvenIndex → FactorTwoCanonicalEvenIndex
  | Sum.inl i => factorTwoCanonicalEvenLowIndex i
  | Sum.inr _ => factorTwoCanonicalEvenTopIndex

theorem factorTwoCanonicalEndpointIndex_injective :
    Function.Injective factorTwoCanonicalEndpointIndex := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · congr 1
    apply Fin.ext
    simpa [factorTwoCanonicalEndpointIndex,
      factorTwoCanonicalEvenLowIndex] using congrArg Fin.val hij
  · have hval := congrArg Fin.val hij
    simp [factorTwoCanonicalEndpointIndex, factorTwoCanonicalEvenLowIndex,
      factorTwoCanonicalEvenTopIndex] at hval
    omega
  · have hval := congrArg Fin.val hij
    simp [factorTwoCanonicalEndpointIndex, factorTwoCanonicalEvenLowIndex,
      factorTwoCanonicalEvenTopIndex] at hval
    omega
  · cases i
    cases j
    rfl

local instance : LinearOrder FactorTwoCanonicalEndpointEvenIndex :=
  LinearOrder.lift' factorTwoCanonicalEndpointIndex
    factorTwoCanonicalEndpointIndex_injective

/-- Canonical clean matrix on frequencies `0, ..., 200`. -/
def factorTwoCanonicalEndpointEvenCleanMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℝ :=
  fun i j ↦
    evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        (factorTwoCanonicalEndpointIndex i).1
        (factorTwoCanonicalEndpointIndex j).1 /
      yoshidaA

/-- Canonical symmetric perturbation matrix on frequencies `0, ..., 200`. -/
def factorTwoCanonicalEndpointEvenPerturbationMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℝ :=
  fun i j ↦ factorTwoCanonicalEvenPerturbationMomentFormula
    (factorTwoCanonicalEndpointIndex i)
    (factorTwoCanonicalEndpointIndex j)

/-- Positive canonical endpoint pencil. -/
def factorTwoCanonicalEndpointEvenPlusPencilMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℝ :=
  factorTwoCanonicalEndpointEvenCleanMatrix +
    factorTwoCanonicalEndpointEvenPerturbationMatrix

/-- Negative canonical endpoint pencil. -/
def factorTwoCanonicalEndpointEvenMinusPencilMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex ℝ :=
  factorTwoCanonicalEndpointEvenCleanMatrix -
    factorTwoCanonicalEndpointEvenPerturbationMatrix

theorem factorTwoCanonicalEndpointEvenCleanMatrix_isHermitian :
    factorTwoCanonicalEndpointEvenCleanMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoCanonicalEndpointEvenCleanMatrix, star_trivial]
  rw [evenMomentGram_comm]

theorem factorTwoCanonicalEndpointEvenPerturbationMatrix_isHermitian :
    factorTwoCanonicalEndpointEvenPerturbationMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoCanonicalEndpointEvenPerturbationMatrix, star_trivial]
  rw [← factorTwoCanonicalEvenPerturbationEntry_eq_moments,
    ← factorTwoCanonicalEvenPerturbationEntry_eq_moments]
  unfold factorTwoCanonicalEvenPerturbationEntry
  rw [factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEndpointIndex j))
        (continuous_factorTwoCenteredCanonicalEvenProfile
          (factorTwoCanonicalEndpointIndex i)),
    factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEndpointIndex i))
        (continuous_factorTwoCenteredCanonicalEvenProfile
          (factorTwoCanonicalEndpointIndex j)),
    factorTwoCenteredSymmetricPerturbationPolarization_comm]

theorem factorTwoCanonicalEndpointEvenPlusPencilMatrix_isHermitian :
    factorTwoCanonicalEndpointEvenPlusPencilMatrix.IsHermitian :=
  factorTwoCanonicalEndpointEvenCleanMatrix_isHermitian.add
    factorTwoCanonicalEndpointEvenPerturbationMatrix_isHermitian

theorem factorTwoCanonicalEndpointEvenMinusPencilMatrix_isHermitian :
    factorTwoCanonicalEndpointEvenMinusPencilMatrix.IsHermitian :=
  factorTwoCanonicalEndpointEvenCleanMatrix_isHermitian.sub
    factorTwoCanonicalEndpointEvenPerturbationMatrix_isHermitian

/-! ## Canonical interval targets -/

/-- Scaled clean target for one canonical endpoint entry. -/
def factorTwoCanonicalEndpointEvenCleanTarget
    (i j : FactorTwoCanonicalEndpointEvenIndex) : RatInterval :=
  factorTwoCanonicalEvenCleanTarget
      (factorTwoCanonicalEndpointIndex i).1
      (factorTwoCanonicalEndpointIndex j).1 /
    factorTwoEndpointScaleTarget

theorem factorTwoCanonicalEndpointEvenCleanTarget_contains
    (i j : FactorTwoCanonicalEndpointEvenIndex) :
    (factorTwoCanonicalEndpointEvenCleanTarget i j).Contains
      (factorTwoCanonicalEndpointEvenCleanMatrix i j) := by
  exact contains_div_of_pos factorTwoEndpointScaleTarget_lower_pos
    (factorTwoCanonicalEvenCleanTarget_contains (by omega) (by omega))
    factorTwoEndpointScaleTarget_contains

/-- Raw positive canonical endpoint target before ordering its indices. -/
def factorTwoCanonicalEndpointEvenPlusRawTarget :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex RatInterval :=
  fun i j ↦ factorTwoCanonicalEndpointEvenCleanTarget i j +
    factorTwoCanonicalEvenPerturbationTarget
      (factorTwoCanonicalEndpointIndex i)
      (factorTwoCanonicalEndpointIndex j)

/-- Raw negative canonical endpoint target before ordering its indices. -/
def factorTwoCanonicalEndpointEvenMinusRawTarget :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex RatInterval :=
  fun i j ↦ factorTwoCanonicalEndpointEvenCleanTarget i j -
    factorTwoCanonicalEvenPerturbationTarget
      (factorTwoCanonicalEndpointIndex i)
      (factorTwoCanonicalEndpointIndex j)

theorem factorTwoCanonicalEndpointEvenPlusRawTarget_contains
    (i j : FactorTwoCanonicalEndpointEvenIndex) :
    (factorTwoCanonicalEndpointEvenPlusRawTarget i j).Contains
      (factorTwoCanonicalEndpointEvenPlusPencilMatrix i j) := by
  exact contains_add
    (factorTwoCanonicalEndpointEvenCleanTarget_contains i j)
    (factorTwoCanonicalEvenPerturbationTarget_contains _ _)

theorem factorTwoCanonicalEndpointEvenMinusRawTarget_contains
    (i j : FactorTwoCanonicalEndpointEvenIndex) :
    (factorTwoCanonicalEndpointEvenMinusRawTarget i j).Contains
      (factorTwoCanonicalEndpointEvenMinusPencilMatrix i j) := by
  exact contains_sub
    (factorTwoCanonicalEndpointEvenCleanTarget_contains i j)
    (factorTwoCanonicalEvenPerturbationTarget_contains _ _)

/-- Symmetric target matrix for the positive canonical endpoint pencil. -/
def factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex RatInterval :=
  orderedIntervalTargetMatrix factorTwoCanonicalEndpointEvenPlusRawTarget

/-- Symmetric target matrix for the negative canonical endpoint pencil. -/
def factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix :
    Matrix FactorTwoCanonicalEndpointEvenIndex
      FactorTwoCanonicalEndpointEvenIndex RatInterval :=
  orderedIntervalTargetMatrix factorTwoCanonicalEndpointEvenMinusRawTarget

theorem factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix i j).Contains
        (factorTwoCanonicalEndpointEvenPlusPencilMatrix i j) :=
  orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoCanonicalEndpointEvenPlusPencilMatrix
    factorTwoCanonicalEndpointEvenPlusRawTarget
    factorTwoCanonicalEndpointEvenPlusPencilMatrix_isHermitian
    factorTwoCanonicalEndpointEvenPlusRawTarget_contains

theorem factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix_contains :
    ∀ i j,
      (factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix i j).Contains
        (factorTwoCanonicalEndpointEvenMinusPencilMatrix i j) :=
  orderedIntervalTargetMatrix_contains_of_isHermitian
    factorTwoCanonicalEndpointEvenMinusPencilMatrix
    factorTwoCanonicalEndpointEvenMinusRawTarget
    factorTwoCanonicalEndpointEvenMinusPencilMatrix_isHermitian
    factorTwoCanonicalEndpointEvenMinusRawTarget_contains

theorem factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoCanonicalEndpointEvenPlusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

theorem factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix_center_isSymm :
    (targetCenterMatrix
      factorTwoCanonicalEndpointEvenMinusPencilTargetMatrix).IsSymm :=
  targetCenterMatrix_orderedIntervalTargetMatrix_isSymm _

/-- The exact coefficient matrix for endpoint adaptation: identity on the
retained frequencies and one trace-correction column. -/
def factorTwoEndpointAdaptationMatrix :
    Matrix YoshidaEvenIndex FactorTwoCanonicalEndpointEvenIndex ℝ :=
  fun i k ↦ match k with
    | Sum.inl j => if i = j then 1 else 0
    | Sum.inr _ => -endpointEvenLowTraceRatio i

theorem factorTwoEndpointAdaptationMatrix_vecMul_injective :
    Function.Injective factorTwoEndpointAdaptationMatrix.vecMul := by
  classical
  intro x y hxy
  funext i
  have hi := congrFun hxy (Sum.inl i)
  simpa [Matrix.vecMul, factorTwoEndpointAdaptationMatrix, dotProduct,
    eq_comm] using hi

theorem factorTwoConcreteEvenPlusPencilMatrix_eq_canonical_congruence :
    factorTwoConcreteEvenPlusPencilMatrix =
      factorTwoEndpointAdaptationMatrix *
        factorTwoCanonicalEndpointEvenPlusPencilMatrix *
          factorTwoEndpointAdaptationMatrixᴴ := by
  ext i j
  rw [factorTwoConcreteEvenPlusPencilMatrix]
  simp only [Matrix.add_apply]
  rw [factorTwoConcreteAdaptedEvenCleanMatrix_apply,
    factorTwoConcreteEvenPerturbationMatrix_eq_moments]
  unfold factorTwoConcreteAdaptedEvenCleanMomentEntry
  simp [Matrix.mul_apply, factorTwoEndpointAdaptationMatrix,
    factorTwoCanonicalEndpointEvenPlusPencilMatrix,
    factorTwoCanonicalEndpointEvenCleanMatrix,
    factorTwoCanonicalEndpointEvenPerturbationMatrix,
    factorTwoCanonicalEndpointIndex, factorTwoCanonicalEvenLowIndex,
    factorTwoCanonicalEvenTopIndex]
  ring

theorem factorTwoConcreteEvenMinusPencilMatrix_eq_canonical_congruence :
    factorTwoConcreteEvenMinusPencilMatrix =
      factorTwoEndpointAdaptationMatrix *
        factorTwoCanonicalEndpointEvenMinusPencilMatrix *
          factorTwoEndpointAdaptationMatrixᴴ := by
  ext i j
  rw [factorTwoConcreteEvenMinusPencilMatrix]
  simp only [Matrix.sub_apply]
  rw [factorTwoConcreteAdaptedEvenCleanMatrix_apply,
    factorTwoConcreteEvenPerturbationMatrix_eq_moments]
  unfold factorTwoConcreteAdaptedEvenCleanMomentEntry
  simp [Matrix.mul_apply, factorTwoEndpointAdaptationMatrix,
    factorTwoCanonicalEndpointEvenMinusPencilMatrix,
    factorTwoCanonicalEndpointEvenCleanMatrix,
    factorTwoCanonicalEndpointEvenPerturbationMatrix,
    factorTwoCanonicalEndpointIndex, factorTwoCanonicalEvenLowIndex,
    factorTwoCanonicalEvenTopIndex]
  ring

/-- Positive definiteness of the canonical positive endpoint pencil pulls
back to positive definiteness of the production adapted pencil. -/
theorem factorTwoConcreteEvenPlusPencilMatrix_posDef_of_canonical
    (h : factorTwoCanonicalEndpointEvenPlusPencilMatrix.PosDef) :
    factorTwoConcreteEvenPlusPencilMatrix.PosDef := by
  rw [factorTwoConcreteEvenPlusPencilMatrix_eq_canonical_congruence]
  exact h.mul_mul_conjTranspose_same
    factorTwoEndpointAdaptationMatrix_vecMul_injective

/-- Positive definiteness of the canonical negative endpoint pencil pulls
back to positive definiteness of the production adapted pencil. -/
theorem factorTwoConcreteEvenMinusPencilMatrix_posDef_of_canonical
    (h : factorTwoCanonicalEndpointEvenMinusPencilMatrix.PosDef) :
    factorTwoConcreteEvenMinusPencilMatrix.PosDef := by
  rw [factorTwoConcreteEvenMinusPencilMatrix_eq_canonical_congruence]
  exact h.mul_mul_conjTranspose_same
    factorTwoEndpointAdaptationMatrix_vecMul_injective

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCanonicalEndpointPencilBridgeStructural
