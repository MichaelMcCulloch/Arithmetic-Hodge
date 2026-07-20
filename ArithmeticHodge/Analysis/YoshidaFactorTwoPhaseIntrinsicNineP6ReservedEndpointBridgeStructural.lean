import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EndpointParityLiftStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6ReservedEndpointBridgeStructural

noncomputable section

open SparseEntriesCertificate
open SparseEntriesRobustCertificate
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EndpointParityLiftStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# The reserved direct `P6` endpoint bridge

The direct cutoff-nine form spends `15/16` of the `P6/P7/P8` low reserve.
On the prefix through `P6`, this is exactly the one-coordinate diagonal
charge `3/2080 * c6^2`.  The definitions below subtract that charge from the
already certified `P0/P2/P4/P6` endpoint lower matrices and re-run the exact
rational robust-congruence certificate.
-/

/-- Exact coefficient of the reserve charged to the `P6` coordinate. -/
def factorTwoP6ReservedEndpointCharge : ℚ := 3 / 2080

/-- Rational one-coordinate reserve matrix in `P0,P2,P4,P6` order. -/
def factorTwoP6ReservedEndpointChargeCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, factorTwoP6ReservedEndpointCharge]

/-- Real one-coordinate reserve matrix in `P0,P2,P4,P6` order. -/
def factorTwoP6ReservedEndpointChargeMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  (Rat.castHom ℝ).mapMatrix factorTwoP6ReservedEndpointChargeCenter

/-- Positive endpoint lower matrix after the exact direct reserve charge. -/
def factorTwoP6EvenReservedPlusLowerMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenPlusLowerMatrix - factorTwoP6ReservedEndpointChargeMatrix

/-- Negative endpoint lower matrix after the exact direct reserve charge. -/
def factorTwoP6EvenReservedMinusLowerMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenMinusLowerMatrix - factorTwoP6ReservedEndpointChargeMatrix

/-- Rational center for the charged positive endpoint matrix. -/
def factorTwoP6EvenReservedPlusCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  factorTwoIntrinsicNineP6EvenPlusCenter -
    factorTwoP6ReservedEndpointChargeCenter

/-- Rational center for the charged negative endpoint matrix. -/
def factorTwoP6EvenReservedMinusCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  factorTwoIntrinsicNineP6EvenMinusCenter -
    factorTwoP6ReservedEndpointChargeCenter

private theorem factorTwoP6EvenReservedPlusCenter_isSymm :
    factorTwoP6EvenReservedPlusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoP6EvenReservedPlusCenter,
      factorTwoP6ReservedEndpointChargeCenter,
      factorTwoP6ReservedEndpointCharge,
      factorTwoIntrinsicNineP6EvenPlusCenter, Matrix.transpose_apply]

private theorem factorTwoP6EvenReservedMinusCenter_isSymm :
    factorTwoP6EvenReservedMinusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoP6EvenReservedMinusCenter,
      factorTwoP6ReservedEndpointChargeCenter,
      factorTwoP6ReservedEndpointCharge,
      factorTwoIntrinsicNineP6EvenMinusCenter, Matrix.transpose_apply]

private theorem factorTwoP6EvenPlusCongruence_lower :
    ∀ i j,
      entriesValue (factorTwoIntrinsicNineP6EvenPlusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenPlusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem factorTwoP6EvenMinusCongruence_lower :
    ∀ i j,
      entriesValue (factorTwoIntrinsicNineP6EvenMinusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenMinusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem factorTwoP6EvenPlusCongruence_diagonal :
    ∀ i,
      entriesValue (factorTwoIntrinsicNineP6EvenPlusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenPlusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem factorTwoP6EvenMinusCongruence_diagonal :
    ∀ i,
      entriesValue (factorTwoIntrinsicNineP6EvenMinusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenMinusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem factorTwoP6EvenRobustWeights_pos :
    ∀ i, 0 < factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenRobustWeights]

private theorem factorTwoP6EvenReservedPlusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
              factorTwoP6EvenReservedPlusCenter
              factorTwoIntrinsicNineP6EvenRobustEpsilon i j *
            factorTwoIntrinsicNineP6EvenRobustWeights j) <
        entriesRobustDiagonalLower
            factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
            factorTwoP6EvenReservedPlusCenter
            factorTwoIntrinsicNineP6EvenRobustEpsilon i *
          factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1,
      factorTwoIntrinsicNineP6EvenPlusCongruenceEntries,
      factorTwoP6EvenReservedPlusCenter,
      factorTwoP6ReservedEndpointChargeCenter,
      factorTwoP6ReservedEndpointCharge,
      factorTwoIntrinsicNineP6EvenPlusCenter,
      factorTwoIntrinsicNineP6EvenRobustEpsilon,
      factorTwoIntrinsicNineP6EvenRobustWeights, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff]

private theorem factorTwoP6EvenReservedMinusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
              factorTwoP6EvenReservedMinusCenter
              factorTwoIntrinsicNineP6EvenRobustEpsilon i j *
            factorTwoIntrinsicNineP6EvenRobustWeights j) <
        entriesRobustDiagonalLower
            factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
            factorTwoP6EvenReservedMinusCenter
            factorTwoIntrinsicNineP6EvenRobustEpsilon i *
          factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1,
      factorTwoIntrinsicNineP6EvenMinusCongruenceEntries,
      factorTwoP6EvenReservedMinusCenter,
      factorTwoP6ReservedEndpointChargeCenter,
      factorTwoP6ReservedEndpointCharge,
      factorTwoIntrinsicNineP6EvenMinusCenter,
      factorTwoIntrinsicNineP6EvenRobustEpsilon,
      factorTwoIntrinsicNineP6EvenRobustWeights, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff]

/-! ## Robust positivity after the charge -/

theorem factorTwoP6ReservedEndpointChargeMatrix_isHermitian :
    factorTwoP6ReservedEndpointChargeMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoP6ReservedEndpointChargeMatrix,
      factorTwoP6ReservedEndpointChargeCenter,
      factorTwoP6ReservedEndpointCharge]

theorem factorTwoP6EvenReservedPlusLowerMatrix_isHermitian :
    factorTwoP6EvenReservedPlusLowerMatrix.IsHermitian :=
  factorTwoP6EvenPlusLowerMatrix_isHermitian.sub
    factorTwoP6ReservedEndpointChargeMatrix_isHermitian

theorem factorTwoP6EvenReservedMinusLowerMatrix_isHermitian :
    factorTwoP6EvenReservedMinusLowerMatrix.IsHermitian :=
  factorTwoP6EvenMinusLowerMatrix_isHermitian.sub
    factorTwoP6ReservedEndpointChargeMatrix_isHermitian

theorem factorTwoP6EvenReservedPlusLowerMatrix_entrywise_close_of_original
    (hclose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ))
    (i j : Fin 4) :
    |factorTwoP6EvenReservedPlusLowerMatrix i j -
        (factorTwoP6EvenReservedPlusCenter i j : ℝ)| ≤
      (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ) := by
  have heq :
      factorTwoP6EvenReservedPlusLowerMatrix i j -
          (factorTwoP6EvenReservedPlusCenter i j : ℝ) =
        factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ) := by
    unfold factorTwoP6EvenReservedPlusLowerMatrix
      factorTwoP6EvenReservedPlusCenter
      factorTwoP6ReservedEndpointChargeMatrix
    simp only [Matrix.sub_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Rat.coe_castHom, Rat.cast_sub]
    ring
  rw [heq]
  exact hclose i j

theorem factorTwoP6EvenReservedMinusLowerMatrix_entrywise_close_of_original
    (hclose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ))
    (i j : Fin 4) :
    |factorTwoP6EvenReservedMinusLowerMatrix i j -
        (factorTwoP6EvenReservedMinusCenter i j : ℝ)| ≤
      (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ) := by
  have heq :
      factorTwoP6EvenReservedMinusLowerMatrix i j -
          (factorTwoP6EvenReservedMinusCenter i j : ℝ) =
        factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ) := by
    unfold factorTwoP6EvenReservedMinusLowerMatrix
      factorTwoP6EvenReservedMinusCenter
      factorTwoP6ReservedEndpointChargeMatrix
    simp only [Matrix.sub_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Rat.coe_castHom, Rat.cast_sub]
    ring
  rw [heq]
  exact hclose i j

/-- The exact rational certificate still proves the charged positive even
endpoint block positive definite. -/
theorem factorTwoP6EvenReservedPlusLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6EvenReservedPlusLowerMatrix.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    factorTwoP6EvenReservedPlusLowerMatrix
    factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
    factorTwoP6EvenReservedPlusCenter
    factorTwoIntrinsicNineP6EvenRobustEpsilon
    factorTwoIntrinsicNineP6EvenRobustWeights
    factorTwoP6EvenReservedPlusLowerMatrix_isHermitian
    factorTwoP6EvenReservedPlusCenter_isSymm
    factorTwoP6EvenPlusCongruence_lower
    factorTwoP6EvenPlusCongruence_diagonal
    (by norm_num [factorTwoIntrinsicNineP6EvenRobustEpsilon])
    (factorTwoP6EvenReservedPlusLowerMatrix_entrywise_close_of_original hclose)
    factorTwoP6EvenRobustWeights_pos
    factorTwoP6EvenReservedPlusDominance

/-- The exact rational certificate still proves the charged negative even
endpoint block positive definite. -/
theorem factorTwoP6EvenReservedMinusLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6EvenReservedMinusLowerMatrix.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    factorTwoP6EvenReservedMinusLowerMatrix
    factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
    factorTwoP6EvenReservedMinusCenter
    factorTwoIntrinsicNineP6EvenRobustEpsilon
    factorTwoIntrinsicNineP6EvenRobustWeights
    factorTwoP6EvenReservedMinusLowerMatrix_isHermitian
    factorTwoP6EvenReservedMinusCenter_isSymm
    factorTwoP6EvenMinusCongruence_lower
    factorTwoP6EvenMinusCongruence_diagonal
    (by norm_num [factorTwoIntrinsicNineP6EvenRobustEpsilon])
    (factorTwoP6EvenReservedMinusLowerMatrix_entrywise_close_of_original hclose)
    factorTwoP6EvenRobustWeights_pos
    factorTwoP6EvenReservedMinusDominance

/-! ## Exact reserve and parity-split bridge -/

theorem factorTwoP6ReservedEndpointChargeMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6ReservedEndpointChargeMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      (3 / 2080 : ℝ) * c6 ^ 2 := by
  simp [factorTwoP6EvenCoefficients,
    factorTwoP6ReservedEndpointChargeMatrix,
    factorTwoP6ReservedEndpointChargeCenter,
    factorTwoP6ReservedEndpointCharge,
    dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- On the `P6` prefix the full `15/16` allocation is exactly the charged
one-coordinate quadratic. -/
theorem factorTwoP6Prefix_lowReserve_eq_charge (c6 : ℝ) :
    (15 / 16 : ℝ) * factorTwoIntrinsicNineP678LowReserve c6 0 0 =
      (3 / 2080 : ℝ) * c6 ^ 2 := by
  unfold factorTwoIntrinsicNineP678LowReserve
  rw [factorTwoCenteredP6_energy]
  ring

theorem factorTwoP6EvenReservedPlusLowerMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenReservedPlusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 -
        (3 / 2080 : ℝ) * c6 ^ 2 := by
  rw [factorTwoP6EvenReservedPlusLowerMatrix, Matrix.sub_mulVec,
    dotProduct_sub, factorTwoP6ReservedEndpointChargeMatrix_quadratic,
    ← factorTwoP6EvenPlusLowerQuadratic_eq_matrixQuadratic]

theorem factorTwoP6EvenReservedMinusLowerMatrix_quadratic
    (c0 c2 c4 c6 : ℝ) :
    star (factorTwoP6EvenCoefficients c0 c2 c4 c6) ⬝ᵥ
        (factorTwoP6EvenReservedMinusLowerMatrix *ᵥ
          factorTwoP6EvenCoefficients c0 c2 c4 c6) =
      factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 -
        (3 / 2080 : ℝ) * c6 ^ 2 := by
  rw [factorTwoP6EvenReservedMinusLowerMatrix, Matrix.sub_mulVec,
    dotProduct_sub, factorTwoP6ReservedEndpointChargeMatrix_quadratic,
    ← factorTwoP6EvenMinusLowerQuadratic_eq_matrixQuadratic]

/-- Charged literal positive endpoint lower block in parity-split order
`P0,P2,P4,P6 | P1,P3,P5`. -/
def factorTwoP6ReservedEndpointPlusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenReservedPlusLowerMatrix 0 0
    rawSixOddPlusMatrix

/-- Charged literal negative endpoint lower block in parity-split order
`P0,P2,P4,P6 | P1,P3,P5`. -/
def factorTwoP6ReservedEndpointMinusSplitLowerMatrix :
    Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks factorTwoP6EvenReservedMinusLowerMatrix 0 0
    rawSixOddMinusMatrix

private theorem posDef_fromBlocks_zero_offDiagonal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} {D : Matrix κ κ ℝ}
    (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hD.isHermitian
  · intro x hx
    have hsplit : (x ∘ Sum.inl) ≠ 0 ∨ (x ∘ Sum.inr) ≠ 0 := by
      by_contra h
      push_neg at h
      rcases h with ⟨he, ho⟩
      apply hx
      funext i
      rcases i with i | i
      · exact congrFun he i
      · exact congrFun ho i
    rcases hsplit with he | ho
    · have hEven := hA.dotProduct_mulVec_pos he
      have hOdd := hD.posSemidef.re_dotProduct_nonneg (x ∘ Sum.inr)
      simpa [dotProduct, mulVec, Fintype.sum_sum_type] using
        add_pos_of_pos_of_nonneg hEven hOdd
    · have hEven := hA.posSemidef.re_dotProduct_nonneg (x ∘ Sum.inl)
      have hOdd := hD.dotProduct_mulVec_pos ho
      simpa [dotProduct, mulVec, Fintype.sum_sum_type] using
        add_pos_of_nonneg_of_pos hEven hOdd

theorem factorTwoP6ReservedEndpointPlusSplitLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6ReservedEndpointPlusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal
    (factorTwoP6EvenReservedPlusLowerMatrix_posDef_of_entrywise_close hclose)
    rawSixOddPlusMatrix_posDef

theorem factorTwoP6ReservedEndpointMinusSplitLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6ReservedEndpointMinusSplitLowerMatrix.PosDef := by
  exact posDef_fromBlocks_zero_offDiagonal
    (factorTwoP6EvenReservedMinusLowerMatrix_posDef_of_entrywise_close hclose)
    rawSixOddMinusMatrix_posDef

private theorem fromBlocks_zero_offDiagonal_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    star (Sum.elim x y) ⬝ᵥ
        (Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim x y) =
      star x ⬝ᵥ (A *ᵥ x) + star y ⬝ᵥ (D *ᵥ y) := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type]

theorem factorTwoP6ReservedEndpointPlusSplitLowerMatrix_quadratic
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) :
    star (factorTwoP6EndpointSplitCoefficients
        c0 c2 c4 c6 c1 c3 c5) ⬝ᵥ
      (factorTwoP6ReservedEndpointPlusSplitLowerMatrix *ᵥ
        factorTwoP6EndpointSplitCoefficients
          c0 c2 c4 c6 c1 c3 c5) =
      factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 -
          (3 / 2080 : ℝ) * c6 ^ 2 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) 1 := by
  unfold factorTwoP6EndpointSplitCoefficients
    factorTwoP6ReservedEndpointPlusSplitLowerMatrix
  rw [fromBlocks_zero_offDiagonal_quadratic,
    factorTwoP6EvenReservedPlusLowerMatrix_quadratic]
  change _ +
      star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix 1 *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) = _
  rw [rawSixOddEndpointMatrix_quadratic_eq_phaseDiagonal]

theorem factorTwoP6ReservedEndpointMinusSplitLowerMatrix_quadratic
    (c0 c2 c4 c6 c1 c3 c5 : ℝ) :
    star (factorTwoP6EndpointSplitCoefficients
        c0 c2 c4 c6 c1 c3 c5) ⬝ᵥ
      (factorTwoP6ReservedEndpointMinusSplitLowerMatrix *ᵥ
        factorTwoP6EndpointSplitCoefficients
          c0 c2 c4 c6 c1 c3 c5) =
      factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 -
          (3 / 2080 : ℝ) * c6 ^ 2 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) (-1) := by
  unfold factorTwoP6EndpointSplitCoefficients
    factorTwoP6ReservedEndpointMinusSplitLowerMatrix
  rw [fromBlocks_zero_offDiagonal_quadratic,
    factorTwoP6EvenReservedMinusLowerMatrix_quadratic]
  change _ +
      star (factorTwoP135OddCoefficients c1 c3 c5) ⬝ᵥ
        (rawSixOddEndpointMatrix (-1) *ᵥ
          factorTwoP135OddCoefficients c1 c3 c5) = _
  rw [rawSixOddEndpointMatrix_quadratic_eq_phaseDiagonal]

/-! ## Reindexing to direct prefix order -/

/-- Direct prefix coefficient order `P0,P2,P4,P1,P3,P5,P6`. -/
def factorTwoP6DirectCoefficients
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) : Fin 7 → ℝ :=
  ![c0, c2, c4, c1, c3, c5, c6]

/-- Permutation from direct prefix order to parity-grouped `Fin 7` order
`P0,P2,P4,P6,P1,P3,P5`. -/
def factorTwoP6DirectToParityOrder : Fin 7 ≃ Fin 7 where
  toFun := ![(0 : Fin 7), 1, 2, 4, 5, 6, 3]
  invFun := ![(0 : Fin 7), 1, 2, 6, 3, 4, 5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Direct prefix order converted to the parity sum index. -/
def factorTwoP6DirectToSplitEquiv : Fin 7 ≃ (Fin 4 ⊕ Fin 3) :=
  factorTwoP6DirectToParityOrder.trans factorTwoP6EndpointParityEquiv.symm

/-- Charged positive lower matrix in direct prefix order. -/
def factorTwoP6ReservedEndpointPlusDirectLowerMatrix :
    Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6ReservedEndpointPlusSplitLowerMatrix.submatrix
    factorTwoP6DirectToSplitEquiv factorTwoP6DirectToSplitEquiv

/-- Charged negative lower matrix in direct prefix order. -/
def factorTwoP6ReservedEndpointMinusDirectLowerMatrix :
    Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoP6ReservedEndpointMinusSplitLowerMatrix.submatrix
    factorTwoP6DirectToSplitEquiv factorTwoP6DirectToSplitEquiv

private theorem posDef_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (e : κ ≃ ι) :
    (A.submatrix e e).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hA.isHermitian.submatrix e)
  intro x hx
  simp only [star_trivial]
  let y : ι → ℝ := x ∘ e.symm
  have hy : y ≠ 0 := by
    intro hzero
    apply hx
    funext i
    have hi := congrFun hzero (e i)
    simpa only [y, Function.comp_apply, Equiv.symm_apply_apply,
      Pi.zero_apply] using hi
  have hpositive := hA.dotProduct_mulVec_pos hy
  simp only [star_trivial] at hpositive
  have hmul : A.submatrix e e *ᵥ x = (A *ᵥ y) ∘ e := by
    simpa only [y] using Matrix.submatrix_mulVec_equiv A x e e
  rw [hmul]
  have hxcomp : x = y ∘ e := by
    funext i
    simp only [y, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hxcomp, comp_equiv_dotProduct_comp_equiv]
  exact hpositive

theorem factorTwoP6ReservedEndpointPlusDirectLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6ReservedEndpointPlusDirectLowerMatrix.PosDef := by
  exact posDef_submatrix_equiv
    (factorTwoP6ReservedEndpointPlusSplitLowerMatrix_posDef_of_entrywise_close
      hclose) factorTwoP6DirectToSplitEquiv

theorem factorTwoP6ReservedEndpointMinusDirectLowerMatrix_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    factorTwoP6ReservedEndpointMinusDirectLowerMatrix.PosDef := by
  exact posDef_submatrix_equiv
    (factorTwoP6ReservedEndpointMinusSplitLowerMatrix_posDef_of_entrywise_close
      hclose) factorTwoP6DirectToSplitEquiv

private theorem submatrix_equiv_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) (x : κ → ℝ) :
    star x ⬝ᵥ ((A.submatrix e e) *ᵥ x) =
      star (x ∘ e.symm) ⬝ᵥ (A *ᵥ (x ∘ e.symm)) := by
  simp only [star_trivial]
  let y : ι → ℝ := x ∘ e.symm
  have hmul : A.submatrix e e *ᵥ x = (A *ᵥ y) ∘ e := by
    simpa only [y] using Matrix.submatrix_mulVec_equiv A x e e
  rw [hmul]
  have hxcomp : x = y ∘ e := by
    funext i
    simp only [y, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hxcomp, comp_equiv_dotProduct_comp_equiv]
  rw [show (y ∘ e) ∘ e.symm = y by
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]]

theorem factorTwoP6ReservedEndpointPlusDirectLowerMatrix_quadratic
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoP6ReservedEndpointPlusDirectLowerMatrix *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) =
      factorTwoP6EvenPlusLowerQuadratic c0 c2 c4 c6 -
          (3 / 2080 : ℝ) * c6 ^ 2 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) 1 := by
  rw [factorTwoP6ReservedEndpointPlusDirectLowerMatrix,
    submatrix_equiv_quadratic]
  have hcoeff :
      factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6 ∘
          factorTwoP6DirectToSplitEquiv.symm =
        factorTwoP6EndpointSplitCoefficients c0 c2 c4 c6 c1 c3 c5 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  rw [hcoeff,
    factorTwoP6ReservedEndpointPlusSplitLowerMatrix_quadratic]

theorem factorTwoP6ReservedEndpointMinusDirectLowerMatrix_quadratic
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoP6ReservedEndpointMinusDirectLowerMatrix *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) =
      factorTwoP6EvenMinusLowerQuadratic c0 c2 c4 c6 -
          (3 / 2080 : ℝ) * c6 ^ 2 +
        factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicSixOddTail c1 c3 c5) (-1) := by
  rw [factorTwoP6ReservedEndpointMinusDirectLowerMatrix,
    submatrix_equiv_quadratic]
  have hcoeff :
      factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6 ∘
          factorTwoP6DirectToSplitEquiv.symm =
        factorTwoP6EndpointSplitCoefficients c0 c2 c4 c6 c1 c3 c5 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  rw [hcoeff,
    factorTwoP6ReservedEndpointMinusSplitLowerMatrix_quadratic]

/-! ## Exact direct-prefix quadratic -/

private def factorTwoP6DirectExtendedCoefficients
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) : Fin 9 → ℝ :=
  ![c0, c2, c4, c1, c3, c5, c6, 0, 0]

theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_quadratic_eq_lowQuadratic
    (a b c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6PrefixMatrix a b *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) =
      factorTwoIntrinsicNineDirectLowQuadratic
        a b c0 c2 c4 c1 c3 c5 c6 0 0 := by
  let x := factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6
  let y := factorTwoP6DirectExtendedCoefficients c0 c2 c4 c1 c3 c5 c6
  have hfull := factorTwoIntrinsicNineDirectLowMatrix_quadratic a b y
  have hprefix :
      star x ⬝ᵥ (factorTwoIntrinsicNineDirectP6PrefixMatrix a b *ᵥ x) =
        star y ⬝ᵥ (factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ y) := by
    unfold factorTwoIntrinsicNineDirectP6PrefixMatrix
      YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural.factorTwoIntrinsicNineDirectPrefix
    simp [x, y, factorTwoP6DirectCoefficients,
      factorTwoP6DirectExtendedCoefficients, dotProduct, mulVec,
      Fin.sum_univ_succ]
  simp only [star_trivial] at hprefix ⊢
  rw [hprefix, hfull]
  rfl

/-! ## Semantic identification of the charged direct prefix -/

private theorem factorTwoIntrinsicNineEvenProfile_P0246
    (c0 c2 c4 c6 : ℝ) :
    factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 0 =
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 := by
  funext t
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicEvenP0246Profile factorTwoIntrinsicEvenP024Profile
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]

private theorem factorTwoIntrinsicNineOddProfile_P135
    (c1 c3 c5 : ℝ) :
    factorTwoIntrinsicNineOddProfile c1 c3 c5 0 =
      factorTwoIntrinsicSixOddTail c1 c3 c5 := by
  funext t
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
  simp only [Pi.add_apply, zero_mul, add_zero]

/-- The direct prefix quadratic is the actual endpoint channel phase after
the exact `P6` reserve charge. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_endpoint_quadratic
    (a c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6PrefixMatrix a 0 *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) =
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6)
          (factorTwoIntrinsicSixOddTail c1 c3 c5) a 0 -
        (3 / 2080 : ℝ) * c6 ^ 2 := by
  rw [factorTwoIntrinsicNineDirectP6PrefixMatrix_quadratic_eq_lowQuadratic,
    factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve,
    factorTwoIntrinsicNineEvenProfile_P0246,
    factorTwoIntrinsicNineOddProfile_P135,
    factorTwoP6Prefix_lowReserve_eq_charge]

/-! ## Structural domination by the charged lower matrices -/

theorem factorTwoP6ReservedEndpointPlusDirectLowerMatrix_quadratic_le_prefix
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoP6ReservedEndpointPlusDirectLowerMatrix *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ≤
      star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6PrefixMatrix 1 0 *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) := by
  rw [factorTwoP6ReservedEndpointPlusDirectLowerMatrix_quadratic,
    factorTwoIntrinsicNineDirectP6PrefixMatrix_endpoint_quadratic,
    factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
  have heven := factorTwoP6EvenPlusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  linarith

theorem factorTwoP6ReservedEndpointMinusDirectLowerMatrix_quadratic_le_prefix
    (c0 c2 c4 c1 c3 c5 c6 : ℝ) :
    star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoP6ReservedEndpointMinusDirectLowerMatrix *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ≤
      star (factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6PrefixMatrix (-1) 0 *ᵥ
          factorTwoP6DirectCoefficients c0 c2 c4 c1 c3 c5 c6) := by
  rw [factorTwoP6ReservedEndpointMinusDirectLowerMatrix_quadratic,
    factorTwoIntrinsicNineDirectP6PrefixMatrix_endpoint_quadratic,
    factorTwoEndpointChannelPhase_intrinsicP0246_P135_b_zero]
  have heven := factorTwoP6EvenMinusLowerQuadratic_le_phaseDiagonal
    c0 c2 c4 c6
  linarith

private theorem factorTwoP6DirectCoefficients_eta (x : Fin 7 → ℝ) :
    factorTwoP6DirectCoefficients
        (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) = x := by
  funext i
  fin_cases i <;> rfl

/-- The exact charged robust certificate implies positive definiteness of
the actual positive direct endpoint prefix. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_plus_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix 1 0).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian 1 0)
  intro x hx
  have hlower :=
    (factorTwoP6ReservedEndpointPlusDirectLowerMatrix_posDef_of_entrywise_close
      hclose).dotProduct_mulVec_pos hx
  have hle :=
    factorTwoP6ReservedEndpointPlusDirectLowerMatrix_quadratic_le_prefix
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  rw [factorTwoP6DirectCoefficients_eta x] at hle
  exact lt_of_lt_of_le hlower hle

/-- The exact charged robust certificate implies positive definiteness of
the actual negative direct endpoint prefix. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_minus_posDef_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix (-1) 0).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian (-1) 0)
  intro x hx
  have hlower :=
    (factorTwoP6ReservedEndpointMinusDirectLowerMatrix_posDef_of_entrywise_close
      hclose).dotProduct_mulVec_pos hx
  have hle :=
    factorTwoP6ReservedEndpointMinusDirectLowerMatrix_quadratic_le_prefix
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  rw [factorTwoP6DirectCoefficients_eta x] at hle
  exact lt_of_lt_of_le hlower hle

/-- The exact conditional endpoint pair consumed by the direct `P6` bridge. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_endpoints_posDef_of_entrywise_close
    (hPlusClose : ∀ i j,
      |factorTwoP6EvenPlusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ))
    (hMinusClose : ∀ i j,
      |factorTwoP6EvenMinusLowerMatrix i j -
          (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix 1 0).PosDef ∧
      (factorTwoIntrinsicNineDirectP6PrefixMatrix (-1) 0).PosDef := by
  exact ⟨
    factorTwoIntrinsicNineDirectP6PrefixMatrix_plus_posDef_of_entrywise_close
      hPlusClose,
    factorTwoIntrinsicNineDirectP6PrefixMatrix_minus_posDef_of_entrywise_close
      hMinusClose⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6ReservedEndpointBridgeStructural
