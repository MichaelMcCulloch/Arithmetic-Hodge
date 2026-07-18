import ArithmeticHodge.Analysis.SparseEntriesRobustCertificate

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural

noncomputable section

open SparseEntriesCertificate
open SparseEntriesRobustCertificate

/-!
# Robust rational certificates for the intrinsic even `P0/P2/P4/P6` block

The analytic endpoint matrices need only be uniformly close to the rational
centers below.  Exact lower-triangular congruences then prove positive
definiteness by strict diagonal dominance.  This module deliberately leaves
the analytic entrywise enclosures as hypotheses.
-/

/-- Uniform entrywise radius accepted at both endpoints. -/
def factorTwoIntrinsicNineP6EvenRobustEpsilon : ℚ := 1 / 25000

/-- Unit weights suffice after the rational congruences. -/
def factorTwoIntrinsicNineP6EvenRobustWeights : Fin 4 → ℚ :=
  ![1, 1, 1, 1]

/-- Rational center for the positive intrinsic even endpoint block. -/
def factorTwoIntrinsicNineP6EvenPlusCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(13868347 / 100000000 : ℚ), 13544326 / 100000000,
      8669679 / 100000000, -341123 / 100000000;
    13544326 / 100000000, 13837151 / 100000000,
      10610216 / 100000000, 1689163 / 100000000;
    8669679 / 100000000, 10610216 / 100000000,
      13776970 / 100000000, 8947720 / 100000000;
    -341123 / 100000000, 1689163 / 100000000,
      8947720 / 100000000, 20808820 / 100000000]

/-- Rational center for the negative intrinsic even endpoint block. -/
def factorTwoIntrinsicNineP6EvenMinusCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(59334714 / 100000000 : ℚ), 54506216 / 100000000,
      11330504 / 100000000, 9864934 / 100000000;
    54506216 / 100000000, 51542316 / 100000000,
      17967593 / 100000000, 9421947 / 100000000;
    11330504 / 100000000, 17967593 / 100000000,
      49085570 / 100000000, 9235655 / 100000000;
    9864934 / 100000000, 9421947 / 100000000,
      9235655 / 100000000, 34093609 / 100000000]

/-- Sparse lower-triangular congruence rows for the positive center. -/
def factorTwoIntrinsicNineP6EvenPlusCongruenceEntries :
    Fin 4 → SparseEntries (Fin 4) :=
  ![[(0, 1)],
    [(0, -9766 / 10000), (1, 1)],
    [(0, 28101 / 10000), (1, -35174 / 10000), (2, 1)],
    [(0, -37596 / 10000), (1, 54751 / 10000),
      (2, -25002 / 10000), (3, 1)]]

/-- Sparse lower-triangular congruence rows for the negative center. -/
def factorTwoIntrinsicNineP6EvenMinusCongruenceEntries :
    Fin 4 → SparseEntries (Fin 4) :=
  ![[(0, 1)],
    [(0, -9186 / 10000), (1, 1)],
    [(0, 45275 / 10000), (1, -51364 / 10000), (2, 1)],
    [(0, -30200 / 10000), (1, 32478 / 10000),
      (2, -6799 / 10000), (3, 1)]]

private theorem factorTwoIntrinsicNineP6EvenPlusCenter_isSymm :
    factorTwoIntrinsicNineP6EvenPlusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenPlusCenter, Matrix.transpose_apply]

private theorem factorTwoIntrinsicNineP6EvenMinusCenter_isSymm :
    factorTwoIntrinsicNineP6EvenMinusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenMinusCenter, Matrix.transpose_apply]

private theorem factorTwoIntrinsicNineP6EvenPlusCongruence_lower :
    ∀ i j,
      entriesValue (factorTwoIntrinsicNineP6EvenPlusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenPlusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem factorTwoIntrinsicNineP6EvenMinusCongruence_lower :
    ∀ i j,
      entriesValue (factorTwoIntrinsicNineP6EvenMinusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwoIntrinsicNineP6EvenMinusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem factorTwoIntrinsicNineP6EvenPlusCongruence_diagonal :
    ∀ i,
      entriesValue (factorTwoIntrinsicNineP6EvenPlusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenPlusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem factorTwoIntrinsicNineP6EvenMinusCongruence_diagonal :
    ∀ i,
      entriesValue (factorTwoIntrinsicNineP6EvenMinusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenMinusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem factorTwoIntrinsicNineP6EvenRobustWeights_pos :
    ∀ i, 0 < factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [factorTwoIntrinsicNineP6EvenRobustWeights]

private theorem factorTwoIntrinsicNineP6EvenPlusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
              factorTwoIntrinsicNineP6EvenPlusCenter
              factorTwoIntrinsicNineP6EvenRobustEpsilon i j *
            factorTwoIntrinsicNineP6EvenRobustWeights j) <
        entriesRobustDiagonalLower
            factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
            factorTwoIntrinsicNineP6EvenPlusCenter
            factorTwoIntrinsicNineP6EvenRobustEpsilon i *
          factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1,
      factorTwoIntrinsicNineP6EvenPlusCongruenceEntries,
      factorTwoIntrinsicNineP6EvenPlusCenter,
      factorTwoIntrinsicNineP6EvenRobustEpsilon,
      factorTwoIntrinsicNineP6EvenRobustWeights, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff]

private theorem factorTwoIntrinsicNineP6EvenMinusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
              factorTwoIntrinsicNineP6EvenMinusCenter
              factorTwoIntrinsicNineP6EvenRobustEpsilon i j *
            factorTwoIntrinsicNineP6EvenRobustWeights j) <
        entriesRobustDiagonalLower
            factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
            factorTwoIntrinsicNineP6EvenMinusCenter
            factorTwoIntrinsicNineP6EvenRobustEpsilon i *
          factorTwoIntrinsicNineP6EvenRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1,
      factorTwoIntrinsicNineP6EvenMinusCongruenceEntries,
      factorTwoIntrinsicNineP6EvenMinusCenter,
      factorTwoIntrinsicNineP6EvenRobustEpsilon,
      factorTwoIntrinsicNineP6EvenRobustWeights, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff]

/-- Every Hermitian matrix in the certified entrywise neighborhood of the
positive endpoint center is positive definite. -/
theorem factorTwoIntrinsicNineP6EvenPlus_posDef_of_entrywise_close
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.IsHermitian)
    (hclose : ∀ i j,
      |A i j - (factorTwoIntrinsicNineP6EvenPlusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    A.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    A factorTwoIntrinsicNineP6EvenPlusCongruenceEntries
    factorTwoIntrinsicNineP6EvenPlusCenter
    factorTwoIntrinsicNineP6EvenRobustEpsilon
    factorTwoIntrinsicNineP6EvenRobustWeights hA
    factorTwoIntrinsicNineP6EvenPlusCenter_isSymm
    factorTwoIntrinsicNineP6EvenPlusCongruence_lower
    factorTwoIntrinsicNineP6EvenPlusCongruence_diagonal
    (by norm_num [factorTwoIntrinsicNineP6EvenRobustEpsilon]) hclose
    factorTwoIntrinsicNineP6EvenRobustWeights_pos
    factorTwoIntrinsicNineP6EvenPlusDominance

/-- Every Hermitian matrix in the certified entrywise neighborhood of the
negative endpoint center is positive definite. -/
theorem factorTwoIntrinsicNineP6EvenMinus_posDef_of_entrywise_close
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.IsHermitian)
    (hclose : ∀ i j,
      |A i j - (factorTwoIntrinsicNineP6EvenMinusCenter i j : ℝ)| ≤
        (factorTwoIntrinsicNineP6EvenRobustEpsilon : ℝ)) :
    A.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    A factorTwoIntrinsicNineP6EvenMinusCongruenceEntries
    factorTwoIntrinsicNineP6EvenMinusCenter
    factorTwoIntrinsicNineP6EvenRobustEpsilon
    factorTwoIntrinsicNineP6EvenRobustWeights hA
    factorTwoIntrinsicNineP6EvenMinusCenter_isSymm
    factorTwoIntrinsicNineP6EvenMinusCongruence_lower
    factorTwoIntrinsicNineP6EvenMinusCongruence_diagonal
    (by norm_num [factorTwoIntrinsicNineP6EvenRobustEpsilon]) hclose
    factorTwoIntrinsicNineP6EvenRobustWeights_pos
    factorTwoIntrinsicNineP6EvenMinusDominance

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural
