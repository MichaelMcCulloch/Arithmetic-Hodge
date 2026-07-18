import ArithmeticHodge.Analysis.SparseEntriesRobustCertificate
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialCertificateStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialRobustCertificateStructural

noncomputable section

open FiniteIntervalMultiplierGramLoewnerStructural
open SparseEntriesCertificate
open SparseEntriesRobustCertificate
open ThreeByThreePositiveMixedDeterminant
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural

/-!
# Robust exact-rational certificates for the polynomial endpoint gaps

The analytic endpoint gaps need only be uniformly close to the rational
centers below.  Exact sparse triangular congruences then certify positive
definiteness by weighted strict diagonal dominance.  Thus the numerical
input is isolated in nine entrywise enclosures at each endpoint, while the
certificate itself is checked entirely in exact rational arithmetic.
-/

/-- Exact entrywise radius required at both endpoints. -/
def directP6PolynomialRobustEpsilon : ℚ := 1 / 200000

/-- Exact positive weights used in the robust dominance inequalities. -/
def directP6PolynomialRobustWeights : Fin 3 → ℚ := ![1, 1, 2]

/-- Rational center for the positive polynomial endpoint gap. -/
def directP6PolynomialPlusCenter : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(18743450 / 1000000000 : ℚ), 19379039 / 1000000000,
      15088095 / 1000000000;
    19379039 / 1000000000, 20367645 / 1000000000,
      16644227 / 1000000000;
    15088095 / 1000000000, 16644227 / 1000000000,
      15746243 / 1000000000]

/-- Rational center for the negative polynomial endpoint gap. -/
def directP6PolynomialMinusCenter : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(166543304 / 1000000000 : ℚ), 152338593 / 1000000000,
      12437894 / 1000000000;
    152338593 / 1000000000, 143834973 / 1000000000,
      35524045 / 1000000000;
    12437894 / 1000000000, 35524045 / 1000000000,
      141854472 / 1000000000]

/-- Sparse lower-triangular congruence rows for the positive center. -/
def directP6PolynomialPlusCongruenceEntries :
    Fin 3 → SparseEntries (Fin 3) :=
  ![[(0, 1)],
    [(0, -1034 / 1000), (1, 1)],
    [(0, 2451 / 1000), (1, -3149 / 1000), (2, 1)]]

/-- Sparse lower-triangular congruence rows for the negative center. -/
def directP6PolynomialMinusCongruenceEntries :
    Fin 3 → SparseEntries (Fin 3) :=
  ![[(0, 1)],
    [(0, -915 / 1000), (1, 1)],
    [(0, 4845 / 1000), (1, -5378 / 1000), (2, 1)]]

/-- The exact low matrix is Hermitian before any endpoint specialization. -/
theorem factorTwoIntrinsicNineDirectP024ExactLowMatrix_isHermitian
    (sigma : ℝ) :
    (factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factorTwoIntrinsicNineDirectP024ExactLowMatrix, symmetricMatrix3,
      Matrix.conjTranspose_apply]

/-- The inverse-weight-free part of the selector Gram is Hermitian. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram_isHermitian
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram sigma q).IsHermitian := by
  ext i j
  change
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
        sigma q j i x) =
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
          sigma q i j x
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
  ring

/-- The polynomial upper selector Gram is Hermitian. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_isHermitian
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
      sigma q).IsHermitian := by
  exact
    (factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram_isHermitian
      sigma q).add
      (finiteIntervalMultiplierGram_isHermitian (-1) 1
        directP6RetainedEvenAtanhReciprocalMajorant
        (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q))

/-- Every polynomial-majorant endpoint gap is Hermitian. -/
theorem factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap_isHermitian
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
      sigma q).IsHermitian := by
  have hLow := factorTwoIntrinsicNineDirectP024ExactLowMatrix_isHermitian sigma
  have hUpper :=
    factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_isHermitian
      sigma q
  apply Matrix.IsHermitian.ext
  intro i j
  have hLow' :
      factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma j i =
        factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma i j := by
    simpa using hLow.apply i j
  have hUpper' :
      factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
          sigma q j i =
        factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
          sigma q i j := by
    simpa using hUpper.apply i j
  simp only [factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap,
    Matrix.sub_apply, Matrix.smul_apply, star_trivial]
  rw [hLow', hUpper']

/-- Positive endpoint polynomial gap Hermiticity. -/
theorem factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusLoewnerGap_isHermitian :
    (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap 1
      factorTwoIntrinsicNineDirectP6ExactSelectorPlus).IsHermitian :=
  factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap_isHermitian
    1 factorTwoIntrinsicNineDirectP6ExactSelectorPlus

/-- Negative endpoint polynomial gap Hermiticity. -/
theorem factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusLoewnerGap_isHermitian :
    (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap (-1)
      factorTwoIntrinsicNineDirectP6ExactSelectorMinus).IsHermitian :=
  factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap_isHermitian
    (-1) factorTwoIntrinsicNineDirectP6ExactSelectorMinus

private theorem directP6PolynomialPlusCenter_isSymm :
    directP6PolynomialPlusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directP6PolynomialPlusCenter, Matrix.transpose_apply]

private theorem directP6PolynomialMinusCenter_isSymm :
    directP6PolynomialMinusCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directP6PolynomialMinusCenter, Matrix.transpose_apply]

private theorem directP6PolynomialPlusCongruence_lower :
    ∀ i j,
      entriesValue (directP6PolynomialPlusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directP6PolynomialPlusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem directP6PolynomialMinusCongruence_lower :
    ∀ i j,
      entriesValue (directP6PolynomialMinusCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directP6PolynomialMinusCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem directP6PolynomialPlusCongruence_diagonal :
    ∀ i, entriesValue (directP6PolynomialPlusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [directP6PolynomialPlusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem directP6PolynomialMinusCongruence_diagonal :
    ∀ i, entriesValue (directP6PolynomialMinusCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [directP6PolynomialMinusCongruenceEntries, entriesValue,
      Fin.ext_iff]

private theorem directP6PolynomialRobustWeights_pos :
    ∀ i, 0 < directP6PolynomialRobustWeights i := by
  intro i
  fin_cases i <;> norm_num [directP6PolynomialRobustWeights]

private theorem directP6PolynomialPlusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius directP6PolynomialPlusCongruenceEntries
              directP6PolynomialPlusCenter directP6PolynomialRobustEpsilon i j *
            directP6PolynomialRobustWeights j) <
        entriesRobustDiagonalLower directP6PolynomialPlusCongruenceEntries
            directP6PolynomialPlusCenter directP6PolynomialRobustEpsilon i *
          directP6PolynomialRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1, directP6PolynomialPlusCongruenceEntries,
      directP6PolynomialPlusCenter, directP6PolynomialRobustEpsilon,
      directP6PolynomialRobustWeights, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

private theorem directP6PolynomialMinusDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius directP6PolynomialMinusCongruenceEntries
              directP6PolynomialMinusCenter directP6PolynomialRobustEpsilon i j *
            directP6PolynomialRobustWeights j) <
        entriesRobustDiagonalLower directP6PolynomialMinusCongruenceEntries
            directP6PolynomialMinusCenter directP6PolynomialRobustEpsilon i *
          directP6PolynomialRobustWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1, directP6PolynomialMinusCongruenceEntries,
      directP6PolynomialMinusCenter, directP6PolynomialRobustEpsilon,
      directP6PolynomialRobustWeights, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

/-- The positive polynomial endpoint certificate follows from a uniform
`1 / 200000` enclosure around its exact rational center. -/
theorem factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
          1 factorTwoIntrinsicNineDirectP6ExactSelectorPlus i j -
        (directP6PolynomialPlusCenter i j : ℝ)| ≤
          (directP6PolynomialRobustEpsilon : ℝ)) :
    FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate := by
  exact posDef_of_sparseEntries_robust_congruence
    (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap 1
      factorTwoIntrinsicNineDirectP6ExactSelectorPlus)
    directP6PolynomialPlusCongruenceEntries directP6PolynomialPlusCenter
    directP6PolynomialRobustEpsilon directP6PolynomialRobustWeights
    factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusLoewnerGap_isHermitian
    directP6PolynomialPlusCenter_isSymm
    directP6PolynomialPlusCongruence_lower
    directP6PolynomialPlusCongruence_diagonal
    (by norm_num [directP6PolynomialRobustEpsilon])
    hclose directP6PolynomialRobustWeights_pos directP6PolynomialPlusDominance

/-- The negative polynomial endpoint certificate follows from a uniform
`1 / 200000` enclosure around its exact rational center. -/
theorem factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate_of_entrywise_close
    (hclose : ∀ i j,
      |factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
          (-1) factorTwoIntrinsicNineDirectP6ExactSelectorMinus i j -
        (directP6PolynomialMinusCenter i j : ℝ)| ≤
          (directP6PolynomialRobustEpsilon : ℝ)) :
    FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate := by
  exact posDef_of_sparseEntries_robust_congruence
    (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap (-1)
      factorTwoIntrinsicNineDirectP6ExactSelectorMinus)
    directP6PolynomialMinusCongruenceEntries directP6PolynomialMinusCenter
    directP6PolynomialRobustEpsilon directP6PolynomialRobustWeights
    factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusLoewnerGap_isHermitian
    directP6PolynomialMinusCenter_isSymm
    directP6PolynomialMinusCongruence_lower
    directP6PolynomialMinusCongruence_diagonal
    (by norm_num [directP6PolynomialRobustEpsilon])
    hclose directP6PolynomialRobustWeights_pos directP6PolynomialMinusDominance

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialRobustCertificateStructural
