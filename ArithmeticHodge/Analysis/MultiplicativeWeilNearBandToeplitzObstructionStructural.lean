import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeGramStructural

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeilNearBandToeplitzObstructionStructural

noncomputable section

/-!
# The width-two Toeplitz band is not positive by itself

The fixed-lattice near band retains the diagonal and lattice lags one and
two.  Positivity of a complete rank-one Toeplitz Gram does not imply
positivity of this truncation: an exact eight-cell phase pattern has zero
complete Gram, negative near band, and a compensating positive far tail.

This is an obstruction to assembly arguments using only rank-one spectral
positivity or a nonnegative near reserve.  It does not claim that arbitrary
scalar phase patterns are realized by Bombieri test functions.
-/

/-- The scalar symbol of the diagonal-plus-two-lags Toeplitz band. -/
def widthTwoToeplitzSymbol (z : ℂ) : ℝ :=
  1 + 2 * z.re + 2 * (z ^ 2).re

/-- On the unit circle, the width-two symbol is a shifted square with sharp
lower edge `-5/4`. -/
theorem widthTwoToeplitzSymbol_eq_square_sub
    (z : ℂ) (hz : Complex.normSq z = 1) :
    widthTwoToeplitzSymbol z =
      4 * (z.re + 1 / 4) ^ 2 - 5 / 4 := by
  unfold widthTwoToeplitzSymbol
  rw [pow_two]
  simp only [Complex.mul_re]
  rw [Complex.normSq_apply] at hz
  nlinarith

theorem neg_five_four_le_widthTwoToeplitzSymbol
    (z : ℂ) (hz : Complex.normSq z = 1) :
    -(5 / 4 : ℝ) ≤ widthTwoToeplitzSymbol z := by
  rw [widthTwoToeplitzSymbol_eq_square_sub z hz]
  nlinarith [sq_nonneg (z.re + 1 / 4)]

/-- A concrete unit-circle phase attaining the negative symbol minimum. -/
def widthTwoToeplitzSymbolMinimizer : ℂ :=
  ((-1 / 4 : ℝ) : ℂ) + ((Real.sqrt 15 / 4 : ℝ) : ℂ) * Complex.I

theorem widthTwoToeplitzSymbolMinimizer_normSq :
    Complex.normSq widthTwoToeplitzSymbolMinimizer = 1 := by
  have hsqrt : (Real.sqrt 15) ^ 2 = 15 :=
    Real.sq_sqrt (by norm_num)
  rw [Complex.normSq_apply]
  norm_num [widthTwoToeplitzSymbolMinimizer]
  nlinarith

theorem widthTwoToeplitzSymbolMinimizer_value :
    widthTwoToeplitzSymbol widthTwoToeplitzSymbolMinimizer = -(5 / 4 : ℝ) := by
  rw [widthTwoToeplitzSymbol_eq_square_sub _
    widthTwoToeplitzSymbolMinimizer_normSq]
  norm_num [widthTwoToeplitzSymbolMinimizer]

theorem exists_unit_widthTwoToeplitzSymbol_negative :
    ∃ z : ℂ,
      Complex.normSq z = 1 ∧ widthTwoToeplitzSymbol z < 0 := by
  refine ⟨widthTwoToeplitzSymbolMinimizer,
    widthTwoToeplitzSymbolMinimizer_normSq, ?_⟩
  rw [widthTwoToeplitzSymbolMinimizer_value]
  norm_num

/-- Diagonal mass for a five-cell scalar sequence. -/
def scalarDiagonalFive (x0 x1 x2 x3 x4 : ℂ) : ℝ :=
  Complex.normSq x0 + Complex.normSq x1 + Complex.normSq x2 +
    Complex.normSq x3 + Complex.normSq x4

/-- Its hard diagonal-plus-lags-one-and-two truncation. -/
def scalarNearFive (x0 x1 x2 x3 x4 : ℂ) : ℝ :=
  scalarDiagonalFive x0 x1 x2 x3 x4 +
    2 * (star x1 * x0).re + 2 * (star x2 * x1).re +
    2 * (star x3 * x2).re + 2 * (star x4 * x3).re +
    2 * (star x2 * x0).re + 2 * (star x3 * x1).re +
    2 * (star x4 * x2).re

/-- Zero-padded energy of the three-tap filter with symbol
`z⁻¹ + 1/2 + z`. -/
def scalarThreeTapFilterEnergyFive (x0 x1 x2 x3 x4 : ℂ) : ℝ :=
  Complex.normSq x0 +
    Complex.normSq ((1 / 2 : ℂ) * x0 + x1) +
    Complex.normSq (x0 + (1 / 2 : ℂ) * x1 + x2) +
    Complex.normSq (x1 + (1 / 2 : ℂ) * x2 + x3) +
    Complex.normSq (x2 + (1 / 2 : ℂ) * x3 + x4) +
    Complex.normSq (x3 + (1 / 2 : ℂ) * x4) +
    Complex.normSq x4

/-- Boundary-exact finite Fejér--Riesz completion of the hard width-two
band. -/
theorem scalarThreeTapFilterEnergyFive_eq_near_add_five_fourths_diagonal
    (x0 x1 x2 x3 x4 : ℂ) :
    scalarThreeTapFilterEnergyFive x0 x1 x2 x3 x4 =
      scalarNearFive x0 x1 x2 x3 x4 +
        (5 / 4 : ℝ) * scalarDiagonalFive x0 x1 x2 x3 x4 := by
  norm_num [scalarThreeTapFilterEnergyFive, scalarNearFive,
    scalarDiagonalFive, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem neg_five_fourths_diagonal_le_scalarNearFive
    (x0 x1 x2 x3 x4 : ℂ) :
    -(5 / 4 : ℝ) * scalarDiagonalFive x0 x1 x2 x3 x4 ≤
      scalarNearFive x0 x1 x2 x3 x4 := by
  have hfilter :
      0 ≤ scalarThreeTapFilterEnergyFive x0 x1 x2 x3 x4 := by
    unfold scalarThreeTapFilterEnergyFive
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (add_nonneg (Complex.normSq_nonneg _)
                (Complex.normSq_nonneg _))
              (Complex.normSq_nonneg _))
            (Complex.normSq_nonneg _))
          (Complex.normSq_nonneg _))
        (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)
  rw [scalarThreeTapFilterEnergyFive_eq_near_add_five_fourths_diagonal]
    at hfilter
  linarith

theorem scalarNearFive_fourthRootOrbit_negative :
    scalarNearFive 1 Complex.I (-1) (-Complex.I) 1 = -1 := by
  norm_num [scalarNearFive, scalarDiagonalFive, Complex.normSq_apply]

theorem scalarFullGramFive_fourthRootOrbit_positive :
    Complex.normSq
      ((1 : ℂ) + Complex.I + (-1) + (-Complex.I) + 1) = 1 := by
  norm_num [Complex.normSq_apply]

/-- Diagonal mass of a finite scalar lattice sequence. -/
def scalarLatticeDiagonal (a : List ℂ) : ℝ :=
  (a.map Complex.normSq).sum

/-- Oriented scalar correlation at a positive lattice lag. -/
def scalarLatticeLagCorrelation (d : ℕ) (a : List ℂ) : ℂ :=
  (List.zipWith (fun x y ↦ starRingEnd ℂ x * y) (a.drop d) a).sum

/-- The diagonal together with lattice lags one and two. -/
def scalarLatticeWidthTwoBand (a : List ℂ) : ℝ :=
  scalarLatticeDiagonal a +
    2 * (scalarLatticeLagCorrelation 1 a).re +
    2 * (scalarLatticeLagCorrelation 2 a).re

/-- The actual sum of all positive lattice lags at least three. -/
def scalarLatticeFarLagSum (a : List ℂ) : ℝ :=
  (((List.range a.length).drop 3).map fun d ↦
    2 * (scalarLatticeLagCorrelation d a).re).sum

/-- The complete rank-one Gram of the scalar sequence. -/
def scalarLatticeFullGram (a : List ℂ) : ℝ :=
  Complex.normSq a.sum

theorem scalarLatticeFullGram_nonnegative (a : List ℂ) :
    0 ≤ scalarLatticeFullGram a := by
  exact Complex.normSq_nonneg _

/-- Two periods of the fourth-root phase pattern. -/
def widthTwoNegativeWitness : List ℂ :=
  [1, Complex.I, -1, -Complex.I, 1, Complex.I, -1, -Complex.I]

theorem widthTwoNegativeWitness_diagonal :
    scalarLatticeDiagonal widthTwoNegativeWitness = 8 := by
  norm_num [scalarLatticeDiagonal, widthTwoNegativeWitness, Complex.normSq]

theorem widthTwoNegativeWitness_lag_one :
    scalarLatticeLagCorrelation 1 widthTwoNegativeWitness = -7 * Complex.I := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]
  ring

theorem widthTwoNegativeWitness_lag_two :
    scalarLatticeLagCorrelation 2 widthTwoNegativeWitness = -6 := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]

theorem widthTwoNegativeWitness_lag_three :
    scalarLatticeLagCorrelation 3 widthTwoNegativeWitness = 5 * Complex.I := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]
  ring

theorem widthTwoNegativeWitness_lag_four :
    scalarLatticeLagCorrelation 4 widthTwoNegativeWitness = 4 := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]

theorem widthTwoNegativeWitness_lag_five :
    scalarLatticeLagCorrelation 5 widthTwoNegativeWitness = -3 * Complex.I := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]
  ring

theorem widthTwoNegativeWitness_lag_six :
    scalarLatticeLagCorrelation 6 widthTwoNegativeWitness = -2 := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]

theorem widthTwoNegativeWitness_lag_seven :
    scalarLatticeLagCorrelation 7 widthTwoNegativeWitness = Complex.I := by
  norm_num [scalarLatticeLagCorrelation, widthTwoNegativeWitness]

theorem widthTwoNegativeWitness_band :
    scalarLatticeWidthTwoBand widthTwoNegativeWitness = -4 := by
  rw [scalarLatticeWidthTwoBand, widthTwoNegativeWitness_diagonal,
    widthTwoNegativeWitness_lag_one, widthTwoNegativeWitness_lag_two]
  norm_num

theorem widthTwoNegativeWitness_far :
    scalarLatticeFarLagSum widthTwoNegativeWitness = 4 := by
  have hrange :
      (List.range widthTwoNegativeWitness.length).drop 3 = [3, 4, 5, 6, 7] := by
    native_decide
  rw [scalarLatticeFarLagSum, hrange]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [widthTwoNegativeWitness_lag_three,
    widthTwoNegativeWitness_lag_four, widthTwoNegativeWitness_lag_five,
    widthTwoNegativeWitness_lag_six, widthTwoNegativeWitness_lag_seven]
  norm_num

theorem widthTwoNegativeWitness_full :
    scalarLatticeFullGram widthTwoNegativeWitness = 0 := by
  norm_num [scalarLatticeFullGram, widthTwoNegativeWitness, Complex.normSq]

theorem widthTwoNegativeWitness_full_eq_band_add_far :
    scalarLatticeFullGram widthTwoNegativeWitness =
      scalarLatticeWidthTwoBand widthTwoNegativeWitness +
        scalarLatticeFarLagSum widthTwoNegativeWitness := by
  rw [widthTwoNegativeWitness_full, widthTwoNegativeWitness_band,
    widthTwoNegativeWitness_far]
  norm_num

/-- A positive-semidefinite complete rank-one Toeplitz Gram can have a
strictly negative width-two band, exactly compensated by its positive far
lags. -/
theorem exists_fullGram_nonnegative_widthTwoBand_negative_far_positive :
    ∃ a : List ℂ,
      0 ≤ scalarLatticeFullGram a ∧
      scalarLatticeWidthTwoBand a < 0 ∧
      0 < scalarLatticeFarLagSum a ∧
      scalarLatticeFullGram a =
        scalarLatticeWidthTwoBand a + scalarLatticeFarLagSum a := by
  refine ⟨widthTwoNegativeWitness,
    scalarLatticeFullGram_nonnegative _, ?_, ?_, ?_⟩
  · rw [widthTwoNegativeWitness_band]
    norm_num
  · rw [widthTwoNegativeWitness_far]
    norm_num
  · exact widthTwoNegativeWitness_full_eq_band_add_far

end

end ArithmeticHodge.Analysis.MultiplicativeWeilNearBandToeplitzObstructionStructural
