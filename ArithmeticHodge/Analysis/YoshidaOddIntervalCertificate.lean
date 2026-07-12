import ArithmeticHodge.Analysis.RationalIntervalSchur
import ArithmeticHodge.Analysis.YoshidaOddGramPrefix

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaOddIntervalCertificate

noncomputable section

open RatInterval
open YoshidaOddGramPrefix

/-!
# Full odd Yoshida interval certificate

The real odd moment Gram depends only on the sine moments, diagonal moments,
and `1 / pi`.  This module encloses that dependence with exact rational
interval arithmetic and connects a kernel-computed sequence of positive Schur
pivots to positive definiteness of the full `10 x 10` production clipped odd
Gram.  The analytic moment enclosures and clipped-form bridge remain explicit
premises.
-/

/-- A rational interval enclosing `1 / pi`. -/
def invPiInterval : RatInterval :=
  ⟨10000 / 31416, 10000 / 31415⟩

theorem invPiInterval_contains :
    invPiInterval.Contains (Real.pi)⁻¹ := by
  constructor
  · norm_num [invPiInterval]
    have hpUpper : Real.pi < (31416 / 10000 : ℝ) := by
      calc
        Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
        _ = 31416 / 10000 := by norm_num
    have hp : 0 < Real.pi := Real.pi_pos
    have := one_div_le_one_div_of_le hp hpUpper.le
    norm_num at this ⊢
    simpa [one_div] using this
  · norm_num [invPiInterval]
    have hpLower : (31415 / 10000 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d20
      norm_num at h ⊢
      linarith
    have hq : (0 : ℝ) < 31415 / 10000 := by norm_num
    have := one_div_le_one_div_of_le hq hpLower.le
    norm_num at this ⊢
    simpa [one_div] using this

/-- Rational coefficient of `S_n / pi` in a diagonal odd Gram entry. -/
def oddDiagonalCoeffQ (n : ℕ) : ℚ :=
  1 / (2 * n : ℚ)

/-- Rational coefficient of the sine-moment difference divided by `pi` in an
off-diagonal odd Gram entry. -/
def oddOffDiagonalCoeffQ (n m : ℕ) : ℚ :=
  (-1 : ℚ) ^ (n + m) / ((n : ℚ) ^ 2 - (m : ℚ) ^ 2)

theorem coe_oddDiagonalCoeffQ (n : ℕ) :
    (oddDiagonalCoeffQ n : ℝ) = 1 / (2 * (n : ℝ)) := by
  norm_num [oddDiagonalCoeffQ]

theorem coe_oddOffDiagonalCoeffQ (n m : ℕ) :
    (oddOffDiagonalCoeffQ n m : ℝ) =
      (-1 : ℝ) ^ (n + m) /
        ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
  norm_num [oddOffDiagonalCoeffQ]

/-- The diagonal odd moment formula with all dependence on `log 2` cancelled. -/
theorem oddMomentGram_diagonal_rational
    (S D : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) :
    oddMomentGram S D n n =
      D n + (oddDiagonalCoeffQ n : ℝ) * Real.pi⁻¹ * S n := by
  rw [oddMomentGram, if_pos rfl]
  simp only [yoshidaKappa]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [coe_oddDiagonalCoeffQ]
  field_simp [oddDiagonalCoeffQ, yoshidaLength_pos.ne', Real.pi_ne_zero, hnR]

/-- The off-diagonal odd moment formula with all dependence on `log 2`
cancelled. -/
theorem oddMomentGram_offDiagonal_rational
    (S D : ℕ → ℝ) (n m : ℕ) (hnm : n ≠ m) :
    oddMomentGram S D n m =
      (oddOffDiagonalCoeffQ n m : ℝ) * Real.pi⁻¹ *
        ((n : ℝ) * S m - (m : ℝ) * S n) := by
  rw [oddMomentGram, if_neg hnm]
  simp only [yoshidaKappa]
  have hsquaresQ : (n : ℚ) ^ 2 - (m : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hsquares : n ^ 2 = m ^ 2 := by
      exact_mod_cast (sub_eq_zero.mp h)
    exact hnm (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsquares)
  have hsquaresR : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    exact_mod_cast hsquaresQ
  rw [coe_oddOffDiagonalCoeffQ]
  field_simp [oddOffDiagonalCoeffQ, yoshidaLength_pos.ne',
    Real.pi_ne_zero, hsquaresQ, hsquaresR]

/-- The full real odd moment-model Gram on frequencies `1, ..., 10`. -/
def oddMomentFullGram (S D : ℕ → ℝ) :
    Matrix YoshidaOddIndex YoshidaOddIndex ℝ :=
  fun i j ↦ oddMomentGram S D (i.1 + 1) (j.1 + 1)

/-- Exact rational interval evaluation of the full odd moment-model Gram. -/
def oddMomentIntervalGram (S D : ℕ → RatInterval) :
    Matrix YoshidaOddIndex YoshidaOddIndex RatInterval :=
  fun i j ↦
    let n := i.1 + 1
    let m := j.1 + 1
    if i = j then
      D n + pure (oddDiagonalCoeffQ n) * invPiInterval * S n
    else
      pure (oddOffDiagonalCoeffQ n m) * invPiInterval *
        (pure (n : ℚ) * S m - pure (m : ℚ) * S n)

/-- The rational interval Gram encloses the corresponding real moment Gram
entrywise. -/
theorem oddMomentIntervalGram_contains
    (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (hS : ∀ n, 1 ≤ n → n ≤ 10 → (SI n).Contains (S n))
    (hD : ∀ n, 1 ≤ n → n ≤ 10 → (DI n).Contains (D n)) :
    ∀ i j, (oddMomentIntervalGram SI DI i j).Contains
      (oddMomentFullGram S D i j) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [oddMomentIntervalGram, ↓reduceIte, oddMomentFullGram]
    rw [oddMomentGram_diagonal_rational]
    · exact contains_add (hD (i.1 + 1) (by omega) (by omega))
        (contains_mul
          (contains_mul (contains_pure (oddDiagonalCoeffQ (i.1 + 1)))
            invPiInterval_contains)
          (hS (i.1 + 1) (by omega) (by omega)))
    · omega
  · simp only [oddMomentIntervalGram, hij, ↓reduceIte, oddMomentFullGram]
    rw [oddMomentGram_offDiagonal_rational]
    · apply contains_mul
      · exact contains_mul
          (contains_pure (oddOffDiagonalCoeffQ (i.1 + 1) (j.1 + 1)))
          invPiInterval_contains
      · apply contains_sub
        · exact contains_mul
            (by simpa using contains_pure ((i.1 + 1 : ℕ) : ℚ))
            (hS (j.1 + 1) (by omega) (by omega))
        · exact contains_mul
            (by simpa using contains_pure ((j.1 + 1 : ℕ) : ℚ))
            (hS (i.1 + 1) (by omega) (by omega))
    · intro hnm
      apply hij
      apply Fin.ext
      omega

/-- Fixed elimination order for the full odd block. -/
def oddPivotOrder : List YoshidaOddIndex :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem oddPivotOrder_nodup : oddPivotOrder.Nodup := by
  decide

theorem oddPivotOrder_cover (i : YoshidaOddIndex) : i ∈ oddPivotOrder := by
  fin_cases i <;> simp [oddPivotOrder]

/-- Scalar moment enclosures whose computed Schur pivots are positive certify
positive definiteness of the full real odd moment Gram. -/
theorem oddMomentFullGram_posDef_of_intervalPivots
    (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (hS : ∀ n, 1 ≤ n → n ≤ 10 → (SI n).Contains (S n))
    (hD : ∀ n, 1 ≤ n → n ≤ 10 → (DI n).Contains (D n))
    (hpos : RationalIntervalSchur.PositivePivots oddPivotOrder
      (oddMomentIntervalGram SI DI)) :
    (oddMomentFullGram S D).PosDef := by
  apply RationalIntervalSchur.posDef_of_intervalPositivePivots
    (oddMomentIntervalGram SI DI) (oddMomentFullGram S D)
    (ps := oddPivotOrder)
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [oddMomentFullGram, star_trivial]
    exact oddMomentGram_comm _ _ _ _
  · exact hpos
  · exact oddPivotOrder_nodup
  · exact oddPivotOrder_cover
  · exact oddMomentIntervalGram_contains S D SI DI hS hD

/-- The production clipped odd Gram at Yoshida's interval length. -/
def clippedOddFullGram : Matrix YoshidaOddIndex YoshidaOddIndex ℂ :=
  yoshidaClippedOddGram yoshidaHalfLength yoshidaHalfLength_pos

/-- Exact analytic boundary identifying the production clipped Gram with the
full real moment model. -/
def ClippedOddFullMomentBridge : Prop :=
  ∀ i j, clippedOddFullGram i j =
    (oddMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j : ℂ)

/-- The analytic bridge, scalar moment boxes, and one kernel-computed Schur
certificate imply positive definiteness of the actual full clipped odd Gram. -/
theorem clippedOddFullGram_posDef_of_bridge_and_intervalPivots
    (SI DI : ℕ → RatInterval)
    (hbridge : ClippedOddFullMomentBridge)
    (hS : ∀ n, 1 ≤ n → n ≤ 10 →
      (SI n).Contains (yoshidaSineMoment n))
    (hD : ∀ n, 1 ≤ n → n ≤ 10 →
      (DI n).Contains (yoshidaDiagonalMoment n))
    (hpos : RationalIntervalSchur.PositivePivots oddPivotOrder
      (oddMomentIntervalGram SI DI)) :
    clippedOddFullGram.PosDef := by
  have hreal := oddMomentFullGram_posDef_of_intervalPivots
    yoshidaSineMoment yoshidaDiagonalMoment SI DI hS hD hpos
  have hcomplex := RationalIntervalSchur.Matrix.PosDef.complexOfReal hreal
  have heq : clippedOddFullGram =
      RationalIntervalSchur.complexOfRealMatrix
        (oddMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment) := by
    ext i j
    exact hbridge i j
  rw [heq]
  exact hcomplex

end

end ArithmeticHodge.Analysis.YoshidaOddIntervalCertificate
