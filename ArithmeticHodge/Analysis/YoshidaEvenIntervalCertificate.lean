import ArithmeticHodge.Analysis.RationalIntervalSchur
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaEvenIntervalCertificate

noncomputable section

open RatInterval
open RationalIntervalSchur
open YoshidaClippedMomentBridge
open YoshidaOddGramPrefix

/-!
# Full even moment interval-certificate interface

This module gives the exact Section 6 even moment model on frequencies
`0, ..., 199`, rewrites every entry using rational coefficients and the two
constants `1 / pi` and `1 / sqrt 2`, and evaluates it with sound rational
interval arithmetic.  It also incorporates a uniform entrywise correction
radius, including Yoshida's source radius `1 / 2000`, before invoking the
kernel-checked Schur-pivot soundness theorem.

No 200-mode numerical payload or analytic moment enclosure is asserted here.
The final bridge from the production clipped form to the moment model remains
an explicit proposition.
-/

/-- The even moment model from Yoshida Section 6.  Frequencies include the
zero mode, hence the separate normalized zero/nonzero branch. -/
def evenMomentGram (S D : ℕ → ℝ) (n m : ℕ) : ℝ :=
  if n = 0 then
    if m = 0 then D 0
    else 2 * (-1 : ℝ) ^ (m + 1) * S m /
      (yoshidaLength * Real.sqrt 2 * yoshidaKappa m)
  else if m = 0 then
    2 * (-1 : ℝ) ^ (n + 1) * S n /
      (yoshidaLength * Real.sqrt 2 * yoshidaKappa n)
  else if n = m then
    D n - S n / (yoshidaLength * yoshidaKappa n)
  else
    (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
      (yoshidaKappa m * S m - yoshidaKappa n * S n) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)

theorem evenMomentGram_comm (S D : ℕ → ℝ) (n m : ℕ) :
    evenMomentGram S D n m = evenMomentGram S D m n := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      rfl
    · simp [evenMomentGram, hm]
  · by_cases hm : m = 0
    · subst m
      simp [evenMomentGram, hn]
    · by_cases hnm : n = m
      · subst m
        rfl
      · rw [evenMomentGram, if_neg hn, if_neg hm, if_neg hnm]
        rw [evenMomentGram, if_neg hm, if_neg hn, if_neg (Ne.symm hnm)]
        rw [add_comm n m]
        have hnum :
            yoshidaKappa n * S n - yoshidaKappa m * S m =
              -(yoshidaKappa m * S m - yoshidaKappa n * S n) := by ring
        have hden : yoshidaKappa m ^ 2 - yoshidaKappa n ^ 2 =
            -(yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by ring
        rw [hnum, hden]
        rw [show 2 * (-1 : ℝ) ^ (m + n) / yoshidaLength *
            -(yoshidaKappa m * S m - yoshidaKappa n * S n) =
            -(2 * (-1 : ℝ) ^ (m + n) / yoshidaLength *
              (yoshidaKappa m * S m - yoshidaKappa n * S n)) by ring]
        rw [neg_div_neg_eq]

def evenInvPiInterval : RatInterval :=
  ⟨10000 / 31416, 10000 / 31415⟩

theorem evenInvPiInterval_contains :
    evenInvPiInterval.Contains (Real.pi)⁻¹ := by
  constructor
  · norm_num [evenInvPiInterval]
    have hpUpper : Real.pi < (31416 / 10000 : ℝ) := by
      calc
        Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
        _ = 31416 / 10000 := by norm_num
    have := one_div_le_one_div_of_le Real.pi_pos hpUpper.le
    norm_num at this ⊢
    simpa [one_div] using this
  · norm_num [evenInvPiInterval]
    have hpLower : (31415 / 10000 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d20
      norm_num at h ⊢
      linarith
    have hq : (0 : ℝ) < 31415 / 10000 := by norm_num
    have := one_div_le_one_div_of_le hq hpLower.le
    norm_num at this ⊢
    simpa [one_div] using this

def evenSqrtTwoInterval : RatInterval :=
  ⟨141421 / 100000, 141422 / 100000⟩

theorem evenSqrtTwoInterval_contains :
    evenSqrtTwoInterval.Contains (Real.sqrt 2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg 2
  constructor <;> norm_num [evenSqrtTwoInterval, Contains] <;> nlinarith

def evenInvSqrtTwoInterval : RatInterval := evenSqrtTwoInterval⁻¹

theorem evenInvSqrtTwoInterval_contains :
    evenInvSqrtTwoInterval.Contains (Real.sqrt 2)⁻¹ := by
  exact contains_inv_of_pos (I := evenSqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [evenSqrtTwoInterval])
    evenSqrtTwoInterval_contains

def evenZeroCoeffQ (m : ℕ) : ℚ := (-1 : ℚ) ^ (m + 1) / m

def evenDiagonalCoeffQ (n : ℕ) : ℚ := 1 / (2 * n : ℚ)

def evenOffDiagonalCoeffQ (n m : ℕ) : ℚ :=
  (-1 : ℚ) ^ (n + m) / ((n : ℚ) ^ 2 - (m : ℚ) ^ 2)

theorem coe_evenZeroCoeffQ (m : ℕ) :
    (evenZeroCoeffQ m : ℝ) = (-1 : ℝ) ^ (m + 1) / m := by
  norm_num [evenZeroCoeffQ]

theorem coe_evenDiagonalCoeffQ (n : ℕ) :
    (evenDiagonalCoeffQ n : ℝ) = 1 / (2 * (n : ℝ)) := by
  norm_num [evenDiagonalCoeffQ]

theorem coe_evenOffDiagonalCoeffQ (n m : ℕ) :
    (evenOffDiagonalCoeffQ n m : ℝ) =
      (-1 : ℝ) ^ (n + m) /
        ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
  norm_num [evenOffDiagonalCoeffQ]

theorem evenMomentGram_zero_zero (S D : ℕ → ℝ) :
    evenMomentGram S D 0 0 = D 0 := by
  simp [evenMomentGram]

theorem evenMomentGram_zero_nonzero
    (S D : ℕ → ℝ) (m : ℕ) (hm : m ≠ 0) :
    evenMomentGram S D 0 m =
      (evenZeroCoeffQ m : ℝ) * Real.pi⁻¹ *
        (Real.sqrt 2)⁻¹ * S m := by
  rw [evenMomentGram, if_pos rfl, if_neg hm]
  rw [coe_evenZeroCoeffQ]
  simp only [yoshidaKappa]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero,
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne', hmR]

theorem evenMomentGram_nonzero_zero
    (S D : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) :
    evenMomentGram S D n 0 =
      (evenZeroCoeffQ n : ℝ) * Real.pi⁻¹ *
        (Real.sqrt 2)⁻¹ * S n := by
  rw [evenMomentGram_comm]
  exact evenMomentGram_zero_nonzero S D n hn

theorem evenMomentGram_diagonal
    (S D : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) :
    evenMomentGram S D n n =
      D n - (evenDiagonalCoeffQ n : ℝ) * Real.pi⁻¹ * S n := by
  rw [evenMomentGram, if_neg hn, if_neg hn, if_pos rfl]
  rw [coe_evenDiagonalCoeffQ]
  simp only [yoshidaKappa]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero, hnR]

theorem evenMomentGram_offDiagonal
    (S D : ℕ → ℝ) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    evenMomentGram S D n m =
      (evenOffDiagonalCoeffQ n m : ℝ) * Real.pi⁻¹ *
        ((m : ℝ) * S m - (n : ℝ) * S n) := by
  rw [evenMomentGram, if_neg hn, if_neg hm, if_neg hnm]
  rw [coe_evenOffDiagonalCoeffQ]
  simp only [yoshidaKappa]
  have hsquaresQ : (n : ℚ) ^ 2 - (m : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hsquares : n ^ 2 = m ^ 2 := by
      exact_mod_cast (sub_eq_zero.mp h)
    exact hnm (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsquares)
  have hsquaresR : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by
    exact_mod_cast hsquaresQ
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero,
    hsquaresQ, hsquaresR]

/-- The full real even moment-model Gram on frequencies `0, ..., 199`. -/
def evenMomentFullGram (S D : ℕ → ℝ) :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦ evenMomentGram S D i.1 j.1

/-- Exact rational interval evaluation of the full even moment-model Gram. -/
def evenMomentIntervalGram (S D : ℕ → RatInterval) :
    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=
  fun i j ↦
    let n := i.1
    let m := j.1
    if n = 0 then
      if m = 0 then D 0
      else pure (evenZeroCoeffQ m) * evenInvPiInterval *
        evenInvSqrtTwoInterval * S m
    else if m = 0 then
      pure (evenZeroCoeffQ n) * evenInvPiInterval *
        evenInvSqrtTwoInterval * S n
    else if i = j then
      D n - pure (evenDiagonalCoeffQ n) * evenInvPiInterval * S n
    else
      pure (evenOffDiagonalCoeffQ n m) * evenInvPiInterval *
        (pure (m : ℚ) * S m - pure (n : ℚ) * S n)

theorem evenMomentIntervalGram_contains
    (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 → (SI n).Contains (S n))
    (hD : ∀ n, n ≤ 199 → (DI n).Contains (D n)) :
    ∀ i j, (evenMomentIntervalGram SI DI i j).Contains
      (evenMomentFullGram S D i j) := by
  intro i j
  by_cases hi : i.1 = 0
  · by_cases hj : j.1 = 0
    · simp [evenMomentIntervalGram, hi, hj, evenMomentFullGram]
      rw [evenMomentGram_zero_zero]
      exact hD 0 (by omega)
    · simp [evenMomentIntervalGram, hi, hj, evenMomentFullGram]
      rw [evenMomentGram_zero_nonzero S D j.1 hj]
      exact contains_mul
        (contains_mul
          (contains_mul (contains_pure (evenZeroCoeffQ j.1))
            evenInvPiInterval_contains)
          evenInvSqrtTwoInterval_contains)
        (hS j.1 (by omega) (by omega))
  · by_cases hj : j.1 = 0
    · simp [evenMomentIntervalGram, hi, hj, evenMomentFullGram]
      rw [evenMomentGram_nonzero_zero S D i.1 hi]
      exact contains_mul
        (contains_mul
          (contains_mul (contains_pure (evenZeroCoeffQ i.1))
            evenInvPiInterval_contains)
          evenInvSqrtTwoInterval_contains)
        (hS i.1 (by omega) (by omega))
    · by_cases hij : i = j
      · subst j
        simp [evenMomentIntervalGram, hi, evenMomentFullGram]
        rw [evenMomentGram_diagonal S D i.1 hi]
        exact contains_sub (hD i.1 (by omega))
          (contains_mul
            (contains_mul (contains_pure (evenDiagonalCoeffQ i.1))
              evenInvPiInterval_contains)
            (hS i.1 (by omega) (by omega)))
      · simp [evenMomentIntervalGram, hi, hj, hij, evenMomentFullGram]
        rw [evenMomentGram_offDiagonal S D i.1 j.1 hi hj]
        · exact contains_mul
            (contains_mul
              (contains_pure (evenOffDiagonalCoeffQ i.1 j.1))
              evenInvPiInterval_contains)
            (contains_sub
              (contains_mul (by simpa using contains_pure (j.1 : ℚ))
                (hS j.1 (by omega) (by omega)))
              (contains_mul (by simpa using contains_pure (i.1 : ℚ))
                (hS i.1 (by omega) (by omega))))
        · intro hval
          apply hij
          exact Fin.ext hval

/-- Outward enlargement by a symmetric rational entrywise error budget. -/
def inflateInterval (r : ℚ) (I : RatInterval) : RatInterval :=
  ⟨I.lower - r, I.upper + r⟩

theorem inflateInterval_contains_of_abs_sub
    {r : ℚ} {I : RatInterval} {x y : ℝ}
    (hI : I.Contains x) (hxy : |y - x| ≤ (r : ℝ)) :
    (inflateInterval r I).Contains y := by
  rw [abs_le] at hxy
  constructor <;> norm_num [inflateInterval, Contains] at hI ⊢ <;> linarith

/-- The source finite-to-tail correction radius for every even low-block
entry. -/
def evenCorrectionRadius : ℚ := 1 / 2000

def inflatedEvenMomentIntervalGram (r : ℚ)
    (S D : ℕ → RatInterval) :
    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=
  fun i j ↦ inflateInterval r (evenMomentIntervalGram S D i j)

theorem inflatedEvenMomentIntervalGram_contains
    (r : ℚ) (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (A : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 → (SI n).Contains (S n))
    (hD : ∀ n, n ≤ 199 → (DI n).Contains (D n))
    (hclose : ∀ i j,
      |A i j - evenMomentFullGram S D i j| ≤ (r : ℝ)) :
    ∀ i j, (inflatedEvenMomentIntervalGram r SI DI i j).Contains (A i j) := by
  intro i j
  exact inflateInterval_contains_of_abs_sub
    (evenMomentIntervalGram_contains S D SI DI hS hD i j)
    (hclose i j)

def evenPivotOrder : List YoshidaEvenIndex := Finset.univ.toList

theorem evenPivotOrder_nodup : evenPivotOrder.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem evenPivotOrder_cover (i : YoshidaEvenIndex) : i ∈ evenPivotOrder := by
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

theorem evenMomentFullGram_posDef_of_intervalPivots
    (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 → (SI n).Contains (S n))
    (hD : ∀ n, n ≤ 199 → (DI n).Contains (D n))
    (hpos : PositivePivots evenPivotOrder
      (evenMomentIntervalGram SI DI)) :
    (evenMomentFullGram S D).PosDef := by
  apply posDef_of_intervalPositivePivots
    (evenMomentIntervalGram SI DI) (evenMomentFullGram S D)
    (ps := evenPivotOrder)
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [evenMomentFullGram, star_trivial]
    exact evenMomentGram_comm _ _ _ _
  · exact hpos
  · exact evenPivotOrder_nodup
  · exact evenPivotOrder_cover
  · exact evenMomentIntervalGram_contains S D SI DI hS hD

/-- A kernel-positive interval elimination with a uniform entrywise radius
certifies any real Hermitian corrected even matrix within that radius. -/
theorem correctedEvenRealMatrix_posDef_of_intervalPivots
    (r : ℚ) (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (A : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (hA : A.IsHermitian)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 → (SI n).Contains (S n))
    (hD : ∀ n, n ≤ 199 → (DI n).Contains (D n))
    (hclose : ∀ i j,
      |A i j - evenMomentFullGram S D i j| ≤ (r : ℝ))
    (hpos : PositivePivots evenPivotOrder
      (inflatedEvenMomentIntervalGram r SI DI)) :
    A.PosDef := by
  apply posDef_of_intervalPositivePivots
    (inflatedEvenMomentIntervalGram r SI DI) A (ps := evenPivotOrder)
  · exact hA
  · exact hpos
  · exact evenPivotOrder_nodup
  · exact evenPivotOrder_cover
  · exact inflatedEvenMomentIntervalGram_contains r S D SI DI A
      hS hD hclose

theorem correctedEvenComplexMatrix_posDef_of_intervalPivots
    (r : ℚ) (S D : ℕ → ℝ) (SI DI : ℕ → RatInterval)
    (A : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (hA : A.IsHermitian)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 → (SI n).Contains (S n))
    (hD : ∀ n, n ≤ 199 → (DI n).Contains (D n))
    (hclose : ∀ i j,
      |A i j - evenMomentFullGram S D i j| ≤ (r : ℝ))
    (hpos : PositivePivots evenPivotOrder
      (inflatedEvenMomentIntervalGram r SI DI)) :
    (complexOfRealMatrix A).PosDef :=
  (correctedEvenRealMatrix_posDef_of_intervalPivots r S D SI DI A
    hA hS hD hclose hpos).complexOfReal

def clippedEvenFullGram : Matrix YoshidaEvenIndex YoshidaEvenIndex ℂ :=
  yoshidaClippedEvenGram yoshidaHalfLength yoshidaHalfLength_pos

def ClippedEvenFullMomentBridge : Prop :=
  ∀ i j : YoshidaEvenIndex,
    clippedEvenFullGram i j =
      (evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j : ℂ)

theorem clippedEvenFullGram_posDef_of_bridge_and_intervalPivots
    (SI DI : ℕ → RatInterval)
    (hbridge : ClippedEvenFullMomentBridge)
    (hS : ∀ n, 1 ≤ n → n ≤ 199 →
      (SI n).Contains (yoshidaSineMoment n))
    (hD : ∀ n, n ≤ 199 →
      (DI n).Contains (yoshidaDiagonalMoment n))
    (hpos : PositivePivots evenPivotOrder
      (evenMomentIntervalGram SI DI)) :
    clippedEvenFullGram.PosDef := by
  have hreal := evenMomentFullGram_posDef_of_intervalPivots
    yoshidaSineMoment yoshidaDiagonalMoment SI DI hS hD hpos
  have hcomplex :
      (complexOfRealMatrix
        (evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment)).PosDef :=
    hreal.complexOfReal
  have heq : clippedEvenFullGram = complexOfRealMatrix
      (evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment) := by
    ext i j
    rw [hbridge i j]
    rfl
  exact heq.symm ▸ hcomplex

end

end ArithmeticHodge.Analysis.YoshidaEvenIntervalCertificate
