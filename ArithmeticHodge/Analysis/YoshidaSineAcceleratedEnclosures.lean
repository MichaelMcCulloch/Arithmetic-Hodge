import ArithmeticHodge.Analysis.YoshidaSineAcceleratedTail
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaSineAcceleratedEnclosures

noncomputable section

open RatInterval
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineAcceleratedTail
open YoshidaSineMomentEnclosures
open YoshidaSineSeriesTail

def tailShiftQ (K : ℕ) : ℚ := K + 1 / 4

def invPowTwoLowerInterval (K : ℕ) : RatInterval :=
  pure (1 / tailShiftQ K)

def invPowTwoUpperInterval (K : ℕ) : RatInterval :=
  pure (1 / tailShiftQ K ^ 2 + 1 / tailShiftQ K)

def invPowFourLowerInterval (K : ℕ) : RatInterval :=
  pure (1 / (3 * tailShiftQ K ^ 3))

def invPowFourUpperInterval (K : ℕ) : RatInterval :=
  pure (1 / tailShiftQ K ^ 4 + 1 / (3 * tailShiftQ K ^ 3))

def invPowSixUpperInterval (K : ℕ) : RatInterval :=
  pure (1 / tailShiftQ K ^ 6 + 1 / (5 * tailShiftQ K ^ 5))

private theorem invPowTwoLowerInterval_contains (K : ℕ) :
    (invPowTwoLowerInterval K).Contains
      (shiftedInvPowLowerPotential ((K : ℝ) + 1 / 4) 2 0) := by
  simpa [invPowTwoLowerInterval, tailShiftQ,
    shiftedInvPowLowerPotential] using contains_pure (1 / tailShiftQ K)

private theorem invPowTwoUpperInterval_contains (K : ℕ) :
    (invPowTwoUpperInterval K).Contains
      (shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 2 0) := by
  change (pure (1 / tailShiftQ K ^ 2 + 1 / tailShiftQ K)).Contains _
  convert contains_pure (1 / tailShiftQ K ^ 2 + 1 / tailShiftQ K) using 1
  norm_num [tailShiftQ, shiftedInvPowUpperPotential,
    shiftedInvPowLowerPotential, shiftedInvPow]

private theorem invPowFourLowerInterval_contains (K : ℕ) :
    (invPowFourLowerInterval K).Contains
      (shiftedInvPowLowerPotential ((K : ℝ) + 1 / 4) 4 0) := by
  change (pure (1 / (3 * tailShiftQ K ^ 3))).Contains _
  convert contains_pure (1 / (3 * tailShiftQ K ^ 3)) using 1
  norm_num [tailShiftQ, shiftedInvPowLowerPotential]

private theorem invPowFourUpperInterval_contains (K : ℕ) :
    (invPowFourUpperInterval K).Contains
      (shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 4 0) := by
  change (pure (1 / tailShiftQ K ^ 4 +
    1 / (3 * tailShiftQ K ^ 3))).Contains _
  convert contains_pure (1 / tailShiftQ K ^ 4 +
    1 / (3 * tailShiftQ K ^ 3)) using 1
  norm_num [tailShiftQ, shiftedInvPowUpperPotential,
    shiftedInvPowLowerPotential, shiftedInvPow]

private theorem invPowSixUpperInterval_contains (K : ℕ) :
    (invPowSixUpperInterval K).Contains
      (shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 6 0) := by
  change (pure (1 / tailShiftQ K ^ 6 +
    1 / (5 * tailShiftQ K ^ 5))).Contains _
  convert contains_pure (1 / tailShiftQ K ^ 6 +
    1 / (5 * tailShiftQ K ^ 5)) using 1
  norm_num [tailShiftQ, shiftedInvPowUpperPotential,
    shiftedInvPowLowerPotential, shiftedInvPow]

def cubeInterval (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 3, I.upper ^ 3⟩

def fifthInterval (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 5, I.upper ^ 5⟩

private theorem cubeInterval_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (cubeInterval I).Contains (x ^ 3) := by
  have hl0 : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hl0.trans hx.1
  constructor
  · norm_num [cubeInterval, Contains]
    exact pow_le_pow_left₀ hl0 hx.1 3
  · norm_num [cubeInterval, Contains]
    exact pow_le_pow_left₀ hx0 hx.2 3

private theorem fifthInterval_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (fifthInterval I).Contains (x ^ 5) := by
  have hl0 : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hl0.trans hx.1
  constructor
  · norm_num [fifthInterval, Contains]
    exact pow_le_pow_left₀ hl0 hx.1 5
  · norm_num [fifthInterval, Contains]
    exact pow_le_pow_left₀ hx0 hx.2 5

private theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

def acceleratedTailLowerFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  y * invPowTwoLowerInterval K -
      cubeInterval y * invPowFourUpperInterval K -
    pure 2 * y / pure ((4 : ℚ) ^ K)

def acceleratedTailUpperFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  y * invPowTwoUpperInterval K -
      cubeInterval y * invPowFourLowerInterval K +
    fifthInterval y * invPowSixUpperInterval K

def acceleratedCauchyTailInterval (n K : ℕ) : RatInterval :=
  ⟨(acceleratedTailLowerFormulaInterval n K).lower,
    (acceleratedTailUpperFormulaInterval n K).upper⟩

private theorem acceleratedTailLowerFormulaInterval_contains (n K : ℕ) :
    (acceleratedTailLowerFormulaInterval n K).Contains
      (yoshidaY n *
          shiftedInvPowLowerPotential ((K : ℝ) + 1 / 4) 2 0 -
        yoshidaY n ^ 3 *
          shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 4 0 -
        2 * yoshidaY n / (4 : ℝ) ^ K) := by
  have hy := yoshidaYInterval_contains n
  have htwo : (pure (2 : ℚ)).Contains (2 : ℝ) := by
    simpa using contains_pure (2 : ℚ)
  have hfour : (pure ((4 : ℚ) ^ K)).Contains ((4 : ℝ) ^ K) := by
    simpa using contains_pure ((4 : ℚ) ^ K)
  exact contains_sub
    (contains_sub
      (contains_mul hy (invPowTwoLowerInterval_contains K))
      (contains_mul (cubeInterval_contains (yoshidaYInterval_lower_nonneg n) hy)
        (invPowFourUpperInterval_contains K)))
    (contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ K
      positivity)
      (contains_mul htwo hy) hfour)

private theorem acceleratedTailUpperFormulaInterval_contains (n K : ℕ) :
    (acceleratedTailUpperFormulaInterval n K).Contains
      (yoshidaY n *
          shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 2 0 -
        yoshidaY n ^ 3 *
          shiftedInvPowLowerPotential ((K : ℝ) + 1 / 4) 4 0 +
        yoshidaY n ^ 5 *
          shiftedInvPowUpperPotential ((K : ℝ) + 1 / 4) 6 0) := by
  have hy := yoshidaYInterval_contains n
  rw [acceleratedTailUpperFormulaInterval]
  exact contains_add
    (contains_sub
      (contains_mul hy (invPowTwoUpperInterval_contains K))
      (contains_mul (cubeInterval_contains (yoshidaYInterval_lower_nonneg n) hy)
        (invPowFourLowerInterval_contains K)))
    (contains_mul (fifthInterval_contains (yoshidaYInterval_lower_nonneg n) hy)
      (invPowSixUpperInterval_contains K))

theorem acceleratedCauchyTailInterval_contains
    {n K : ℕ} (hn : n ≠ 0) (hK : 0 < K) :
    (acceleratedCauchyTailInterval n K).Contains
      (∑' j : ℕ, sineCauchyTerm n (K + j)) := by
  change
    ((acceleratedTailLowerFormulaInterval n K).lower : ℝ) ≤
        (∑' j : ℕ, sineCauchyTerm n (K + j)) ∧
      (∑' j : ℕ, sineCauchyTerm n (K + j)) ≤
        ((acceleratedTailUpperFormulaInterval n K).upper : ℝ)
  have ht := sineCauchyTerm_tail_accelerated_bounds hn hK
  rw [yoshidaScaledFrequency_eq_y] at ht
  have hlo := acceleratedTailLowerFormulaInterval_contains n K
  have hup := acceleratedTailUpperFormulaInterval_contains n K
  exact ⟨hlo.1.trans ht.1, ht.2.trans hup.2⟩

def acceleratedSineSeriesInterval (n K : ℕ) : RatInterval :=
  sinePolarInterval n -
    (scaledCauchyHeadInterval n K + acceleratedCauchyTailInterval n K)

theorem acceleratedSineSeriesInterval_contains
    {n K : ℕ} (hn : n ≠ 0) (hK : 0 < K) :
    (acceleratedSineSeriesInterval n K).Contains (yoshidaSineMoment n) := by
  rw [yoshidaSineMoment_eq_finiteHead_sub_tail hn K]
  exact contains_sub (sinePolarInterval_contains n)
    (contains_add (scaledCauchyHeadInterval_contains_production hn K)
      (acceleratedCauchyTailInterval_contains hn hK))

end

end ArithmeticHodge.Analysis.YoshidaSineAcceleratedEnclosures
