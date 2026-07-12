import ArithmeticHodge.Analysis.YoshidaOddMomentTargets

set_option autoImplicit false
set_option maxHeartbeats 10000000

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaOddComparisonReserve

noncomputable section

open RatInterval
open YoshidaOddIntervalCertificate
open YoshidaOddGramPrefix
open YoshidaOddMomentTargets

/-!
# Entrywise reserve for Yoshida's odd comparison certificate

The target moment boxes dominate the positive-definite rational comparison
matrix by an additional entrywise margin of `1 / 40`.  This module transports
that finite kernel calculation to the actual clipped Gram under the existing
moment bridge and enclosure propositions, then records the resulting robust
perturbation theorem.
-/

/-- The target interval evaluation of the complete odd moment Gram. -/
def targetMomentIntervalGram :
    Matrix YoshidaOddIndex YoshidaOddIndex RatInterval :=
  oddMomentIntervalGram yoshidaOddSineIntervals yoshidaOddDiagonalIntervals

/-- A rational upper bound for the absolute value of every real number in an
interval. -/
def intervalAbsUpper (I : RatInterval) : ℚ :=
  max |I.lower| |I.upper|

/-- Every contained real number has absolute value at most
`intervalAbsUpper`. -/
theorem abs_le_intervalAbsUpper_of_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (intervalAbsUpper I : ℝ) := by
  have hlo : ((|I.lower| : ℚ) : ℝ) ≤ (intervalAbsUpper I : ℝ) := by
    exact_mod_cast le_max_left |I.lower| |I.upper|
  have hup : ((|I.upper| : ℚ) : ℝ) ≤ (intervalAbsUpper I : ℝ) := by
    exact_mod_cast le_max_right |I.lower| |I.upper|
  rw [abs_le]
  constructor
  · calc
      -(intervalAbsUpper I : ℝ) ≤ -((|I.lower| : ℚ) : ℝ) :=
        neg_le_neg hlo
      _ = -|(I.lower : ℝ)| := by norm_num
      _ ≤ (I.lower : ℝ) := neg_abs_le _
      _ ≤ x := hx.1
  · calc
      x ≤ (I.upper : ℝ) := hx.2
      _ ≤ |(I.upper : ℝ)| := le_abs_self _
      _ = ((|I.upper| : ℚ) : ℝ) := by norm_num
      _ ≤ (intervalAbsUpper I : ℝ) := hup

/-- Exact finite reserve left by the target moment boxes over the rational
comparison matrix. -/
theorem targetMomentIntervalGram_comparison_reserve :
    (∀ i, yoshidaOddComparison10 i i + 1 / 40 ≤
      (targetMomentIntervalGram i i).lower) ∧
    (∀ i j, i ≠ j →
      intervalAbsUpper (targetMomentIntervalGram i j) + 1 / 40 ≤
        -yoshidaOddComparison10 i j) := by
  decide +kernel

/-- A complex matrix has a `1 / 40` entrywise reserve over Yoshida's fixed
rational comparison matrix. -/
def HasYoshidaOddComparisonReserve
    (G : Matrix YoshidaOddIndex YoshidaOddIndex ℂ) : Prop :=
  (∀ i, (yoshidaOddComparison10 i i : ℝ) + 1 / 40 ≤ (G i i).re) ∧
  (∀ i j, i ≠ j →
    ‖G i j‖ + 1 / 40 ≤ -(yoshidaOddComparison10 i j : ℝ))

/-- The moment bridge and target scalar enclosures transport the finite
interval reserve to the actual clipped odd Gram. -/
theorem clippedOddFullGram_has_yoshidaOddComparisonReserve
    (hbridge : ClippedOddFullMomentBridge)
    (hS : YoshidaOddSineTargetEnclosures)
    (hD : YoshidaOddDiagonalTargetEnclosures) :
    HasYoshidaOddComparisonReserve clippedOddFullGram := by
  have hcontains := oddMomentIntervalGram_contains
    yoshidaSineMoment yoshidaDiagonalMoment
    yoshidaOddSineIntervals yoshidaOddDiagonalIntervals hS hD
  constructor
  · intro i
    have hreserve := targetMomentIntervalGram_comparison_reserve.1 i
    have hreserveReal :
        (yoshidaOddComparison10 i i : ℝ) + 1 / 40 ≤
          ((targetMomentIntervalGram i i).lower : ℝ) := by
      have hcast := (Rat.cast_le (K := ℝ)).2 hreserve
      norm_num at hcast ⊢
      exact hcast
    rw [hbridge i i]
    simpa only [Complex.ofReal_re] using
      hreserveReal.trans (hcontains i i).1
  · intro i j hij
    have hreserve := targetMomentIntervalGram_comparison_reserve.2 i j hij
    have hreserveReal :
        (intervalAbsUpper (targetMomentIntervalGram i j) : ℝ) + 1 / 40 ≤
          -(yoshidaOddComparison10 i j : ℝ) := by
      have hcast := (Rat.cast_le (K := ℝ)).2 hreserve
      norm_num at hcast ⊢
      exact hcast
    have habs := abs_le_intervalAbsUpper_of_contains (hcontains i j)
    have hfinal :
        |oddMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j| +
            1 / 40 ≤ -(yoshidaOddComparison10 i j : ℝ) := by
      dsimp only [targetMomentIntervalGram] at habs hreserveReal
      linarith
    rw [hbridge i j]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hfinal

/-- Any Hermitian entrywise perturbation bounded by the reserve preserves
positive definiteness. -/
theorem posDef_sub_of_yoshidaOddComparisonReserve
    {G E : Matrix YoshidaOddIndex YoshidaOddIndex ℂ}
    (hG : G.IsHermitian) (hreserve : HasYoshidaOddComparisonReserve G)
    (hE : E.IsHermitian) (hEbound : ∀ i j, ‖E i j‖ ≤ 1 / 40) :
    (G - E).PosDef := by
  apply Matrix.posDef_of_abs_entry_comparison
    (G - E) ((Rat.castHom ℝ).mapMatrix yoshidaOddComparison10)
  · exact hG.sub hE
  · exact yoshidaOddComparison10_posDef_real
  · intro i
    have hre : (E i i).re ≤ 1 / 40 :=
      (Complex.re_le_norm _).trans (hEbound i i)
    have hdiag := hreserve.1 i
    simp only [sub_apply, Complex.sub_re, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    change (yoshidaOddComparison10 i i : ℝ) ≤
      (G i i).re - (E i i).re
    linarith
  · intro i j hij
    have hoff := hreserve.2 i j hij
    simp only [sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    change ‖G i j - E i j‖ ≤ -(yoshidaOddComparison10 i j : ℝ)
    calc
      ‖G i j - E i j‖ ≤ ‖G i j‖ + ‖E i j‖ := norm_sub_le _ _
      _ ≤ ‖G i j‖ + 1 / 40 := add_le_add_right (hEbound i j) _
      _ ≤ -(yoshidaOddComparison10 i j : ℝ) := hoff

/-- In particular, the conditionally certified clipped Gram remains positive
definite after every Hermitian entrywise perturbation of norm at most
`1 / 40`. -/
theorem clippedOddFullGram_sub_posDef_of_bridge_and_target_enclosures
    (hbridge : ClippedOddFullMomentBridge)
    (hS : YoshidaOddSineTargetEnclosures)
    (hD : YoshidaOddDiagonalTargetEnclosures)
    (E : Matrix YoshidaOddIndex YoshidaOddIndex ℂ)
    (hE : E.IsHermitian) (hEbound : ∀ i j, ‖E i j‖ ≤ 1 / 40) :
    (clippedOddFullGram - E).PosDef := by
  apply posDef_sub_of_yoshidaOddComparisonReserve
  · exact yoshidaClippedOddGram_isHermitian
      yoshidaHalfLength yoshidaHalfLength_pos
  · exact clippedOddFullGram_has_yoshidaOddComparisonReserve hbridge hS hD
  · exact hE
  · exact hEbound

end

end ArithmeticHodge.Analysis.YoshidaOddComparisonReserve
