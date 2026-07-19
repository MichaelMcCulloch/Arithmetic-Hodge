import ArithmeticHodge.Analysis.YoshidaFourCellEndpointHalfFoldStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural

noncomputable section

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointSquareStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellWidthPerturbationStructural

/-!
# Scalar, polar, and endpoint terms on the positive half interval

These identities fold every nonsingular term in the four-cell parity sectors
to `[0,1]`.  Together with the endpoint trace fold, they leave only the raw
logarithmic and regular-kernel double integrals to expose before a genuine
half-interval capacity argument can be attempted.
-/

/-- An interval-integrable even scalar density has twice its positive-half
integral on the centered interval. -/
theorem integral_neg_one_one_eq_two_mul_zero_one_of_even
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (-1) 1)
    (heven : Function.Even f) :
    (∫ x : ℝ in -1..1, f x) = 2 * ∫ x : ℝ in 0..1, f x := by
  have hleft : (∫ x : ℝ in -1..0, f x) = ∫ x : ℝ in 0..1, f x := by
    have h := intervalIntegral.integral_comp_neg
      (f := f) (a := (-1 : ℝ)) (b := 0)
    rw [show (fun x : ℝ ↦ f (-x)) = f by
      funext x
      exact heven x] at h
    simpa using h
  have hl : IntervalIntegrable f volume (-1) 0 := hf.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith :
      uIcc (-1 : ℝ) 0 ⊆ uIcc (-1 : ℝ) 1)
  have hr : IntervalIntegrable f volume 0 1 := hf.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith :
      uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  have hs := intervalIntegral.integral_add_adjacent_intervals hl hr
  rw [← hs, hleft]
  ring

/-- Squaring erases either reflection sign, so centered mass always folds to
twice the positive-half mass. -/
theorem integral_sq_eq_two_mul_positiveHalf
    (w : ℝ → ℝ) (hw : Continuous w)
    (hparity : Function.Even w ∨ Function.Odd w) :
    (∫ x : ℝ in -1..1, w x ^ 2) =
      2 * ∫ x : ℝ in 0..1, w x ^ 2 := by
  apply integral_neg_one_one_eq_two_mul_zero_one_of_even
  · exact (hw.pow 2).intervalIntegrable _ _
  · intro x
    rcases hparity with heven | hodd
    · change w (-x) ^ 2 = w x ^ 2
      rw [heven]
    · change w (-x) ^ 2 = w x ^ 2
      rw [hodd]
      ring

/-- The logarithmic endpoint potential is even, so its weighted mass has the
same parity fold. -/
theorem endpointPotential_eq_two_mul_positiveHalf
    (w : ℝ → ℝ) (hw : Continuous w)
    (hparity : Function.Even w ∨ Function.Odd w) :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) =
      2 * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  apply integral_neg_one_one_eq_two_mul_zero_one_of_even
  · exact intervalIntegrable_endpointPotential_mul_sq w hw
  · intro x
    unfold yoshidaEndpointPotential
    rcases hparity with heven | hodd
    · change (-Real.log (1 - (-x) ^ 2) / 2) * w (-x) ^ 2 =
        (-Real.log (1 - x ^ 2) / 2) * w x ^ 2
      rw [heven]
      ring_nf
    · change (-Real.log (1 - (-x) ^ 2) / 2) * w (-x) ^ 2 =
        (-Real.log (1 - x ^ 2) / 2) * w x ^ 2
      rw [hodd]
      ring_nf

/-- The positive-half even Laplace rank. -/
def fourCellPositiveCoshMoment (w : ℝ → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, Real.cosh (lambda * x) * w x

/-- The positive-half odd Laplace rank. -/
def fourCellPositiveSinhMoment (w : ℝ → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, Real.sinh (lambda * x) * w x

/-- The centered cosh rank of an even profile is twice its positive-half
rank. -/
theorem centeredCoshMoment_eq_two_mul_positive_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (lambda : ℝ) :
    centeredCoshMoment w lambda =
      2 * fourCellPositiveCoshMoment w lambda := by
  unfold centeredCoshMoment fourCellPositiveCoshMoment
  apply integral_neg_one_one_eq_two_mul_zero_one_of_even
  · exact (by fun_prop : Continuous
      (fun x : ℝ ↦ Real.cosh (lambda * x) * w x)).intervalIntegrable _ _
  · intro x
    change Real.cosh (lambda * (-x)) * w (-x) =
      Real.cosh (lambda * x) * w x
    rw [show lambda * -x = -(lambda * x) by ring, Real.cosh_neg, heven]

/-- The centered sinh rank of an odd profile is twice its positive-half
rank. -/
theorem centeredSinhMoment_eq_two_mul_positive_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w)
    (lambda : ℝ) :
    centeredSinhMoment w lambda =
      2 * fourCellPositiveSinhMoment w lambda := by
  unfold centeredSinhMoment fourCellPositiveSinhMoment
  apply integral_neg_one_one_eq_two_mul_zero_one_of_even
  · exact (by fun_prop : Continuous
      (fun x : ℝ ↦ Real.sinh (lambda * x) * w x)).intervalIntegrable _ _
  · intro x
    change Real.sinh (lambda * (-x)) * w (-x) =
      Real.sinh (lambda * x) * w x
    rw [show lambda * -x = -(lambda * x) by ring, Real.sinh_neg, hodd]
    ring

/-- On an even profile the physical polar product is one positive cosh rank
on `[0,1]`, with its exact coefficient. -/
theorem physicalPolarProduct_eq_positiveCoshSquare_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (a : ℝ) :
    2 * a *
        (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x) *
        (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x) =
      8 * a * fourCellPositiveCoshMoment w (a / 2) ^ 2 := by
  have hpolar := centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq w hw a
  calc
    _ = 2 * a *
        (centeredCoshMoment w (a / 2) ^ 2 -
          centeredSinhMoment w (a / 2) ^ 2) := by
      linear_combination (2 * a) * hpolar
    _ = _ := by
      rw [centeredSinhMoment_eq_zero_of_even heven,
        centeredCoshMoment_eq_two_mul_positive_of_even w hw heven]
      ring

/-- On an odd profile the physical polar product is the negative odd sinh
rank on `[0,1]`, again with its exact coefficient. -/
theorem physicalPolarProduct_eq_neg_positiveSinhSquare_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w)
    (a : ℝ) :
    2 * a *
        (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x) *
        (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x) =
      -8 * a * fourCellPositiveSinhMoment w (a / 2) ^ 2 := by
  have hpolar := centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq w hw a
  calc
    _ = 2 * a *
        (centeredCoshMoment w (a / 2) ^ 2 -
          centeredSinhMoment w (a / 2) ^ 2) := by
      linear_combination (2 * a) * hpolar
    _ = _ := by
      rw [centeredCoshMoment_eq_zero_of_odd hodd,
        centeredSinhMoment_eq_two_mul_positive_of_odd w hw hodd]
      ring

/-- Symmetric endpoint-strip mass of the two traces exchanged by the
four-cell involution. -/
def fourCellEndpointHalfMass (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ in 0..2 / 5,
    (w (3 / 5 + t) ^ 2 + w (1 - t) ^ 2)

/-- The two endpoint channels satisfy the pointwise parallelogram identity
after integration. -/
theorem halfMatched_add_halfAntimatched_eq_four_mul_halfMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2 / 5, fourCellEndpointHalfMatched w t ^ 2) +
        (∫ t : ℝ in 0..2 / 5,
          fourCellEndpointHalfAntimatched w t ^ 2) =
      4 * fourCellEndpointHalfMass w := by
  have hplusCont : Continuous
      (fun t : ℝ ↦ fourCellEndpointHalfMatched w t ^ 2) := by
    unfold fourCellEndpointHalfMatched
    fun_prop
  have hminusCont : Continuous
      (fun t : ℝ ↦ fourCellEndpointHalfAntimatched w t ^ 2) := by
    unfold fourCellEndpointHalfAntimatched
    fun_prop
  have hplus : IntervalIntegrable
      (fun t : ℝ ↦ fourCellEndpointHalfMatched w t ^ 2) volume 0 (2 / 5) :=
    hplusCont.intervalIntegrable _ _
  have hminus : IntervalIntegrable
      (fun t : ℝ ↦ fourCellEndpointHalfAntimatched w t ^ 2) volume 0 (2 / 5) :=
    hminusCont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hplus hminus]
  unfold fourCellEndpointHalfMatched fourCellEndpointHalfAntimatched
    fourCellEndpointHalfMass
  rw [show (fun t : ℝ ↦
      (w (3 / 5 + t) + w (1 - t)) ^ 2 +
        (w (3 / 5 + t) - w (1 - t)) ^ 2) =
      fun t ↦ 2 * (w (3 / 5 + t) ^ 2 + w (1 - t) ^ 2) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- In the even sector the retained prime atom is an antimatched endpoint
square minus the exact symmetric strip mass. -/
theorem neg_primePairing_eq_halfAntimatched_sub_mass_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -(Real.sqrt 2 * Real.log 2) * fourCellEndpointPairing w =
      (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 5,
            fourCellEndpointHalfAntimatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w := by
  have hp := four_mul_fourCellEndpointPairing_eq_matched_sub_antimatched w hw
  rw [fourCellEndpointMatchedSquare_eq_halfMatched_of_even w heven,
    fourCellEndpointAntimatchedSquare_eq_halfAntimatched_of_even w heven] at hp
  have hs := halfMatched_add_halfAntimatched_eq_four_mul_halfMass w hw
  linear_combination
    (-(Real.sqrt 2 * Real.log 2) / 4) * hp +
      (-(Real.sqrt 2 * Real.log 2) / 4) * hs

/-- In the odd sector parity swaps the endpoint channels, so the same prime
atom retains the matched positive-half square. -/
theorem neg_primePairing_eq_halfMatched_sub_mass_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(Real.sqrt 2 * Real.log 2) * fourCellEndpointPairing w =
      (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 5,
            fourCellEndpointHalfMatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w := by
  have hp := four_mul_fourCellEndpointPairing_eq_matched_sub_antimatched w hw
  rw [fourCellEndpointMatchedSquare_eq_halfAntimatched_of_odd w hodd,
    fourCellEndpointAntimatchedSquare_eq_halfMatched_of_odd w hodd] at hp
  have hs := halfMatched_add_halfAntimatched_eq_four_mul_halfMass w hw
  linear_combination
    (-(Real.sqrt 2 * Real.log 2) / 4) * hp +
      (-(Real.sqrt 2 * Real.log 2) / 4) * hs

end

end ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural
