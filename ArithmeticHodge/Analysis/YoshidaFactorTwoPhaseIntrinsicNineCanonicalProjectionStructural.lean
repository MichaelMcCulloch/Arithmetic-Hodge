import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural

noncomputable section

open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# The canonical cutoff-nine projection in intrinsic coordinates

The canonical Hilbert projection through degrees below nine is already a
finite shifted-Legendre sum.  Centered parity removes exactly half of those
coordinates.  The remaining five even, respectively four odd, coordinates
are precisely the intrinsic profiles used by the cutoff-nine static handoff.
-/

/-- The coefficient of the unnormalised centered Legendre mode of degree
`n` in the canonical finite projection. -/
def factorTwoCanonicalLegendreCoefficient
    (w : ℝ → ℝ) (hw : Continuous w) (n : ℕ) : ℝ :=
  shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) n *
    ‖shiftedLegendreL2 n‖⁻¹

private theorem shiftedLegendreReal_zero_centered (x : ℝ) :
    (shiftedLegendreReal 0).eval ((x + 1) / 2) = centeredEvenP0 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP0]

private theorem shiftedLegendreReal_one_centered (x : ℝ) :
    (shiftedLegendreReal 1).eval ((x + 1) / 2) = -centeredP1 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP1]
  ring

private theorem shiftedLegendreReal_two_centered (x : ℝ) :
    (shiftedLegendreReal 2).eval ((x + 1) / 2) = centeredEvenP2 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP2]
  ring

private theorem shiftedLegendreReal_three_centered (x : ℝ) :
    (shiftedLegendreReal 3).eval ((x + 1) / 2) = -centeredP3 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3]
  ring

private theorem shiftedLegendreReal_four_centered (x : ℝ) :
    (shiftedLegendreReal 4).eval ((x + 1) / 2) = factorTwoCenteredP4 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP4]
  ring

private theorem shiftedLegendreReal_five_centered (x : ℝ) :
    (shiftedLegendreReal 5).eval ((x + 1) / 2) = -factorTwoCenteredP5 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5]
  ring

/-- The canonical cutoff-nine projection of an even profile is exactly the
five-coordinate intrinsic even profile, with its Hilbert coefficients
converted from the normalised basis to the classical Legendre basis. -/
theorem centeredLegendreLowProjection_nine_eq_intrinsicNineEvenProfile
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    centeredLegendreLowProjection e hec 9 =
      factorTwoIntrinsicNineEvenProfile
        (factorTwoCanonicalLegendreCoefficient e hec 0)
        (factorTwoCanonicalLegendreCoefficient e hec 2)
        (factorTwoCanonicalLegendreCoefficient e hec 4)
        (factorTwoCanonicalLegendreCoefficient e hec 6)
        (factorTwoCanonicalLegendreCoefficient e hec 8) := by
  have h1 := centeredPullback_repr_eq_zero_of_even_of_odd
    e (centeredPullback_memLp_two e hec) heven 1 (by norm_num : Odd 1)
  have h3 := centeredPullback_repr_eq_zero_of_even_of_odd
    e (centeredPullback_memLp_two e hec) heven 3 (by norm_num : Odd 3)
  have h5 := centeredPullback_repr_eq_zero_of_even_of_odd
    e (centeredPullback_memLp_two e hec) heven 5 (by norm_num : Odd 5)
  have h7 := centeredPullback_repr_eq_zero_of_even_of_odd
    e (centeredPullback_memLp_two e hec) heven 7 (by norm_num : Odd 7)
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 e hec) 1 = 0 at h1
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 e hec) 3 = 0 at h3
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 e hec) 5 = 0 at h5
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 e hec) 7 = 0 at h7
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [normalizedShiftedLegendrePolynomial, Polynomial.eval_smul,
    smul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    h1, h3, h5, h7, zero_mul, zero_add, add_zero]
  rw [shiftedLegendreReal_zero_centered, shiftedLegendreReal_two_centered,
    shiftedLegendreReal_four_centered]
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
    factorTwoCanonicalLegendreCoefficient factorTwoCenteredP6 factorTwoCenteredP8
  simp only [Pi.add_apply]
  ring

/-- The canonical cutoff-nine projection of an odd profile is exactly the
four-coordinate intrinsic odd profile.  The signs record that the project's
shifted odd modes are the negatives of the classical centered modes. -/
theorem centeredLegendreLowProjection_nine_eq_intrinsicNineOddProfile
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    centeredLegendreLowProjection o hoc 9 =
      factorTwoIntrinsicNineOddProfile
        (-factorTwoCanonicalLegendreCoefficient o hoc 1)
        (-factorTwoCanonicalLegendreCoefficient o hoc 3)
        (-factorTwoCanonicalLegendreCoefficient o hoc 5)
        (-factorTwoCanonicalLegendreCoefficient o hoc 7) := by
  have h0 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 0 (by norm_num : Even 0)
  have h2 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 2 (by norm_num : Even 2)
  have h4 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 4 (by norm_num : Even 4)
  have h6 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 6 (by norm_num : Even 6)
  have h8 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 8 (by norm_num : Even 8)
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 0 = 0 at h0
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 2 = 0 at h2
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 4 = 0 at h4
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 6 = 0 at h6
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 8 = 0 at h8
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [normalizedShiftedLegendrePolynomial, Polynomial.eval_smul,
    smul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    h0, h2, h4, h6, h8, zero_mul, zero_add, add_zero]
  rw [shiftedLegendreReal_one_centered, shiftedLegendreReal_three_centered,
    shiftedLegendreReal_five_centered]
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    factorTwoCanonicalLegendreCoefficient factorTwoCenteredP7
  simp only [Pi.add_apply]
  ring

/-- Existential coordinate form of the canonical cutoff-nine even
projection, convenient for the finite static handoff. -/
theorem centeredLegendreLowProjection_nine_even_exists_intrinsicCoordinates
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    ∃ c0 c2 c4 c6 c8 : ℝ,
      centeredLegendreLowProjection e hec 9 =
        factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 := by
  exact ⟨factorTwoCanonicalLegendreCoefficient e hec 0,
    factorTwoCanonicalLegendreCoefficient e hec 2,
    factorTwoCanonicalLegendreCoefficient e hec 4,
    factorTwoCanonicalLegendreCoefficient e hec 6,
    factorTwoCanonicalLegendreCoefficient e hec 8,
    centeredLegendreLowProjection_nine_eq_intrinsicNineEvenProfile
      e hec heven⟩

/-- Existential coordinate form of the canonical cutoff-nine odd
projection, convenient for the finite static handoff. -/
theorem centeredLegendreLowProjection_nine_odd_exists_intrinsicCoordinates
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    ∃ c1 c3 c5 c7 : ℝ,
      centeredLegendreLowProjection o hoc 9 =
        factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 := by
  exact ⟨-factorTwoCanonicalLegendreCoefficient o hoc 1,
    -factorTwoCanonicalLegendreCoefficient o hoc 3,
    -factorTwoCanonicalLegendreCoefficient o hoc 5,
    -factorTwoCanonicalLegendreCoefficient o hoc 7,
    centeredLegendreLowProjection_nine_eq_intrinsicNineOddProfile
      o hoc hodd⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
