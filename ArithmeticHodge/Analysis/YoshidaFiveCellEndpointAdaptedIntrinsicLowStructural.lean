import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedLowTailStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural

noncomputable section

open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFiveCellEndpointAdaptedLowTailStructural
open YoshidaFiveCellEndpointOperatorProbeStructural

/-!
# Intrinsic coordinates for the endpoint-adapted five-cell low block

The cutoff-nine projection has five even coordinates and four odd
coordinates.  Endpoint adaptation does not add free coordinates: the degree
ten, respectively degree nine, reserve coefficient is forced by the endpoint
trace.  Thus the finite five-cell low problem is exactly a five-coordinate
even problem and a four-coordinate odd problem.
-/

/-- The endpoint-zero five-coordinate even low profile.  The coefficient of
the degree-ten reserve is forced by the value at the right endpoint. -/
def fiveCellEndpointAdaptedIntrinsicEvenProfile
    (c0 c2 c4 c6 c8 : ℝ) : ℝ → ℝ :=
  let p := factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8
  fun x ↦ p x - p 1 * fiveCellEvenEndpointReserve x

/-- The endpoint-zero four-coordinate odd low profile.  The sign reflects
the endpoint signature `(1,-1)` of the degree-nine reserve. -/
def fiveCellEndpointAdaptedIntrinsicOddProfile
    (c1 c3 c5 c7 : ℝ) : ℝ → ℝ :=
  let p := factorTwoIntrinsicNineOddProfile c1 c3 c5 c7
  fun x ↦ p x + p 1 * fiveCellOddEndpointReserve x

/-- For an even source, the endpoint-adapted low projection is exactly the
five-coordinate intrinsic even profile above. -/
theorem fiveCellEndpointAdaptedLow_even_eq_intrinsic
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    fiveCellEndpointAdaptedLow e hec =
      fiveCellEndpointAdaptedIntrinsicEvenProfile
        (factorTwoCanonicalLegendreCoefficient e hec 0)
        (factorTwoCanonicalLegendreCoefficient e hec 2)
        (factorTwoCanonicalLegendreCoefficient e hec 4)
        (factorTwoCanonicalLegendreCoefficient e hec 6)
        (factorTwoCanonicalLegendreCoefficient e hec 8) := by
  let p := centeredLegendreLowProjection e hec 9
  have hpEven : Function.Even p := by
    simpa only [p] using centeredLegendreLowProjection_even e hec heven 9
  have hpNeg : p (-1) = p 1 := by
    have h := hpEven 1
    norm_num at h ⊢
    exact h
  have hp := centeredLegendreLowProjection_nine_eq_intrinsicNineEvenProfile
    e hec heven
  change p = _ at hp
  funext x
  have hpx := congrFun hp x
  have hp1 := congrFun hp 1
  unfold fiveCellEndpointAdaptedLow fiveCellLowEndpointMean
    fiveCellLowEndpointAlternating
  change p x - (p (-1) + p 1) / 2 * fiveCellEvenEndpointReserve x -
      (p (-1) - p 1) / 2 * fiveCellOddEndpointReserve x = _
  rw [hpNeg, hpx, hp1]
  unfold fiveCellEndpointAdaptedIntrinsicEvenProfile
  ring

/-- For an odd source, the endpoint-adapted low projection is exactly the
four-coordinate intrinsic odd profile above. -/
theorem fiveCellEndpointAdaptedLow_odd_eq_intrinsic
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    fiveCellEndpointAdaptedLow o hoc =
      fiveCellEndpointAdaptedIntrinsicOddProfile
        (-factorTwoCanonicalLegendreCoefficient o hoc 1)
        (-factorTwoCanonicalLegendreCoefficient o hoc 3)
        (-factorTwoCanonicalLegendreCoefficient o hoc 5)
        (-factorTwoCanonicalLegendreCoefficient o hoc 7) := by
  let p := centeredLegendreLowProjection o hoc 9
  have hpOdd : Function.Odd p := by
    simpa only [p] using centeredLegendreLowProjection_odd o hoc hodd 9
  have hpNeg : p (-1) = -p 1 := by
    have h := hpOdd 1
    norm_num at h ⊢
    exact h
  have hp := centeredLegendreLowProjection_nine_eq_intrinsicNineOddProfile
    o hoc hodd
  change p = _ at hp
  funext x
  have hpx := congrFun hp x
  have hp1 := congrFun hp 1
  unfold fiveCellEndpointAdaptedLow fiveCellLowEndpointMean
    fiveCellLowEndpointAlternating
  change p x - (p (-1) + p 1) / 2 * fiveCellEvenEndpointReserve x -
      (p (-1) - p 1) / 2 * fiveCellOddEndpointReserve x = _
  rw [hpNeg, hpx, hp1]
  unfold fiveCellEndpointAdaptedIntrinsicOddProfile
  ring

/-- Exact finite coordinate handoff for every even source. -/
theorem fiveCellEndpointAdaptedLow_even_exists_intrinsicCoordinates
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    ∃ c0 c2 c4 c6 c8 : ℝ,
      fiveCellEndpointAdaptedLow e hec =
        fiveCellEndpointAdaptedIntrinsicEvenProfile c0 c2 c4 c6 c8 := by
  exact ⟨factorTwoCanonicalLegendreCoefficient e hec 0,
    factorTwoCanonicalLegendreCoefficient e hec 2,
    factorTwoCanonicalLegendreCoefficient e hec 4,
    factorTwoCanonicalLegendreCoefficient e hec 6,
    factorTwoCanonicalLegendreCoefficient e hec 8,
    fiveCellEndpointAdaptedLow_even_eq_intrinsic e hec heven⟩

/-- Exact finite coordinate handoff for every odd source. -/
theorem fiveCellEndpointAdaptedLow_odd_exists_intrinsicCoordinates
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    ∃ c1 c3 c5 c7 : ℝ,
      fiveCellEndpointAdaptedLow o hoc =
        fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 := by
  exact ⟨-factorTwoCanonicalLegendreCoefficient o hoc 1,
    -factorTwoCanonicalLegendreCoefficient o hoc 3,
    -factorTwoCanonicalLegendreCoefficient o hoc 5,
    -factorTwoCanonicalLegendreCoefficient o hoc 7,
    fiveCellEndpointAdaptedLow_odd_eq_intrinsic o hoc hodd⟩

/-- The concrete finite diagonal certificate has only a five-coordinate
even block and a four-coordinate odd block. -/
def FiveCellEndpointAdaptedIntrinsicLowNonnegative : Prop :=
  (∀ c0 c2 c4 c6 c8 : ℝ,
      0 ≤ fiveCellEndpointOperator
        (fiveCellEndpointAdaptedIntrinsicEvenProfile c0 c2 c4 c6 c8)) ∧
    (∀ c1 c3 c5 c7 : ℝ,
      0 ≤ fiveCellEndpointOperator
        (fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7))

theorem fiveCellEndpointAdaptedLow_nonnegative_of_even
    (hfinite : FiveCellEndpointAdaptedIntrinsicLowNonnegative)
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    0 ≤ fiveCellEndpointOperator (fiveCellEndpointAdaptedLow e hec) := by
  rw [fiveCellEndpointAdaptedLow_even_eq_intrinsic e hec heven]
  exact hfinite.1 _ _ _ _ _

theorem fiveCellEndpointAdaptedLow_nonnegative_of_odd
    (hfinite : FiveCellEndpointAdaptedIntrinsicLowNonnegative)
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    0 ≤ fiveCellEndpointOperator (fiveCellEndpointAdaptedLow o hoc) := by
  rw [fiveCellEndpointAdaptedLow_odd_eq_intrinsic o hoc hodd]
  exact hfinite.2 _ _ _ _

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural
