import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedLowTailStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural

noncomputable section

open YoshidaFactorTwoEndpointParityPencil
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open UnitIntervalLogEnergyAffine
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

private theorem centeredPullbackL2_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    centeredPullbackL2 (u + v) (hu.add hv) =
      centeredPullbackL2 u hu + centeredPullbackL2 v hv := by
  let fu : unitInterval → ℝ := fun t ↦ centeredPullback u (t : ℝ)
  let fv : unitInterval → ℝ := fun t ↦ centeredPullback v (t : ℝ)
  have huLp : MeasureTheory.MemLp fu 2 := by
    simpa only [fu] using centeredPullback_memLp_two u hu
  have hvLp : MeasureTheory.MemLp fv 2 := by
    simpa only [fv] using centeredPullback_memLp_two v hv
  have huvLp := centeredPullback_memLp_two (u + v) (hu.add hv)
  unfold centeredPullbackL2
  calc
    huvLp.toLp (fun t : unitInterval ↦
        centeredPullback (u + v) (t : ℝ)) =
        (huLp.add hvLp).toLp (fu + fv) := by
      apply MeasureTheory.MemLp.toLp_congr
      filter_upwards [] with t
      simp only [fu, fv, Pi.add_apply]
      unfold centeredPullback
      rfl
    _ = huLp.toLp fu + hvLp.toLp fv :=
      MeasureTheory.MemLp.toLp_add huLp hvLp
    _ = _ := by rfl

private theorem centeredLegendreLowProjection_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (k : ℕ) :
    centeredLegendreLowProjection (u + v) (hu.add hv) k =
      centeredLegendreLowProjection u hu k +
        centeredLegendreLowProjection v hv k := by
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [centeredPullbackL2_add u v hu hv]
  simp only [map_add, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    Pi.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [lp.coeFn_add, Pi.add_apply]
  ring

private theorem fiveCellLowEndpointMean_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fiveCellLowEndpointMean (u + v) (hu.add hv) =
      fiveCellLowEndpointMean u hu + fiveCellLowEndpointMean v hv := by
  unfold fiveCellLowEndpointMean
  rw [centeredLegendreLowProjection_add u v hu hv 9]
  simp only [Pi.add_apply]
  ring

private theorem fiveCellLowEndpointAlternating_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fiveCellLowEndpointAlternating (u + v) (hu.add hv) =
      fiveCellLowEndpointAlternating u hu +
        fiveCellLowEndpointAlternating v hv := by
  unfold fiveCellLowEndpointAlternating
  rw [centeredLegendreLowProjection_add u v hu hv 9]
  simp only [Pi.add_apply]
  ring

/-- Endpoint adaptation is a real-linear operation.  This is the bridge
needed to split an arbitrary finite low profile into its reflection sectors. -/
theorem fiveCellEndpointAdaptedLow_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fiveCellEndpointAdaptedLow (u + v) (hu.add hv) =
      fiveCellEndpointAdaptedLow u hu +
        fiveCellEndpointAdaptedLow v hv := by
  funext x
  unfold fiveCellEndpointAdaptedLow
  rw [centeredLegendreLowProjection_add u v hu hv 9,
    fiveCellLowEndpointMean_add u v hu hv,
    fiveCellLowEndpointAlternating_add u v hu hv]
  simp only [Pi.add_apply]
  ring

private theorem fiveCellEndpointAdaptedLow_congr
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (h : u = v) :
    fiveCellEndpointAdaptedLow u hu =
      fiveCellEndpointAdaptedLow v hv := by
  subst v
  rfl

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

/-- Every endpoint-adapted cutoff-nine low profile, without a parity
hypothesis, is the sum of one five-coordinate even profile and one
four-coordinate odd profile.  This is the exact nine-dimensional finite
handoff used by the five-cell diagonal problem. -/
theorem fiveCellEndpointAdaptedLow_exists_intrinsicParityCoordinates
    (w : ℝ → ℝ) (hw : Continuous w) :
    ∃ c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ,
      fiveCellEndpointAdaptedLow w hw =
        fiveCellEndpointAdaptedIntrinsicEvenProfile c0 c2 c4 c6 c8 +
          fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 := by
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  have hec : Continuous e := by
    simpa only [e] using continuous_factorTwoReflectionEvenPart hw
  have hoc : Continuous o := by
    simpa only [o] using continuous_factorTwoReflectionOddPart hw
  have heven : Function.Even e := by
    simpa only [e] using factorTwoReflectionEvenPart_even w
  have hodd : Function.Odd o := by
    simpa only [o] using factorTwoReflectionOddPart_odd w
  obtain ⟨c0, c2, c4, c6, c8, heq⟩ :=
    fiveCellEndpointAdaptedLow_even_exists_intrinsicCoordinates
      e hec heven
  obtain ⟨c1, c3, c5, c7, hoq⟩ :=
    fiveCellEndpointAdaptedLow_odd_exists_intrinsicCoordinates
      o hoc hodd
  refine ⟨c0, c2, c4, c6, c8, c1, c3, c5, c7, ?_⟩
  have hadd := fiveCellEndpointAdaptedLow_add e o hec hoc
  have hsplit : e + o = w := by
    simpa only [e, o] using factorTwoReflectionEvenPart_add_oddPart w
  have hleft :
      fiveCellEndpointAdaptedLow w hw =
        fiveCellEndpointAdaptedLow (e + o) (hec.add hoc) := by
    exact fiveCellEndpointAdaptedLow_congr
      w (e + o) hw (hec.add hoc) hsplit.symm
  calc
    fiveCellEndpointAdaptedLow w hw =
        fiveCellEndpointAdaptedLow e hec +
          fiveCellEndpointAdaptedLow o hoc := by
      exact hleft.trans hadd
    _ = fiveCellEndpointAdaptedIntrinsicEvenProfile c0 c2 c4 c6 c8 +
        fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 := by
      rw [heq, hoq]

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
