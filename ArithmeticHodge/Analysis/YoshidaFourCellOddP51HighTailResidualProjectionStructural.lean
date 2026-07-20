import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualProjectionStructural

noncomputable section

open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open YoshidaEndpointPotentialOddTailParsevalStructural
open YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51HighTailResidualRepresenterStructural
open YoshidaFourCellOddP51Polynomial18TailStructural
open YoshidaFourCellOddP51UpperStripTailStructural

/-!
# Exact orthogonal-projection identity for the complete P51 main row

The three analytic channels are first added in `L²`; only then is the
complete shifted-Legendre block below `P53` removed.  This file proves that
this single projection is exactly the combined high-tail representer from
the production row, and records its Pythagorean norm deficit.
-/

/-- Complete unprojected Hilbert source of the degree-eighteen main row. -/
def fourCellOddP51Kernel18MainSourceL2 : UnitIntervalL2 :=
  fourCellOddQ51ScaledEndpointPotentialSourceL2 +
    fourCellOddP51Polynomial18RegularSourceL2 +
      fourCellOddP51UpperStripOddL2

/-- Every genuine `P53+` vector pairs identically with the combined source
and with the sum of the three separately projected tails. -/
theorem inner_fourCellOddP51Kernel18MainP53PlusL2_eq_source
    (R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ fourCellOddP51Kernel18MainP53PlusL2 R =
      inner ℝ fourCellOddP51Kernel18MainSourceL2 R := by
  have hpotential :=
    inner_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_source R hR
  have hregular :=
    inner_fourCellOddP51Polynomial18RegularSourceL2_eq_P53PlusL2 R hR
  have hupper :=
    inner_fourCellOddP51UpperStripOddL2_eq_P53PlusL2 R hR
  unfold fourCellOddP51Kernel18MainP53PlusL2
    fourCellOddP51Kernel18MainSourceL2
  repeat' rw [inner_add_left]
  rw [hpotential, ← hregular, ← hupper]

private theorem oddP53PlusHilbertTail_shiftedLegendreHilbertBasis
    (n : ℕ) (hn : 53 ≤ n) :
    OddP53PlusHilbertTail (shiftedLegendreHilbertBasis n) := by
  intro k hk
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    (orthonormal_iff_ite.mp shiftedLegendreHilbertBasis.orthonormal k n),
    if_neg (by omega)]

/-- Projection after summing is exactly the sum of the three honest
`P53+` channel tails.  The proof uses Hilbert-coordinate uniqueness and
therefore does not enumerate a single retained mode. -/
theorem fourCellOddP51Kernel18MainP53PlusL2_eq_projectionResidual :
    fourCellOddP51Kernel18MainP53PlusL2 =
      fourCellOddP51Kernel18MainSourceL2 -
        shiftedLegendrePartialProjection
          fourCellOddP51Kernel18MainSourceL2 53 := by
  apply shiftedLegendreHilbertBasis.repr.injective
  ext n
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis.repr_apply_apply,
    inner_sub_right,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    YoshidaEndpointPotentialOddTailParsevalStructural.repr_shiftedLegendrePartialProjection]
  by_cases hn : n < 53
  · rw [if_pos hn]
    have hzero :=
      oddP53PlusHilbertTail_fourCellOddP51Kernel18MainP53PlusL2 n hn
    rw [hzero]
    ring
  · rw [if_neg hn, sub_zero]
    have hpair :=
      inner_fourCellOddP51Kernel18MainP53PlusL2_eq_source
        (shiftedLegendreHilbertBasis n)
        (oddP53PlusHilbertTail_shiftedLegendreHilbertBasis n (by omega))
    rw [real_inner_comm (shiftedLegendreHilbertBasis n)
        fourCellOddP51Kernel18MainP53PlusL2,
      real_inner_comm (shiftedLegendreHilbertBasis n)
        fourCellOddP51Kernel18MainSourceL2] at hpair
    simpa only [shiftedLegendreHilbertBasis.repr_apply_apply] using hpair

private theorem inner_shiftedLegendrePartialProjection_eq_partialNormSq
    (F : UnitIntervalL2) (N : ℕ) :
    inner ℝ F (shiftedLegendrePartialProjection F N) =
      shiftedLegendrePartialNormSq F N := by
  rw [shiftedLegendrePartialProjection, inner_sum,
    shiftedLegendrePartialNormSq]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [real_inner_smul_right]
  have hrepr : inner ℝ F (shiftedLegendreHilbertBasis n) =
      shiftedLegendreHilbertBasis.repr F n := by
    rw [real_inner_comm]
    exact (shiftedLegendreHilbertBasis.repr_apply_apply F n).symm
  rw [hrepr]
  ring

/-- Exact combined Pythagorean deficit.  All endpoint, regular, and strip
cross terms remain inside the full-source norm and its low projection. -/
theorem norm_sq_fourCellOddP51Kernel18MainP53PlusL2_eq_deficit :
    ‖fourCellOddP51Kernel18MainP53PlusL2‖ ^ 2 =
      ‖fourCellOddP51Kernel18MainSourceL2‖ ^ 2 -
        shiftedLegendrePartialNormSq
          fourCellOddP51Kernel18MainSourceL2 53 := by
  rw [fourCellOddP51Kernel18MainP53PlusL2_eq_projectionResidual,
    norm_sub_sq_real,
    inner_shiftedLegendrePartialProjection_eq_partialNormSq,
    norm_sq_shiftedLegendrePartialProjection]
  ring

/-- The production main-row norm certificate is literally the single
Pythagorean deficit inequality. -/
theorem fourCellOddP51Kernel18MainP53PlusNormCertificate_iff_deficit
    (rho kappa : ℝ) :
    FourCellOddP51Kernel18MainP53PlusNormCertificate rho kappa ↔
      ‖fourCellOddP51Kernel18MainSourceL2‖ ^ 2 -
          shiftedLegendrePartialNormSq
            fourCellOddP51Kernel18MainSourceL2 53 ≤
        rho * (fourCellOddP51GalerkinPivot * kappa) := by
  unfold FourCellOddP51Kernel18MainP53PlusNormCertificate
  rw [norm_sq_fourCellOddP51Kernel18MainP53PlusL2_eq_deficit]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualProjectionStructural
