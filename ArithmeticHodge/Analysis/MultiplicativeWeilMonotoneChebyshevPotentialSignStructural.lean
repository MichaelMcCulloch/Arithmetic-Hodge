import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevCriterionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevPotentialSignStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# The sign carried by the corrected Chebyshev potential

For a far monotone-cell pair, integration by parts does not create a new
positive term.  The corrected-potential summand is exactly the negative of a
strictly positive rational kernel paired with the physical directed
correlation.  Consequently its sign is controlled by the sign of that
correlation, not by the negativity of the potential alone.

This file records the exact identity and its sharp sign equivalences.  No
sign of a general real-parent correlation is assumed.
-/

/-- The corrected-potential part of one far monotone-cell numerator. -/
def monotoneQuarterFarCorrectedPotentialPairing
    (parent : BombieriTest) (k lag : ℤ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0,
    ((correctedChebyshevPotential
        (quarterLogLatticePoint lag * x) : ℝ) : ℂ) *
      deriv (fun y : ℝ ↦
        starRingEnd ℂ
          (bombieriDirectedCorrelation
            (monotoneQuarterNormalizedCell parent (k + lag))
            (monotoneQuarterNormalizedCell parent k) y)) x

/-- The physical correlation paired with the positive inverse-Cauchy kernel
which is the derivative of the corrected potential. -/
def monotoneQuarterFarPhysicalPotentialPairing
    (parent : BombieriTest) (k lag : ℤ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0,
    ((((x * ((quarterLogLatticePoint lag * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) *
      starRingEnd ℂ
        (bombieriDirectedCorrelation
          (monotoneQuarterNormalizedCell parent (k + lag))
          (monotoneQuarterNormalizedCell parent k) x))

/-- To the right of its pole, the corrected Chebyshev potential is strictly
negative. -/
theorem correctedChebyshevPotential_neg_of_one_lt
    {t : ℝ} (ht : 1 < t) :
    correctedChebyshevPotential t < 0 := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hinv0 : 0 < t⁻¹ := inv_pos.mpr ht0
  have hinv1 : t⁻¹ < 1 := (inv_lt_one₀ ht0).2 ht
  have hsquare : t⁻¹ ^ 2 < 1 := by
    nlinarith [mul_self_lt_mul_self hinv0.le hinv1]
  have harg0 : 0 < 1 - t⁻¹ ^ 2 := sub_pos.mpr hsquare
  have harg1 : 1 - t⁻¹ ^ 2 < 1 := by
    nlinarith [sq_pos_of_pos hinv0]
  unfold correctedChebyshevPotential
  have hlog := Real.log_neg harg0 harg1
  apply mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 1 / 2)
  simpa only [inv_pow] using hlog

/-- Exact integration-by-parts identity for a far monotone-cell pair.  The
corrected-potential term is the negative physical-kernel pairing. -/
theorem monotoneQuarterFarCorrectedPotentialPairing_eq_neg_physical
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    monotoneQuarterFarCorrectedPotentialPairing parent k lag =
      -monotoneQuarterFarPhysicalPotentialPairing parent k lag := by
  let f : BombieriTest :=
    monotoneQuarterNormalizedCell parent (k + lag)
  let g : BombieriTest := monotoneQuarterNormalizedCell parent k
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let q₂ : ℝ := quarterLogLatticePoint 2
  let r : ℝ := quarterLogLatticePoint lag
  have hq₂pos : 0 < q₂ := quarterLogLatticePoint_pos 2
  have hr : 0 < r := quarterLogLatticePoint_pos lag
  have hf : tsupport f ⊆ Set.Icc 1 q₂ := by
    exact monotoneQuarterNormalizedCell_tsupport_subset parent (k + lag)
  have hg : tsupport g ⊆ Set.Icc 1 q₂ := by
    exact monotoneQuarterNormalizedCell_tsupport_subset parent k
  have hsupport : tsupport H ⊆ Set.Icc (1 / q₂) q₂ := by
    apply isClosed_Icc.closure_subset_iff.mpr
    intro x hx
    by_contra hout
    apply hx
    dsimp only [H]
    apply star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
      f g (by norm_num) (by norm_num) hq₂pos hf hg
    simpa only [div_one] using hout
  have hq₂one : 1 ≤ q₂ := by
    dsimp only [q₂]
    simpa only [quarterLogLatticePoint_zero] using
      (quarterLogLatticePoint_mono (m := (0 : ℤ)) (n := 2) (by omega))
  have hab : 1 / q₂ ≤ q₂ := by
    exact ((div_le_one hq₂pos).2 hq₂one).trans hq₂one
  have hqfar : q₂ < r := by
    exact quarterLogLatticePoint_two_lt_of_three_le lag hfar
  have hsep : 1 < r * (1 / q₂) := by
    calc
      (1 : ℝ) = q₂ / q₂ := by field_simp [hq₂pos.ne']
      _ < r / q₂ := (div_lt_div_iff_of_pos_right hq₂pos).2 hqfar
      _ = r * (1 / q₂) := by ring
  have hparts :=
    integral_inverseKernel_mul_eq_neg_integral_potential_mul_deriv
      H (star_bombieriDirectedCorrelation_contDiff_one f g)
      hr hab hsupport hsep
  have hneg := congrArg Neg.neg hparts
  simpa only [f, g, H, q₂, r,
      monotoneQuarterFarCorrectedPotentialPairing,
      monotoneQuarterFarPhysicalPotentialPairing, neg_neg] using hneg.symm

/-- A favorable nonnegative corrected-potential contribution is equivalent
to a nonpositive physical correlation average against the positive rational
kernel. -/
theorem monotoneQuarterFarCorrectedPotentialPairing_re_nonnegative_iff
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    0 ≤ (monotoneQuarterFarCorrectedPotentialPairing parent k lag).re ↔
      (monotoneQuarterFarPhysicalPotentialPairing parent k lag).re ≤ 0 := by
  rw [monotoneQuarterFarCorrectedPotentialPairing_eq_neg_physical
    parent k lag hfar]
  simp

/-- Conversely, a nonnegative physical correlation average makes the
corrected-potential contribution nonpositive. -/
theorem monotoneQuarterFarCorrectedPotentialPairing_re_nonpositive_iff
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    (monotoneQuarterFarCorrectedPotentialPairing parent k lag).re ≤ 0 ↔
      0 ≤ (monotoneQuarterFarPhysicalPotentialPairing parent k lag).re := by
  rw [monotoneQuarterFarCorrectedPotentialPairing_eq_neg_physical
    parent k lag hfar]
  simp

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevPotentialSignStructural
