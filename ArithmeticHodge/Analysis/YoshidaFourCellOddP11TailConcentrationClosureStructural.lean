import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveFactorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailConcentrationClosureStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11TailReserveFactorStructural
open YoshidaFourCellOddP11TailReserveThreeHalvesStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaRegularKernelBound

/-!
# Structural reduction of the remaining `P₁₁+` concentration inequality

The prime diagonal, the weighted upper-strip term, and the bounded lower
part of the endpoint potential can all be discharged without a mode list.
What remains is a single retained Hardy-capacity residual: the raw-strip
reserve left after its sharp lower/weighted-upper payment must control the
singular upper endpoint potential and an explicit lower-mass charge.
-/

/-- On the endpoint strip, the exact `1/x` mass is at most `5/3` times
ordinary mass. -/
theorem upperStripWeightedMass_le_fiveThirds_mass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) ≤
      (5 / 3 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hr.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  have hmass : IntervalIntegrable (fun x : ℝ ↦ (5 / 3 : ℝ) * r x ^ 2)
      volume (3 / 5) 1 :=
    ((hr.pow 2).intervalIntegrable _ _).const_mul _
  calc
    (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) ≤
        ∫ x : ℝ in 3 / 5..1, (5 / 3 : ℝ) * r x ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hweighted hmass
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      rw [div_le_iff₀ hxpos]
      have hxscale : (1 : ℝ) ≤ (5 / 3 : ℝ) * x := by
        linarith [hx.1]
      calc
        r x ^ 2 = 1 * r x ^ 2 := by ring
        _ ≤ ((5 / 3 : ℝ) * x) * r x ^ 2 :=
          mul_le_mul_of_nonneg_right hxscale (sq_nonneg _)
        _ = (5 / 3 : ℝ) * r x ^ 2 * x := by ring
    _ = (5 / 3 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

/-- The prime diagonal and the `171/50` favorable upper mass pay the whole
`9/5` weighted upper term and retain `7/5` of upper mass. -/
theorem upperStripTerms_retain_sevenFifths_mass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (7 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) +
        (9 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) ≤
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass r +
        (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass r +
        (171 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
  have hweighted := upperStripWeightedMass_le_fiveThirds_mass r hr
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal r hr
  linarith

/-- The endpoint potential is uniformly at most `1/4` on `[0,3/5]`.
This uses monotonicity of `log` and `log(5/4) ≤ 1/4`; it does not expand the
potential into moments. -/
theorem endpointPotential_le_oneQuarter_on_lower
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (3 / 5)) :
    yoshidaEndpointPotential x ≤ (1 / 4 : ℝ) := by
  have hden : 0 < 1 - x ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hdenLower : (16 / 25 : ℝ) ≤ 1 - x ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hinvUpper : (1 - x ^ 2)⁻¹ ≤ (25 / 16 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hden).2
    nlinarith [hdenLower]
  have hlogInv := Real.log_le_log (inv_pos.mpr hden) hinvUpper
  have hlogFiveFour : Real.log (5 / 4 : ℝ) ≤ 1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h ⊢
    exact h
  have hlogUpper : Real.log (25 / 16 : ℝ) ≤ 1 / 2 := by
    rw [show (25 / 16 : ℝ) = (5 / 4 : ℝ) * (5 / 4 : ℝ) by norm_num,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0)
        (by norm_num : (5 / 4 : ℝ) ≠ 0)]
    linarith
  rw [Real.log_inv] at hlogInv
  unfold yoshidaEndpointPotential
  linarith

/-- Integrated lower-potential bound used by the concentration reduction. -/
theorem lowerPotential_le_oneQuarter_lowerMass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..3 / 5,
        yoshidaEndpointPotential x * r x ^ 2) ≤
      (1 / 4 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * r x ^ 2)
      volume 0 (3 / 5) := by
    apply (intervalIntegrable_endpointPotential_mul_sq r hr).mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 4 : ℝ) * r x ^ 2)
      volume 0 (3 / 5) :=
    ((hr.pow 2).intervalIntegrable _ _).const_mul _
  calc
    (∫ x : ℝ in 0..3 / 5,
        yoshidaEndpointPotential x * r x ^ 2) ≤
      ∫ x : ℝ in 0..3 / 5, (1 / 4 : ℝ) * r x ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          hpotential hmass
        intro x hx
        exact mul_le_mul_of_nonneg_right
          (endpointPotential_le_oneQuarter_on_lower hx) (sq_nonneg _)
    _ = (1 / 4 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

/-- Exact split of positive-half endpoint potential at the strip boundary. -/
theorem positiveHalfPotential_eq_lower_add_upper
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * r x ^ 2) =
      (∫ x : ℝ in 0..3 / 5,
        yoshidaEndpointPotential x * r x ^ 2) +
      ∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * r x ^ 2 := by
  have hfull := intervalIntegrable_endpointPotential_mul_sq r hr
  have hlower : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * r x ^ 2)
      volume 0 (3 / 5) := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hupper : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * r x ^ 2)
      volume (3 / 5) 1 := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  exact (intervalIntegral.integral_add_adjacent_intervals hlower hupper).symm

/-- Nonnegative part of the raw-strip reserve left after the strongest
currently public simultaneous lower-mass and weighted-upper payment. -/
def fourCellOddP11RetainedHardySurplus (r : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve r -
    2 * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x)

theorem retainedHardySurplus_nonneg
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    0 ≤ fourCellOddP11RetainedHardySurplus r := by
  have hraw := lowerMass_add_weightedUpperMass_le_rawStripCancellationReserve
    r hr hodd
  unfold fourCellOddP11RetainedHardySurplus
  linarith

/-- Cauchy control of the lower `P₁` moment. -/
theorem lowerP1Moment_sq_le_nine_oneTwentyFifths_lowerMass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..3 / 5, x * r x) ^ 2 ≤
      (9 / 125 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let f : ℝ → ℝ := fun x ↦ x
  have hf : Continuous f := continuous_id
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f r
    (by simp) (by simpa using hfLp) (by simpa using hrLp)
  have hx2 : (∫ x : ℝ in 0..3 / 5, x ^ 2) = (9 / 125 : ℝ) := by
    rw [integral_pow]
    norm_num
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  change (∫ x : ℝ in Ioc 0 (3 / 5), x * r x) ^ 2 ≤
    (9 / 125 : ℝ) * ∫ x : ℝ in Ioc 0 (3 / 5), r x ^ 2
  rw [← hx2, intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, f, div_one, one_mul] using hcauchy

/-- `P₁` orthogonality upgrades the raw Hardy surplus from coefficient `2`
to `421/125`: the cross-square pays nineteen copies of the lower moment,
and Cauchy pays the remaining `112/27` moment loss. -/
def fourCellOddP11P1RetainedHardySurplus (r : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve r -
    (421 / 125 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x)

theorem p1RetainedHardySurplus_nonneg
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    0 ≤ fourCellOddP11P1RetainedHardySurplus r := by
  have hraw := lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_le_rawReserve
    r hr hodd
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    r hr hodd h1
  have hmoment := lowerP1Moment_sq_le_nine_oneTwentyFifths_lowerMass
    r hr.continuous
  unfold fourCellOddP11P1RetainedHardySurplus
  nlinarith

/-- The precise Hardy-capacity residual left after all elementary terms have
been discharged.  Only the upper singular potential remains; its coefficient
is exactly the adverse `93/100` from the factor-`3/2` gap. -/
def fourCellOddP11TailHardyResidual (r : ℝ → ℝ) : ℝ :=
  fourCellOddP11RetainedHardySurplus r +
    (2813 / 20000 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    (33077 / 20000 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (93 / 100 : ℝ) *
      (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * r x ^ 2)

/-- In the actual `P₁`-orthogonal sector, the same exact residual has only
`5717/20000` of exposed lower mass left outside a certified nonnegative raw
surplus. -/
theorem tailHardyResidual_eq_p1RetainedSurplus
    (r : ℝ → ℝ) :
    fourCellOddP11TailHardyResidual r =
      fourCellOddP11P1RetainedHardySurplus r +
        (2813 / 20000 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
        (5717 / 20000 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
        (93 / 100 : ℝ) *
          (∫ x : ℝ in 3 / 5..1,
            yoshidaEndpointPotential x * r x ^ 2) := by
  unfold fourCellOddP11TailHardyResidual
    fourCellOddP11RetainedHardySurplus
    fourCellOddP11P1RetainedHardySurplus
  ring

/-- Every elementary term in the rational concentration budget dominates
the displayed Hardy residual.  This is the substantive reduction: the
strip-odd raw term, the full potential, both exact scalar weights, and both
prime parities have disappeared from the remaining obligation. -/
theorem tailHardyResidual_le_rationalConcentrationBudget
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddP11TailHardyResidual r ≤
      fourCellOddP11ThreeHalvesRationalConcentrationBudget r := by
  have hrawFold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    r (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)) hodd
  have hrawReserve :
      fourCellOddRawStripCancellationReserve r =
        centeredRawLogEnergy r / 4 -
          (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy r := by
    unfold fourCellOddRawStripCancellationReserve
    rw [hrawFold]
  have hmass := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hodd)
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume 0 (3 / 5) := (hr.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (3 / 5) 1 := (hr.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit :
      (∫ x : ℝ in 0..3 / 5, r x ^ 2) +
          (∫ x : ℝ in 3 / 5..1, r x ^ 2) =
        ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hpotentialSplit := positiveHalfPotential_eq_lower_add_upper
    r hr.continuous
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    r hr.continuous
  have hweighted := upperStripWeightedMass_le_fiveThirds_mass
    r hr.continuous
  have hlowerPotential := lowerPotential_le_oneQuarter_lowerMass
    r hr.continuous
  unfold fourCellOddP11TailHardyResidual
    fourCellOddP11RetainedHardySurplus
    fourCellOddP11ThreeHalvesRationalConcentrationBudget
    factorTwoIntrinsicEnergy
  rw [hrawReserve, hmass, ← hhalfSplit, hpotentialSplit,
    fourCellOddP11ThreeHalvesHalfMassReserve_eq]
  ring_nf at hprime hweighted hlowerPotential ⊢
  linarith

/-- Hence nonnegativity of the retained Hardy residual proves the complete
rational concentration budget for that profile. -/
theorem rationalConcentrationBudget_nonneg_of_tailHardyResidual
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hHardy : 0 ≤ fourCellOddP11TailHardyResidual r) :
    0 ≤ fourCellOddP11ThreeHalvesRationalConcentrationBudget r :=
  hHardy.trans (tailHardyResidual_le_rationalConcentrationBudget r hr hodd)

/-- The now-minimal structural endpoint Hardy statement on genuine
`P₁₁+` tails.  Unlike the original factor reserve, it contains only the
unused raw capacity, lower/upper mass, and the singular upper potential. -/
def FourCellOddP11TailHardyConcentration : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddP11TailHardyResidual r

/-- The Hardy-capacity statement is sufficient for the rational
concentration certificate. -/
theorem rationalConcentration_of_tailHardyConcentration
    (hHardy : FourCellOddP11TailHardyConcentration) :
    FourCellOddP11ThreeHalvesRationalConcentration := by
  intro r hr hodd h1 h3 h5 h7 h9
  exact rationalConcentrationBudget_nonneg_of_tailHardyResidual r hr hodd
    (hHardy r hr hodd h1 h3 h5 h7 h9)

/-- Consequently the single retained Hardy-capacity inequality closes the
actual factor-`3/2` tail reserve. -/
theorem tailReserveAtFactor_threeHalves_of_tailHardyConcentration
    (hHardy : FourCellOddP11TailHardyConcentration) :
    FourCellOddP11TailReserveAtFactor (3 / 2 : ℝ) :=
  tailReserveAtFactor_threeHalves_of_rationalConcentration
    (rationalConcentration_of_tailHardyConcentration hHardy)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailConcentrationClosureStructural
