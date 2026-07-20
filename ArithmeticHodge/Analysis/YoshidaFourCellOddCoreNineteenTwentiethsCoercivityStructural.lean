import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural

noncomputable section

open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open CenteredOddOneThreeEnergy

/-!
# Coercivity after retaining nineteen twentieths of the odd raw reserve

The folded regular row costs at most one twentieth of the complete raw
strip-cancellation reserve.  This file isolates what remains after that
payment and proves its strongest natural scalar consequence from the
existing lower-`P₁` spectral and cross-rectangle estimates.

The exact coercivity constant is not rounded down in the main theorem.  Its
rational lower bound `343 / 12500` is recorded separately for consumers that
prefer a purely rational weight.
-/

/-- The signed scalar mass coefficient in the odd four-cell local form. -/
def fourCellOddLocalScalarMassCoefficient : ℝ :=
  2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200

/-- The exact global `L²` constant left by the lower-`P₁` spectral payment
after retaining `19 / 20` of the raw reserve. -/
def fourCellOddNineteenTwentiethsCoercivityConstant : ℝ :=
  7999 / 2500 - fourCellOddLocalScalarMassCoefficient

/-- The diagonal form available once the folded regular row has been paid
pointwise by one twentieth of the raw strip-cancellation reserve. -/
def fourCellOddNineteenTwentiethsRetainedQuadratic (w : ℝ → ℝ) : ℝ :=
  (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve w +
    fourCellOddRetainedPrimePotentialQuadratic w -
      fourCellOddLocalScalarMassCoefficient *
        (∫ x : ℝ in 0..1, w x ^ 2)

/-- The exact spatially weighted reserve delivered by the retained raw,
prime, and endpoint-potential terms on the `P₁`-orthogonal odd sector. -/
def fourCellOddNineteenTwentiethsExactTailWeight (w : ℝ → ℝ) : ℝ :=
  fourCellOddNineteenTwentiethsCoercivityConstant *
      (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
    (57 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
    ((49 / 50 : ℝ) - fourCellOddLocalScalarMassCoefficient) *
      (∫ x : ℝ in 3 / 5..1, w x ^ 2) +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2)

/-- The fine shared-scalar enclosure leaves the explicit rational floor
`343 / 12500` beneath the exact coercivity constant. -/
theorem threeHundredFortyThree_div_twelveThousandFiveHundred_lt_coercivityConstant :
    (343 / 12500 : ℝ) <
      fourCellOddNineteenTwentiethsCoercivityConstant := by
  have hscalar := fourCellScalar_fine_bounds.2
  unfold fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddLocalScalarMassCoefficient
  linarith

theorem fourCellOddNineteenTwentiethsCoercivityConstant_pos :
    0 < fourCellOddNineteenTwentiethsCoercivityConstant := by
  linarith [
    threeHundredFortyThree_div_twelveThousandFiveHundred_lt_coercivityConstant]

/-- Public lower-interval Cauchy estimate used to eliminate the remaining
negative `P₁` moment coefficient. -/
private theorem sq_intervalIntegral_mul_le_zero_three_fifths
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in 0..3 / 5, f x * g x) ^ 2 ≤
      (∫ x : ℝ in 0..3 / 5, f x ^ 2) *
        (∫ x : ℝ in 0..3 / 5, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

theorem lowerP1Moment_sq_le_nine_div_oneHundredTwentyFive_lowerMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..3 / 5, x * w x) ^ 2 ≤
      (9 / 125 : ℝ) * ∫ x : ℝ in 0..3 / 5, w x ^ 2 := by
  have hcauchy := sq_intervalIntegral_mul_le_zero_three_fifths
    (fun x : ℝ ↦ x) w (by fun_prop) hw
  have hx2 : (∫ x : ℝ in 0..3 / 5, x ^ 2) = 9 / 125 := by
    rw [integral_pow]
    norm_num
  rw [hx2] at hcauchy
  exact hcauchy

/-- On the odd `P₁`-orthogonal sector, nineteen twentieths of the exact
raw reserve still pay `7999 / 2500` of the lower mass and `57 / 50` of the
upper `1/x` mass.  No regular-kernel estimate is used here. -/
theorem lowerMass_add_weightedUpperMass_le_nineteenTwentieths_rawReserve_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (7999 / 2500 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
        (57 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) ≤
      (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve w := by
  have hraw := lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_le_rawReserve
    w hw hodd
  have hrawScaled := mul_le_mul_of_nonneg_left hraw
    (by norm_num : (0 : ℝ) ≤ 19 / 20)
  have hcross := nineteen_mul_lowerP1Moment_sq_le_crossP1Square
    w hw hodd hone
  have hmoment :=
    lowerP1Moment_sq_le_nine_div_oneHundredTwentyFive_lowerMass
      w hw.continuous
  nlinarith

/-- Strong form-level lower bound: the exact weighted tail reserve is
dominated by the complete diagonal left after the regular-row payment. -/
theorem fourCellOddNineteenTwentiethsExactTailWeight_le_retainedQuadratic
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    fourCellOddNineteenTwentiethsExactTailWeight w ≤
      fourCellOddNineteenTwentiethsRetainedQuadratic w := by
  let L : ℝ := ∫ x : ℝ in 0..3 / 5, w x ^ 2
  let U : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2
  let H : ℝ := ∫ x : ℝ in 0..1, w x ^ 2
  let J : ℝ := ∫ x : ℝ in 3 / 5..1, w x ^ 2 / x
  let P : ℝ := ∫ x : ℝ in 0..1,
    yoshidaEndpointPotential x * w x ^ 2
  have hraw :=
    lowerMass_add_weightedUpperMass_le_nineteenTwentieths_rawReserve_of_P1
      w hw hodd hone
  have hprime := forty_nine_fiftieths_upperStripMass_le_primeDiagonal
    w hw.continuous
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit : L + U = H := by
    simpa only [L, U, H] using
      intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hscalarSplit :
      fourCellOddLocalScalarMassCoefficient * H =
        fourCellOddLocalScalarMassCoefficient * L +
          fourCellOddLocalScalarMassCoefficient * U := by
    rw [← hhalfSplit]
    ring
  unfold fourCellOddNineteenTwentiethsExactTailWeight
    fourCellOddNineteenTwentiethsRetainedQuadratic
    fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddRetainedPrimePotentialQuadratic
  dsimp only [L, U, H, J, P] at hraw hprime hhalfSplit hscalarSplit ⊢
  linarith

/-! ## Endpoint density and the exact scalar consequence -/

/-- Bernstein-positive endpoint density.  Its left side is exactly the
lower-strip coefficient before the common scalar mass is subtracted. -/
theorem sevenThousandNineHundredNinetyNine_div_twoThousandFiveHundred_le_endpointDensity
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    (7999 / 2500 : ℝ) ≤
      57 / (50 * x) + 49 / 50 +
        (93 / 50) * yoshidaEndpointPotential x := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hpoly : 0 ≤
      (57 / 50 : ℝ) - (5549 / 2500) * x +
        (93 / 50) * x * yoshidaEndpointOctic x := by
    rw [show
        (57 / 50 : ℝ) - (5549 / 2500) * x +
            (93 / 50) * x * yoshidaEndpointOctic x =
          (43983969 / 781250000 : ℝ) * (1 - t) ^ 9 +
          (30577987 / 156250000 : ℝ) * t * (1 - t) ^ 8 +
          (670621 / 7812500 : ℝ) * t ^ 2 * (1 - t) ^ 7 +
          (10339 / 62500 : ℝ) * t ^ 3 * (1 - t) ^ 6 +
          (2005847 / 625000 : ℝ) * t ^ 4 * (1 - t) ^ 5 +
          (1254029 / 125000 : ℝ) * t ^ 5 * (1 - t) ^ 4 +
          (182401 / 12500 : ℝ) * t ^ 6 * (1 - t) ^ 3 +
          (144379 / 12500 : ℝ) * t ^ 7 * (1 - t) ^ 2 +
          (242897 / 50000 : ℝ) * t ^ 8 * (1 - t) +
          (8579 / 10000 : ℝ) * t ^ 9 by
      dsimp only [t]
      unfold yoshidaEndpointOctic
      ring]
    positivity
  have hxpos : 0 < x := by linarith
  have hoctic : yoshidaEndpointOctic x ≤ yoshidaEndpointPotential x := by
    apply octic_le_endpointPotential
    rw [abs_lt]
    constructor <;> linarith
  have hpotential := mul_le_mul_of_nonneg_left hoctic
    (by positivity : 0 ≤ (93 / 50 : ℝ) * x)
  apply le_of_mul_le_mul_right ?_ hxpos
  rw [show
      (57 / (50 * x) + 49 / 50 +
          (93 / 50) * yoshidaEndpointPotential x) * x =
        57 / 50 + (49 / 50) * x +
          ((93 / 50) * x) * yoshidaEndpointPotential x by
    field_simp [hxpos.ne']]
  nlinarith

private theorem upperStripPotential_le_positiveHalfPotential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  have hfull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 (3 / 5) := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤
      ∫ x : ℝ in 0..3 / 5,
        yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (yoshidaEndpointPotential_nonneg_on_Icc
        ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- The upper-strip part of the exact weighted reserve dominates the same
coercivity constant as the lower strip. -/
theorem coercivityConstant_mul_upperMass_le_exactUpperTailWeight
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddNineteenTwentiethsCoercivityConstant *
        (∫ x : ℝ in 3 / 5..1, w x ^ 2) ≤
      (57 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) +
      ((49 / 50 : ℝ) - fourCellOddLocalScalarMassCoefficient) *
        (∫ x : ℝ in 3 / 5..1, w x ^ 2) +
      (93 / 50 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.pow 2).intervalIntegrable _ _
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hw.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq w hw).mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hmono :
      (∫ x : ℝ in 3 / 5..1, (7999 / 2500 : ℝ) * w x ^ 2) ≤
        ∫ x : ℝ in 3 / 5..1,
          ((57 / 50 : ℝ) * (w x ^ 2 / x) +
            (49 / 50 : ℝ) * w x ^ 2) +
              (93 / 50 : ℝ) *
                (yoshidaEndpointPotential x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hmass.const_mul _) ((hweighted.const_mul _).add
        (hmass.const_mul _) |>.add (hpotential.const_mul _))
    intro x hx
    have hdensity :=
      sevenThousandNineHundredNinetyNine_div_twoThousandFiveHundred_le_endpointDensity
        hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_right hdensity (sq_nonneg (w x))
    convert hmul using 1
    field_simp [ne_of_gt (by linarith [hx.1] : 0 < x)]
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add
      ((hweighted.const_mul _).add (hmass.const_mul _))
      (hpotential.const_mul _),
    intervalIntegral.integral_add (hweighted.const_mul _)
      (hmass.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have hpotentialFull := upperStripPotential_le_positiveHalfPotential w hw
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotentialFull
    (by norm_num : (0 : ℝ) ≤ 93 / 50)
  unfold fourCellOddNineteenTwentiethsCoercivityConstant
  linarith

/-- Exact unconditional scalar coercivity of the nineteen-twentieths
retained odd core on the `P₁`-orthogonal sector. -/
theorem coercivityConstant_mul_positiveHalfMass_le_retainedQuadratic_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    fourCellOddNineteenTwentiethsCoercivityConstant *
        (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddNineteenTwentiethsRetainedQuadratic w := by
  have htail :=
    fourCellOddNineteenTwentiethsExactTailWeight_le_retainedQuadratic
      w hw hodd hone
  have hupper := coercivityConstant_mul_upperMass_le_exactUpperTailWeight
    w hw.continuous
  have hlowerInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.continuous.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.continuous.pow 2).intervalIntegrable _ _
  have hhalfSplit :=
    intervalIntegral.integral_add_adjacent_intervals hlowerInt hupperInt
  have hcoercivitySplit :
      fourCellOddNineteenTwentiethsCoercivityConstant *
          (∫ x : ℝ in 0..1, w x ^ 2) =
        fourCellOddNineteenTwentiethsCoercivityConstant *
            (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
          fourCellOddNineteenTwentiethsCoercivityConstant *
            (∫ x : ℝ in 3 / 5..1, w x ^ 2) := by
    rw [← hhalfSplit]
    ring
  unfold fourCellOddNineteenTwentiethsExactTailWeight at htail
  linarith

/-- Purely rational coercivity corollary for downstream weighted Cauchy or
Riesz estimates. -/
theorem threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_retainedQuadratic_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (343 / 12500 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddNineteenTwentiethsRetainedQuadratic w := by
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hconstant :=
    threeHundredFortyThree_div_twelveThousandFiveHundred_lt_coercivityConstant.le
  have hmul := mul_le_mul_of_nonneg_right hconstant hmass
  exact hmul.trans
    (coercivityConstant_mul_positiveHalfMass_le_retainedQuadratic_of_P1
      w hw hodd hone)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
