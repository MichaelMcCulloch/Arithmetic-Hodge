import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Joint weighted dual for the odd `P₁₁+` selector

The previous weighted-dual interface allocates a scalar `D₀` independently
between the pure `P₁` tail row and the corrected finite--tail row.  That
forgets their correlation.  The invariant actually needed by the corrected
determinant is the single joint inequality

`F * x² + X² ≤ F * A * W`,

where `F = A*C-b²` and `X = A*y-b*x`.  This is the inverse-free `2 × 2`
Loewner condition for the two selector rows.  It is strictly weaker than a
diagonal `D₀` allocation and feeds the production corrected determinant
directly.
-/

/-! ## The exact multiplication weight -/

/-- Multiplication density on the lower positive half-strip. -/
def fourCellOddP11SelectorLowerWeight (x : ℝ) : ℝ :=
  (27 / 250 : ℝ) + (93 / 50 : ℝ) * yoshidaEndpointPotential x

/-- Multiplication density on the upper positive half-strip.  Splitting at
`3/5` avoids introducing an artificial discontinuous global weight. -/
def fourCellOddP11SelectorUpperWeight (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * yoshidaEndpointPotential x +
    (6 / 5 : ℝ) / x - 57 / 25

/-- Two-strip multiplication reserve used by the selector Cauchy estimate. -/
def fourCellOddP11SelectorWeightedReserve (w : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11SelectorLowerWeight x * w x ^ 2) +
    ∫ x : ℝ in 3 / 5..1,
      fourCellOddP11SelectorUpperWeight x * w x ^ 2

theorem fourCellOddP11SelectorLowerWeight_pos
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (3 / 5)) :
    0 < fourCellOddP11SelectorLowerWeight x := by
  have hV : 0 ≤ yoshidaEndpointPotential x :=
    yoshidaEndpointPotential_nonneg_on_Icc
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold fourCellOddP11SelectorLowerWeight
  nlinarith

/-- Bernstein-positive lower bound for the upper selector density. -/
private theorem one_fiftieth_mul_x_le_selectorUpperOcticDensity
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (1 / 50 : ℝ) * x ≤
      (6 / 5 : ℝ) - (57 / 25) * x +
        (93 / 50) * x * yoshidaEndpointOctic x := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [← sub_nonneg]
  rw [show
      (6 / 5 : ℝ) - (57 / 25) * x +
          (93 / 50) * x * yoshidaEndpointOctic x - (1 / 50) * x =
        (53171469 / 781250000 : ℝ) * (1 - t) ^ 9 +
        (42090487 / 156250000 : ℝ) * t * (1 - t) ^ 8 +
        (1968121 / 7812500 : ℝ) * t ^ 2 * (1 - t) ^ 7 +
        (15799 / 62500 : ℝ) * t ^ 3 * (1 - t) ^ 6 +
        (1806347 / 625000 : ℝ) * t ^ 4 * (1 - t) ^ 5 +
        (1157849 / 125000 : ℝ) * t ^ 5 * (1 - t) ^ 4 +
        (172237 / 12500 : ℝ) * t ^ 6 * (1 - t) ^ 3 +
        (27683 / 2500 : ℝ) * t ^ 7 * (1 - t) ^ 2 +
        (9413 / 2000 : ℝ) * t ^ 8 * (1 - t) +
        (67 / 80 : ℝ) * t ^ 9 by
    dsimp only [t]
    unfold yoshidaEndpointOctic
    ring]
  positivity

theorem one_fiftieth_le_fourCellOddP11SelectorUpperWeight
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    (1 / 50 : ℝ) ≤ fourCellOddP11SelectorUpperWeight x := by
  have hxpos : 0 < x := by linarith
  have hoctic := one_fiftieth_mul_x_le_selectorUpperOcticDensity
    hx0.le hx1.le
  have hpotential : yoshidaEndpointOctic x ≤ yoshidaEndpointPotential x :=
    octic_le_endpointPotential (x := x) (by
      rw [abs_lt]
      constructor <;> linarith)
  have hpotentialMul := mul_le_mul_of_nonneg_left hpotential
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 93 / 50) hxpos.le)
  apply le_of_mul_le_mul_right ?_ hxpos
  unfold fourCellOddP11SelectorUpperWeight
  rw [show
      ((93 / 50 : ℝ) * yoshidaEndpointPotential x +
          (6 / 5) / x - 57 / 25) * x =
        (6 / 5 : ℝ) - (57 / 25) * x +
          (93 / 50) * x * yoshidaEndpointPotential x by
    field_simp [hxpos.ne']
    ring]
  nlinarith

/-- The two-strip multiplication reserve is definitionally the exact tail
weight already known to lie below the complete odd core. -/
theorem fourCellOddP11SelectorWeightedReserve_eq_exactTailWeight
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddP11SelectorWeightedReserve w =
      fourCellOddP1ExactTailWeight w := by
  have hmassLower : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume 0 (3 / 5) := (hw.pow 2).intervalIntegrable _ _
  have hmassUpper : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2)
      volume (3 / 5) 1 := (hw.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotentialLower : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 (3 / 5) := by
    apply hpotentialFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpotentialUpper : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume (3 / 5) 1 := by
    apply hpotentialFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hw.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  have hpotentialSplit := intervalIntegral.integral_add_adjacent_intervals
    hpotentialLower hpotentialUpper
  unfold fourCellOddP11SelectorWeightedReserve
    fourCellOddP11SelectorLowerWeight fourCellOddP11SelectorUpperWeight
    fourCellOddP1ExactTailWeight
  rw [show (fun x : ℝ ↦
      ((27 / 250 : ℝ) + (93 / 50) * yoshidaEndpointPotential x) *
        w x ^ 2) = fun x ↦
      (27 / 250 : ℝ) * w x ^ 2 +
        (93 / 50) * (yoshidaEndpointPotential x * w x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_add
      (hmassLower.const_mul _) (hpotentialLower.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ ↦
      ((93 / 50 : ℝ) * yoshidaEndpointPotential x +
          (6 / 5) / x - 57 / 25) * w x ^ 2) = fun x ↦
      (93 / 50 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) +
        (6 / 5) * (w x ^ 2 / x) - (57 / 25) * w x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_sub
      ((hpotentialUpper.const_mul _).add (hweighted.const_mul _))
      (hmassUpper.const_mul _),
    intervalIntegral.integral_add
      (hpotentialUpper.const_mul _) (hweighted.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [← hpotentialSplit]
  ring

/-! ## Two-strip selector Cauchy -/

def fourCellOddP11SelectorResidual
    (F q : ℝ → ℝ) (x : ℝ) : ℝ := F x - q x

/-- Exact dual cost of one positive-half selector, retaining the lower and
upper multiplication weights separately. -/
def fourCellOddP11SelectorDual
    (F q : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11SelectorResidual F q x ^ 2 /
        fourCellOddP11SelectorLowerWeight x) +
    ∫ x : ℝ in 3 / 5..1,
      fourCellOddP11SelectorResidual F q x ^ 2 /
        fourCellOddP11SelectorUpperWeight x

/-- Weighted Cauchy after one exact finite selector has been subtracted.
The pairing identity is deliberately separated from the analytic `MemLp`
facts: for the production rows it follows from the five vanishing odd
moments, while the latter follow from endpoint growth of the concrete
representers. -/
theorem sq_pairing_le_selectorDual_mul_weightedReserve
    (F q r : ℝ → ℝ) (L : ℝ)
    (hpairing : L =
      (∫ x : ℝ in 0..3 / 5,
          fourCellOddP11SelectorResidual F q x * r x) +
        ∫ x : ℝ in 3 / 5..1,
          fourCellOddP11SelectorResidual F q x * r x)
    (hdualLower : MemLp (fun x ↦
        fourCellOddP11SelectorResidual F q x /
          Real.sqrt (fourCellOddP11SelectorLowerWeight x)) 2
      (volume.restrict (Ioc (0 : ℝ) (3 / 5))))
    (hprimalLower : MemLp (fun x ↦
        Real.sqrt (fourCellOddP11SelectorLowerWeight x) * r x) 2
      (volume.restrict (Ioc (0 : ℝ) (3 / 5))))
    (hdualUpper : MemLp (fun x ↦
        fourCellOddP11SelectorResidual F q x /
          Real.sqrt (fourCellOddP11SelectorUpperWeight x)) 2
      (volume.restrict (Ioc (3 / 5 : ℝ) 1)))
    (hprimalUpper : MemLp (fun x ↦
        Real.sqrt (fourCellOddP11SelectorUpperWeight x) * r x) 2
      (volume.restrict (Ioc (3 / 5 : ℝ) 1))) :
    L ^ 2 ≤ fourCellOddP11SelectorDual F q *
      fourCellOddP11SelectorWeightedReserve r := by
  let G : ℝ → ℝ := fourCellOddP11SelectorResidual F q
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  let DL : ℝ := ∫ x, G x ^ 2 / fourCellOddP11SelectorLowerWeight x ∂μL
  let DU : ℝ := ∫ x, G x ^ 2 / fourCellOddP11SelectorUpperWeight x ∂μU
  let RL : ℝ := ∫ x, fourCellOddP11SelectorLowerWeight x * r x ^ 2 ∂μL
  let RU : ℝ := ∫ x, fourCellOddP11SelectorUpperWeight x * r x ^ 2 ∂μU
  let IL : ℝ := ∫ x, G x * r x ∂μL
  let IU : ℝ := ∫ x, G x * r x ∂μU
  have hWL : ∀ᵐ x ∂μL, 0 < fourCellOddP11SelectorLowerWeight x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact fourCellOddP11SelectorLowerWeight_pos ⟨hx.1.le, hx.2⟩
  have hWU : ∀ᵐ x ∂μU, 0 < fourCellOddP11SelectorUpperWeight x := by
    have hne : ∀ᵐ x ∂μU, x ≠ 1 :=
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
        (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with x hx hxne
    have hlt : x < 1 := lt_of_le_of_ne hx.2 hxne
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 50)
      (one_fiftieth_le_fourCellOddP11SelectorUpperWeight hx.1 hlt)
  have hlower : IL ^ 2 ≤ DL * RL := by
    dsimp only [IL, DL, RL, μL, G]
    exact sq_integral_mul_le_weighted
      (volume.restrict (Ioc (0 : ℝ) (3 / 5)))
      fourCellOddP11SelectorLowerWeight
      (fourCellOddP11SelectorResidual F q) r hWL
      hdualLower hprimalLower
  have hupper : IU ^ 2 ≤ DU * RU := by
    dsimp only [IU, DU, RU, μU, G]
    exact sq_integral_mul_le_weighted
      (volume.restrict (Ioc (3 / 5 : ℝ) 1))
      fourCellOddP11SelectorUpperWeight
      (fourCellOddP11SelectorResidual F q) r hWU
      hdualUpper hprimalUpper
  have hDL : 0 ≤ DL := by
    dsimp only [DL]
    apply integral_nonneg_of_ae
    filter_upwards [hWL] with x hx
    exact div_nonneg (sq_nonneg _) hx.le
  have hDU : 0 ≤ DU := by
    dsimp only [DU]
    apply integral_nonneg_of_ae
    filter_upwards [hWU] with x hx
    exact div_nonneg (sq_nonneg _) hx.le
  have hRL : 0 ≤ RL := by
    dsimp only [RL]
    apply integral_nonneg_of_ae
    filter_upwards [hWL] with x hx
    exact mul_nonneg hx.le (sq_nonneg _)
  have hRU : 0 ≤ RU := by
    dsimp only [RU]
    apply integral_nonneg_of_ae
    filter_upwards [hWU] with x hx
    exact mul_nonneg hx.le (sq_nonneg _)
  have hsum := TwoByTwoSchur.determinant_bound_add
    DL RL (2 * IL) DU RU (2 * IU)
    hDL hRL hDU hRU (by nlinarith) (by nlinarith)
  have hcombined : (IL + IU) ^ 2 ≤ (DL + DU) * (RL + RU) := by
    nlinarith
  rw [hpairing]
  unfold fourCellOddP11SelectorDual fourCellOddP11SelectorWeightedReserve
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [G, μL, μU, DL, DU, RL, RU, IL, IU] using hcombined

/-- Direct joint weighted-dual closure of the corrected determinant.  The
first row keeps the pure tail pivot nonnegative; the second row is the exact
two-row Loewner inequality, with no independent allocation of its two
summands. -/
theorem coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    {A b C x y z W : ℝ}
    (hA : 0 ≤ A)
    (hfinite : 0 ≤ A * C - b ^ 2)
    (hWz : W ≤ z)
    (hpure : x ^ 2 ≤ A * W)
    (hjoint :
      (A * C - b ^ 2) * x ^ 2 + (A * y - b * x) ^ 2 ≤
        (A * C - b ^ 2) * A * W) :
    0 ≤ coupledP1TailSchurDefect A b C x y z := by
  let F := A * C - b ^ 2
  let X := A * y - b * x
  let T := A * z - x ^ 2
  have hAW : A * W ≤ A * z := mul_le_mul_of_nonneg_left hWz hA
  have htail : 0 ≤ T := by
    dsimp only [T]
    linarith [hpure.trans hAW]
  have hFW : F * A * W ≤ F * (A * z) := by
    have := mul_le_mul_of_nonneg_left hAW hfinite
    simpa only [F, mul_assoc] using this
  have hcross : X ^ 2 ≤ F * T := by
    dsimp only [F, X, T] at hjoint hFW ⊢
    nlinarith
  exact coupledP1TailSchurDefect_nonneg_of_correctedCross
    hfinite htail hcross

/-- Algebraic equivalence between the joint two-row energy and its
inverse-free Loewner formulation.  The reverse implication tests the
Loewner inequality at the output vector `(x,X)` itself, so there is no
dimension-two trace loss. -/
theorem jointWeightedDual_iff_twoRowLoewner
    {A F W x X : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F) (hW : 0 ≤ W) :
    F * x ^ 2 + X ^ 2 ≤ F * A * W ↔
      ∀ s t : ℝ,
        (F * s * x + t * X) ^ 2 ≤
          F * A * (F * s ^ 2 + t ^ 2) * W := by
  constructor
  · intro hjoint s t
    have hcoeff : 0 ≤ F * s ^ 2 + t ^ 2 := by positivity
    have hcauchy :
        (F * s * x + t * X) ^ 2 ≤
          (F * s ^ 2 + t ^ 2) * (F * x ^ 2 + X ^ 2) := by
      nlinarith [mul_nonneg hF (sq_nonneg (s * X - t * x))]
    have hmul := mul_le_mul_of_nonneg_left hjoint hcoeff
    calc
      (F * s * x + t * X) ^ 2 ≤
          (F * s ^ 2 + t ^ 2) * (F * x ^ 2 + X ^ 2) := hcauchy
      _ ≤ (F * s ^ 2 + t ^ 2) * (F * A * W) := hmul
      _ = F * A * (F * s ^ 2 + t ^ 2) * W := by ring
  · intro hloewner
    let S := F * x ^ 2 + X ^ 2
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hK : 0 ≤ F * A * W := by positivity
    have htest := hloewner x X
    have hsq : S ^ 2 ≤ (F * A * W) * S := by
      dsimp only [S]
      convert htest using 1 <;> ring
    by_cases hS0 : S = 0
    · change S ≤ F * A * W
      rw [hS0]
      exact hK
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      nlinarith

/-- Correlation-preserving replacement for
`FourCellOddP11CoupledWeightedDualCertificate`.  Its second inequality is a
single quadratic inequality for the two selector rows, rather than two
independent norm allocations. -/
def FourCellOddP11CoupledJointWeightedDualCertificate : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight r ∧
      fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalBilinear centeredP1 r ^ 2 +
          fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddCoreLocalQuadratic centeredP1 *
            fourCellOddP1ExactTailWeight r

/-- The selector-facing version of the joint certificate.  For every finite
profile and tail, the two output rows define a contraction from the weighted
tail space to the two-dimensional metric `diag(F,1)`.  This is the exact
`2 × 2` Loewner inequality a pair of degree-`< 11` selectors must prove. -/
def FourCellOddP11CoupledSelectorLoewnerCertificate : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight r ∧
      ∀ s t : ℝ,
        (fourCellOddP11FiniteCorrectedReserve d e f g * s *
              fourCellOddCoreLocalBilinear centeredP1 r +
            t * fourCellOddP11FiniteTailCorrectedCross d e f g r) ^ 2 ≤
          fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalQuadratic centeredP1 *
              (fourCellOddP11FiniteCorrectedReserve d e f g * s ^ 2 +
                t ^ 2) * fourCellOddP1ExactTailWeight r

/-- The joint-energy and two-row Loewner interfaces are exactly equivalent.
The finite corrected reserve is already nonnegative unconditionally. -/
theorem fourCellOddP11CoupledSelectorLoewnerCertificate_iff_joint :
    FourCellOddP11CoupledSelectorLoewnerCertificate ↔
      FourCellOddP11CoupledJointWeightedDualCertificate := by
  constructor
  · intro hloewner d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
    rcases hloewner d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
      ⟨hpure, hloewner⟩
    constructor
    · exact hpure
    · apply (jointWeightedDual_iff_twoRowLoewner
        (A := fourCellOddCoreLocalQuadratic centeredP1)
        (F := fourCellOddP11FiniteCorrectedReserve d e f g)
        (W := fourCellOddP1ExactTailWeight r)
        (x := fourCellOddCoreLocalBilinear centeredP1 r)
        (X := fourCellOddP11FiniteTailCorrectedCross d e f g r)
        fourCellOddCoreLocalQuadratic_centeredP1_nonneg
        (fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g)
        (fourCellOddP1ExactTailWeight_nonneg r hr.continuous)).2
      exact hloewner
  · intro hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
    rcases hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
      ⟨hpure, hjoint⟩
    constructor
    · exact hpure
    · apply (jointWeightedDual_iff_twoRowLoewner
        (A := fourCellOddCoreLocalQuadratic centeredP1)
        (F := fourCellOddP11FiniteCorrectedReserve d e f g)
        (W := fourCellOddP1ExactTailWeight r)
        (x := fourCellOddCoreLocalBilinear centeredP1 r)
        (X := fourCellOddP11FiniteTailCorrectedCross d e f g r)
        fourCellOddCoreLocalQuadratic_centeredP1_nonneg
        (fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g)
        (fourCellOddP1ExactTailWeight_nonneg r hr.continuous)).1
      exact hjoint

/-- The old diagonal allocation implies the joint certificate.  The reverse
direction is intentionally not asserted: the joint condition retains the
off-diagonal correlation discarded by `D₀`. -/
theorem fourCellOddP11CoupledJointWeightedDualCertificate_of_diagonal
    (hdual : FourCellOddP11CoupledWeightedDualCertificate) :
    FourCellOddP11CoupledJointWeightedDualCertificate := by
  rcases hdual with ⟨D₀, hD₀, hdual⟩
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  rcases hdual d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
    ⟨hpure, hcross⟩
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let W := fourCellOddP1ExactTailWeight r
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let X := fourCellOddP11FiniteTailCorrectedCross d e f g r
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact fourCellOddP1ExactTailWeight_nonneg r hr.continuous
  have hFD : F * D₀ * W ≤ F * A * W := by
    have hmul := mul_le_mul_of_nonneg_left hD₀ hF
    exact mul_le_mul_of_nonneg_right hmul hW
  have hpureA : x ^ 2 ≤ A * W := by
    dsimp only [x, A, W] at hpure ⊢
    exact hpure.trans (mul_le_mul_of_nonneg_right hD₀ hW)
  constructor
  · exact hpureA
  · dsimp only [F, W, x, X, A] at hpure hcross hFD ⊢
    nlinarith

/-- The joint selector inequality closes the actual universal corrected
`P₁₁+` defect without passing through the stronger diagonal allocation. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_jointWeightedDual
    (hjoint : FourCellOddP11CoupledJointWeightedDualCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  let C := fourCellOddCoreLocalQuadratic p
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let y := fourCellOddCoreLocalBilinear p r
  let z := fourCellOddCoreLocalQuadratic r
  let W := fourCellOddP1ExactTailWeight r
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hF : 0 ≤ A * C - b ^ 2 := by
    simpa only [A, b, C, p, fourCellOddP11FiniteCorrectedReserve] using
      fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hWz : W ≤ z := by
    dsimp only [W, z]
    exact fourCellOddP1ExactTailWeight_le_core r hr hrodd hr1
  rcases hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
    ⟨hpure, hcoupled⟩
  have h := coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    (A := A) (b := b) (C := C) (x := x) (y := y) (z := z) (W := W)
    hA hF hWz
    (by simpa only [A, x, W] using hpure)
    (by simpa only [A, b, C, x, y, W, p,
        fourCellOddP11FiniteCorrectedReserve,
        fourCellOddP11FiniteTailCorrectedCross] using hcoupled)
  simpa only [fourCellOddP11CoupledRieszDefect, p, A, b, C, x, y, z]
    using h

/-- Final selector-facing handoff to the production corrected defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_selectorLoewner
    (hselector : FourCellOddP11CoupledSelectorLoewnerCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_jointWeightedDual
    (fourCellOddP11CoupledSelectorLoewnerCertificate_iff_joint.mp hselector)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural
