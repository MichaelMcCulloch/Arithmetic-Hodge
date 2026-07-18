import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleEntropyStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

open TwoByTwoSchur
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoForwardPolePolynomialReductionStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoReflectedPoleEntropyStructural
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural
open YoshidaRegularKernelBound

noncomputable section

/-!
# The retained constrained dual at cutoff eleven

Retaining `1 / 64` of the singular Gram changes the multiplication weights.
The even and odd weights below encode exactly the reserve left by
`factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four`.
The two-channel theorem charges the retained representer row to that reserve
without a triangle inequality.
-/

/-- Even multiplication weight after retaining `1 / 64` of the singular
Gram. -/
def factorTwoIntrinsicElevenRetainedEvenWeight (x : ℝ) : ℝ :=
  (13 / 100 : ℝ) + (63 / 128 : ℝ) * yoshidaEndpointPotential x

/-- Odd multiplication weight after retaining `1 / 64` of the singular
Gram. -/
def factorTwoIntrinsicElevenRetainedOddWeight (x : ℝ) : ℝ :=
  (1 / 30 : ℝ) + (63 / 128 : ℝ) * yoshidaEndpointPotential x

/-- Sum of the two retained constrained selector costs. -/
def factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
    (FE FO : ℝ → ℝ) (pE pO : ℝ[X]) : ℝ :=
  factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenRetainedEvenWeight FE pE +
    factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenRetainedOddWeight FO pO

theorem factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenRetainedEvenWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenRetainedEvenWeight
  nlinarith

theorem factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenRetainedOddWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenRetainedOddWeight
  nlinarith

theorem intervalIntegrable_retainedEvenWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenWeight x * r x ^ 2)
      volume (-1) 1 := by
  have hmass : IntervalIntegrable
      (fun x : ℝ ↦ (13 / 100 : ℝ) * r x ^ 2) volume (-1) 1 :=
    ((hr.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * r x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq r hr).const_mul _
  apply (hmass.add hpotential).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedEvenWeight
  ring

theorem intervalIntegrable_retainedOddWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddWeight x * r x ^ 2)
      volume (-1) 1 := by
  have hmass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 30 : ℝ) * r x ^ 2) volume (-1) 1 :=
    ((hr.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * r x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq r hr).const_mul _
  apply (hmass.add hpotential).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedOddWeight
  ring

private theorem measurable_retainedEvenWeight :
    Measurable factorTwoIntrinsicElevenRetainedEvenWeight := by
  unfold factorTwoIntrinsicElevenRetainedEvenWeight yoshidaEndpointPotential
  fun_prop

private theorem measurable_retainedOddWeight :
    Measurable factorTwoIntrinsicElevenRetainedOddWeight := by
  unfold factorTwoIntrinsicElevenRetainedOddWeight yoshidaEndpointPotential
  fun_prop

/-- A residual with at most linear growth in a positive multiplication
weight belongs to the corresponding weighted dual `L²` space.  This packages
the endpoint cancellation `W / sqrt W = sqrt W`; it avoids proving square
integrability of the logarithmic weight itself. -/
theorem div_sqrt_memLp_two_of_abs_le_const_mul_weight
    (W G : ℝ → ℝ) (hW : Measurable W)
    (hG : AEStronglyMeasurable G
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (C : ℝ)
    (hWpos : ∀ x ∈ Ioc (-1 : ℝ) 1, 0 < W x)
    (hbound : ∀ x ∈ Ioc (-1 : ℝ) 1, |G x| ≤ C * W x)
    (hsqrt : MemLp (fun x : ℝ ↦ Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp (fun x : ℝ ↦ G x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have htargetMeas : AEStronglyMeasurable
      (fun x : ℝ ↦ G x / Real.sqrt (W x))
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    by
      simpa only [div_eq_mul_inv] using
        hG.mul hW.sqrt.inv.aestronglyMeasurable
  refine MemLp.of_le_mul (c := C) hsqrt htargetMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hWx : 0 < W x := hWpos x hx
  have hsqrtPos : 0 < Real.sqrt (W x) := Real.sqrt_pos.2 hWx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos hsqrtPos]
  calc
    |G x| / Real.sqrt (W x) ≤
        (C * W x) / Real.sqrt (W x) :=
      (div_le_div_iff_of_pos_right hsqrtPos).2 (hbound x hx)
    _ = C * Real.sqrt (W x) := by
      apply (div_eq_iff hsqrtPos.ne').2
      calc
        C * W x = C * Real.sqrt (W x) ^ 2 :=
          congrArg (fun t : ℝ ↦ C * t) (Real.sq_sqrt hWx.le).symm
        _ = C * Real.sqrt (W x) * Real.sqrt (W x) := by ring

private theorem reflectedEndpointLogPlus_nonneg
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ -Real.log ((x + 1) / 2) := by
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith [hx.1]) (by linarith [hx.2]))

private theorem reflectedEndpointLogMinus_nonneg
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ -Real.log ((1 - x) / 2) := by
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))

private theorem reflectedEndpointLogs_sum_le
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -Real.log ((x + 1) / 2) + -Real.log ((1 - x) / 2) ≤
      2 * (1 + yoshidaEndpointPotential x) := by
  rw [reflectedEndpointLogs_sum_eq_potential hx]
  linarith [Real.log_two_lt_d9]

private theorem exists_polynomial_eval_abs_bound (p : ℝ[X]) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Icc (-1 : ℝ) 2, |p.eval z| ≤ M := by
  have hp : Continuous (fun z : ℝ ↦ p.eval z) := by fun_prop
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)) hp.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro z hz
  have hzBound := hM z hz
  rw [Real.norm_eq_abs] at hzBound
  linarith [le_abs_self M]

private theorem exists_reflectedPoleLogSelectors_linearGrowth
    (p : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |reflectedPoleKLogSelector p x| ≤
          C * (1 + yoshidaEndpointPotential x) ∧
        |reflectedPoleJLogSelector p x| ≤
          C * (1 + yoshidaEndpointPotential x) := by
  obtain ⟨M, hMpos, hM⟩ := exists_polynomial_eval_abs_bound p
  refine ⟨2 * M, mul_pos (by norm_num) hMpos, ?_⟩
  intro x hx
  by_cases hxOne : x = 1
  · subst x
    constructor <;>
      simp [reflectedPoleKLogSelector, reflectedPoleJLogSelector,
        yoshidaEndpointPotential] <;>
      nlinarith [hMpos]
  · have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hx.1, lt_of_le_of_ne hx.2 hxOne⟩
    let Lplus : ℝ := -Real.log ((x + 1) / 2)
    let Lminus : ℝ := -Real.log ((1 - x) / 2)
    have hLplus : 0 ≤ Lplus := by
      simpa only [Lplus] using reflectedEndpointLogPlus_nonneg hxIoo
    have hLminus : 0 ≤ Lminus := by
      simpa only [Lminus] using reflectedEndpointLogMinus_nonneg hxIoo
    have hLsum : Lplus + Lminus ≤
        2 * (1 + yoshidaEndpointPotential x) := by
      simpa only [Lplus, Lminus] using reflectedEndpointLogs_sum_le hxIoo
    have hEvalPlus : |p.eval ((x + 3) / 2)| ≤ M :=
      hM _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hEvalMinus : |p.eval ((x - 1) / 2)| ≤ M :=
      hM _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hterms :
        |p.eval ((x + 3) / 2)| * Lplus +
            |p.eval ((x - 1) / 2)| * Lminus ≤
          M * (Lplus + Lminus) := by
      calc
        |p.eval ((x + 3) / 2)| * Lplus +
              |p.eval ((x - 1) / 2)| * Lminus ≤
            M * Lplus + M * Lminus :=
          add_le_add (mul_le_mul_of_nonneg_right hEvalPlus hLplus)
            (mul_le_mul_of_nonneg_right hEvalMinus hLminus)
        _ = M * (Lplus + Lminus) := by ring
    have hscale : M * (Lplus + Lminus) ≤
        (2 * M) * (1 + yoshidaEndpointPotential x) := by
      calc
        M * (Lplus + Lminus) ≤
            M * (2 * (1 + yoshidaEndpointPotential x)) :=
          mul_le_mul_of_nonneg_left hLsum hMpos.le
        _ = (2 * M) * (1 + yoshidaEndpointPotential x) := by ring
    have habsTerms :
        |p.eval ((x + 3) / 2) * Lplus| +
            |p.eval ((x - 1) / 2) * Lminus| ≤
          M * (Lplus + Lminus) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLplus,
        abs_of_nonneg hLminus]
      exact hterms
    constructor
    · unfold reflectedPoleKLogSelector
      rw [show
        -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) -
            p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) =
          p.eval ((x + 3) / 2) * Lplus +
            p.eval ((x - 1) / 2) * Lminus by
        dsimp only [Lplus, Lminus]
        ring]
      exact (abs_add_le _ _).trans (habsTerms.trans hscale)
    · unfold reflectedPoleJLogSelector
      rw [show
        -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) +
            p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) =
          p.eval ((x + 3) / 2) * Lplus -
            p.eval ((x - 1) / 2) * Lminus by
        dsimp only [Lplus, Lminus]
        ring]
      exact (abs_sub _ _).trans (habsTerms.trans hscale)

private def HasRetainedEndpointLinearGrowth (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
    |f x| ≤ C * (1 + yoshidaEndpointPotential x)

private theorem hasRetainedEndpointLinearGrowth_add
    {f g : ℝ → ℝ} (hf : HasRetainedEndpointLinearGrowth f)
    (hg : HasRetainedEndpointLinearGrowth g) :
    HasRetainedEndpointLinearGrowth (fun x ↦ f x + g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_pos hC hD, ?_⟩
  intro x hx
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * (1 + yoshidaEndpointPotential x) +
        D * (1 + yoshidaEndpointPotential x) :=
      add_le_add (hf x hx) (hg x hx)
    _ = (C + D) * (1 + yoshidaEndpointPotential x) := by ring

private theorem hasRetainedEndpointLinearGrowth_sub
    {f g : ℝ → ℝ} (hf : HasRetainedEndpointLinearGrowth f)
    (hg : HasRetainedEndpointLinearGrowth g) :
    HasRetainedEndpointLinearGrowth (fun x ↦ f x - g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_pos hC hD, ?_⟩
  intro x hx
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ C * (1 + yoshidaEndpointPotential x) +
        D * (1 + yoshidaEndpointPotential x) :=
      add_le_add (hf x hx) (hg x hx)
    _ = (C + D) * (1 + yoshidaEndpointPotential x) := by ring

private theorem hasRetainedEndpointLinearGrowth_const_mul
    (c : ℝ) {f : ℝ → ℝ} (hf : HasRetainedEndpointLinearGrowth f) :
    HasRetainedEndpointLinearGrowth (fun x ↦ c * f x) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨|c| * C + 1, by positivity, ?_⟩
  intro x hx
  have hV := yoshidaEndpointPotential_nonneg_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  calc
    |c * f x| = |c| * |f x| := abs_mul _ _
    _ ≤ |c| * (C * (1 + yoshidaEndpointPotential x)) :=
      mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg c)
    _ = (|c| * C) * (1 + yoshidaEndpointPotential x) := by ring
    _ ≤ (|c| * C + 1) * (1 + yoshidaEndpointPotential x) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num))
        (by linarith)

private theorem hasRetainedEndpointLinearGrowth_of_abs_bound
    (f : ℝ → ℝ) (B : ℝ) (hB : 0 < B)
    (hf : ∀ x ∈ Ioc (-1 : ℝ) 1, |f x| ≤ B) :
    HasRetainedEndpointLinearGrowth f := by
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hV := yoshidaEndpointPotential_nonneg_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  exact (hf x hx).trans (by nlinarith)

private theorem hasRetainedEndpointLinearGrowth_potential_mul_of_abs_bound
    (f : ℝ → ℝ) (B : ℝ) (hB : 0 < B)
    (hf : ∀ x ∈ Ioc (-1 : ℝ) 1, |f x| ≤ B) :
    HasRetainedEndpointLinearGrowth
      (fun x ↦ yoshidaEndpointPotential x * f x) := by
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hV := yoshidaEndpointPotential_nonneg_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [abs_mul, abs_of_nonneg hV]
  calc
    yoshidaEndpointPotential x * |f x| ≤
        yoshidaEndpointPotential x * B :=
      mul_le_mul_of_nonneg_left (hf x hx) hV
    _ ≤ B * (1 + yoshidaEndpointPotential x) := by nlinarith

/-- A continuous real row on the compact endpoint interval has a strictly
positive uniform absolute bound.  The positive slack is convenient when
combining several representer bounds. -/
theorem exists_abs_bound_of_continuousOn_Icc
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hf
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro x hx
  have hxBound := hB x hx
  rw [Real.norm_eq_abs] at hxBound
  linarith [le_abs_self B]

private theorem hasRetainedEndpointLinearGrowth_of_continuousOn_Icc
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    HasRetainedEndpointLinearGrowth f := by
  obtain ⟨B, hB, hbound⟩ := exists_abs_bound_of_continuousOn_Icc f hf
  exact hasRetainedEndpointLinearGrowth_of_abs_bound f B hB
    (fun x hx ↦ hbound x ⟨hx.1.le, hx.2⟩)

private theorem exists_regularRepresenter_abs_bound (p : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |yoshidaEndpointEvenRegularRepresenter
          (centeredPolynomialLift p) x| ≤ B := by
  obtain ⟨M, hMpos, hM⟩ := exists_polynomial_eval_abs_bound p
  refine ⟨M / 2, by positivity, ?_⟩
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  rw [← Real.norm_eq_abs]
  unfold yoshidaEndpointEvenRegularRepresenter
  calc
    ‖∫ y : ℝ in Icc (-1) 1,
        yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
          centeredPolynomialLift p y‖ ≤
        (M / 4) * volume.real (Icc (-1 : ℝ) 1) := by
      apply MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (measure_Icc_lt_top (a := (-1 : ℝ)) (b := 1))
      intro y hy
      have hdist : |x - y| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hxIcc.1, hxIcc.2, hy.1, hy.2]
      have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
        mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
      have harg2 : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
        unfold yoshidaEndpointA
        nlinarith [mul_le_mul_of_nonneg_left hdist
          (by positivity : 0 ≤ Real.log 2 / 2)]
      have hkernel := yoshidaRegularKernel_mem_Icc harg0 harg2
      have hyEval : |p.eval ((y + 1) / 2)| ≤ M :=
        hM _ ⟨by linarith [hy.1], by linarith [hy.2]⟩
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hkernel.1,
        Real.norm_eq_abs]
      unfold centeredPolynomialLift
      calc
        yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            |p.eval ((y + 1) / 2)| ≤ (1 / 4 : ℝ) * M :=
          mul_le_mul hkernel.2 hyEval (abs_nonneg _) (by norm_num)
        _ = M / 4 := by ring
    _ = M / 2 := by
      norm_num [Measure.real, Real.volume_Icc]
      ring

private theorem hasRetainedEndpointLinearGrowth_cleanSurvivor
    (p : ℝ[X]) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenCleanSurvivorRepresenter p) := by
  obtain ⟨M, hMpos, hp⟩ := exists_polynomial_eval_abs_bound p
  have hpoly : ∀ x ∈ Ioc (-1 : ℝ) 1,
      |centeredPolynomialLift p x| ≤ M := by
    intro x hx
    unfold centeredPolynomialLift
    exact hp _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpotential :=
    hasRetainedEndpointLinearGrowth_potential_mul_of_abs_bound
      (centeredPolynomialLift p) M hMpos hpoly
  obtain ⟨R, hR, hregular⟩ := exists_regularRepresenter_abs_bound p
  have hregularGrowth := hasRetainedEndpointLinearGrowth_const_mul
    yoshidaEndpointA
    (hasRetainedEndpointLinearGrowth_of_abs_bound
      (yoshidaEndpointEvenRegularRepresenter (centeredPolynomialLift p))
      R hR hregular)
  let rankRow : ℝ → ℝ := fun x ↦
    2 * yoshidaEndpointA *
      (yoshidaEndpointCoshMoment (centeredPolynomialLift p) *
          Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointSinhMoment (centeredPolynomialLift p) *
          Real.sinh (yoshidaEndpointA * x / 2))
  have hrank : HasRetainedEndpointLinearGrowth rankRow :=
    hasRetainedEndpointLinearGrowth_of_continuousOn_Icc rankRow (by
      dsimp only [rankRow]
      fun_prop)
  have hsum := hasRetainedEndpointLinearGrowth_add
    (hasRetainedEndpointLinearGrowth_sub hpotential hregularGrowth) hrank
  simpa only [factorTwoIntrinsicElevenCleanSurvivorRepresenter, rankRow] using hsum

private theorem continuousOn_forwardPoleKLogSelector (p : ℝ[X]) :
    ContinuousOn (forwardPoleKLogSelector p) (Icc (-1 : ℝ) 1) := by
  have hminus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 - x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    norm_num
    linarith [hx.2]
  have hplus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 + x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    norm_num
    linarith [hx.1]
  unfold forwardPoleKLogSelector
  exact (by fun_prop : Continuous (fun x : ℝ ↦ p.eval ((x - 1) / 2)))
    |>.continuousOn.mul hminus |>.add
      ((by fun_prop : Continuous (fun x : ℝ ↦ p.eval ((x + 3) / 2)))
        |>.continuousOn.mul hplus)

private theorem continuousOn_forwardPoleLLogSelector (p : ℝ[X]) :
    ContinuousOn (forwardPoleLLogSelector p) (Icc (-1 : ℝ) 1) := by
  have hminus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 - x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    norm_num
    linarith [hx.2]
  have hplus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 + x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    norm_num
    linarith [hx.1]
  unfold forwardPoleLLogSelector
  exact (by fun_prop : Continuous (fun x : ℝ ↦ p.eval ((x - 1) / 2)))
    |>.continuousOn.mul hminus |>.sub
      ((by fun_prop : Continuous (fun x : ℝ ↦ p.eval ((x + 3) / 2)))
        |>.continuousOn.mul hplus)

private theorem hasRetainedEndpointLinearGrowth_forwardPoleKLogSelector
    (p : ℝ[X]) : HasRetainedEndpointLinearGrowth (forwardPoleKLogSelector p) :=
  hasRetainedEndpointLinearGrowth_of_continuousOn_Icc _
    (continuousOn_forwardPoleKLogSelector p)

private theorem hasRetainedEndpointLinearGrowth_forwardPoleLLogSelector
    (p : ℝ[X]) : HasRetainedEndpointLinearGrowth (forwardPoleLLogSelector p) :=
  hasRetainedEndpointLinearGrowth_of_continuousOn_Icc _
    (continuousOn_forwardPoleLLogSelector p)

private theorem hasRetainedEndpointLinearGrowth_reflectedPoleKLogSelector
    (p : ℝ[X]) : HasRetainedEndpointLinearGrowth (reflectedPoleKLogSelector p) := by
  obtain ⟨C, hC, hbound⟩ := exists_reflectedPoleLogSelectors_linearGrowth p
  exact ⟨C, hC, fun x hx ↦ (hbound x hx).1⟩

private theorem hasRetainedEndpointLinearGrowth_reflectedPoleJLogSelector
    (p : ℝ[X]) : HasRetainedEndpointLinearGrowth (reflectedPoleJLogSelector p) := by
  obtain ⟨C, hC, hbound⟩ := exists_reflectedPoleLogSelectors_linearGrowth p
  exact ⟨C, hC, fun x hx ↦ (hbound x hx).2⟩

private theorem abs_continuousLagKJ_le
    (q : ℝ → ℝ) (p : ℝ[X]) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hq : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hp : ∀ z ∈ Icc (-1 : ℝ) 2, |p.eval z| ≤ M)
    {x : ℝ} (hx : x ∈ Ioc (-1 : ℝ) 1) :
    |factorTwoContinuousLagK q (centeredPolynomialLift p) x| ≤
        4 * C * M ∧
      |factorTwoContinuousLagJ q (centeredPolynomialLift p) x| ≤
        4 * C * M := by
  have hpLift {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
      |centeredPolynomialLift p y| ≤ M := by
    unfold centeredPolynomialLift
    exact hp _ ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hright :
      |factorTwoContinuousLagRightRepresenter
          q (centeredPolynomialLift p) x| ≤ 2 * C * M := by
    rw [← Real.norm_eq_abs]
    unfold factorTwoContinuousLagRightRepresenter
    calc
      ‖∫ y : ℝ in x..1, q (y - x) * centeredPolynomialLift p y‖ ≤
          (C * M) * |1 - x| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        rw [uIoc_of_le hx.2] at hy
        have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
          ⟨by linarith [hx.1, hy.1], hy.2⟩
        have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
          ⟨by linarith [hy.1], by linarith [hy.2, hx.1]⟩
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hq _ hlag) (hpLift hyIcc)
          (abs_nonneg _) hC
      _ ≤ (C * M) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hM)
        rw [abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
      _ = 2 * C * M := by ring
  have hleft :
      |factorTwoContinuousLagLeftRepresenter
          q (centeredPolynomialLift p) x| ≤ 2 * C * M := by
    rw [← Real.norm_eq_abs]
    unfold factorTwoContinuousLagLeftRepresenter
    calc
      ‖∫ y : ℝ in -1..x, q (x - y) * centeredPolynomialLift p y‖ ≤
          (C * M) * |x - (-1)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        rw [uIoc_of_le hx.1.le] at hy
        have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
          ⟨hy.1.le, by linarith [hy.2, hx.2]⟩
        have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
          ⟨by linarith [hy.2], by linarith [hx.2, hy.1]⟩
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hq _ hlag) (hpLift hyIcc)
          (abs_nonneg _) hC
      _ ≤ (C * M) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hM)
        rw [abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2]
      _ = 2 * C * M := by ring
  constructor
  · unfold factorTwoContinuousLagK
    exact (abs_add_le _ _).trans
      ((add_le_add hright hleft).trans_eq (by ring))
  · unfold factorTwoContinuousLagJ
    exact (abs_sub _ _).trans
      ((add_le_add hright hleft).trans_eq (by ring))

private theorem hasRetainedEndpointLinearGrowth_continuousLagK_of_abs_le
    (q : ℝ → ℝ) (p : ℝ[X]) (C : ℝ) (hC : 0 < C)
    (hq : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    HasRetainedEndpointLinearGrowth
      (factorTwoContinuousLagK q (centeredPolynomialLift p)) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  refine hasRetainedEndpointLinearGrowth_of_abs_bound _ (4 * C * M)
    (by positivity) ?_
  intro x hx
  exact (abs_continuousLagKJ_le q p C M hC.le hM.le hq hp hx).1

private theorem hasRetainedEndpointLinearGrowth_continuousLagJ_of_abs_le
    (q : ℝ → ℝ) (p : ℝ[X]) (C : ℝ) (hC : 0 < C)
    (hq : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    HasRetainedEndpointLinearGrowth
      (factorTwoContinuousLagJ q (centeredPolynomialLift p)) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  refine hasRetainedEndpointLinearGrowth_of_abs_bound _ (4 * C * M)
    (by positivity) ?_
  intro x hx
  exact (abs_continuousLagKJ_le q p C M hC.le hM.le hq hp hx).2

private theorem exists_fixedLagKJ_abs_bound
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) (p : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoFixedLagK τ (centeredPolynomialLift p) x| ≤ B ∧
        |factorTwoFixedLagJ τ (centeredPolynomialLift p) x| ≤ B := by
  obtain ⟨M, hMpos, hM⟩ := exists_polynomial_eval_abs_bound p
  refine ⟨2 * M, mul_pos (by norm_num) hMpos, ?_⟩
  intro x hx
  have hRightEval : |centeredPolynomialLift p (τ + x)| ≤ M := by
    unfold centeredPolynomialLift
    exact hM _ ⟨by linarith [hx.1, hτ.1], by linarith [hx.2, hτ.2]⟩
  have hLeftEval : |centeredPolynomialLift p (x - τ)| ≤ M := by
    unfold centeredPolynomialLift
    exact hM _ ⟨by linarith [hx.1, hτ.2], by linarith [hx.2, hτ.1]⟩
  have hright :
      |factorTwoFixedLagRightRepresenter τ
          (centeredPolynomialLift p) x| ≤ M := by
    unfold factorTwoFixedLagRightRepresenter
    by_cases hs : x ∈ Icc (-1 : ℝ) (1 - τ)
    · rw [Set.indicator_of_mem hs]
      exact hRightEval
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact hMpos.le
  have hleft :
      |factorTwoFixedLagLeftRepresenter τ
          (centeredPolynomialLift p) x| ≤ M := by
    unfold factorTwoFixedLagLeftRepresenter
    by_cases hs : x ∈ Icc (-1 + τ) (1 : ℝ)
    · rw [Set.indicator_of_mem hs]
      exact hLeftEval
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact hMpos.le
  constructor
  · unfold factorTwoFixedLagK
    exact (abs_add_le _ _).trans
      ((add_le_add hright hleft).trans_eq (by ring))
  · unfold factorTwoFixedLagJ
    exact (abs_sub _ _).trans
      ((add_le_add hright hleft).trans_eq (by ring))

private def HasRetainedIocAbsBound (f : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1, |f x| ≤ B

private theorem hasRetainedIocAbsBound_add
    {f g : ℝ → ℝ} (hf : HasRetainedIocAbsBound f)
    (hg : HasRetainedIocAbsBound g) :
    HasRetainedIocAbsBound (fun x ↦ f x + g x) := by
  obtain ⟨B, hB, hf⟩ := hf
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨B + C, add_pos hB hC, ?_⟩
  intro x hx
  exact (abs_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))

private theorem hasRetainedIocAbsBound_sub
    {f g : ℝ → ℝ} (hf : HasRetainedIocAbsBound f)
    (hg : HasRetainedIocAbsBound g) :
    HasRetainedIocAbsBound (fun x ↦ f x - g x) := by
  obtain ⟨B, hB, hf⟩ := hf
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨B + C, add_pos hB hC, ?_⟩
  intro x hx
  exact (abs_sub _ _).trans (add_le_add (hf x hx) (hg x hx))

private theorem hasRetainedIocAbsBound_const_mul
    (c : ℝ) {f : ℝ → ℝ} (hf : HasRetainedIocAbsBound f) :
    HasRetainedIocAbsBound (fun x ↦ c * f x) := by
  obtain ⟨B, hB, hf⟩ := hf
  refine ⟨|c| * B + 1, by positivity, ?_⟩
  intro x hx
  rw [abs_mul]
  calc
    |c| * |f x| ≤ |c| * B :=
      mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg c)
    _ ≤ |c| * B + 1 := by linarith

private theorem hasRetainedIocAbsBound_of_continuousOn_Icc
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    HasRetainedIocAbsBound f := by
  obtain ⟨B, hB, hbound⟩ := exists_abs_bound_of_continuousOn_Icc f hf
  exact ⟨B, hB, fun x hx ↦ hbound x ⟨hx.1.le, hx.2⟩⟩

private theorem hasRetainedIocAbsBound_centeredPolynomialLift (p : ℝ[X]) :
    HasRetainedIocAbsBound (centeredPolynomialLift p) :=
  hasRetainedIocAbsBound_of_continuousOn_Icc _ (by
    unfold centeredPolynomialLift
    fun_prop)

private theorem hasRetainedIocAbsBound_regularRepresenter (p : ℝ[X]) :
    HasRetainedIocAbsBound
      (yoshidaEndpointEvenRegularRepresenter (centeredPolynomialLift p)) :=
  exists_regularRepresenter_abs_bound p

private theorem hasRetainedIocAbsBound_continuousLagK
    (q : ℝ → ℝ) (p : ℝ[X]) (C : ℝ) (hC : 0 < C)
    (hq : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    HasRetainedIocAbsBound
      (factorTwoContinuousLagK q (centeredPolynomialLift p)) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  refine ⟨4 * C * M, by positivity, ?_⟩
  intro x hx
  exact (abs_continuousLagKJ_le q p C M hC.le hM.le hq hp hx).1

private theorem hasRetainedIocAbsBound_continuousLagJ
    (q : ℝ → ℝ) (p : ℝ[X]) (C : ℝ) (hC : 0 < C)
    (hq : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    HasRetainedIocAbsBound
      (factorTwoContinuousLagJ q (centeredPolynomialLift p)) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  refine ⟨4 * C * M, by positivity, ?_⟩
  intro x hx
  exact (abs_continuousLagKJ_le q p C M hC.le hM.le hq hp hx).2

private theorem hasRetainedIocAbsBound_fixedLagK
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) (p : ℝ[X]) :
    HasRetainedIocAbsBound
      (factorTwoFixedLagK τ (centeredPolynomialLift p)) := by
  obtain ⟨B, hB, hbound⟩ := exists_fixedLagKJ_abs_bound τ hτ p
  exact ⟨B, hB, fun x hx ↦ (hbound x hx).1⟩

private theorem hasRetainedIocAbsBound_fixedLagJ
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) (p : ℝ[X]) :
    HasRetainedIocAbsBound
      (factorTwoFixedLagJ τ (centeredPolynomialLift p)) := by
  obtain ⟨B, hB, hbound⟩ := exists_fixedLagKJ_abs_bound τ hτ p
  exact ⟨B, hB, fun x hx ↦ (hbound x hx).2⟩

/-! ## Uniform bounds for the nonsingular complete-representer pieces -/

/-- Removing the explicit endpoint-potential row from the clean survivor
leaves a uniformly bounded regular-plus-rank representer. -/
theorem exists_cleanSurvivor_sub_potential_abs_bound (p : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenCleanSurvivorRepresenter p x -
          yoshidaEndpointPotential x * centeredPolynomialLift p x| ≤ B := by
  let rankRow : ℝ → ℝ := fun x ↦
    2 * yoshidaEndpointA *
      (yoshidaEndpointCoshMoment (centeredPolynomialLift p) *
          Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointSinhMoment (centeredPolynomialLift p) *
          Real.sinh (yoshidaEndpointA * x / 2))
  have hregular := hasRetainedIocAbsBound_const_mul (-yoshidaEndpointA)
    (hasRetainedIocAbsBound_regularRepresenter p)
  have hrank : HasRetainedIocAbsBound rankRow :=
    hasRetainedIocAbsBound_of_continuousOn_Icc rankRow (by
      dsimp only [rankRow]
      fun_prop)
  have hsum := hasRetainedIocAbsBound_add hregular hrank
  have heq : (fun x ↦
      factorTwoIntrinsicElevenCleanSurvivorRepresenter p x -
        yoshidaEndpointPotential x * centeredPolynomialLift p x) =
      fun x ↦
        -yoshidaEndpointA *
            yoshidaEndpointEvenRegularRepresenter
              (centeredPolynomialLift p) x + rankRow x := by
    funext x
    unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter rankRow
    ring
  change HasRetainedIocAbsBound (fun x ↦
    factorTwoIntrinsicElevenCleanSurvivorRepresenter p x -
      yoshidaEndpointPotential x * centeredPolynomialLift p x)
  rw [heq]
  exact hsum

/-- The analytic even complete-representer piece is uniformly bounded on
the endpoint interval. -/
theorem exists_analyticEvenRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x| ≤ B := by
  have hK := hasRetainedIocAbsBound_continuousLagK
    factorTwoSymmetricAnalyticLag pE (3 / 8000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hJ := hasRetainedIocAbsBound_continuousLagJ
    factorTwoAlternatingAnalyticLag pO (1 / 1000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  simpa only [factorTwoIntrinsicElevenAnalyticEvenRepresenter] using
    hasRetainedIocAbsBound_add
      (hasRetainedIocAbsBound_const_mul (a / 2) hK)
      (hasRetainedIocAbsBound_const_mul (b / 2) hJ)

/-- The analytic odd complete-representer piece is uniformly bounded on
the endpoint interval. -/
theorem exists_analyticOddRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x| ≤ B := by
  have hK := hasRetainedIocAbsBound_continuousLagK
    factorTwoSymmetricAnalyticLag pO (3 / 8000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hJ := hasRetainedIocAbsBound_continuousLagJ
    factorTwoAlternatingAnalyticLag pE (1 / 1000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  simpa only [factorTwoIntrinsicElevenAnalyticOddRepresenter] using
    hasRetainedIocAbsBound_sub
      (hasRetainedIocAbsBound_const_mul (a / 2) hK)
      (hasRetainedIocAbsBound_const_mul (b / 2) hJ)

/-- The forward-log even complete-representer piece is uniformly bounded;
its logarithm stays away from zero on the compact endpoint interval. -/
theorem exists_forwardEvenRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x| ≤ B := by
  apply hasRetainedIocAbsBound_of_continuousOn_Icc
  unfold factorTwoIntrinsicElevenForwardEvenRepresenter
  exact (continuousOn_const.mul (continuousOn_forwardPoleKLogSelector pE)).sub
    (continuousOn_const.mul (continuousOn_forwardPoleLLogSelector pO))

/-- The forward-log odd complete-representer piece is uniformly bounded. -/
theorem exists_forwardOddRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x| ≤ B := by
  apply hasRetainedIocAbsBound_of_continuousOn_Icc
  unfold factorTwoIntrinsicElevenForwardOddRepresenter
  exact (continuousOn_const.mul (continuousOn_forwardPoleKLogSelector pO)).add
    (continuousOn_const.mul (continuousOn_forwardPoleLLogSelector pE))

/-- The retained fixed-prime even representer is uniformly bounded. -/
theorem exists_primeEvenRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x| ≤ B := by
  have hτ12 := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hτ : factorTwoPrimeShift / yoshidaEndpointA ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [hτ12.1], hτ12.2⟩
  have hK := hasRetainedIocAbsBound_fixedLagK
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pE
  have hJ := hasRetainedIocAbsBound_fixedLagJ
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pO
  change HasRetainedIocAbsBound (fun x ↦
    -(Real.log 3 / (2 * Real.sqrt 3)) *
      (a * factorTwoFixedLagK
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pE) x +
        b * factorTwoFixedLagJ
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pO) x))
  exact hasRetainedIocAbsBound_const_mul _
    (hasRetainedIocAbsBound_add
      (hasRetainedIocAbsBound_const_mul a hK)
      (hasRetainedIocAbsBound_const_mul b hJ))

/-- The retained fixed-prime odd representer is uniformly bounded. -/
theorem exists_primeOddRepresenter_abs_bound
    (pE pO : ℝ[X]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x| ≤ B := by
  have hτ12 := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hτ : factorTwoPrimeShift / yoshidaEndpointA ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [hτ12.1], hτ12.2⟩
  have hK := hasRetainedIocAbsBound_fixedLagK
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pO
  have hJ := hasRetainedIocAbsBound_fixedLagJ
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pE
  change HasRetainedIocAbsBound (fun x ↦
    -(Real.log 3 / (2 * Real.sqrt 3)) *
      (a * factorTwoFixedLagK
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pO) x -
        b * factorTwoFixedLagJ
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pE) x))
  exact hasRetainedIocAbsBound_const_mul _
    (hasRetainedIocAbsBound_sub
      (hasRetainedIocAbsBound_const_mul a hK)
      (hasRetainedIocAbsBound_const_mul b hJ))

/-- A transported polynomial row is uniformly bounded on the endpoint
interval. -/
theorem exists_centeredPolynomialLift_abs_bound (p : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |centeredPolynomialLift p x| ≤ B :=
  hasRetainedIocAbsBound_centeredPolynomialLift p

private theorem hasRetainedEndpointLinearGrowth_fixedLagK
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) (p : ℝ[X]) :
    HasRetainedEndpointLinearGrowth
      (factorTwoFixedLagK τ (centeredPolynomialLift p)) := by
  obtain ⟨B, hB, hbound⟩ := exists_fixedLagKJ_abs_bound τ hτ p
  exact hasRetainedEndpointLinearGrowth_of_abs_bound _ B hB
    (fun x hx ↦ (hbound x hx).1)

private theorem hasRetainedEndpointLinearGrowth_fixedLagJ
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) (p : ℝ[X]) :
    HasRetainedEndpointLinearGrowth
      (factorTwoFixedLagJ τ (centeredPolynomialLift p)) := by
  obtain ⟨B, hB, hbound⟩ := exists_fixedLagKJ_abs_bound τ hτ p
  exact hasRetainedEndpointLinearGrowth_of_abs_bound _ B hB
    (fun x hx ↦ (hbound x hx).2)

private theorem hasRetainedEndpointLinearGrowth_analyticEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b) := by
  have hK := hasRetainedEndpointLinearGrowth_continuousLagK_of_abs_le
    factorTwoSymmetricAnalyticLag pE (3 / 8000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hJ := hasRetainedEndpointLinearGrowth_continuousLagJ_of_abs_le
    factorTwoAlternatingAnalyticLag pO (1 / 1000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  simpa only [factorTwoIntrinsicElevenAnalyticEvenRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_const_mul (a / 2) hK)
      (hasRetainedEndpointLinearGrowth_const_mul (b / 2) hJ)

private theorem hasRetainedEndpointLinearGrowth_analyticOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b) := by
  have hK := hasRetainedEndpointLinearGrowth_continuousLagK_of_abs_le
    factorTwoSymmetricAnalyticLag pO (3 / 8000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hJ := hasRetainedEndpointLinearGrowth_continuousLagJ_of_abs_le
    factorTwoAlternatingAnalyticLag pE (1 / 1000 : ℝ) (by norm_num)
      (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  simpa only [factorTwoIntrinsicElevenAnalyticOddRepresenter] using
    hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_const_mul (a / 2) hK)
      (hasRetainedEndpointLinearGrowth_const_mul (b / 2) hJ)

private theorem hasRetainedEndpointLinearGrowth_forwardEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenForwardEvenRepresenter] using
    hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_const_mul (-(a / 4))
        (hasRetainedEndpointLinearGrowth_forwardPoleKLogSelector pE))
      (hasRetainedEndpointLinearGrowth_const_mul (b / 4)
        (hasRetainedEndpointLinearGrowth_forwardPoleLLogSelector pO))

private theorem hasRetainedEndpointLinearGrowth_forwardOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenForwardOddRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_const_mul (-(a / 4))
        (hasRetainedEndpointLinearGrowth_forwardPoleKLogSelector pO))
      (hasRetainedEndpointLinearGrowth_const_mul (b / 4)
        (hasRetainedEndpointLinearGrowth_forwardPoleLLogSelector pE))

private theorem hasRetainedEndpointLinearGrowth_reflectedEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenReflectedEvenRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_const_mul (-(a / 4))
        (hasRetainedEndpointLinearGrowth_reflectedPoleKLogSelector pE))
      (hasRetainedEndpointLinearGrowth_const_mul (b / 4)
        (hasRetainedEndpointLinearGrowth_reflectedPoleJLogSelector pO))

private theorem hasRetainedEndpointLinearGrowth_reflectedOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenReflectedOddRepresenter] using
    hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_const_mul (-(a / 4))
        (hasRetainedEndpointLinearGrowth_reflectedPoleKLogSelector pO))
      (hasRetainedEndpointLinearGrowth_const_mul (b / 4)
        (hasRetainedEndpointLinearGrowth_reflectedPoleJLogSelector pE))

private theorem hasRetainedEndpointLinearGrowth_primeEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b) := by
  have hτ12 := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hτ : factorTwoPrimeShift / yoshidaEndpointA ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [hτ12.1], hτ12.2⟩
  have hK := hasRetainedEndpointLinearGrowth_fixedLagK
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pE
  have hJ := hasRetainedEndpointLinearGrowth_fixedLagJ
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pO
  change HasRetainedEndpointLinearGrowth (fun x ↦
    -(Real.log 3 / (2 * Real.sqrt 3)) *
      (a * factorTwoFixedLagK
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pE) x +
        b * factorTwoFixedLagJ
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pO) x))
  exact hasRetainedEndpointLinearGrowth_const_mul _
    (hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_const_mul a hK)
      (hasRetainedEndpointLinearGrowth_const_mul b hJ))

private theorem hasRetainedEndpointLinearGrowth_primeOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b) := by
  have hτ12 := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hτ : factorTwoPrimeShift / yoshidaEndpointA ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [hτ12.1], hτ12.2⟩
  have hK := hasRetainedEndpointLinearGrowth_fixedLagK
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pO
  have hJ := hasRetainedEndpointLinearGrowth_fixedLagJ
    (factorTwoPrimeShift / yoshidaEndpointA) hτ pE
  change HasRetainedEndpointLinearGrowth (fun x ↦
    -(Real.log 3 / (2 * Real.sqrt 3)) *
      (a * factorTwoFixedLagK
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pO) x -
        b * factorTwoFixedLagJ
          (factorTwoPrimeShift / yoshidaEndpointA)
          (centeredPolynomialLift pE) x))
  exact hasRetainedEndpointLinearGrowth_const_mul _
    (hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_const_mul a hK)
      (hasRetainedEndpointLinearGrowth_const_mul b hJ))

private theorem hasRetainedEndpointLinearGrowth_potential_centeredPolynomialLift
    (p : ℝ[X]) :
    HasRetainedEndpointLinearGrowth (fun x ↦
      yoshidaEndpointPotential x * centeredPolynomialLift p x) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  apply hasRetainedEndpointLinearGrowth_potential_mul_of_abs_bound
    (centeredPolynomialLift p) M hM
  intro x hx
  unfold centeredPolynomialLift
  exact hp _ ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem hasRetainedEndpointLinearGrowth_completeEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b) := by
  have hClean := hasRetainedEndpointLinearGrowth_cleanSurvivor pE
  have hAnalytic := hasRetainedEndpointLinearGrowth_analyticEvenRepresenter
    pE pO a b
  have hForward := hasRetainedEndpointLinearGrowth_forwardEvenRepresenter
    pE pO a b
  have hReflected := hasRetainedEndpointLinearGrowth_reflectedEvenRepresenter
    pE pO a b
  have hPrime := hasRetainedEndpointLinearGrowth_primeEvenRepresenter
    pE pO a b
  simpa only [factorTwoIntrinsicElevenEvenMixedRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_add
        (hasRetainedEndpointLinearGrowth_add
          (hasRetainedEndpointLinearGrowth_add hClean hAnalytic) hForward)
        hReflected)
      hPrime

private theorem hasRetainedEndpointLinearGrowth_completeOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b) := by
  have hClean := hasRetainedEndpointLinearGrowth_cleanSurvivor pO
  have hAnalytic := hasRetainedEndpointLinearGrowth_analyticOddRepresenter
    pE pO a b
  have hForward := hasRetainedEndpointLinearGrowth_forwardOddRepresenter
    pE pO a b
  have hReflected := hasRetainedEndpointLinearGrowth_reflectedOddRepresenter
    pE pO a b
  have hPrime := hasRetainedEndpointLinearGrowth_primeOddRepresenter
    pE pO a b
  simpa only [factorTwoIntrinsicElevenOddMixedRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_add
        (hasRetainedEndpointLinearGrowth_add
          (hasRetainedEndpointLinearGrowth_add hClean hAnalytic) hForward)
        hReflected)
      hPrime

private theorem hasRetainedEndpointLinearGrowth_potentialPoleEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenPotentialPoleEvenRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_potential_centeredPolynomialLift pE)
      (hasRetainedEndpointLinearGrowth_reflectedEvenRepresenter pE pO a b)

private theorem hasRetainedEndpointLinearGrowth_potentialPoleOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenPotentialPoleOddRepresenter] using
    hasRetainedEndpointLinearGrowth_add
      (hasRetainedEndpointLinearGrowth_potential_centeredPolynomialLift pO)
      (hasRetainedEndpointLinearGrowth_reflectedOddRepresenter pE pO a b)

private theorem hasRetainedEndpointLinearGrowth_retainedEvenRepresenterAt
    (gamma : ℝ) (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt] using
    hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_completeEvenRepresenter pE pO a b)
      (hasRetainedEndpointLinearGrowth_const_mul gamma
        (hasRetainedEndpointLinearGrowth_potentialPoleEvenRepresenter
          pE pO a b))

private theorem hasRetainedEndpointLinearGrowth_retainedOddRepresenterAt
    (gamma : ℝ) (pE pO : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma pE pO a b) := by
  simpa only [factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt] using
    hasRetainedEndpointLinearGrowth_sub
      (hasRetainedEndpointLinearGrowth_completeOddRepresenter pE pO a b)
      (hasRetainedEndpointLinearGrowth_const_mul gamma
        (hasRetainedEndpointLinearGrowth_potentialPoleOddRepresenter
          pE pO a b))

private theorem hasRetainedEndpointLinearGrowth_centeredPolynomialLift
    (p : ℝ[X]) :
    HasRetainedEndpointLinearGrowth (centeredPolynomialLift p) := by
  obtain ⟨M, hM, hp⟩ := exists_polynomial_eval_abs_bound p
  apply hasRetainedEndpointLinearGrowth_of_abs_bound
    (centeredPolynomialLift p) M hM
  intro x hx
  unfold centeredPolynomialLift
  exact hp _ ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem hasRetainedEndpointLinearGrowth_evenSelectorResidual
    (gamma : ℝ) (pE pO q : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenSelectorResidual
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
          gamma pE pO a b) q) := by
  unfold factorTwoIntrinsicElevenSelectorResidual
  exact hasRetainedEndpointLinearGrowth_sub
    (hasRetainedEndpointLinearGrowth_retainedEvenRepresenterAt
      gamma pE pO a b)
    (hasRetainedEndpointLinearGrowth_centeredPolynomialLift q)

private theorem hasRetainedEndpointLinearGrowth_oddSelectorResidual
    (gamma : ℝ) (pE pO q : ℝ[X]) (a b : ℝ) :
    HasRetainedEndpointLinearGrowth
      (factorTwoIntrinsicElevenSelectorResidual
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
          gamma pE pO a b) q) := by
  unfold factorTwoIntrinsicElevenSelectorResidual
  exact hasRetainedEndpointLinearGrowth_sub
    (hasRetainedEndpointLinearGrowth_retainedOddRepresenterAt
      gamma pE pO a b)
    (hasRetainedEndpointLinearGrowth_centeredPolynomialLift q)

/-- Continuity of a residual profile automatically supplies the retained
even primal `L²` hypothesis. -/
theorem sqrt_retainedEvenWeight_mul_memLp_two
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) * r x)
      (volume.restrict (Ioc (-1) 1)) :=
    (measurable_retainedEvenWeight.sqrt.mul hr.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hweight : Integrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenWeight x * r x ^ 2)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_retainedEvenWeight_mul_sq r hr)
  apply hweight.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hweightPos.le]

/-- Continuity of a residual profile automatically supplies the retained odd
primal `L²` hypothesis. -/
theorem sqrt_retainedOddWeight_mul_memLp_two
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) * r x)
      (volume.restrict (Ioc (-1) 1)) :=
    (measurable_retainedOddWeight.sqrt.mul hr.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hweight : Integrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddWeight x * r x ^ 2)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_retainedOddWeight_mul_sq r hr)
  apply hweight.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hweightPos.le]

/-- Every retained even selector residual has the weighted dual `L²`
regularity required by the cutoff-eleven Schur handoff.  The result is uniform
in the retained pole coefficient and in the selector polynomial. -/
theorem factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
    (gamma : ℝ) (pE pO q : ℝ[X]) (a b : ℝ) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            gamma pE pO a b) q x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let G : ℝ → ℝ := factorTwoIntrinsicElevenSelectorResidual
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      gamma pE pO a b) q
  obtain ⟨C, hC, hGrowth⟩ :=
    hasRetainedEndpointLinearGrowth_evenSelectorResidual
      gamma pE pO q a b
  have hF : IntervalIntegrable
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma pE pO a b) volume (-1) 1 := by
    simpa only [mul_one] using
      (intervalIntegrable_retainedEvenRepresenterAt_mul
        gamma pE pO (fun _ : ℝ ↦ (1 : ℝ)) continuous_const a b)
  have hq : IntervalIntegrable (centeredPolynomialLift q)
      volume (-1) 1 :=
    (continuous_centeredPolynomialLift q).intervalIntegrable (-1) 1
  have hG : AEStronglyMeasurable G
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [G, factorTwoIntrinsicElevenSelectorResidual] using
      (hF.sub hq).aestronglyMeasurable
  have hbound : ∀ x ∈ Ioc (-1 : ℝ) 1,
      |G x| ≤ (10 * C) * factorTwoIntrinsicElevenRetainedEvenWeight x := by
    intro x hx
    have hV := yoshidaEndpointPotential_nonneg_on_Icc
      (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
    have hcompare : 1 + yoshidaEndpointPotential x ≤
        10 * factorTwoIntrinsicElevenRetainedEvenWeight x := by
      unfold factorTwoIntrinsicElevenRetainedEvenWeight
      nlinarith
    calc
      |G x| ≤ C * (1 + yoshidaEndpointPotential x) := by
        simpa only [G] using hGrowth x hx
      _ ≤ C * (10 * factorTwoIntrinsicElevenRetainedEvenWeight x) :=
        mul_le_mul_of_nonneg_left hcompare hC.le
      _ = (10 * C) * factorTwoIntrinsicElevenRetainedEvenWeight x := by ring
  have hsqrt : MemLp
      (fun x : ℝ ↦ Real.sqrt
        (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [mul_one] using
      (sqrt_retainedEvenWeight_mul_memLp_two
        (fun _ : ℝ ↦ (1 : ℝ)) continuous_const)
  simpa only [G] using
    div_sqrt_memLp_two_of_abs_le_const_mul_weight
      factorTwoIntrinsicElevenRetainedEvenWeight G
      measurable_retainedEvenWeight hG (10 * C)
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
        ⟨hx.1.le, hx.2⟩)
      hbound hsqrt

/-- Every retained odd selector residual has the weighted dual `L²`
regularity required by the cutoff-eleven Schur handoff. -/
theorem factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
    (gamma : ℝ) (pE pO q : ℝ[X]) (a b : ℝ) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            gamma pE pO a b) q x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let G : ℝ → ℝ := factorTwoIntrinsicElevenSelectorResidual
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
      gamma pE pO a b) q
  obtain ⟨C, hC, hGrowth⟩ :=
    hasRetainedEndpointLinearGrowth_oddSelectorResidual
      gamma pE pO q a b
  have hF : IntervalIntegrable
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma pE pO a b) volume (-1) 1 := by
    simpa only [mul_one] using
      (intervalIntegrable_retainedOddRepresenterAt_mul
        gamma pE pO (fun _ : ℝ ↦ (1 : ℝ)) continuous_const a b)
  have hq : IntervalIntegrable (centeredPolynomialLift q)
      volume (-1) 1 :=
    (continuous_centeredPolynomialLift q).intervalIntegrable (-1) 1
  have hG : AEStronglyMeasurable G
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [G, factorTwoIntrinsicElevenSelectorResidual] using
      (hF.sub hq).aestronglyMeasurable
  have hbound : ∀ x ∈ Ioc (-1 : ℝ) 1,
      |G x| ≤ (32 * C) * factorTwoIntrinsicElevenRetainedOddWeight x := by
    intro x hx
    have hV := yoshidaEndpointPotential_nonneg_on_Icc
      (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
    have hcompare : 1 + yoshidaEndpointPotential x ≤
        32 * factorTwoIntrinsicElevenRetainedOddWeight x := by
      unfold factorTwoIntrinsicElevenRetainedOddWeight
      nlinarith
    calc
      |G x| ≤ C * (1 + yoshidaEndpointPotential x) := by
        simpa only [G] using hGrowth x hx
      _ ≤ C * (32 * factorTwoIntrinsicElevenRetainedOddWeight x) :=
        mul_le_mul_of_nonneg_left hcompare hC.le
      _ = (32 * C) * factorTwoIntrinsicElevenRetainedOddWeight x := by ring
  have hsqrt : MemLp
      (fun x : ℝ ↦ Real.sqrt
        (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [mul_one] using
      (sqrt_retainedOddWeight_mul_memLp_two
        (fun _ : ℝ ↦ (1 : ℝ)) continuous_const)
  simpa only [G] using
    div_sqrt_memLp_two_of_abs_le_const_mul_weight
      factorTwoIntrinsicElevenRetainedOddWeight G
      measurable_retainedOddWeight hG (32 * C)
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
        ⟨hx.1.le, hx.2⟩)
      hbound hsqrt

/-- The two retained multiplication integrals are exactly the algebraic
reserve carried by the gap-eleven tail theorem. -/
theorem factorTwoIntrinsicElevenRetainedWeightedReserve_eq_integrals
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    factorTwoIntrinsicElevenRetainedWeightedReserve e o =
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2) +
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2 := by
  have heMass : IntervalIntegrable
      (fun x : ℝ ↦ (13 / 100 : ℝ) * e x ^ 2) volume (-1) 1 :=
    ((hec.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hoMass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 30 : ℝ) * o x ^ 2) volume (-1) 1 :=
    ((hoc.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hePotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * e x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq e hec).const_mul _
  have hoPotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * o x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq o hoc).const_mul _
  have heExpand :
      (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2) =
        (13 / 100 : ℝ) * factorTwoIntrinsicEnergy e +
          (63 / 128 : ℝ) * factorTwoIntrinsicPotentialEnergy e := by
    unfold factorTwoIntrinsicElevenRetainedEvenWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (13 / 100 : ℝ) * e x ^ 2 +
            (63 / 128 : ℝ) *
              (yoshidaEndpointPotential x * e x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add heMass hePotential,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hoExpand :
      (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2) =
        (1 / 30 : ℝ) * factorTwoIntrinsicEnergy o +
          (63 / 128 : ℝ) * factorTwoIntrinsicPotentialEnergy o := by
    unfold factorTwoIntrinsicElevenRetainedOddWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (1 / 30 : ℝ) * o x ^ 2 +
            (63 / 128 : ℝ) *
              (yoshidaEndpointPotential x * o x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hoMass hoPotential,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicElevenRetainedWeightedReserve
  rw [heExpand, hoExpand]
  ring

theorem factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
    (FE FO : ℝ → ℝ) (pE pO : ℝ[X]) :
    0 ≤ factorTwoIntrinsicElevenRetainedConstrainedSelectorDual FE FO pE pO := by
  unfold factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
  exact add_nonneg
    (factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx))
    (factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx))

/-- Sharp two-channel weighted Cauchy estimate for the retained row.  The
primal `L²` hypotheses are discharged from continuity; only the two concrete
dual residuals remain as regularity obligations. -/
theorem factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (FE FO e o : ℝ → ℝ)
    (hec : Continuous e) (hoc : Continuous o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (pE pO : ℝ[X]) (hpE : pE.natDegree < 11)
    (hpO : pO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FE pE x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FO pO x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    factorTwoIntrinsicElevenMixedPairing FE FO e o ^ 2 ≤
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual FE FO pE pO *
        factorTwoIntrinsicElevenRetainedWeightedReserve e o := by
  let IE : ℝ := ∫ x : ℝ in -1..1, FE x * e x
  let IO : ℝ := ∫ x : ℝ in -1..1, FO x * o x
  let DE : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenRetainedEvenWeight FE pE
  let DO : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenRetainedOddWeight FO pO
  let RE : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2
  let RO : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2
  have hIE : IE ^ 2 ≤ DE * RE := by
    dsimp only [IE, DE, RE]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenRetainedEvenWeight FE e hec heLow pE hpE
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      hdualE (sqrt_retainedEvenWeight_mul_memLp_two e hec)
  have hIO : IO ^ 2 ≤ DO * RO := by
    dsimp only [IO, DO, RO]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenRetainedOddWeight FO o hoc hoLow pO hpO
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      hdualO (sqrt_retainedOddWeight_mul_memLp_two o hoc)
  have hDE : 0 ≤ DE := by
    dsimp only [DE]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
  have hDO : 0 ≤ DO := by
    dsimp only [DO]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
  have hRE : 0 ≤ RE := by
    dsimp only [RE]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx).le
      (sq_nonneg _)
  have hRO : 0 ≤ RO := by
    dsimp only [RO]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx).le
      (sq_nonneg _)
  have hsum := determinant_bound_add
    DE RE (2 * IE) DO RO (2 * IO)
    hDE hRE hDO hRO (by nlinarith) (by nlinarith)
  rw [factorTwoIntrinsicElevenRetainedWeightedReserve_eq_integrals e o hec hoc]
  dsimp only [factorTwoIntrinsicElevenMixedPairing,
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual]
  dsimp only [IE, IO, DE, DO, RE, RO] at hsum
  nlinarith

/-- Final retained cutoff-eleven Schur handoff.  The only quantitative input
left is a finite selector whose retained dual cost fits below the exact low
complement. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 64 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO
    (by
      simpa only [factorTwoIntrinsicElevenRetainedEvenMixedRepresenter,
        factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt] using
        (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
          (1 / 64 : ℝ) pE pO qE a b))
    (by
      simpa only [factorTwoIntrinsicElevenRetainedOddMixedRepresenter,
        factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt] using
        (factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
          (1 / 64 : ℝ) pE pO qO a b))
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 64 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_one_div_sixty_four_potentialPole_eq_pairing
      pE pO eR oR heRc hoRc heRlocal hoRlocal heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_sixty_four
    pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
      heGap hoGap hpE hpO a b lowComplement hab hlowComplement
      hlowRetains hremaining

/-- Asymmetric retained-selector handoff with low fraction `1 / 1024`, tail
fraction `1 / 64`, and pole-row coefficient `1 / 256`.  The only quantitative
input is the finite selector cost below the corrected low complement. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_asymmetricRetainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 2048 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 2048 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 256 : ℝ) pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        (1 / 256 : ℝ) pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 1024 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 256 : ℝ) pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
      (1 / 256 : ℝ) pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      (1 / 256 : ℝ) pE pO qE a b)
    (factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      (1 / 256 : ℝ) pE pO qO a b)
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 256 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_potentialPole_eq_pairing
      (1 / 256 : ℝ) pE pO eR oR heRc hoRc heRlocal hoRlocal
      heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_one_thousand_twenty_four
      pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap hpE hpO a b lowComplement hab hlowComplement
        hlowRetains hremaining

/-- Retuned retained-selector handoff with low fraction `1 / 2048`, tail
fraction `1 / 64`, and pole-row coefficient `1 / 512`.  It keeps the existing
cutoff-eleven tail reserve while replacing the nonviable positive-endpoint
low charge. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retunedAsymmetricRetainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 4096 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 4096 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        (1 / 512 : ℝ) pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
      (1 / 512 : ℝ) pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) pE pO qE a b)
    (factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) pE pO qO a b)
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_potentialPole_eq_pairing
      (1 / 512 : ℝ) pE pO eR oR heRc hoRc heRlocal hoRlocal
      heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_two_thousand_forty_eight
      pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap hpE hpO a b lowComplement hab hlowComplement
        hlowRetains hremaining

/-- Saturated retuning of the retained-selector handoff.  The tail fraction
and retained representer stay exactly the same as in
`factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retunedAsymmetricRetainedSelector`;
only the low singular charge is reduced to the smallest value compatible
with the unchanged `1 / 512` pole row. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_sharpRetunedAsymmetricRetainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 8192 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 8192 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        (1 / 512 : ℝ) pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 4096 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
      (1 / 512 : ℝ) pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) pE pO qE a b)
    (factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) pE pO qO a b)
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_potentialPole_eq_pairing
      (1 / 512 : ℝ) pE pO eR oR heRc hoRc heRlocal hoRlocal
      heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_four_thousand_ninety_six
      pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap hpE hpO a b lowComplement hab hlowComplement
        hlowRetains hremaining

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
