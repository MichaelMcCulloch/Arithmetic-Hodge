import ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRegularRowMassBoundStructural

noncomputable section

open YoshidaEndpointPotentialBound
open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaRegularKernelBound

/-!
# Uniform payment of the four-cell regular row potential

Both positive-half regular kernels lie between zero and `1 / 4` on the
four-cell range.  Their exact symmetric row potential therefore costs at
most half of the positive-half scalar mass.  This keeps the completed kernel
squares and replaces the only negative regular term by a scalar charge.
-/

private theorem fourCellOperatorHalfWidth_nonneg :
    0 ≤ fourCellOperatorHalfWidth := by
  unfold fourCellOperatorHalfWidth
  positivity

private theorem fourCellOperatorHalfWidth_two_mul_le_log_three :
    2 * fourCellOperatorHalfWidth ≤ Real.log 3 := by
  have h := five_mul_log_two_div_four_lt_log_three
  unfold fourCellOperatorHalfWidth
  linarith

/-- The exact regular row mass is at most one half of the positive-half
`L²` mass. -/
theorem fourCellPositiveHalfRegularRowMass_le_half_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth ≤
      (1 / 2 : ℝ) * ∫ x : ℝ in 0..1, w x ^ 2 := by
  let P : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let F : ℝ × ℝ → ℝ := fun p ↦
    (yoshidaRegularKernel
          (fourCellOperatorHalfWidth * |p.1 - p.2|) +
        yoshidaRegularKernel
          (fourCellOperatorHalfWidth * (p.1 + p.2))) *
      ((w p.1 ^ 2 + w p.2 ^ 2) / 2)
  let G : ℝ × ℝ → ℝ := fun p ↦
    (1 / 4 : ℝ) * w p.1 ^ 2 + (1 / 4 : ℝ) * w p.2 ^ 2
  have hPmeas : MeasurableSet P :=
    measurableSet_Icc.prod measurableSet_Icc
  have hG : IntegrableOn G P ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact (by fun_prop : Continuous G).continuousOn
  have hFMeas : Measurable F := by
    dsimp only [F]
    exact (((measurable_yoshidaRegularKernel.comp
          (measurable_const.mul
            ((measurable_fst.sub measurable_snd).abs))).add
        (measurable_yoshidaRegularKernel.comp
          (measurable_const.mul
            (measurable_fst.add measurable_snd)))).mul
      (by fun_prop : Measurable (fun p : ℝ × ℝ ↦
        (w p.1 ^ 2 + w p.2 ^ 2) / 2)))
  have hpoint : ∀ p ∈ P, 0 ≤ F p ∧ F p ≤ G p := by
    intro p hp
    have hdiff0 : 0 ≤ fourCellOperatorHalfWidth * |p.1 - p.2| :=
      mul_nonneg fourCellOperatorHalfWidth_nonneg (abs_nonneg _)
    have hsum0 : 0 ≤ fourCellOperatorHalfWidth * (p.1 + p.2) := by
      have : 0 ≤ p.1 + p.2 := by linarith [hp.1.1, hp.2.1]
      exact mul_nonneg fourCellOperatorHalfWidth_nonneg this
    have hdiff2 : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    have hsum2 : p.1 + p.2 ≤ 2 := by
      linarith [hp.1.2, hp.2.2]
    have hdiff3 :
        fourCellOperatorHalfWidth * |p.1 - p.2| ≤ Real.log 3 :=
      (mul_le_mul_of_nonneg_left hdiff2
        fourCellOperatorHalfWidth_nonneg).trans_eq
        (by ring : fourCellOperatorHalfWidth * 2 =
          2 * fourCellOperatorHalfWidth) |>.trans
            fourCellOperatorHalfWidth_two_mul_le_log_three
    have hsum3 :
        fourCellOperatorHalfWidth * (p.1 + p.2) ≤ Real.log 3 :=
      (mul_le_mul_of_nonneg_left hsum2
        fourCellOperatorHalfWidth_nonneg).trans_eq
        (by ring : fourCellOperatorHalfWidth * 2 =
          2 * fourCellOperatorHalfWidth) |>.trans
            fourCellOperatorHalfWidth_two_mul_le_log_three
    have hKdiff0 :=
      yoshidaRegularKernel_nonneg_of_le_log_three hdiff0 hdiff3
    have hKsum0 :=
      yoshidaRegularKernel_nonneg_of_le_log_three hsum0 hsum3
    have hKdiff4 := yoshidaRegularKernel_le_quarter hdiff0
    have hKsum4 := yoshidaRegularKernel_le_quarter hsum0
    have hmass0 : 0 ≤ (w p.1 ^ 2 + w p.2 ^ 2) / 2 := by positivity
    dsimp only [F, G]
    constructor
    · exact mul_nonneg (add_nonneg hKdiff0 hKsum0) hmass0
    · have hK :
          yoshidaRegularKernel
                (fourCellOperatorHalfWidth * |p.1 - p.2|) +
              yoshidaRegularKernel
                (fourCellOperatorHalfWidth * (p.1 + p.2)) ≤
            (1 / 2 : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hK hmass0
      nlinarith
  have hF : IntegrableOn F P ((volume : Measure ℝ).prod volume) := by
    apply hG.mono'
    · exact hFMeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hPmeas] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (hpoint p hp).1]
      exact (hpoint p hp).2
  have hmono :
      (∫ p : ℝ × ℝ in P, F p) ≤ ∫ p : ℝ × ℝ in P, G p :=
    setIntegral_mono_on hF hG hPmeas (fun p hp ↦ (hpoint p hp).2)
  have hmassSet :
      (∫ x : ℝ in Icc (0 : ℝ) 1, w x ^ 2) =
        ∫ x : ℝ in 0..1, w x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  have hGvalue :
      (∫ p : ℝ × ℝ in P, G p) =
        (1 / 2 : ℝ) * ∫ x : ℝ in 0..1, w x ^ 2 := by
    let H₁ : ℝ × ℝ → ℝ := fun p ↦
      ((1 / 4 : ℝ) * w p.1 ^ 2) * 1
    let H₂ : ℝ × ℝ → ℝ := fun p ↦
      1 * ((1 / 4 : ℝ) * w p.2 ^ 2)
    have hH₁ : IntegrableOn H₁ P ((volume : Measure ℝ).prod volume) := by
      apply ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
      exact (by fun_prop : Continuous H₁).continuousOn
    have hH₂ : IntegrableOn H₂ P ((volume : Measure ℝ).prod volume) := by
      apply ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
      exact (by fun_prop : Continuous H₂).continuousOn
    have hsplit : G = fun p ↦ H₁ p + H₂ p := by
      funext p
      dsimp only [G, H₁, H₂]
      ring
    rw [hsplit]
    change (∫ p : ℝ × ℝ in P, H₁ p + H₂ p) = _
    have hadd :
        (∫ p : ℝ × ℝ in P, H₁ p + H₂ p) =
          (∫ p : ℝ × ℝ in P, H₁ p) +
            ∫ p : ℝ × ℝ in P, H₂ p := by
      simpa only [Pi.add_apply] using integral_add hH₁ hH₂
    rw [hadd]
    dsimp only [H₁, H₂, P]
    have hprod₁ :
        (∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            ((1 / 4 : ℝ) * w p.1 ^ 2) * 1) =
          (∫ x : ℝ in Icc (0 : ℝ) 1, (1 / 4 : ℝ) * w x ^ 2) *
            ∫ _y : ℝ in Icc (0 : ℝ) 1, (1 : ℝ) := by
      exact setIntegral_prod_mul
        (fun x : ℝ ↦ (1 / 4 : ℝ) * w x ^ 2)
        (fun _y : ℝ ↦ (1 : ℝ)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
    have hprod₂ :
        (∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            1 * ((1 / 4 : ℝ) * w p.2 ^ 2)) =
          (∫ _x : ℝ in Icc (0 : ℝ) 1, (1 : ℝ)) *
            ∫ y : ℝ in Icc (0 : ℝ) 1, (1 / 4 : ℝ) * w y ^ 2 := by
      exact setIntegral_prod_mul
        (fun _x : ℝ ↦ (1 : ℝ))
        (fun y : ℝ ↦ (1 / 4 : ℝ) * w y ^ 2)
        (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
    rw [hprod₁, hprod₂]
    simp only [integral_const_mul]
    have hone : (∫ _x : ℝ in Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
      norm_num
    rw [hone, mul_one, one_mul, hmassSet]
    ring
  unfold fourCellPositiveHalfRegularRowMass
  change (∫ p : ℝ × ℝ in P, F p) ≤ _
  rw [← hGvalue]
  exact hmono

/-- Charging the negative regular row term costs at most one copy of the
halfwidth times scalar mass. -/
theorem neg_halfWidth_mass_le_neg_two_halfWidth_rowMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    -fourCellOperatorHalfWidth * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      -2 * fourCellOperatorHalfWidth *
        fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth := by
  have hrow := fourCellPositiveHalfRegularRowMass_le_half_mass w hw
  have ha : 0 ≤ fourCellOperatorHalfWidth :=
    fourCellOperatorHalfWidth_nonneg
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellRegularRowMassBoundStructural
