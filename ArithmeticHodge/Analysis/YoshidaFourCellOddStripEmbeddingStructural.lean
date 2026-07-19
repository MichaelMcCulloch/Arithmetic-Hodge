import ArithmeticHodge.Analysis.YoshidaFourCellOddEndpointStripCoercivityStructural
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddStripEmbeddingStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellRawParityFoldStructural

/-!
# Embedding the odd endpoint strip in the positive-half raw energy

The affine pullback `z ↦ 4/5 + z/5` identifies the centered strip energy
with the physical logarithmic difference energy on `[3/5,1]²`.  Since the
kernel is nonnegative, this square is controlled by the complete positive
half square `[0,1]²`.  Product integrability is retained explicitly; no
singular diagonal is discarded or rearranged formally.
-/

private theorem intervalIntegral_integral_eq_setIntegral_square
    (F : ℝ × ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc a b)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p := by
  calc
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
        ∫ x : ℝ in Icc a b, ∫ y : ℝ in Icc a b, F (x, y) := by
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in a..b, F (x, y)) =
        ∫ y : ℝ in Icc a b, F (x, y)
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p := by
      exact (setIntegral_prod F hF).symm

/-- Exact affine normalization of the pulled-back endpoint-strip energy.
The two Jacobians contribute `1/25`, while the degree-minus-one logarithmic
kernel contributes `5`, leaving the defining factor `1/5`. -/
theorem fourCellOddEndpointStripRawEnergy_eq_physicalSquare
    (w : ℝ → ℝ) :
    fourCellOddEndpointStripRawEnergy w =
      ∫ x : ℝ in 3 / 5..1, ∫ y : ℝ in 3 / 5..1,
        (w x - w y) ^ 2 / |x - y| := by
  let f := fourCellOddEndpointStripPullback w
  let H : ℝ → ℝ → ℝ := fun z q ↦
    (f z - f q) ^ 2 / |z - q|
  let K : ℝ → ℝ → ℝ := fun x y ↦
    (w x - w y) ^ 2 / |x - y|
  have hpoint (x y : ℝ) :
      K x y = 5 * H (5 * x - 4) (5 * y - 4) := by
    dsimp only [K, H, f, fourCellOddEndpointStripPullback]
    rw [show 4 / 5 + (5 * x - 4) / 5 = x by ring,
      show 4 / 5 + (5 * y - 4) / 5 = y by ring,
      show (5 * x - 4) - (5 * y - 4) = 5 * (x - y) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    by_cases hxy : |x - y| = 0
    · simp [hxy]
    · field_simp [hxy]
  have hinner (x : ℝ) :
      (∫ y : ℝ in 3 / 5..1, K x y) =
        ∫ q : ℝ in -1..1, H (5 * x - 4) q := by
    have hsubst := intervalIntegral.integral_comp_mul_add
      (a := (3 / 5 : ℝ)) (b := 1)
      (fun q : ℝ ↦ H (5 * x - 4) q)
      (by norm_num : (5 : ℝ) ≠ 0) (-4)
    have hsubst' :
        (∫ y : ℝ in 3 / 5..1, H (5 * x - 4) (5 * y - 4)) =
          (1 / 5 : ℝ) * ∫ q : ℝ in -1..1, H (5 * x - 4) q := by
      convert hsubst using 1
      all_goals norm_num
    calc
      (∫ y : ℝ in 3 / 5..1, K x y) =
          ∫ y : ℝ in 3 / 5..1,
            5 * H (5 * x - 4) (5 * y - 4) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact hpoint x y
      _ = 5 * ∫ y : ℝ in 3 / 5..1,
          H (5 * x - 4) (5 * y - 4) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ q : ℝ in -1..1, H (5 * x - 4) q := by
        rw [hsubst']
        ring
  have houter :
      (∫ x : ℝ in 3 / 5..1,
          ∫ q : ℝ in -1..1, H (5 * x - 4) q) =
        (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
          ∫ q : ℝ in -1..1, H z q := by
    have hsubst := intervalIntegral.integral_comp_mul_add
      (a := (3 / 5 : ℝ)) (b := 1)
      (fun z : ℝ ↦ ∫ q : ℝ in -1..1, H z q)
      (by norm_num : (5 : ℝ) ≠ 0) (-4)
    convert hsubst using 1
    all_goals norm_num
  unfold fourCellOddEndpointStripRawEnergy centeredRawLogEnergy
  calc
    (1 / 5 : ℝ) *
        (∫ z : ℝ in -1..1, ∫ q : ℝ in -1..1,
          (fourCellOddEndpointStripPullback w z -
            fourCellOddEndpointStripPullback w q) ^ 2 / |z - q|) =
      ∫ x : ℝ in 3 / 5..1, ∫ q : ℝ in -1..1,
        ((fourCellOddEndpointStripPullback w (5 * x - 4) -
          fourCellOddEndpointStripPullback w q) ^ 2 /
            |(5 * x - 4) - q|) := houter.symm
    _ = ∫ x : ℝ in 3 / 5..1, ∫ y : ℝ in 3 / 5..1,
        (w x - w y) ^ 2 / |x - y| := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact (hinner x).symm

/-- Product-integrable form of the endpoint-strip embedding. -/
theorem fourCellOddEndpointStripRawEnergy_le_positiveHalf_of_integrable
    (w : ℝ → ℝ)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    fourCellOddEndpointStripRawEnergy w ≤
      fourCellPositiveHalfRawSameSignEnergy w := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let P : Set ℝ := Icc (0 : ℝ) 1
  let S : Set ℝ := Icc (3 / 5 : ℝ) 1
  have hSsub : S ⊆ P := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hstrip : IntegrableOn K (S ×ˢ S)
      ((volume : Measure ℝ).prod volume) := by
    exact henergy.mono_set (Set.prod_mono hSsub hSsub)
  have hnonneg : ∀ p : ℝ × ℝ, 0 ≤ K p := by
    intro p
    dsimp only [K]
    unfold centeredLogDifferenceKernel
    exact div_nonneg (sq_nonneg _) (abs_nonneg _)
  have hmono :
      (∫ p : ℝ × ℝ in S ×ˢ S, K p) ≤
        ∫ p : ℝ × ℝ in P ×ˢ P, K p := by
    exact setIntegral_mono_set henergy
      (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall (Set.prod_mono hSsub hSsub))
  rw [fourCellOddEndpointStripRawEnergy_eq_physicalSquare]
  unfold fourCellPositiveHalfRawSameSignEnergy
  change (∫ x : ℝ in 3 / 5..1, ∫ y : ℝ in 3 / 5..1, K (x, y)) ≤
    ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, K (x, y)
  rw [intervalIntegral_integral_eq_setIntegral_square K
      (3 / 5) 1 (by norm_num) hstrip,
    intervalIntegral_integral_eq_setIntegral_square K
      0 1 (by norm_num) henergy]
  simpa only [K, P, S, centeredLogDifferenceKernel] using hmono

/-- Local Lipschitz regularity on the centered interval supplies the genuine
product integrability needed by the endpoint-strip embedding. -/
theorem fourCellOddEndpointStripRawEnergy_le_positiveHalf_of_locallyLipschitzOn
    (w : ℝ → ℝ)
    (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    fourCellOddEndpointStripRawEnergy w ≤
      fourCellPositiveHalfRawSameSignEnergy w := by
  obtain ⟨C, hC⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hunit : Icc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  apply fourCellOddEndpointStripRawEnergy_le_positiveHalf_of_integrable w
  exact hfull.mono_set (Set.prod_mono hunit hunit)

/-- The production `C¹` wrapper used by the odd four-cell coercivity chain. -/
theorem fourCellOddEndpointStripRawEnergy_le_positiveHalf
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellOddEndpointStripRawEnergy w ≤
      fourCellPositiveHalfRawSameSignEnergy w := by
  exact
    fourCellOddEndpointStripRawEnergy_le_positiveHalf_of_locallyLipschitzOn
      w (hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddStripEmbeddingStructural
