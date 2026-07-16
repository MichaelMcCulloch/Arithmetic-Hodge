import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural

noncomputable section

open YoshidaEndpointTriangleInterchange
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# Structural cancellation of the affine alternating border

The affine model in the antisymmetric regular kernel is not estimated.  Its
lag-weighted cross difference factors exactly into zeroth and first moments
on the centered interval.  Hence a mean-zero even-side profile paired with
an odd-side profile kills it identically.  This is the cancellation needed
for both `P₆`--odd-residual and even-residual--`P₇` rows.
-/

private theorem integral_integral_linear_crossDifference
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
      (y - x) * (v y * u x - u y * v x)) =
      2 * (((∫ x : ℝ in -1..1, u x) *
          (∫ x : ℝ in -1..1, x * v x)) -
        ((∫ x : ℝ in -1..1, x * u x) *
          (∫ x : ℝ in -1..1, v x))) := by
  let U₀ : ℝ := ∫ x : ℝ in -1..1, u x
  let U₁ : ℝ := ∫ x : ℝ in -1..1, x * u x
  let V₀ : ℝ := ∫ x : ℝ in -1..1, v x
  let V₁ : ℝ := ∫ x : ℝ in -1..1, x * v x
  have huI : IntervalIntegrable u volume (-1) 1 :=
    hu.intervalIntegrable _ _
  have hvI : IntervalIntegrable v volume (-1) 1 :=
    hv.intervalIntegrable _ _
  have hxuI : IntervalIntegrable (fun x : ℝ ↦ x * u x) volume (-1) 1 :=
    (continuous_id.mul hu).intervalIntegrable _ _
  have hxvI : IntervalIntegrable (fun x : ℝ ↦ x * v x) volume (-1) 1 :=
    (continuous_id.mul hv).intervalIntegrable _ _
  have hinner (y : ℝ) :
      (∫ x : ℝ in -1..1,
        (y - x) * (v y * u x - u y * v x)) =
        y * v y * U₀ - v y * U₁ - y * u y * V₀ + u y * V₁ := by
    have hA : IntervalIntegrable (fun x : ℝ ↦ (y * v y) * u x)
        volume (-1) 1 := huI.const_mul (y * v y)
    have hB : IntervalIntegrable (fun x : ℝ ↦ v y * (x * u x))
        volume (-1) 1 := hxuI.const_mul (v y)
    have hC : IntervalIntegrable (fun x : ℝ ↦ (y * u y) * v x)
        volume (-1) 1 := hvI.const_mul (y * u y)
    have hD : IntervalIntegrable (fun x : ℝ ↦ u y * (x * v x))
        volume (-1) 1 := hxvI.const_mul (u y)
    rw [show (fun x : ℝ ↦
        (y - x) * (v y * u x - u y * v x)) = fun x ↦
          (y * v y) * u x - v y * (x * u x) -
            (y * u y) * v x + u y * (x * v x) by
      funext x
      ring,
      intervalIntegral.integral_add ((hA.sub hB).sub hC) hD,
      intervalIntegral.integral_sub (hA.sub hB) hC,
      intervalIntegral.integral_sub hA hB]
    repeat rw [intervalIntegral.integral_const_mul]
  rw [show (fun y : ℝ ↦ ∫ x : ℝ in -1..1,
      (y - x) * (v y * u x - u y * v x)) = fun y ↦
        y * v y * U₀ - v y * U₁ - y * u y * V₀ + u y * V₁ by
    funext y
    exact hinner y]
  rw [intervalIntegral.integral_add,
    intervalIntegral.integral_sub,
    intervalIntegral.integral_sub]
  all_goals try
    apply Continuous.intervalIntegrable
    fun_prop
  repeat rw [intervalIntegral.integral_mul_const]
  dsimp only [U₀, U₁, V₀, V₁]
  ring

/-- The lag-linear ordered cross difference is exactly the determinant of
the zeroth/first moment vectors of the two profiles. -/
theorem integral_linear_mul_crossDifference_eq_moment_determinant
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation v u t -
        factorTwoCenteredCrossCorrelation u v t)) =
      ((∫ x : ℝ in -1..1, u x) *
          (∫ x : ℝ in -1..1, x * v x)) -
        ((∫ x : ℝ in -1..1, x * u x) *
          (∫ x : ℝ in -1..1, v x)) := by
  let q : ℝ → ℝ := fun t ↦ t
  let K : ℝ × ℝ → ℝ := fun p ↦
    (p.1 - p.2) * (v p.1 * u p.2 - u p.1 * v p.2)
  let Kvu : ℝ × ℝ → ℝ := fun p ↦
    (p.1 - p.2) * v p.1 * u p.2
  let Kuv : ℝ × ℝ → ℝ := fun p ↦
    (p.1 - p.2) * u p.1 * v p.2
  have hq : Continuous q := continuous_id
  have hK : Continuous K := by
    dsimp only [K]
    fun_prop
  have hKswap : ∀ p : ℝ × ℝ, K p.swap = K p := by
    intro p
    rcases p with ⟨y, x⟩
    dsimp only [K, Prod.swap_prod_mk]
    ring
  have hUpperVu := integral_weight_mul_crossCorrelation_eq_upperTriangle
    v u hv hu q hq
  have hUpperUv := integral_weight_mul_crossCorrelation_eq_upperTriangle
    u v hu hv q hq
  have hVuInt : IntervalIntegrable
      (fun t : ℝ ↦ q t * factorTwoCenteredCrossCorrelation v u t)
      volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation v u hv hu))
      |>.intervalIntegrable 0 2
  have hUvInt : IntervalIntegrable
      (fun t : ℝ ↦ q t * factorTwoCenteredCrossCorrelation u v t)
      volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation u v hu hv))
      |>.intervalIntegrable 0 2
  have hUsub : centeredUpperTriangle ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hUmeas : MeasurableSet centeredUpperTriangle := by
    unfold centeredUpperTriangle
    measurability
  have hKvu : IntegrableOn Kvu centeredUpperTriangle := by
    have hcont : Continuous Kvu := by
      dsimp only [Kvu]
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hKuv : IntegrableOn Kuv centeredUpperTriangle := by
    have hcont : Continuous Kuv := by
      dsimp only [Kuv]
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hUpper :
      (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
    rw [show (fun t : ℝ ↦
        q t * (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) = fun t ↦
        q t * factorTwoCenteredCrossCorrelation v u t -
          q t * factorTwoCenteredCrossCorrelation u v t by
      funext t
      ring,
      intervalIntegral.integral_sub hVuInt hUvInt,
      hUpperVu, hUpperUv,
      ← MeasureTheory.integral_sub hKvu hKuv]
    apply setIntegral_congr_fun hUmeas
    intro p _hp
    dsimp only [K, Kvu, Kuv, q]
    ring
  have hSquare :=
    two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare K hK hKswap
  have hIterated := setIntegral_centeredSquare_eq_iterated K hK
  have hFull := integral_integral_linear_crossDifference u v hu hv
  change (∫ t : ℝ in 0..2,
      q t * (factorTwoCenteredCrossCorrelation v u t -
        factorTwoCenteredCrossCorrelation u v t)) = _
  rw [hUpper]
  dsimp only [K] at hIterated
  rw [hIterated, hFull] at hSquare
  linarith

/-- Mean zero on the first profile and oddness of the second profile kill
the entire affine alternating model. -/
theorem integral_linear_mul_crossDifference_eq_zero_of_mean_zero_odd
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huMean : (∫ x : ℝ in -1..1, u x) = 0)
    (hvOdd : Function.Odd v) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation v u t -
        factorTwoCenteredCrossCorrelation u v t)) = 0 := by
  have hvMean := centered_interval_integral_eq_zero_of_odd v hvOdd
  rw [integral_linear_mul_crossDifference_eq_moment_determinant u v hu hv,
    huMean, hvMean]
  ring

/-- The `P₆`--odd-residual affine row vanishes structurally. -/
theorem integral_linear_mul_P6_oddResidual_crossDifference_eq_zero
    (o : ℝ → ℝ) (hoc : Continuous o) (ho : Function.Odd o)
    (c : ℝ) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation o (c • factorTwoCenteredP6) t -
        factorTwoCenteredCrossCorrelation (c • factorTwoCenteredP6) o t)) = 0 := by
  apply integral_linear_mul_crossDifference_eq_zero_of_mean_zero_odd
    (c • factorTwoCenteredP6) o
    (continuous_factorTwoCenteredP6.const_smul c) hoc
  · rw [show (fun x : ℝ ↦ (c • factorTwoCenteredP6) x) =
        fun x ↦ c * factorTwoCenteredP6 x by rfl,
      intervalIntegral.integral_const_mul, integral_factorTwoCenteredP6,
      mul_zero]
  · exact ho

/-- The even-residual--`P₇` affine row vanishes from the residual mean gap
and the odd parity of `P₇`. -/
theorem integral_linear_mul_evenResidual_P7_crossDifference_eq_zero
    (e : ℝ → ℝ) (hec : Continuous e)
    (heLow : centeredLegendreMomentsVanishBelow e 8)
    (d : ℝ) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation (d • factorTwoCenteredP7) e t -
        factorTwoCenteredCrossCorrelation e (d • factorTwoCenteredP7) t)) = 0 := by
  have heP0 := centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
    e (by norm_num) heLow
  have heMean : (∫ x : ℝ in -1..1, e x) = 0 := by
    unfold centeredEvenP0Coefficient at heP0
    linarith
  apply integral_linear_mul_crossDifference_eq_zero_of_mean_zero_odd
    e (d • factorTwoCenteredP7) hec
    (continuous_factorTwoCenteredP7.const_smul d) heMean
  exact odd_factorTwoCenteredP7.const_smul d

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural
