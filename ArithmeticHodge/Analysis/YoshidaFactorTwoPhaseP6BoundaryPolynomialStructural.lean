import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP6BoundaryPolynomialStructural

open YoshidaEndpointHyperbolicBound
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

noncomputable section

/-!
# The degree-six boundary term at the `P6` cutoff

A moment gap at six annihilates the constant, quadratic, and quartic pieces
of the pole-free degree-six kernel.  Unlike a gap strictly above six, it does
not annihilate the top-degree piece.  This file retains that piece exactly.
-/

/-- At the exact cutoff six, the polynomial kernel is a single degree-six
correlation moment.  This is the cutoff-boundary version of
`integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_zero`. -/
theorem integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_sixth
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t *
        factorTwoCenteredCorrelationBilinear u r t) =
      poleFreeCoeff6 yoshidaEndpointA *
        ∫ t : ℝ in 0..2,
          t ^ 6 * factorTwoCenteredCorrelationBilinear u r t := by
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u r
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u r hu hr).add
      (continuous_factorTwoCenteredCrossCorrelation r u hr hu)).div_const 2
  have h0 : (∫ t : ℝ in 0..2, t ^ 0 * B t) = 0 := by
    exact integral_evenPower_mul_correlationBilinear_eq_zero
      u r hu hr hlow (by norm_num : 2 * 0 < 6)
  have h2 : (∫ t : ℝ in 0..2, t ^ 2 * B t) = 0 := by
    simpa only [Nat.reduceMul] using
      (integral_evenPower_mul_correlationBilinear_eq_zero
        u r hu hr hlow (by norm_num : 2 * 1 < 6))
  have h4 : (∫ t : ℝ in 0..2, t ^ 4 * B t) = 0 := by
    simpa only [Nat.reduceMul] using
      (integral_evenPower_mul_correlationBilinear_eq_zero
        u r hu hr hlow (by norm_num : 2 * 2 < 6))
  have h0Int : IntervalIntegrable B volume 0 2 := hB.intervalIntegrable 0 2
  have h2Int : IntervalIntegrable (fun t : ℝ ↦ t ^ 2 * B t)
      volume 0 2 := ((continuous_id.pow 2).mul hB).intervalIntegrable 0 2
  have h4Int : IntervalIntegrable (fun t : ℝ ↦ t ^ 4 * B t)
      volume 0 2 := ((continuous_id.pow 4).mul hB).intervalIntegrable 0 2
  have h6Int : IntervalIntegrable (fun t : ℝ ↦ t ^ 6 * B t)
      volume 0 2 := ((continuous_id.pow 6).mul hB).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * B t) = fun t ↦
      poleFreeCoeff0 yoshidaEndpointA * B t +
        poleFreeCoeff2 yoshidaEndpointA * (t ^ 2 * B t) +
        poleFreeCoeff4 yoshidaEndpointA * (t ^ 4 * B t) +
        poleFreeCoeff6 yoshidaEndpointA * (t ^ 6 * B t) by
    funext t
    rw [poleFreeKernelPolynomial6_expansion]
    ring,
    intervalIntegral.integral_add
      (((h0Int.const_mul _).add (h2Int.const_mul _)).add (h4Int.const_mul _))
      (h6Int.const_mul _),
    intervalIntegral.integral_add
      ((h0Int.const_mul _).add (h2Int.const_mul _)) (h4Int.const_mul _),
    intervalIntegral.integral_add (h0Int.const_mul _) (h2Int.const_mul _)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [show (∫ t : ℝ in 0..2, B t) = 0 by simpa using h0,
    h2, h4]
  ring

/-- The surviving sixth-power lag is rank one.  Folding the two ordered
correlations fills the centered square; the moment gap then kills
`(y - x)^6 - x^6` as a polynomial of degree below six in `x`. -/
theorem integral_sixthPower_mul_correlationBilinear_eq_rankOne
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 6) :
    (∫ t : ℝ in 0..2,
      t ^ 6 * factorTwoCenteredCorrelationBilinear u r t) =
      (1 / 2 : ℝ) * (∫ y : ℝ in -1..1, u y) *
        ∫ x : ℝ in -1..1, r x * x ^ 6 := by
  let q : ℝ → ℝ := fun t ↦ t ^ 6
  let K₀ : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * u p.1 * r p.2
  let K₁ : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * r p.1 * u p.2
  let K : ℝ × ℝ → ℝ := fun p ↦ K₀ p + K₁ p
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hK₀ : Continuous K₀ := by
    dsimp only [K₀]
    fun_prop
  have hK₁ : Continuous K₁ := by
    dsimp only [K₁]
    fun_prop
  have hK : Continuous K := hK₀.add hK₁
  have hKswap : ∀ p : ℝ × ℝ, K p.swap = K p := by
    intro p
    rcases p with ⟨y, x⟩
    dsimp only [K, K₀, K₁, q, Prod.swap_prod_mk]
    rw [show x - y = -(y - x) by ring, Even.neg_pow (by norm_num : Even 6)]
    ring
  have hUpper₀ := integral_weight_mul_crossCorrelation_eq_upperTriangle
    u r hu hr q hq
  have hUpper₁ := integral_weight_mul_crossCorrelation_eq_upperTriangle
    r u hr hu q hq
  have hCorr₀Int : IntervalIntegrable
      (fun t : ℝ ↦ q t * factorTwoCenteredCrossCorrelation u r t)
      volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation u r hu hr))
      |>.intervalIntegrable 0 2
  have hCorr₁Int : IntervalIntegrable
      (fun t : ℝ ↦ q t * factorTwoCenteredCrossCorrelation r u t)
      volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation r u hr hu))
      |>.intervalIntegrable 0 2
  have hUsub : centeredUpperTriangle ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hK₀Upper : IntegrableOn K₀ centeredUpperTriangle :=
    (hK₀.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hK₁Upper : IntegrableOn K₁ centeredUpperTriangle :=
    (hK₁.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hIupper :
      2 * (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCorrelationBilinear u r t) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
    calc
      2 * (∫ t : ℝ in 0..2,
          q t * factorTwoCenteredCorrelationBilinear u r t) =
          ∫ t : ℝ in 0..2,
            q t * factorTwoCenteredCrossCorrelation u r t +
              q t * factorTwoCenteredCrossCorrelation r u t := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _ht
        unfold factorTwoCenteredCorrelationBilinear
        ring
      _ = (∫ t : ℝ in 0..2,
            q t * factorTwoCenteredCrossCorrelation u r t) +
          ∫ t : ℝ in 0..2,
            q t * factorTwoCenteredCrossCorrelation r u t := by
        rw [intervalIntegral.integral_add hCorr₀Int hCorr₁Int]
      _ = (∫ p : ℝ × ℝ in centeredUpperTriangle, K₀ p) +
          ∫ p : ℝ × ℝ in centeredUpperTriangle, K₁ p := by
        rw [hUpper₀, hUpper₁]
      _ = ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
        rw [show K = fun p ↦ K₀ p + K₁ p by rfl,
          MeasureTheory.integral_add hK₀Upper hK₁Upper]
  have hinner (y : ℝ) :
      (∫ x : ℝ in -1..1, K₀ (y, x)) =
        u y * ∫ x : ℝ in -1..1, r x * x ^ 6 := by
    let Qy : ℝ[X] :=
      (Polynomial.C (y + 1) - Polynomial.C 2 * Polynomial.X) ^ 6 -
        (Polynomial.C 2 * Polynomial.X - 1) ^ 6
    have hQy : Qy.natDegree < 6 := by
      dsimp only [Qy]
      have hdeg : ((Polynomial.C (y + 1) -
          Polynomial.C 2 * Polynomial.X) ^ 6 -
          (Polynomial.C 2 * Polynomial.X - 1) ^ 6 : ℝ[X]).natDegree ≤ 5 := by
        ring_nf
        compute_degree
      omega
    have horth := intervalIntegral_mul_shiftedPolynomial_eq_zero
      r hr hlow Qy hQy
    have hQeval (x : ℝ) :
        Qy.eval ((x + 1) / 2) = (y - x) ^ 6 - x ^ 6 := by
      dsimp only [Qy]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one]
      congr 1 <;> ring
    have hleftInt : IntervalIntegrable
        (fun x : ℝ ↦ r x * (y - x) ^ 6) volume (-1) 1 :=
      (hr.mul ((continuous_const.sub continuous_id).pow 6)).intervalIntegrable _ _
    have hrightInt : IntervalIntegrable
        (fun x : ℝ ↦ r x * x ^ 6) volume (-1) 1 :=
      (hr.mul (continuous_id.pow 6)).intervalIntegrable _ _
    rw [show (fun x : ℝ ↦ r x * Qy.eval ((x + 1) / 2)) =
        fun x ↦ r x * (y - x) ^ 6 - r x * x ^ 6 by
      funext x
      rw [hQeval]
      ring,
      intervalIntegral.integral_sub hleftInt hrightInt] at horth
    have heq : (∫ x : ℝ in -1..1, r x * (y - x) ^ 6) =
        ∫ x : ℝ in -1..1, r x * x ^ 6 := by
      linarith
    rw [show (fun x : ℝ ↦ K₀ (y, x)) =
        fun x ↦ u y * (r x * (y - x) ^ 6) by
      funext x
      dsimp only [K₀, q]
      ring,
      intervalIntegral.integral_const_mul, heq]
  have hK₀Square :
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K₀ p) =
        (∫ y : ℝ in -1..1, u y) *
          ∫ x : ℝ in -1..1, r x * x ^ 6 := by
    rw [setIntegral_centeredSquare_eq_iterated K₀ hK₀]
    rw [show (fun y : ℝ ↦ ∫ x : ℝ in -1..1, K₀ (y, x)) =
        fun y ↦ u y * (∫ x : ℝ in -1..1, r x * x ^ 6) by
      funext y
      exact hinner y,
      intervalIntegral.integral_mul_const]
  have hK₁Square :
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K₁ p) =
        (∫ y : ℝ in -1..1, u y) *
          ∫ x : ℝ in -1..1, r x * x ^ 6 := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) K₀
    rw [show (fun p : ℝ × ℝ ↦ K₀ p.swap) = K₁ by
      funext p
      rcases p with ⟨y, x⟩
      dsimp only [K₀, K₁, q, Prod.swap_prod_mk]
      rw [show x - y = -(y - x) by ring,
        Even.neg_pow (by norm_num : Even 6)]
      ring] at hswap
    have hK₀Square' : MeasureTheory.integral
        (((volume : Measure ℝ).prod volume).restrict
          (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) K₀ =
        (∫ y : ℝ in -1..1, u y) *
          ∫ x : ℝ in -1..1, r x * x ^ 6 := by
      simpa only [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using
        hK₀Square
    change MeasureTheory.integral
      (((volume : Measure ℝ).prod volume).restrict
        (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) K₁ = _
    exact hswap.trans hK₀Square'
  have hK₀SquareInt : IntegrableOn K₀
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    hK₀.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hK₁SquareInt : IntegrableOn K₁
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    hK₁.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hKSquare :
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) =
        2 * ((∫ y : ℝ in -1..1, u y) *
          ∫ x : ℝ in -1..1, r x * x ^ 6) := by
    rw [show K = fun p ↦ K₀ p + K₁ p by rfl,
      MeasureTheory.integral_add hK₀SquareInt hK₁SquareInt,
      hK₀Square, hK₁Square]
    ring
  have hfold :=
    two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare K hK hKswap
  rw [hKSquare] at hfold
  change (∫ t : ℝ in 0..2,
    q t * factorTwoCenteredCorrelationBilinear u r t) = _
  linarith [hIupper, hfold]

/-- The top centered moment of `P6`, normalized through its leading
coefficient. -/
theorem integral_factorTwoCenteredP6_mul_pow_six :
    (∫ x : ℝ in -1..1, factorTwoCenteredP6 x * x ^ 6) =
      (32 / 3003 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 x * x ^ 6) = fun x ↦
      ((231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16) *
        x ^ 6 by
    funext x
    rw [factorTwoCenteredP6_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-- Only the `P0` coefficient contributes to the mass of the even low
profile. -/
theorem integral_factorTwoP024Profile
    (c0 c2 c4 : ℝ) :
    (∫ x : ℝ in -1..1,
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) x) = 2 * c0 := by
  rw [show (fun x : ℝ ↦
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) x) = fun x ↦
      c0 * centeredEvenP0 x + c2 * centeredEvenP2 x +
        c4 * factorTwoCenteredP4 x by
    funext x
    unfold factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    simp only [Pi.add_apply]]
  have h0Int : IntervalIntegrable
      (fun x : ℝ ↦ c0 * centeredEvenP0 x) volume (-1) 1 :=
    (by unfold centeredEvenP0; fun_prop : Continuous (fun x : ℝ ↦
      c0 * centeredEvenP0 x)).intervalIntegrable _ _
  have h2Int : IntervalIntegrable
      (fun x : ℝ ↦ c2 * centeredEvenP2 x) volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous (fun x : ℝ ↦
      c2 * centeredEvenP2 x)).intervalIntegrable _ _
  have h4Int : IntervalIntegrable
      (fun x : ℝ ↦ c4 * factorTwoCenteredP4 x) volume (-1) 1 :=
    (by unfold factorTwoCenteredP4; fun_prop : Continuous (fun x : ℝ ↦
      c4 * factorTwoCenteredP4 x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0Int.add h2Int) h4Int,
    intervalIntegral.integral_add h0Int h2Int]
  repeat rw [intervalIntegral.integral_const_mul]
  have hP0 : (∫ x : ℝ in -1..1, centeredEvenP0 x) = 2 := by
    simp only [centeredEvenP0]
    norm_num
  have hP2 : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using
      integral_centeredEvenP0_mul_p2
  rw [hP0, hP2, integral_factorTwoCenteredP4]
  ring

/-- The cutoff-boundary degree-six lag sees exactly one low coordinate. -/
theorem integral_sixthPower_mul_P024_P6
    (c0 c2 c4 : ℝ) :
    (∫ t : ℝ in 0..2, t ^ 6 *
      factorTwoCenteredCorrelationBilinear
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        factorTwoCenteredP6 t) = (32 / 3003 : ℝ) * c0 := by
  have hLow : Continuous
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) := by
    exact (continuous_factorTwoEvenStructuralLowProfile c0 c2).add
      (continuous_const.mul continuous_factorTwoCenteredP4)
  rw [integral_sixthPower_mul_correlationBilinear_eq_rankOne
    _ _ hLow continuous_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow,
    integral_factorTwoP024Profile,
    integral_factorTwoCenteredP6_mul_pow_six]
  ring

/-- Consequently the entire degree-six polynomial kernel is a single `P0`
row at the `P6` boundary. -/
theorem integral_poleFreeKernelPolynomial6_mul_P024_P6
    (c0 c2 c4 : ℝ) :
    (∫ t : ℝ in 0..2, poleFreeKernelPolynomial6 t *
      factorTwoCenteredCorrelationBilinear
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        factorTwoCenteredP6 t) =
      poleFreeCoeff6 yoshidaEndpointA * (32 / 3003 : ℝ) * c0 := by
  have hLow : Continuous
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4) := by
    exact (continuous_factorTwoEvenStructuralLowProfile c0 c2).add
      (continuous_const.mul continuous_factorTwoCenteredP4)
  rw [integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_sixth
    _ _ hLow continuous_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow,
    integral_sixthPower_mul_P024_P6]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP6BoundaryPolynomialStructural
