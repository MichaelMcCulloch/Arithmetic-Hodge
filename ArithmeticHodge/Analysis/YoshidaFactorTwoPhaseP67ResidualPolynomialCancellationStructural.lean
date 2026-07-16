import ArithmeticHodge.Analysis.ShiftedLegendreBasis
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import Mathlib.Algebra.Polynomial.Eval.SMul

set_option autoImplicit false

open MeasureTheory Polynomial Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCoupledRankSquares
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

noncomputable section

/-!
# Polynomial cancellation from a shifted-Legendre moment gap

The defining moment conditions for a higher residual annihilate the entire
polynomial space below the cutoff, not merely the named Legendre generators.
The proof uses the strictly degree-increasing shifted-Legendre basis and hence
does not enumerate monomials or coefficients.
-/

/-- A continuous centered profile whose first `k` shifted-Legendre moments
vanish is orthogonal to every real polynomial of degree below `k`. -/
theorem integral_centeredPullback_mul_polynomial_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow w k)
    (Q : ℝ[X]) (hQ : Q.natDegree < k) :
    (∫ t : unitInterval,
      centeredPullback w (t : ℝ) * Q.eval (t : ℝ)) = 0 := by
  have hintegrable : ∀ R : ℝ[X], Integrable (fun t : unitInterval ↦
      centeredPullback w (t : ℝ) * R.eval (t : ℝ)) := by
    intro R
    have hcontinuous : Continuous (fun t : unitInterval ↦
        centeredPullback w (t : ℝ) * R.eval (t : ℝ)) := by
      apply Continuous.mul
      · simpa only [centeredPullback] using
          hw.comp (by fun_prop : Continuous (fun t : unitInterval ↦
            2 * (t : ℝ) - 1))
      · exact R.continuous.comp continuous_subtype_val
    exact hcontinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hspan : Q ∈ Submodule.span ℝ
      (shiftedLegendreRealSequence '' Iio k) := by
    rw [shiftedLegendreRealSequence.span_degreeLT
      (fun i _hi ↦ shiftedLegendreReal_leadingCoeff_isUnit i)]
    by_cases hzero : Q = 0
    · subst Q
      exact Submodule.zero_mem _
    · rw [Polynomial.mem_degreeLT,
        ← Polynomial.natDegree_lt_iff_degree_lt hzero]
      exact hQ
  refine Submodule.span_induction
    (p := fun R _hR ↦
      (∫ t : unitInterval,
        centeredPullback w (t : ℝ) * R.eval (t : ℝ)) = 0)
    ?_ ?_ ?_ ?_ hspan
  · intro R hR
    obtain ⟨n, hn, rfl⟩ := hR
    simpa only [shiftedLegendreRealSequence_apply] using
      hlow n (Set.mem_Iio.mp hn)
  · simp
  · intro R S _hR _hS hRzero hSzero
    rw [show (fun t : unitInterval ↦
        centeredPullback w (t : ℝ) * (R + S).eval (t : ℝ)) =
        fun t : unitInterval ↦
          centeredPullback w (t : ℝ) * R.eval (t : ℝ) +
            centeredPullback w (t : ℝ) * S.eval (t : ℝ) by
      funext t
      rw [Polynomial.eval_add, mul_add]]
    rw [
      MeasureTheory.integral_add (hintegrable R) (hintegrable S),
      hRzero, hSzero, add_zero]
  · intro a R _hR hRzero
    simp only [Polynomial.eval_smul, smul_eq_mul]
    rw [show (fun t : unitInterval ↦
        centeredPullback w (t : ℝ) * (a * R.eval (t : ℝ))) =
        fun t : unitInterval ↦
          a * (centeredPullback w (t : ℝ) * R.eval (t : ℝ)) by
      funext t
      ring]
    rw [MeasureTheory.integral_const_mul, hRzero, mul_zero]

/-- Centered-interval form of
`integral_centeredPullback_mul_polynomial_eq_zero`.  The affine argument in
the polynomial is exactly the inverse transport from `[-1,1]` to `[0,1]`. -/
theorem intervalIntegral_mul_shiftedPolynomial_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow w k)
    (Q : ℝ[X]) (hQ : Q.natDegree < k) :
    (∫ x : ℝ in -1..1, w x * Q.eval ((x + 1) / 2)) = 0 := by
  have hunit : (∫ t : unitInterval,
      centeredPullback w (t : ℝ) * Q.eval (t : ℝ)) = 0 :=
    integral_centeredPullback_mul_polynomial_eq_zero w hw hlow Q hQ
  have hreal : (∫ t : ℝ in 0..1,
      centeredPullback w t * Q.eval t) = 0 := by
    rw [← integral_unitInterval_eq_intervalIntegral]
    exact hunit
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ w x * Q.eval ((x + 1) / 2))
  have hpullback : (fun t : ℝ ↦
      w (2 * t - 1) * Q.eval (((2 * t - 1) + 1) / 2)) =
      fun t : ℝ ↦ centeredPullback w t * Q.eval t := by
    funext t
    simp only [centeredPullback]
    congr 2
    ring
  rw [hpullback, hreal] at htransport
  linarith

/-- Every even lag monomial below the residual cutoff annihilates the
symmetric cross-correlation.  Folding the two ordered correlations fills the
whole centered square; one variable then pairs the residual with a polynomial
of degree `2 * j`. -/
theorem integral_evenPower_mul_correlationBilinear_eq_zero
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    {k j : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hjk : 2 * j < k) :
    (∫ t : ℝ in 0..2,
      t ^ (2 * j) * factorTwoCenteredCorrelationBilinear u r t) = 0 := by
  let q : ℝ → ℝ := fun t ↦ t ^ (2 * j)
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
    rw [show x - y = -(y - x) by ring,
      (even_two.mul_right j).neg_pow]
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
      (∫ x : ℝ in -1..1, K₀ (y, x)) = 0 := by
    let Qy : ℝ[X] :=
      (Polynomial.C (y + 1) - Polynomial.C 2 * Polynomial.X) ^ (2 * j)
    have hbase :
        (Polynomial.C (y + 1) - Polynomial.C 2 * Polynomial.X).natDegree ≤ 1 := by
      have hC : (Polynomial.C (y + 1) : ℝ[X]).natDegree ≤ 0 := by
        simp
      have hX : (Polynomial.C 2 * Polynomial.X : ℝ[X]).natDegree ≤ 1 := by
        norm_num
      exact (Polynomial.natDegree_sub_le_of_le hC hX).trans (by norm_num)
    have hQy : Qy.natDegree < k := by
      refine lt_of_le_of_lt
        (Polynomial.natDegree_pow_le_of_le (2 * j) hbase) ?_
      simpa only [Nat.mul_one] using hjk
    have horth := intervalIntegral_mul_shiftedPolynomial_eq_zero
      r hr hlow Qy hQy
    have hQeval (x : ℝ) :
        Qy.eval ((x + 1) / 2) = (y - x) ^ (2 * j) := by
      dsimp only [Qy]
      simp only [Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      congr 1
      ring
    rw [show (fun x : ℝ ↦ K₀ (y, x)) = fun x ↦
        u y * (r x * Qy.eval ((x + 1) / 2)) by
      funext x
      dsimp only [K₀, q]
      rw [hQeval]
      ring,
      intervalIntegral.integral_const_mul, horth, mul_zero]
  have hK₀Square :
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K₀ p) = 0 := by
    rw [setIntegral_centeredSquare_eq_iterated K₀ hK₀]
    rw [show (fun y : ℝ ↦ ∫ x : ℝ in -1..1, K₀ (y, x)) =
        fun _y : ℝ ↦ 0 by
      funext y
      exact hinner y]
    simp
  have hK₁Square :
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K₁ p) = 0 := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) K₀
    rw [show (fun p : ℝ × ℝ ↦ K₀ p.swap) = K₁ by
      funext p
      rcases p with ⟨y, x⟩
      dsimp only [K₀, K₁, q, Prod.swap_prod_mk]
      rw [show x - y = -(y - x) by ring,
        (even_two.mul_right j).neg_pow]
      ring] at hswap
    have hK₀Square' : MeasureTheory.integral
        (((volume : Measure ℝ).prod volume).restrict
          (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) K₀ = 0 := by
      simpa only [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using
        hK₀Square
    change MeasureTheory.integral
      (((volume : Measure ℝ).prod volume).restrict
        (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) K₁ = 0
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
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) = 0 := by
    rw [show K = fun p ↦ K₀ p + K₁ p by rfl,
      MeasureTheory.integral_add hK₀SquareInt hK₁SquareInt,
      hK₀Square, hK₁Square, add_zero]
  have hfold :=
    two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare K hK hKswap
  rw [hKSquare] at hfold
  change (∫ t : ℝ in 0..2,
    q t * factorTwoCenteredCorrelationBilinear u r t) = 0
  linarith

/-- The complete degree-six pole-free symmetric model vanishes on every
low--residual row whose residual cutoff lies strictly above degree six. -/
theorem integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_zero
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    {k : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hcut : 6 < k) :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t *
        factorTwoCenteredCorrelationBilinear u r t) = 0 := by
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u r
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u r hu hr).add
      (continuous_factorTwoCenteredCrossCorrelation r u hr hu)).div_const 2
  have h0 : (∫ t : ℝ in 0..2, t ^ 0 * B t) = 0 := by
    exact integral_evenPower_mul_correlationBilinear_eq_zero
      u r hu hr hlow (by omega : 2 * 0 < k)
  have h2 : (∫ t : ℝ in 0..2, t ^ 2 * B t) = 0 := by
    simpa only [Nat.reduceMul] using
      (integral_evenPower_mul_correlationBilinear_eq_zero
        u r hu hr hlow (by omega : 2 * 1 < k))
  have h4 : (∫ t : ℝ in 0..2, t ^ 4 * B t) = 0 := by
    simpa only [Nat.reduceMul] using
      (integral_evenPower_mul_correlationBilinear_eq_zero
        u r hu hr hlow (by omega : 2 * 2 < k))
  have h6 : (∫ t : ℝ in 0..2, t ^ 6 * B t) = 0 := by
    simpa only [Nat.reduceMul] using
      (integral_evenPower_mul_correlationBilinear_eq_zero
        u r hu hr hlow (by omega : 2 * 3 < k))
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
    h2, h4, h6]
  ring

/-- The symmetric degree-six model contributes exactly zero to the
`P₆`--even-residual row at the production cutoff. -/
theorem integral_poleFreeKernelPolynomial6_mul_P6_evenResidual_eq_zero
    (e : ℝ → ℝ) (hec : Continuous e)
    (heLow : centeredLegendreMomentsVanishBelow e 8) (c : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t *
        factorTwoCenteredCorrelationBilinear
          (c • factorTwoCenteredP6) e t) = 0 := by
  exact integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_zero
    (c • factorTwoCenteredP6) e
    (continuous_factorTwoCenteredP6.const_smul c) hec heLow (by norm_num)

/-- The same structural cancellation kills the `P₇`--odd-residual row;
no separate coefficient calculation is needed. -/
theorem integral_poleFreeKernelPolynomial6_mul_P7_oddResidual_eq_zero
    (o : ℝ → ℝ) (hoc : Continuous o)
    (hoLow : centeredLegendreMomentsVanishBelow o 9) (d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t *
        factorTwoCenteredCorrelationBilinear
          (d • factorTwoCenteredP7) o t) = 0 := by
  exact integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_zero
    (d • factorTwoCenteredP7) o
    (continuous_factorTwoCenteredP7.const_smul d) hoc hoLow (by norm_num)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
