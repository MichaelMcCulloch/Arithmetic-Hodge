import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOperatorContraction

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseTailCoercivity

/-!
# Complex operator form of the factor-two phase channel

The real symmetric and alternating overlap channels are the real and
imaginary parts of one complex autocorrelation of `u + i v`.  This packages
the phase disk as multiplication by a scalar contraction, without separating
the two channel estimates.
-/

/-- The complex profile whose real and imaginary coordinates are the two
real endpoint profiles. -/
def factorTwoComplexProfile (u v : ℝ → ℝ) (x : ℝ) : ℂ :=
  (u x : ℂ) + Complex.I * (v x : ℂ)

/-- The ordered complex autocorrelation on the centered endpoint interval. -/
def factorTwoComplexOverlap
    (u v : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ in -1..1 - t,
    starRingEnd ℂ (factorTwoComplexProfile u v x) *
      factorTwoComplexProfile u v (t + x)

/-- Exact complexification of the dot and oriented-area overlap channels. -/
theorem factorTwoComplexOverlap_eq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (t : ℝ) :
    factorTwoComplexOverlap u v t =
      ((centeredEndpointCorrelation u t +
          centeredEndpointCorrelation v t : ℝ) : ℂ) +
        Complex.I *
          ((factorTwoCenteredCrossCorrelation v u t -
              factorTwoCenteredCrossCorrelation u v t : ℝ) : ℂ) := by
  have huu : IntervalIntegrable
      (fun x : ℝ ↦ u (t + x) * u x) volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have hvv : IntervalIntegrable
      (fun x : ℝ ↦ v (t + x) * v x) volume (-1) (1 - t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hvu : IntervalIntegrable
      (fun x : ℝ ↦ v (t + x) * u x) volume (-1) (1 - t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have huv : IntervalIntegrable
      (fun x : ℝ ↦ u (t + x) * v x) volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hreal : IntervalIntegrable
      (fun x : ℝ ↦
        ((u (t + x) * u x + v (t + x) * v x : ℝ) : ℂ))
      volume (-1) (1 - t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have himag : IntervalIntegrable
      (fun x : ℝ ↦
        Complex.I *
          ((v (t + x) * u x - u (t + x) * v x : ℝ) : ℂ))
      volume (-1) (1 - t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have himagIntegral :
      (∫ x : ℝ in -1..1 - t,
        Complex.I *
          ((v (t + x) * u x - u (t + x) * v x : ℝ) : ℂ)) =
        Complex.I *
          (∫ x : ℝ in -1..1 - t,
            ((v (t + x) * u x - u (t + x) * v x : ℝ) : ℂ)) := by
    exact intervalIntegral.integral_const_mul Complex.I _
  unfold factorTwoComplexOverlap factorTwoComplexProfile
  rw [show (fun x : ℝ ↦
      starRingEnd ℂ ((u x : ℂ) + Complex.I * (v x : ℂ)) *
        ((u (t + x) : ℂ) + Complex.I * (v (t + x) : ℂ))) =
      fun x ↦
        ((u (t + x) * u x + v (t + x) * v x : ℝ) : ℂ) +
          Complex.I *
            ((v (t + x) * u x - u (t + x) * v x : ℝ) : ℂ) by
    funext x
    apply Complex.ext <;>
      norm_num [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal] <;>
      ring]
  rw [intervalIntegral.integral_add
      hreal himag,
    intervalIntegral.integral_ofReal,
    himagIntegral,
    intervalIntegral.integral_ofReal,
    intervalIntegral.integral_add huu hvv,
    intervalIntegral.integral_sub hvu huv]
  unfold centeredEndpointCorrelation factorTwoCenteredCrossCorrelation
  ring

/-- A phase direction is literally the numerical-range pairing of the
complex overlap with the scalar `a - i b`. -/
theorem factorTwoCenteredPhaseCorrelation_eq_re_mul_complexOverlap
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b t : ℝ) :
    factorTwoCenteredPhaseCorrelation u v a b t =
      (((a : ℂ) - Complex.I * (b : ℂ)) *
        factorTwoComplexOverlap u v t).re := by
  rw [factorTwoComplexOverlap_eq u v hu hv t]
  unfold factorTwoCenteredPhaseCorrelation
  norm_num

/-- The complex phase multiplier has exactly the Euclidean disk norm. -/
@[simp] theorem normSq_phaseMultiplier (a b : ℝ) :
    Complex.normSq ((a : ℂ) - Complex.I * (b : ℂ)) =
      a ^ 2 + b ^ 2 := by
  norm_num [Complex.normSq_apply]
  ring

/-- The overlap operator is a contraction from the two endpoint pieces into
the complex scalar field.  This is the sharp norm form of the real
two-vector estimate: choosing the phase in the direction of the complex
overlap loses no constant. -/
theorem two_mul_norm_complexOverlap_two_sub_le_boundaryTail
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    {r : ℝ} (hr0 : 0 ≤ r) :
    2 * ‖factorTwoComplexOverlap u v (2 - r)‖ ≤
      centeredEndpointBoundaryTail u r +
        centeredEndpointBoundaryTail v r := by
  let C : ℂ := factorTwoComplexOverlap u v (2 - r)
  let R : ℝ := centeredEndpointCorrelation u (2 - r) +
    centeredEndpointCorrelation v (2 - r)
  let D : ℝ := factorTwoCenteredCrossCorrelation v u (2 - r) -
    factorTwoCenteredCrossCorrelation u v (2 - r)
  let N : ℝ := ‖C‖
  have hC : C = (R : ℂ) + Complex.I * (D : ℂ) := by
    simpa only [C, R, D] using
      factorTwoComplexOverlap_eq u v hu hv (2 - r)
  have hN0 : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hN2 : N ^ 2 = R ^ 2 + D ^ 2 := by
    dsimp only [N]
    rw [Complex.sq_norm, hC]
    norm_num [Complex.normSq_apply]
    ring
  have hboundary0 :
      0 ≤ centeredEndpointBoundaryTail u r +
        centeredEndpointBoundaryTail v r := by
    have hzero := two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
      u v hu hv 0 0 (by norm_num) hr0
    simp [factorTwoCenteredPhaseCorrelation] at hzero
    exact hzero
  by_cases hNzero : N = 0
  · dsimp only [N] at hNzero ⊢
    rw [hNzero]
    norm_num
    exact hboundary0
  · let a : ℝ := R / N
    let b : ℝ := D / N
    have hab : a ^ 2 + b ^ 2 ≤ 1 := by
      have hN2ne : N ^ 2 ≠ 0 := pow_ne_zero 2 hNzero
      dsimp only [a, b]
      rw [div_pow, div_pow, ← add_div, ← hN2,
        div_self hN2ne]
    have hphase :
        factorTwoCenteredPhaseCorrelation u v a b (2 - r) = N := by
      unfold factorTwoCenteredPhaseCorrelation
      dsimp only [a, b, R, D]
      field_simp [hNzero]
      nlinarith
    have hcontract := two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
      u v hu hv a b hab hr0
    rw [hphase, abs_of_nonneg hN0] at hcontract
    simpa only [C, N] using hcontract

/-- The nonsingular forward/reflected pair acts on the complex overlap by
one scalar multiplier.  Its real and imaginary coefficients are respectively
the sum and difference of the two real kernel branches. -/
def factorTwoRegularPhaseMultiplier (a b t : ℝ) : ℂ :=
  (a * (yoshidaEndpointA *
      (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
        factorTwoCenteredReflectedRegularKernel t)) : ℝ) -
    Complex.I *
      (b * (yoshidaEndpointA *
        (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) -
          factorTwoCenteredReflectedRegularKernel t)) : ℝ)

/-- Exact whole-kernel operator factorization of the two regular branches.
In particular, the alternating channel is governed by the branch difference,
not by the sum of their absolute values. -/
theorem regular_phaseKernel_eq_re_multiplier_mul_overlap
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) {t : ℝ} (ht2 : t < 2) :
    yoshidaEndpointA *
          factorTwoCenteredForwardPhaseKernel u v a b t +
        factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t =
      (factorTwoRegularPhaseMultiplier a b t *
        factorTwoComplexOverlap u v t).re := by
  have hreflected :=
    factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
      u v a b ht2
  rw [hreflected]
  unfold factorTwoCenteredForwardPhaseKernel
  rw [factorTwoCenteredPhaseCorrelation_eq_re_mul_complexOverlap
      u v hu hv a b t,
    factorTwoCenteredPhaseCorrelation_eq_re_mul_complexOverlap
      u v hu hv a (-b) t]
  unfold factorTwoRegularPhaseMultiplier
  norm_num
  ring

/-- The exact squared operator norm of the regular phase multiplier. -/
@[simp] theorem normSq_factorTwoRegularPhaseMultiplier
    (a b t : ℝ) :
    Complex.normSq (factorTwoRegularPhaseMultiplier a b t) =
      (a * (yoshidaEndpointA *
        (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
          factorTwoCenteredReflectedRegularKernel t))) ^ 2 +
      (b * (yoshidaEndpointA *
        (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) -
          factorTwoCenteredReflectedRegularKernel t))) ^ 2 := by
  unfold factorTwoRegularPhaseMultiplier
  norm_num [Complex.normSq_apply]
  ring

/-- The whole nonsingular kernel multiplier has norm at most `11/8` on the
closed phase disk. -/
theorem normSq_factorTwoRegularPhaseMultiplier_le
    {a b t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    Complex.normSq (factorTwoRegularPhaseMultiplier a b t) ≤
      (11 / 8 : ℝ) ^ 2 := by
  rw [normSq_factorTwoRegularPhaseMultiplier]
  exact factorTwo_regular_phase_coefficient_radius ht0 ht2 hab

/-- Exact value of the forward adjacent branch at the leftmost regular
argument.  This is the structural normalization needed to test whether the
regular multiplier could possibly be a unit contraction. -/
theorem factorTwoAdjacentSmoothKernel_log_two_eq :
    factorTwoAdjacentSmoothKernel (Real.log 2) =
      5 * Real.sqrt 2 / 6 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hexpHalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.exp_log hsqrtPos
  have hexpPos : Real.exp (Real.log 2) = 2 :=
    Real.exp_log (by norm_num)
  have hexpNeg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, hexpPos]
    norm_num
  have hexpNegHalf : Real.exp (-(Real.log 2 / 2)) =
      (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, hexpHalf]
  unfold factorTwoAdjacentSmoothKernel
    YoshidaRenormalizedGeometricKernel.oddKernel
  rw [Real.cosh_eq, hexpHalf, hexpNegHalf, hexpPos, hexpNeg]
  field_simp [hsqrtPos.ne']
  nlinarith

/-- The symmetric regular multiplier is strictly expansive at every overlap
distance.  Thus the complete phase proof cannot come from a pointwise unit
contraction of the regular branches alone; it must retain cancellation with
the clean diagonal, mass, hyperbolic, and prime terms. -/
theorem one_lt_factorTwo_regular_symmetric_multiplier
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    1 < yoshidaEndpointA *
      (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
        factorTwoCenteredReflectedRegularKernel t) := by
  let F : ℝ := factorTwoAdjacentSmoothKernel
    (yoshidaEndpointA * (2 + t))
  let R : ℝ := factorTwoCenteredReflectedRegularKernel t
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hzLower : Real.log 2 ≤ yoshidaEndpointA * (2 + t) := by
    unfold yoshidaEndpointA
    nlinarith
  have hF : 5 * Real.sqrt 2 / 6 ≤ F := by
    dsimp only [F]
    rw [← factorTwoAdjacentSmoothKernel_log_two_eq]
    exact factorTwoAdjacentSmoothKernel_mono_of_pos hlogPos hzLower
  have hbounds := factorTwo_regular_phase_scalar_bounds ht0 ht2
  change (1 : ℝ) ≤ F ∧ F ≤ 2 ∧
      (7 / 4 : ℝ) ≤ R ∧ R ≤ (61 / 32 : ℝ) ∧
      yoshidaEndpointA * (F + R) ≤ (11 / 8 : ℝ) ∧
      yoshidaEndpointA * |F - R| ≤ (203 / 640 : ℝ) at hbounds
  have hR : (7 / 4 : ℝ) ≤ R := hbounds.2.2.1
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hsum : (35 / 12 : ℝ) < F + R := by
    nlinarith
  have hlogLower : (693 / 1000 : ℝ) < Real.log 2 :=
    (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hA : (693 / 2000 : ℝ) < yoshidaEndpointA := by
    unfold yoshidaEndpointA
    linarith
  have hfirst :
      (693 / 2000 : ℝ) * (35 / 12 : ℝ) <
        yoshidaEndpointA * (35 / 12 : ℝ) :=
    mul_lt_mul_of_pos_right hA (by norm_num)
  have hsecond :
      yoshidaEndpointA * (35 / 12 : ℝ) <
        yoshidaEndpointA * (F + R) :=
    mul_lt_mul_of_pos_left hsum yoshidaEndpointA_pos
  change 1 < yoshidaEndpointA * (F + R)
  calc
    (1 : ℝ) < (693 / 2000 : ℝ) * (35 / 12 : ℝ) := by
      norm_num
    _ < yoshidaEndpointA * (35 / 12 : ℝ) := hfirst
    _ < yoshidaEndpointA * (F + R) := hsecond

/-- In operator-norm language, the preceding obstruction says that the
regular multiplier already has squared norm greater than one in the purely
symmetric phase direction. -/
theorem one_lt_normSq_factorTwoRegularPhaseMultiplier_symmetric
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    1 < Complex.normSq (factorTwoRegularPhaseMultiplier 1 0 t) := by
  rw [normSq_factorTwoRegularPhaseMultiplier]
  simp only [one_mul, zero_mul]
  have h := one_lt_factorTwo_regular_symmetric_multiplier ht0 ht2
  nlinarith [sq_nonneg
    (yoshidaEndpointA *
      (factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) +
        factorTwoCenteredReflectedRegularKernel t) - 1)]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOperatorContraction
