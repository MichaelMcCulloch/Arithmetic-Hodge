import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares

noncomputable section

open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointTriangleInterchange
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaRenormalizedGeometricKernel

/-!
# Coupled hyperbolic rank squares

The symmetric even and odd phase ranks have opposite signs, while the
alternating channel supplies their mixed term.  The identities in this file
make that structure explicit before any estimate is applied.
-/

/-- A closed-disk phase acts contractively on the doubled-angle rank vector
`(C² - S², 2CS)`. -/
theorem abs_coupledRank_phase_le_sq_add_sq
    (a b C S : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    |a * (C ^ 2 - S ^ 2) + 2 * b * C * S| ≤ C ^ 2 + S ^ 2 := by
  have hphase : a ^ 2 + (-b) ^ 2 ≤ 1 := by
    simpa only [neg_sq] using hab
  have h := two_mul_abs_phase_pairing_le
    a (-b) C S C (-S) hphase
  have hrewrite :
      a * (C * C + -S * S) +
          -b * (-S * C - C * S) =
        a * (C ^ 2 - S ^ 2) + 2 * b * C * S := by ring
  rw [hrewrite] at h
  nlinarith

/-- Equivalently, adding the unphased rank energy leaves a nonnegative
quadratic for every phase in the closed unit disk. -/
theorem coupledRank_phase_nonneg
    (a b C S : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ C ^ 2 + S ^ 2 +
      (a * (C ^ 2 - S ^ 2) + 2 * b * C * S) := by
  have h := abs_coupledRank_phase_le_sq_add_sq a b C S hab
  nlinarith [neg_abs_le (a * (C ^ 2 - S ^ 2) + 2 * b * C * S)]

/-- A continuous lag weight transports an ordered endpoint cross-correlation
to the upper half of the centered square. -/
theorem integral_weight_mul_crossCorrelation_eq_upperTriangle
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ p : ℝ × ℝ in centeredUpperTriangle,
        q (p.1 - p.2) * u p.1 * v p.2 := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * u p.1 * v p.2
  let H : ℝ × ℝ → ℝ := fun p ↦ K (p.1 + p.2, p.2)
  have hTmeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hKcont : Continuous K := by
    dsimp only [K]
    fun_prop
  have hHcont : Continuous H := by
    dsimp only [H]
    exact hKcont.comp (by fun_prop)
  have hHRectangle : IntegrableOn H
      (Icc (0 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hHcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hTsubset : positiveDistanceTriangle ⊆
      Icc (0 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, by linarith [hp.2.2.2, hp.1]⟩⟩
  have hHTriangle : IntegrableOn H positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) :=
    hHRectangle.mono_set hTsubset
  have hHIndicator : Integrable
      (positiveDistanceTriangle.indicator H)
      ((volume : Measure ℝ).prod volume) :=
    hHTriangle.integrable_indicator hTmeas
  have hOuter :
      (∫ t : ℝ in 0..2,
          q t * factorTwoCenteredCrossCorrelation u v t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold factorTwoCenteredCrossCorrelation
    change q t * (∫ x : ℝ in -1..1 - t, u (t + x) * v x) =
      ∫ x : ℝ in -1..1 - t,
        q ((t + x) - x) * u (t + x) * v x
    rw [show (fun x : ℝ ↦
        q ((t + x) - x) * u (t + x) * v x) =
      fun x ↦ q t * (u (t + x) * v x) by
        funext x
        rw [show t + x - x = t by ring]
        ring,
      intervalIntegral.integral_const_mul]
  have hTriangleFold :
      (∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x)) =
        ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := by
    rw [← integral_indicator hTmeas,
      Measure.volume_eq_prod ℝ ℝ,
      integral_prod _ hHIndicator]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      calc
        (∫ x : ℝ in -1..1 - t, H (t, x)) =
            ∫ x : ℝ,
              (Icc (-1 : ℝ) (1 - t)).indicator (fun x ↦ H (t, x)) x := by
          rw [intervalIntegral.integral_of_le (by linarith [ht.2]),
            ← integral_Icc_eq_integral_Ioc,
            ← integral_indicator measurableSet_Icc]
        _ = ∫ x : ℝ,
            positiveDistanceTriangle.indicator H (t, x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
          · have hp : (t, x) ∈ positiveDistanceTriangle :=
                ⟨ht.1.le, ht.2, hx.1, hx.2⟩
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp]
          · have hp : (t, x) ∉ positiveDistanceTriangle := by
              intro hp
              exact hx ⟨hp.2.2.1, hp.2.2.2⟩
            rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hp]
    · rw [Set.indicator_of_notMem ht]
      have hrow : (fun x : ℝ ↦
          positiveDistanceTriangle.indicator H (t, x)) = 0 := by
        funext x
        by_cases hp : (t, x) ∈ positiveDistanceTriangle
        · exfalso
          apply ht
          exact ⟨lt_of_le_of_ne hp.1 (Ne.symm ht0), hp.2.1⟩
        · rw [Set.indicator_of_notMem hp]
          rfl
      rw [hrow]
      simp
  calc
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := hOuter
    _ = ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := hTriangleFold
    _ = ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
      simpa only [H] using setIntegral_positiveDistanceTriangle_shear K
    _ = ∫ p : ℝ × ℝ in centeredUpperTriangle,
        q (p.1 - p.2) * u p.1 * v p.2 := by rfl

/-- On an even--odd pair, the full-square hyperbolic cross difference is
exactly twice the product of the corresponding even and odd Laplace moments.
This is the bilinear identity behind the coupled rank squares. -/
theorem integral_integral_sinh_crossDifference_of_even_odd
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) (lambda : ℝ) :
    (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
      Real.sinh (lambda * (y - x)) *
        (o y * e x - e y * o x)) =
      2 * centeredCoshMoment e lambda * centeredSinhMoment o lambda := by
  let Ce : ℝ := centeredCoshMoment e lambda
  let Se : ℝ := centeredSinhMoment e lambda
  let Co : ℝ := centeredCoshMoment o lambda
  let So : ℝ := centeredSinhMoment o lambda
  have hSe : Se = 0 := by
    simpa only [Se] using centeredSinhMoment_eq_zero_of_even heven lambda
  have hCo : Co = 0 := by
    simpa only [Co] using centeredCoshMoment_eq_zero_of_odd hodd lambda
  have hinner (y : ℝ) :
      (∫ x : ℝ in -1..1,
        Real.sinh (lambda * (y - x)) *
          (o y * e x - e y * o x)) =
        (Real.sinh (lambda * y) * o y) * Ce -
          (Real.sinh (lambda * y) * e y) * Co -
          (Real.cosh (lambda * y) * o y) * Se +
          (Real.cosh (lambda * y) * e y) * So := by
    rw [show (fun x : ℝ ↦
        Real.sinh (lambda * (y - x)) *
          (o y * e x - e y * o x)) = fun x ↦
        (Real.sinh (lambda * y) * o y) *
            (Real.cosh (lambda * x) * e x) -
          (Real.sinh (lambda * y) * e y) *
            (Real.cosh (lambda * x) * o x) -
          (Real.cosh (lambda * y) * o y) *
            (Real.sinh (lambda * x) * e x) +
          (Real.cosh (lambda * y) * e y) *
            (Real.sinh (lambda * x) * o x) by
      funext x
      rw [show lambda * (y - x) = lambda * y - lambda * x by ring,
        Real.sinh_sub]
      ring]
    rw [intervalIntegral.integral_add,
      intervalIntegral.integral_sub,
      intervalIntegral.integral_sub]
    all_goals try
      apply Continuous.intervalIntegrable
      fun_prop
    repeat rw [intervalIntegral.integral_const_mul]
    rfl
  rw [show (fun y : ℝ ↦ ∫ x : ℝ in -1..1,
      Real.sinh (lambda * (y - x)) *
        (o y * e x - e y * o x)) = fun y ↦
      (Real.sinh (lambda * y) * o y) * Ce -
        (Real.sinh (lambda * y) * e y) * Co -
        (Real.cosh (lambda * y) * o y) * Se +
        (Real.cosh (lambda * y) * e y) * So by
    funext y
    exact hinner y]
  rw [hSe, hCo]
  simp only [mul_zero, sub_zero]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const]
    change So * Ce + Ce * So = 2 * Ce * So
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- The one-sided alternating hyperbolic rank is the product of the even
cosh moment and the odd sinh moment. -/
theorem integral_sinh_mul_crossDifference_of_even_odd
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) (lambda : ℝ) :
    (∫ t : ℝ in 0..2,
      Real.sinh (lambda * t) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
      centeredCoshMoment e lambda * centeredSinhMoment o lambda := by
  let q : ℝ → ℝ := fun t ↦ Real.sinh (lambda * t)
  let K : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * (o p.1 * e p.2 - e p.1 * o p.2)
  let Koe : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * o p.1 * e p.2
  let Keo : ℝ × ℝ → ℝ := fun p ↦
    q (p.1 - p.2) * e p.1 * o p.2
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hK : Continuous K := by
    dsimp only [K]
    fun_prop
  have hKswap : ∀ p : ℝ × ℝ, K p.swap = K p := by
    intro p
    rcases p with ⟨y, x⟩
    dsimp only [K, q, Prod.swap_prod_mk]
    rw [show lambda * (x - y) = -(lambda * (y - x)) by ring,
      Real.sinh_neg]
    ring
  have hUpperOe := integral_weight_mul_crossCorrelation_eq_upperTriangle
    o e hoc hec q hq
  have hUpperEo := integral_weight_mul_crossCorrelation_eq_upperTriangle
    e o hec hoc q hq
  have hOeInt : IntervalIntegrable
      (fun t : ℝ ↦
        q t * factorTwoCenteredCrossCorrelation o e t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation o e hoc hec))
      |>.intervalIntegrable 0 2
  have hEoInt : IntervalIntegrable
      (fun t : ℝ ↦
        q t * factorTwoCenteredCrossCorrelation e o t) volume 0 2 :=
    (hq.mul (continuous_factorTwoCenteredCrossCorrelation e o hec hoc))
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
  have hKoe : IntegrableOn Koe centeredUpperTriangle := by
    have hcont : Continuous Koe := by
      dsimp only [Koe]
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hKeo : IntegrableOn Keo centeredUpperTriangle := by
    have hcont : Continuous Keo := by
      dsimp only [Keo]
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hUsub
  have hUpper :
      (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
    rw [show (fun t : ℝ ↦
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) = fun t ↦
        q t * factorTwoCenteredCrossCorrelation o e t -
          q t * factorTwoCenteredCrossCorrelation e o t by
      funext t
      ring,
      intervalIntegral.integral_sub hOeInt hEoInt,
      hUpperOe, hUpperEo,
      ← MeasureTheory.integral_sub hKoe hKeo]
    apply setIntegral_congr_fun hUmeas
    intro p _hp
    dsimp only [K, Koe, Keo]
    ring
  have hSquare :=
    two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare K hK hKswap
  have hIterated := setIntegral_centeredSquare_eq_iterated K hK
  have hFull := integral_integral_sinh_crossDifference_of_even_odd
    e o hec hoc heven hodd lambda
  change (∫ t : ℝ in 0..2,
      q t * (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t)) = _
  rw [hUpper]
  dsimp only [K, q] at hIterated
  rw [hIterated, hFull] at hSquare
  nlinarith

/-- The finite antisymmetric hyperbolic-rank weight on a coupled profile.
Its signs are opposite to the decaying signs in the symmetric weight. -/
def factorTwoCoupledAlternatingRankPartialWeight (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp yoshidaEndpointA *
      Real.sinh (yoshidaEndpointA * t / 2) +
    ∑ m ∈ Finset.range N,
      2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.sinh
          (yoshidaEndpointA * oddRate (m + 1) * t)

/-- The alternating quadratic attached to the finite antisymmetric rank
weight. -/
def factorTwoCenteredAlternatingRankPartialSum
    (e o : ℝ → ℝ) (N : ℕ) : ℝ :=
  yoshidaEndpointA *
    ∫ t : ℝ in 0..2,
      factorTwoCoupledAlternatingRankPartialWeight N t *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)

/-- Exact finite-rank product expansion of the alternating channel. -/
theorem factorTwoCenteredAlternatingRankPartialSum_eq_products
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) (N : ℕ) :
    factorTwoCenteredAlternatingRankPartialSum e o N =
      yoshidaEndpointA *
        (2 * Real.exp yoshidaEndpointA *
            centeredCoshMoment e (yoshidaEndpointA / 2) *
              centeredSinhMoment o (yoshidaEndpointA / 2) +
          ∑ m ∈ Finset.range N,
            2 * Real.exp
                (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1))) := by
  let D : ℝ → ℝ := fun t ↦
    factorTwoCenteredCrossCorrelation o e t -
      factorTwoCenteredCrossCorrelation e o t
  have hD : Continuous D :=
    (continuous_factorTwoCenteredCrossCorrelation o e hoc hec).sub
      (continuous_factorTwoCenteredCrossCorrelation e o hec hoc)
  have hhead := integral_sinh_mul_crossDifference_of_even_odd
    e o hec hoc heven hodd (yoshidaEndpointA / 2)
  have htail (m : ℕ) := integral_sinh_mul_crossDifference_of_even_odd
    e o hec hoc heven hodd
      (yoshidaEndpointA * oddRate (m + 1))
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) * D t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt (m : ℕ) : IntervalIntegrable
      (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) * D t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailSumInt : IntervalIntegrable
      (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) * D t)
      volume 0 2 := by
    rw [show (fun t : ℝ ↦
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) * D t) =
      ∑ m ∈ Finset.range N, fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) * D t by
      funext t
      simp only [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.range N)
      (fun m _hm ↦ htailInt m)
  have hheadScaled :
      (∫ t : ℝ in 0..2,
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) * D t) =
        2 * Real.exp yoshidaEndpointA *
          centeredCoshMoment e (yoshidaEndpointA / 2) *
            centeredSinhMoment o (yoshidaEndpointA / 2) := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) * D t) =
      fun t ↦ (2 * Real.exp yoshidaEndpointA) *
        (Real.sinh ((yoshidaEndpointA / 2) * t) * D t) by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
    rw [show (∫ t : ℝ in 0..2,
        Real.sinh ((yoshidaEndpointA / 2) * t) * D t) =
      centeredCoshMoment e (yoshidaEndpointA / 2) *
        centeredSinhMoment o (yoshidaEndpointA / 2) by
      simpa only [D] using hhead]
    ring
  have htailScaled (m : ℕ) :
      (∫ t : ℝ in 0..2,
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) * D t) =
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) := by
    rw [show (fun t : ℝ ↦
        2 * Real.exp
            (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.sinh
            (yoshidaEndpointA * oddRate (m + 1) * t) * D t) =
      fun t ↦
        (2 * Real.exp
          (-2 * yoshidaEndpointA * oddRate (m + 1))) *
        (Real.sinh
          ((yoshidaEndpointA * oddRate (m + 1)) * t) * D t) by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
    rw [show (∫ t : ℝ in 0..2,
        Real.sinh
          ((yoshidaEndpointA * oddRate (m + 1)) * t) * D t) =
      centeredCoshMoment e
          (yoshidaEndpointA * oddRate (m + 1)) *
        centeredSinhMoment o
          (yoshidaEndpointA * oddRate (m + 1)) by
      simpa only [D] using htail m]
    ring
  unfold factorTwoCenteredAlternatingRankPartialSum
    factorTwoCoupledAlternatingRankPartialWeight
  rw [show (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) +
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t)) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) = fun t ↦
      2 * Real.exp yoshidaEndpointA *
          Real.sinh (yoshidaEndpointA * t / 2) * D t +
        ∑ m ∈ Finset.range N,
          2 * Real.exp
              (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.sinh
              (yoshidaEndpointA * oddRate (m + 1) * t) * D t by
      funext t
      dsimp only [D]
      rw [add_mul, Finset.sum_mul],
    intervalIntegral.integral_add hheadInt htailSumInt,
    intervalIntegral.integral_finset_sum (fun m _hm ↦ htailInt m),
    hheadScaled]
  simp_rw [htailScaled]

/-! ## Coupled finite-rank phase contraction -/

/-- A nonnegative weighted family of coupled ranks stays nonnegative after
the growing rank is phased by `(a,b)` and every decaying rank by `(-a,b)`.
This is the finite-dimensional numerical-radius argument, with no choice of
basis and no enumeration of phase values. -/
theorem coupledRank_weighted_sum_nonneg
    {ι : Type*} (s : Finset ι) (a b C₀ S₀ r₀ : ℝ)
    (C S r : ι → ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hr₀ : 0 ≤ r₀) (hr : ∀ i ∈ s, 0 ≤ r i) :
    0 ≤
      r₀ * (C₀ ^ 2 + S₀ ^ 2 +
        (a * (C₀ ^ 2 - S₀ ^ 2) + 2 * b * C₀ * S₀)) +
      ∑ i ∈ s,
        r i * (C i ^ 2 + S i ^ 2 +
          ((-a) * (C i ^ 2 - S i ^ 2) +
            2 * b * C i * S i)) := by
  apply add_nonneg
  · exact mul_nonneg hr₀ (coupledRank_phase_nonneg a b C₀ S₀ hab)
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hr i hi)
      (coupledRank_phase_nonneg (-a) b (C i) (S i) (by
        simpa only [neg_sq] using hab))

/-- Distribute a common phase across a finite decaying rank family.  Keeping
this as a separate algebraic identity lets the analytic proof reason one rank
at a time while the exact archimedean formulas retain their three natural
moment sums. -/
theorem coupledRank_tail_phase_sum_expand
    {ι : Type*} (s : Finset ι) (a b : ℝ)
    (r C S : ι → ℝ) :
    (∑ i ∈ s,
        r i * ((-a) * (C i ^ 2 - S i ^ 2) +
          2 * b * C i * S i)) =
      (-a) * (∑ i ∈ s, r i * C i ^ 2) +
        a * (∑ i ∈ s, r i * S i ^ 2) +
        b * (∑ i ∈ s, 2 * r i * C i * S i) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The positive rank energy against which the complete finite phase family
is contractive. -/
def factorTwoCoupledRankEnergyPartialSum
    (e o : ℝ → ℝ) (N : ℕ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
          centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2) +
      ∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2 +
            centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2))

/-- Exact finite-rank expansion of the symmetric-plus-alternating phase
coordinate.  The sign change on `a` between the head and tail is the entire
reason the coupled rank lemma applies to both families at once. -/
theorem factorTwoCoupledRankPhasePartialSum_eq
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (N : ℕ) (a b : ℝ) :
    a * (factorTwoCenteredArchRankPartialSum e N +
          factorTwoCenteredArchRankPartialSum o N) +
        b * factorTwoCenteredAlternatingRankPartialSum e o N =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            (a * (centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 -
                centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2) +
              2 * b * centeredCoshMoment e (yoshidaEndpointA / 2) *
                centeredSinhMoment o (yoshidaEndpointA / 2)) +
          ∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              ((-a) *
                  (centeredCoshMoment e
                        (yoshidaEndpointA * oddRate (m + 1)) ^ 2 -
                    centeredSinhMoment o
                        (yoshidaEndpointA * oddRate (m + 1)) ^ 2) +
                2 * b *
                  centeredCoshMoment e
                    (yoshidaEndpointA * oddRate (m + 1)) *
                  centeredSinhMoment o
                    (yoshidaEndpointA * oddRate (m + 1)))) := by
  rw [factorTwoCenteredArchRankPartialSum_eq_evenSquares e hec heven N,
    factorTwoCenteredArchRankPartialSum_eq_oddSquares o hoc hodd N,
    factorTwoCenteredAlternatingRankPartialSum_eq_products
      e o hec hoc heven hodd N]
  rw [coupledRank_tail_phase_sum_expand (Finset.range N) a b
    (fun m ↦ Real.exp
      (-2 * yoshidaEndpointA * oddRate (m + 1)))
    (fun m ↦ centeredCoshMoment e
      (yoshidaEndpointA * oddRate (m + 1)))
    (fun m ↦ centeredSinhMoment o
      (yoshidaEndpointA * oddRate (m + 1)))]
  ring

/-- Every finite coupled hyperbolic-rank phase is bounded below by the
negative of its positive rank energy, uniformly over the closed phase disk. -/
theorem factorTwoCoupledRankEnergy_add_phase_nonneg
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (N : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoCoupledRankEnergyPartialSum e o N +
      (a * (factorTwoCenteredArchRankPartialSum e N +
          factorTwoCenteredArchRankPartialSum o N) +
        b * factorTwoCenteredAlternatingRankPartialSum e o N) := by
  rw [factorTwoCoupledRankPhasePartialSum_eq
    e o hec hoc heven hodd N a b]
  unfold factorTwoCoupledRankEnergyPartialSum
  have hRanks := coupledRank_weighted_sum_nonneg
    (Finset.range N) a b
    (centeredCoshMoment e (yoshidaEndpointA / 2))
    (centeredSinhMoment o (yoshidaEndpointA / 2))
    (Real.exp yoshidaEndpointA)
    (fun m ↦ centeredCoshMoment e
      (yoshidaEndpointA * oddRate (m + 1)))
    (fun m ↦ centeredSinhMoment o
      (yoshidaEndpointA * oddRate (m + 1)))
    (fun m ↦ Real.exp
      (-2 * yoshidaEndpointA * oddRate (m + 1)))
    hab (by positivity) (by
      intro m hm
      positivity)
  have hA : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  apply mul_nonneg hA at hRanks
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib] at hRanks ⊢
  ring_nf at hRanks ⊢
  exact hRanks

/-- Absolute numerical-radius form of the finite coupled-rank contraction. -/
theorem abs_factorTwoCoupledRankPhasePartialSum_le_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (N : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    |a * (factorTwoCenteredArchRankPartialSum e N +
          factorTwoCenteredArchRankPartialSum o N) +
        b * factorTwoCenteredAlternatingRankPartialSum e o N| ≤
      factorTwoCoupledRankEnergyPartialSum e o N := by
  have hplus := factorTwoCoupledRankEnergy_add_phase_nonneg
    e o hec hoc heven hodd N a b hab
  have hminus := factorTwoCoupledRankEnergy_add_phase_nonneg
    e o hec hoc heven hodd N (-a) (-b) (by
      simpa only [neg_sq] using hab)
  rw [abs_le]
  constructor <;> nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankSquares
