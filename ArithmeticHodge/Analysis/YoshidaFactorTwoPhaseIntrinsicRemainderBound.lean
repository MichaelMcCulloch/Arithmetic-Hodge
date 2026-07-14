import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.YoshidaRegularKernelSharpMeanZeroSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRemainderBound

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

noncomputable section

/-!
# Structural bound for the intrinsic signed remainder

The reflected pole has already been absorbed by the exact square in
`YoshidaFactorTwoPhaseIntrinsicResidual`.  Here the two remaining regular
branches are kept as one phase operator, while the mean-zero regular
quadratics and the parity-sensitive hyperbolic terms use their structural
operator bounds.  No finite spectral cutoff is introduced.
-/

/-- The complete nonsingular forward/reflected phase block. -/
def factorTwoIntrinsicRegularPhaseBlock
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoCenteredForwardPhaseKernel u v a b t) +
    ∫ t : ℝ in 0..2,
      factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t

/-- The even energy coefficient produced by the presently available
operator-norm estimates for the signed remainder. -/
def factorTwoIntrinsicEvenRemainderLoss (a : ℝ) : ℝ :=
  11 / 8 +
    (Real.log 2 / Real.sqrt 2) * |a| +
    (Real.log 3 / Real.sqrt 3) / 2 +
    yoshidaEndpointScalarMassLoss + Real.log 2 / 64

/-- The odd coefficient has the additional possible negative hyperbolic
rank-one loss. -/
def factorTwoIntrinsicOddRemainderLoss (a : ℝ) : ℝ :=
  factorTwoIntrinsicEvenRemainderLoss a +
    (1 / Real.sqrt 2 - Real.log 2)

/-- Gap between the available even remainder norm and the protected raw
spectral coefficient. -/
def factorTwoIntrinsicEvenRemainderGap (a : ℝ) : ℝ :=
  factorTwoIntrinsicEvenRemainderLoss a -
    (25 / 12 - Real.log 2 / 2)

/-- Odd counterpart of the norm gap. -/
def factorTwoIntrinsicOddRemainderGap (a : ℝ) : ℝ :=
  factorTwoIntrinsicOddRemainderLoss a -
    (137 / 60 - Real.log 2 / 2)

/-- Boundary tails vary continuously with their overlap length. -/
theorem continuous_centeredEndpointBoundaryTail
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (centeredEndpointBoundaryTail w) := by
  let q : ℝ → ℝ := fun x ↦ w x ^ 2
  let L : ℝ → ℝ := fun t ↦ ∫ x : ℝ in -1..-1 + t, q x
  have hq : Continuous q := hw.pow 2
  have hL : Continuous L := by
    dsimp only [L]
    exact (intervalIntegral.differentiable_integral_of_continuous
      (a := (-1 : ℝ)) hq).continuous.comp
        (continuous_const.add continuous_id)
  have hpoint (t : ℝ) :
      centeredEndpointBoundaryTail w t =
        (∫ x : ℝ in -1..1, q x) - L (2 - t) + L t := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      (hq.intervalIntegrable (-1) (1 - t))
      (hq.intervalIntegrable (1 - t) 1)
    unfold centeredEndpointBoundaryTail
    dsimp only [L, q]
    rw [show -1 + (2 - t) = 1 - t by ring]
    linarith
  rw [show centeredEndpointBoundaryTail w = fun t ↦
      (∫ x : ℝ in -1..1, q x) - L (2 - t) + L t by
    funext t
    exact hpoint t]
  fun_prop

theorem intervalIntegrable_centeredEndpointBoundaryTail
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable (centeredEndpointBoundaryTail w) volume 0 2 :=
  (continuous_centeredEndpointBoundaryTail w hw).intervalIntegrable 0 2

/-- The whole nonsingular phase block costs at most `11/8` of the sum of
the two endpoint energies.  The two kernel branches are recombined before
the phase-disk estimate. -/
theorem abs_factorTwoIntrinsicRegularPhaseBlock_le
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    |factorTwoIntrinsicRegularPhaseBlock u v a b| ≤
      (11 / 8 : ℝ) *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
  let G : ℝ → ℝ := fun t ↦
    yoshidaEndpointA *
        factorTwoCenteredForwardPhaseKernel u v a b t +
      factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t
  let B : ℝ → ℝ := fun t ↦
    (11 / 16 : ℝ) *
      (centeredEndpointBoundaryTail u (2 - t) +
        centeredEndpointBoundaryTail v (2 - t))
  have hforward := intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    u v hu hv a b
  have hreflected :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      u v hu hv a b
  have hG : IntervalIntegrable G volume 0 2 := by
    dsimp only [G]
    exact (hforward.const_mul yoshidaEndpointA).add hreflected
  have huTail := intervalIntegrable_centeredEndpointBoundaryTail u hu
  have hvTail := intervalIntegrable_centeredEndpointBoundaryTail v hv
  have huReflect : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointBoundaryTail u (2 - t)) volume 0 2 := by
    convert (huTail.comp_sub_left 2).symm using 1 <;> norm_num
  have hvReflect : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointBoundaryTail v (2 - t)) volume 0 2 := by
    convert (hvTail.comp_sub_left 2).symm using 1 <;> norm_num
  have hB : IntervalIntegrable B volume 0 2 := by
    dsimp only [B]
    exact (huReflect.add hvReflect).const_mul (11 / 16 : ℝ)
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) 2, |G t| ≤ B t := by
    intro t ht
    have h := two_mul_abs_regular_phaseKernel_le_boundaryTail
      u v hu hv a b hab ht.1.le ht.2
    dsimp only [G, B]
    nlinarith
  have hintegral :
      (∫ t : ℝ in 0..2, |G t|) ≤ ∫ t : ℝ in 0..2, B t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hG.abs hB
    exact hpoint
  have habsIntegral :
      |∫ t : ℝ in 0..2, G t| ≤ ∫ t : ℝ in 0..2, |G t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have huReflectIntegral := intervalIntegral.integral_comp_sub_left
    (f := centeredEndpointBoundaryTail u) (a := (0 : ℝ)) (b := 2) 2
  have hvReflectIntegral := intervalIntegral.integral_comp_sub_left
    (f := centeredEndpointBoundaryTail v) (a := (0 : ℝ)) (b := 2) 2
  have hblock : factorTwoIntrinsicRegularPhaseBlock u v a b =
      ∫ t : ℝ in 0..2, G t := by
    unfold factorTwoIntrinsicRegularPhaseBlock
    dsimp only [G]
    rw [intervalIntegral.integral_add
      (hforward.const_mul yoshidaEndpointA) hreflected,
      intervalIntegral.integral_const_mul]
  rw [hblock]
  calc
    |∫ t : ℝ in 0..2, G t| ≤ ∫ t : ℝ in 0..2, |G t| := habsIntegral
    _ ≤ ∫ t : ℝ in 0..2, B t := hintegral
    _ = (11 / 8 : ℝ) *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
      dsimp only [B]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add huReflect hvReflect,
        huReflectIntegral, hvReflectIntegral]
      norm_num only [sub_self, sub_zero]
      rw [integral_centeredEndpointBoundaryTail_eq_two_mul_energy u hu,
        integral_centeredEndpointBoundaryTail_eq_two_mul_energy v hv]
      unfold factorTwoIntrinsicEnergy
      ring

/-- On a real mean-zero profile, the regular endpoint quadratic costs only
`log 2 / 64` after endpoint scaling. -/
theorem endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
    (w : ℝ → ℝ) (hw : Continuous w)
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤
      (Real.log 2 / 64) * factorTwoIntrinsicEnergy w := by
  let f : ℝ → ℂ := fun x ↦ (w x : ℂ)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hmeanInterval : (∫ x : ℝ in -1..1, f x) = 0 := by
    change (∫ x : ℝ in -1..1, (w x : ℂ)) = (0 : ℂ)
    rw [intervalIntegral.integral_ofReal, hmean]
    norm_num
  have hmeanSet : (∫ x : ℝ in Icc (-1) 1, f x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hmeanInterval
  have hmass :
      (∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2) =
        factorTwoIntrinsicEnergy w := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    unfold factorTwoIntrinsicEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [f]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm :=
    norm_yoshidaEndpointRegularQuadratic_le_one_thirty_second_of_integral_eq_zero
      f hf hmeanSet
  rw [hmass] at hnorm
  have hre : (yoshidaEndpointRegularQuadratic f).re ≤
      ‖yoshidaEndpointRegularQuadratic f‖ := Complex.re_le_norm _
  have hA : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hscaled := mul_le_mul_of_nonneg_left (hre.trans hnorm) hA
  change yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤ _
  calc
    yoshidaEndpointA *
          (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤
        yoshidaEndpointA * ((1 / 32 : ℝ) * factorTwoIntrinsicEnergy w) :=
      hscaled
    _ = (Real.log 2 / 64) * factorTwoIntrinsicEnergy w := by
      unfold yoshidaEndpointA
      ring

/-- Odd reflection forces the centered mean to vanish. -/
theorem centered_interval_integral_eq_zero_of_odd
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    (∫ x : ℝ in -1..1, w x) = 0 := by
  have hreflect := intervalIntegral.integral_comp_neg
    (f := w) (a := (-1 : ℝ)) (b := 1)
  have hneg : (∫ x : ℝ in -1..1, w (-x)) =
      -(∫ x : ℝ in -1..1, w x) := by
    rw [show (fun x : ℝ ↦ w (-x)) = fun x ↦ -w x by
      funext x
      exact hodd x]
    exact intervalIntegral.integral_neg
  have heq : (∫ x : ℝ in -1..1, w (-x)) =
      ∫ x : ℝ in -1..1, w x := by
    simpa only [neg_neg] using hreflect
  rw [hneg] at heq
  exact CharZero.neg_eq_self_iff.mp heq

/-- Both intrinsic residual profiles are mean zero, so their regular
quadratics share the sharp centered-kernel bound. -/
theorem endpoint_mul_regularQuadratic_re_sum_le
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he0 : centeredEvenP0Coefficient e = 0) (ho : Function.Odd o) :
    yoshidaEndpointA *
        ((yoshidaEndpointRegularQuadratic (fun x ↦ (e x : ℂ))).re +
          (yoshidaEndpointRegularQuadratic (fun x ↦ (o x : ℂ))).re) ≤
      (Real.log 2 / 64) *
        (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
  have heMean : (∫ x : ℝ in -1..1, e x) = 0 := by
    unfold centeredEvenP0Coefficient at he0
    linarith
  have hoMean := centered_interval_integral_eq_zero_of_odd o ho
  have heReg :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      e hec heMean
  have hoReg :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      o hoc hoMean
  linarith

/-- Even parity makes the hyperbolic block nonnegative; only the odd
`sinh` rank can contribute to the negative remainder. -/
theorem neg_hyperbolic_sum_le_odd_energy
    (e o : ℝ → ℝ) (hoc : Continuous o)
    (he : Function.Even e) :
    -(yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (o x : ℂ))) ≤
      (1 / Real.sqrt 2 - Real.log 2) * factorTwoIntrinsicEnergy o := by
  have heHyper := yoshidaEndpointHyperbolicQuadratic_nonneg_of_even e he
  have hoHyper := yoshidaEndpointHyperbolicQuadratic_lower
    (fun x ↦ (o x : ℂ)) (by fun_prop)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hoHyper
  unfold factorTwoIntrinsicEnergy
  linarith

/-- The signed retained `p = 3` phase atom costs its exact arithmetic
coefficient times half the total mass. -/
theorem weighted_prime_phase_le_half_mass
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (Real.log 3 / Real.sqrt 3) *
        factorTwoCenteredPhaseCorrelation u v a b
          (factorTwoPrimeShift / yoshidaEndpointA) ≤
      ((Real.log 3 / Real.sqrt 3) / 2) *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
  let C := factorTwoCenteredPhaseCorrelation u v a b
    (factorTwoPrimeShift / yoshidaEndpointA)
  let M := factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v
  have hcorr := two_mul_abs_phaseCorrelation_primeShift_le_mass
    u v hu hv a b hab
  change 2 * |C| ≤ M at hcorr
  have hbeta : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have hC : C ≤ M / 2 := by
    have := le_abs_self C
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hC hbeta
  dsimp only [C, M] at hscaled ⊢
  nlinarith

/-- The dyadic mass atom keeps the phase sign; a uniform disk estimate only
replaces `a` by `|a|`. -/
theorem dyadic_phase_mass_le_abs
    (u v : ℝ → ℝ) (a : ℝ) :
    (Real.log 2 / Real.sqrt 2) * a *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) ≤
      (Real.log 2 / Real.sqrt 2) * |a| *
        (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) := by
  have hcoeff : 0 ≤ Real.log 2 / Real.sqrt 2 := by positivity
  have hmass : 0 ≤ factorTwoIntrinsicEnergy u +
      factorTwoIntrinsicEnergy v :=
    add_nonneg (factorTwoIntrinsicEnergy_nonneg u)
      (factorTwoIntrinsicEnergy_nonneg v)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_abs_self a) hcoeff) hmass

/-- Structural energy bound for the exact signed remainder.  The regular
phase branches remain coupled through their `11/8` disk multiplier; the
one-profile regular kernels use mean-zero cancellation, and only the odd
hyperbolic rank contributes a possible loss. -/
theorem neg_factorTwoIntrinsicSignedRemainder_le_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    -factorTwoIntrinsicSignedRemainder e o a b ≤
      factorTwoIntrinsicEvenRemainderLoss a * factorTwoIntrinsicEnergy e +
        factorTwoIntrinsicOddRemainderLoss a * factorTwoIntrinsicEnergy o := by
  let Ee := factorTwoIntrinsicEnergy e
  let Eo := factorTwoIntrinsicEnergy o
  let M := Ee + Eo
  let R := factorTwoIntrinsicRegularPhaseBlock e o a b
  let C := factorTwoCenteredPhaseCorrelation e o a b
    (factorTwoPrimeShift / yoshidaEndpointA)
  let H := yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) +
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (o x : ℂ))
  let K := yoshidaEndpointA *
    ((yoshidaEndpointRegularQuadratic (fun x ↦ (e x : ℂ))).re +
      (yoshidaEndpointRegularQuadratic (fun x ↦ (o x : ℂ))).re)
  let alpha := Real.log 2 / Real.sqrt 2
  let beta := Real.log 3 / Real.sqrt 3
  let delta := 1 / Real.sqrt 2 - Real.log 2
  have hregularAbs := abs_factorTwoIntrinsicRegularPhaseBlock_le
    e o hec hoc a b hab
  change |R| ≤ (11 / 8 : ℝ) * M at hregularAbs
  have hregular : -R ≤ (11 / 8 : ℝ) * M :=
    (neg_le_abs R).trans hregularAbs
  have hdyadic := dyadic_phase_mass_le_abs e o a
  change alpha * a * M ≤ alpha * |a| * M at hdyadic
  have hprime := weighted_prime_phase_le_half_mass
    e o hec hoc a b hab
  change beta * C ≤ (beta / 2) * M at hprime
  have hkernel := endpoint_mul_regularQuadratic_re_sum_le
    e o hec hoc he0 ho
  change K ≤ (Real.log 2 / 64) * M at hkernel
  have hhyper := neg_hyperbolic_sum_le_odd_energy e o hoc he
  change -H ≤ delta * Eo at hhyper
  have hdecomp :
      -factorTwoIntrinsicSignedRemainder e o a b =
        -R + alpha * a * M + beta * C +
          yoshidaEndpointScalarMassLoss * M + K - H := by
    dsimp only [R, M, Ee, Eo, C, H, K, alpha, beta]
    unfold factorTwoIntrinsicSignedRemainder
      factorTwoIntrinsicRegularPhaseBlock
    ring
  rw [hdecomp]
  calc
    -R + alpha * a * M + beta * C +
          yoshidaEndpointScalarMassLoss * M + K - H ≤
        (11 / 8 : ℝ) * M + alpha * |a| * M +
          (beta / 2) * M + yoshidaEndpointScalarMassLoss * M +
          (Real.log 2 / 64) * M + delta * Eo := by
      linarith
    _ = factorTwoIntrinsicEvenRemainderLoss a *
          factorTwoIntrinsicEnergy e +
        factorTwoIntrinsicOddRemainderLoss a *
          factorTwoIntrinsicEnergy o := by
      dsimp only [M, Ee, Eo, alpha, beta, delta]
      unfold factorTwoIntrinsicOddRemainderLoss
        factorTwoIntrinsicEvenRemainderLoss
      ring

/-!
## The exact remaining norm gap

The following lower bounds show that this operator-norm estimate cannot by
itself fit inside the protected raw reserve.  They do not assert that the
actual signed remainder saturates the norm bounds.
-/

theorem seven_sixths_lt_yoshidaEndpointScalarMassLoss :
    (7 / 6 : ℝ) < yoshidaEndpointScalarMassLoss := by
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hprod1 : (2 : ℝ) < Real.pi * (2 / 3 : ℝ) := by
    have := mul_lt_mul_of_pos_right Real.pi_gt_three (by norm_num : (0 : ℝ) < 2 / 3)
    nlinarith
  have hprod2 : Real.pi * (2 / 3 : ℝ) < Real.pi * Real.log 2 :=
    mul_lt_mul_of_pos_left hlogTwo Real.pi_pos
  have hprod : (2 : ℝ) < Real.pi * Real.log 2 := hprod1.trans hprod2
  have hlogProd : Real.log 2 < Real.log (Real.pi * Real.log 2) :=
    Real.strictMonoOn_log (by norm_num)
      ((by norm_num : (0 : ℝ) < 2).trans hprod) hprod
  unfold yoshidaEndpointScalarMassLoss
  linarith [Real.one_half_lt_eulerMascheroniConstant]

theorem one_half_lt_factorTwoPrimeThreeWeight :
    (1 / 2 : ℝ) < Real.log 3 / Real.sqrt 3 := by
  have hlogThree : (1 : ℝ) < Real.log 3 := by
    have h := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
      Real.exp_one_lt_three
    simpa using h
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtUpper : Real.sqrt 3 < 2 := by
    nlinarith [Real.sqrt_nonneg 3]
  rw [lt_div_iff₀ hsqrtPos]
  nlinarith

theorem sixty_seven_div_twenty_four_lt_even_remainderLoss
    (a : ℝ) :
    (67 / 24 : ℝ) < factorTwoIntrinsicEvenRemainderLoss a := by
  have hscalar := seven_sixths_lt_yoshidaEndpointScalarMassLoss
  have hprime := one_half_lt_factorTwoPrimeThreeWeight
  have hdyadic : 0 ≤ (Real.log 2 / Real.sqrt 2) * |a| := by positivity
  have hregular : 0 < Real.log 2 / 64 := by positivity
  unfold factorTwoIntrinsicEvenRemainderLoss
  nlinarith

theorem hyperbolic_loss_nonneg :
    0 ≤ 1 / Real.sqrt 2 - Real.log 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hseven : (7 / 10 : ℝ) < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ hsqrtPos]
    nlinarith [Real.sqrt_nonneg 2]
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  linarith

/-- Even after all mean-zero and parity improvements above, the available
even energy coefficient exceeds its protected raw reserve by more than
`17/24`. -/
theorem seventeen_div_twenty_four_lt_even_remainderGap (a : ℝ) :
    (17 / 24 : ℝ) < factorTwoIntrinsicEvenRemainderGap a := by
  have hloss := sixty_seven_div_twenty_four_lt_even_remainderLoss a
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold factorTwoIntrinsicEvenRemainderGap
  linarith

/-- The analogous odd norm gap is already larger than `61/120`. -/
theorem sixty_one_div_one_hundred_twenty_lt_odd_remainderGap (a : ℝ) :
    (61 / 120 : ℝ) < factorTwoIntrinsicOddRemainderGap a := by
  have hloss := sixty_seven_div_twenty_four_lt_even_remainderLoss a
  have hhyper := hyperbolic_loss_nonneg
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold factorTwoIntrinsicOddRemainderGap
    factorTwoIntrinsicOddRemainderLoss
  linarith

/-- With the present operator bounds, the exact remaining sufficient
condition is that the retained endpoint potential absorb the two positive
norm gaps.  Any future signed improvement can replace this hypothesis
directly without changing the singular-square argument. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_potential_dominates_normGap
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hpotential :
      factorTwoIntrinsicEvenRemainderGap a * factorTwoIntrinsicEnergy e +
          factorTwoIntrinsicOddRemainderGap a * factorTwoIntrinsicEnergy o ≤
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o)) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have hrem := neg_factorTwoIntrinsicSignedRemainder_le_energy
    e o hec hoc he ho he0 a b hab
  apply factorTwoEndpointChannelPhase_nonneg_of_intrinsic_signedRemainder
    e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal a b hab
  unfold factorTwoIntrinsicEvenRemainderGap
    factorTwoIntrinsicOddRemainderGap at hpotential
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRemainderBound
