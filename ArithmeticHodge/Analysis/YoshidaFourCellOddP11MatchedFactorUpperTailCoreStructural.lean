import ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorObstructionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorUpperTailWeightStructural
import ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorUpperTailCoreStructural

noncomputable section

open CenteredEndpointCorrelation
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogKernel
open ShiftedLegendreLogEigen
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open ShiftedLogKernelRawPolynomial
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11MatchedFactorObstructionStructural
open YoshidaFourCellOddP11MatchedFactorUpperTailWeightStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaConstantBounds
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaRegularKernelBound

/-!
# Core upper bound for the fixed matched-factor obstruction

The only singular estimate needed below is a finite-rank affine connection
formula.  It rewrites the endpoint-strip image of the eight-mode structural
packet in the same Legendre eigenbasis.  All logarithmic energies are then
evaluated by the all-degree eigenidentity, not by sampling a kernel.
-/

/-- Unit-interval polynomial of the reflection-odd endpoint-strip image of
the fixed upper-tail packet. -/
def matchedFactorUpperTailEndpointStripOddShiftedPolynomial : ℝ[X] :=
  (1 / 2 : ℝ) •
    (fourCellOddP11MatchedFactorUpperTailPolynomial.comp
        ((2 / 5 : ℝ) • X + C (3 / 5 : ℝ)) -
      fourCellOddP11MatchedFactorUpperTailPolynomial.comp
        ((-(2 / 5 : ℝ)) • X + C 1))

theorem centeredPullback_matchedFactorUpperTail_endpointStripOdd_eq
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd
          fourCellOddP11MatchedFactorUpperTail) t =
      matchedFactorUpperTailEndpointStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback
    fourCellOddP11MatchedFactorUpperTail
    matchedFactorUpperTailEndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]
  rw [show (4 / 5 : ℝ) + (2 * t - 1) / 5 =
      t * (2 / 5) + 3 / 5 by ring,
    show (4 / 5 : ℝ) + -(2 * t - 1) / 5 =
      t * (-(2 / 5)) + 1 by ring]
  rw [mul_comm t (2 / 5), mul_comm t (-(2 / 5))]
  ring

set_option maxHeartbeats 5000000 in
/-- The affine strip map has a compact exact connection expansion.  The
small high-degree coefficients are consequences of the width `1/5`; they
are not numerical enclosures. -/
theorem matchedFactorUpperTailEndpointStripOddShiftedPolynomial_eq :
    matchedFactorUpperTailEndpointStripOddShiftedPolynomial =
      (6444014056042848 / 59604644775390625 : ℝ) • shiftedLegendreReal 1 +
      (75474320022112 / 59604644775390625 : ℝ) • shiftedLegendreReal 3 +
      (63623895213644128 / 59604644775390625 : ℝ) • shiftedLegendreReal 5 +
      (11326162459718368 / 11920928955078125 : ℝ) • shiftedLegendreReal 7 +
      (16501883020284384 / 11920928955078125 : ℝ) • shiftedLegendreReal 9 +
      (31711443412104273 / 59604644775390625 : ℝ) • shiftedLegendreReal 11 +
      (2996734566982277 / 59604644775390625 : ℝ) • shiftedLegendreReal 13 +
      (18677294474613 / 11920928955078125 : ℝ) • shiftedLegendreReal 15 +
      (218170980217 / 11920928955078125 : ℝ) • shiftedLegendreReal 17 +
      (4897323137 / 59604644775390625 : ℝ) • shiftedLegendreReal 19 +
      (7869813 / 59604644775390625 : ℝ) • shiftedLegendreReal 21 +
      (3577 / 59604644775390625 : ℝ) • shiftedLegendreReal 23 +
      (1 / 298023223876953125 : ℝ) • shiftedLegendreReal 25 := by
  apply Polynomial.funext
  intro x
  unfold matchedFactorUpperTailEndpointStripOddShiftedPolynomial
    fourCellOddP11MatchedFactorUpperTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, Polynomial.eval_comp, smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

/-- Exact bridge from a centered polynomial profile to the diagonalized
unit-interval logarithmic form. -/
private theorem centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
    (q : ℝ → ℝ) (p : ℝ[X])
    (hmode : ∀ t : ℝ, centeredPullback q t = p.eval t) :
    centeredRawLogEnergy q =
      4 * ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback q (t : ℝ)
  have hfeq : f = fun t : unitInterval ↦ p.eval (t : ℝ) := by
    funext t
    exact hmode t
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) := by
    rw [hfeq]
    exact integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hbridge := unitIntervalLogEnergy_centeredPullback q henergy
  change unitIntervalLogEnergy f = (1 / 4 : ℝ) * centeredRawLogEnergy q
    at hbridge
  rw [hfeq] at hbridge
  have hpoly := integral_unitIntervalRawLogEnergyIntegrand_polynomial p
  unfold unitIntervalLogEnergy at hbridge
  rw [hpoly] at hbridge
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    ← integral_unitInterval_eq_intervalIntegral]
  linarith

private theorem integral_shiftedLegendreReal_sq_closed (n : ℕ) :
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
      1 / (2 * (n : ℝ) + 1) := by
  have hdiag := centeredLegendreL2Diagonal_closed n
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ (centeredShiftedLegendreReal n).eval x ^ 2)
  rw [show (fun t : ℝ ↦
      (centeredShiftedLegendreReal n).eval (2 * t - 1) ^ 2) =
      fun t ↦ (shiftedLegendreReal n).eval t ^ 2 by
    funext t
    rw [eval_centeredShiftedLegendreReal]
    congr 2
    ring] at htransport
  rw [show (fun x : ℝ ↦
      (centeredShiftedLegendreReal n).eval x ^ 2) = fun x ↦
      (centeredShiftedLegendreReal n).eval x *
        (centeredShiftedLegendreReal n).eval x by
    funext x
    ring,
    hdiag] at htransport
  calc
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
        (1 / 2 : ℝ) * (2 / (2 * (n : ℝ) + 1)) := htransport
    _ = 1 / (2 * (n : ℝ) + 1) := by ring

private theorem shiftedLogEnergyBilinear_legendre_ne
    {m n : ℕ} (hmn : m ≠ n) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) = 0 := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal m).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal m).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    ShiftedLegendreBasis.integral_shiftedLegendreReal_mul_eq_zero hmn]
  ring

private theorem shiftedLogEnergyBilinear_legendre_self (n : ℕ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal n) (shiftedLegendreReal n) =
      2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal n).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal n).eval x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    integral_shiftedLegendreReal_sq_closed]
  ring

private theorem shiftedLogEnergyBilinear_legendre_eq (m n : ℕ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) =
      if m = n then 2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, shiftedLogEnergyBilinear_legendre_self]
  · rw [if_neg hmn, shiftedLogEnergyBilinear_legendre_ne hmn]

private theorem shiftedLogEnergyBilinear_add_left
    (p q r : ℝ[X]) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear (p + q) r =
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p r +
        ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear q r := by
  rw [map_add, LinearMap.add_apply]

private theorem shiftedLogEnergyBilinear_add_right
    (p q r : ℝ[X]) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p (q + r) =
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p q +
        ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p r := by
  exact map_add
    (ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p) q r

private theorem shiftedLogEnergyBilinear_smul_left
    (a : ℝ) (p q : ℝ[X]) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (a • p) q =
      a * ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p q := by
  have h := congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ ↦ L q)
    (map_smul ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear a p)
  simpa only [LinearMap.smul_apply, smul_eq_mul] using h

private theorem shiftedLogEnergyBilinear_smul_right
    (b : ℝ) (p q : ℝ[X]) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        p (b • q) =
      b * ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p q := by
  simpa only [smul_eq_mul] using
    (map_smul (ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p) b q)

/-- The same packet in unit-interval shifted coordinates. -/
def matchedFactorUpperTailShiftedPolynomial : ℝ[X] :=
  shiftedLegendreReal 11 + shiftedLegendreReal 13 +
    shiftedLegendreReal 15 + shiftedLegendreReal 17 +
      shiftedLegendreReal 19 + shiftedLegendreReal 21 +
        shiftedLegendreReal 23 + shiftedLegendreReal 25

theorem centeredPullback_matchedFactorUpperTail_eq (t : ℝ) :
    centeredPullback fourCellOddP11MatchedFactorUpperTail t =
      matchedFactorUpperTailShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddP11MatchedFactorUpperTail
    fourCellOddP11MatchedFactorUpperTailPolynomial
    matchedFactorUpperTailShiftedPolynomial
  simp only [Polynomial.eval_add, eval_centeredShiftedLegendreReal]
  rw [show ((2 * t - 1) + 1) / 2 = t by ring]

/-- The packet's complete centered raw energy stays below `157/100` after
the quarter normalization.  This is the all-degree harmonic eigenformula
specialized to the structural packet. -/
theorem matchedFactorUpperTail_raw_div_four_lt :
    centeredRawLogEnergy fourCellOddP11MatchedFactorUpperTail / 4 <
      (157 / 100 : ℝ) := by
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
      fourCellOddP11MatchedFactorUpperTail
      matchedFactorUpperTailShiftedPolynomial
      centeredPullback_matchedFactorUpperTail_eq]
  unfold matchedFactorUpperTailShiftedPolynomial
  simp only [shiftedLogEnergyBilinear_add_left,
    shiftedLogEnergyBilinear_add_right,
    shiftedLogEnergyBilinear_legendre_eq]
  norm_num [harmonic, Finset.sum_range_succ]

set_option maxHeartbeats 5000000 in
/-- The affine endpoint-strip image retains more than `57/50` of physical
reflection-odd raw energy.  The proof is the exact connection formula above
followed by the uniform Legendre logarithmic eigenidentity. -/
theorem fifty_seven_fiftieths_lt_matchedFactorUpperTail_stripOddRaw :
    (57 / 50 : ℝ) <
      fourCellOddEndpointStripOddRawEnergy
        fourCellOddP11MatchedFactorUpperTail := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
      (fourCellOddEndpointStripOdd fourCellOddP11MatchedFactorUpperTail)
      matchedFactorUpperTailEndpointStripOddShiftedPolynomial
      centeredPullback_matchedFactorUpperTail_endpointStripOdd_eq,
    matchedFactorUpperTailEndpointStripOddShiftedPolynomial_eq]
  simp only [shiftedLogEnergyBilinear_add_left,
    shiftedLogEnergyBilinear_add_right,
    shiftedLogEnergyBilinear_smul_left,
    shiftedLogEnergyBilinear_smul_right,
    shiftedLogEnergyBilinear_legendre_eq]
  norm_num [harmonic, Finset.sum_range_succ]

/-- Consequently the exact raw-strip cancellation reserve of the packet is
strictly smaller than one. -/
theorem matchedFactorUpperTail_rawStripCancellationReserve_lt_one :
    fourCellOddRawStripCancellationReserve
        fourCellOddP11MatchedFactorUpperTail < 1 := by
  have hfold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    fourCellOddP11MatchedFactorUpperTail
    (contDiff_fourCellOddP11MatchedFactorUpperTail.contDiffOn.locallyLipschitzOn
      (convex_Icc (-1 : ℝ) 1))
    odd_fourCellOddP11MatchedFactorUpperTail
  have hraw := matchedFactorUpperTail_raw_div_four_lt
  have hstrip :=
    fifty_seven_fiftieths_lt_matchedFactorUpperTail_stripOddRaw
  unfold fourCellOddRawStripCancellationReserve
  linarith

/-- The signed scalar plus regular-kernel charge removes more than `7/10`
from the packet.  The regular row is controlled once, globally, by its
operator envelope; no modewise regular-kernel estimate is used. -/
theorem seven_tenths_lt_matchedFactorUpperTail_scalarRegularCharge :
    (7 / 10 : ℝ) <
      (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
          (∫ x : ℝ in 0..1,
            fourCellOddP11MatchedFactorUpperTail x ^ 2) +
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation
                fourCellOddP11MatchedFactorUpperTail t) := by
  let H : ℝ := ∫ x : ℝ in 0..1,
    fourCellOddP11MatchedFactorUpperTail x ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellOddP11MatchedFactorUpperTail t
  let C : ℝ := 2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  have hmassFold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11MatchedFactorUpperTail
    contDiff_fourCellOddP11MatchedFactorUpperTail.continuous
    (Or.inr odd_fourCellOddP11MatchedFactorUpperTail)
  have hRabs : |R| ≤ (1 / 20 : ℝ) * (2 * H) := by
    have h := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
      fourCellOddP11MatchedFactorUpperTail
      contDiff_fourCellOddP11MatchedFactorUpperTail.continuous
      odd_fourCellOddP11MatchedFactorUpperTail
    simpa only [R, H, hmassFold] using h
  have hRlower : -((1 / 20 : ℝ) * (2 * H)) ≤ R :=
    (neg_le_of_abs_le hRabs)
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hregular :
      -(fourCellOperatorHalfWidth / 5 * H) ≤
        2 * fourCellOperatorHalfWidth * R := by
    calc
      -(fourCellOperatorHalfWidth / 5 * H) =
          2 * fourCellOperatorHalfWidth *
            (-((1 / 20 : ℝ) * (2 * H))) := by ring
      _ ≤ 2 * fourCellOperatorHalfWidth * R :=
        mul_le_mul_of_nonneg_left hRlower hwidth0
  have hscalar := fourCellScalar_fine_bounds.1
  have hlog := strict_log_two_bounds.2
  have hcoefficient :
      (77 / 25 : ℝ) < C - fourCellOperatorHalfWidth / 5 := by
    dsimp only [C]
    unfold fourCellOperatorHalfWidth at hscalar ⊢
    nlinarith
  have hmass : (23 / 100 : ℝ) < H := by
    simpa only [H] using
      twenty_three_hundredths_lt_matchedFactorUpperTail_mass
  have hcoefficient0 : 0 < C - fourCellOperatorHalfWidth / 5 :=
    (by linarith : 0 < C - fourCellOperatorHalfWidth / 5)
  have hproduct :
      (7 / 10 : ℝ) < (C - fourCellOperatorHalfWidth / 5) * H := by
    calc
      (7 / 10 : ℝ) < (77 / 25 : ℝ) * (23 / 100 : ℝ) := by norm_num
      _ < (C - fourCellOperatorHalfWidth / 5) * (23 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hcoefficient (by norm_num)
      _ < (C - fourCellOperatorHalfWidth / 5) * H :=
        mul_lt_mul_of_pos_left hmass hcoefficient0
  dsimp only [C, H, R] at hproduct hregular ⊢
  linarith

private theorem fourCellEndpointHalfMass_eq_upperStripMass_local
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEndpointHalfMass w =
      ∫ x : ℝ in 3 / 5..1, w x ^ 2 := by
  have hleft := intervalIntegral.integral_comp_add_mul
    (a := (0 : ℝ)) (b := 2 / 5) (c := (1 : ℝ))
    (fun x : ℝ ↦ w x ^ 2) (by norm_num) (3 / 5)
  have hright := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 / 5) (fun x : ℝ ↦ w x ^ 2) 1
  norm_num at hleft hright
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦ w (3 / 5 + t) ^ 2) volume 0 (2 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hrightInt : IntervalIntegrable
      (fun t : ℝ ↦ w (1 - t) ^ 2) volume 0 (2 / 5) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold fourCellEndpointHalfMass
  rw [intervalIntegral.integral_add hleftInt hrightInt, hleft, hright]
  ring

/-- Both endpoint-prime coefficients are within `1/50` of one, and the
parity-channel masses sum exactly to the upper-strip mass.  Hence the whole
prime contribution of the packet is below `23/100`. -/
theorem matchedFactorUpperTail_primeMass_lt_twenty_three_hundredths :
    Real.sqrt 2 * Real.log 2 *
        fourCellOddEndpointStripEvenMass
          fourCellOddP11MatchedFactorUpperTail +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass
          fourCellOddP11MatchedFactorUpperTail <
      (23 / 100 : ℝ) := by
  let k : ℝ := Real.sqrt 2 * Real.log 2
  let E : ℝ := fourCellOddEndpointStripEvenMass
    fourCellOddP11MatchedFactorUpperTail
  let O : ℝ := fourCellOddEndpointStripOddMass
    fourCellOddP11MatchedFactorUpperTail
  let U : ℝ := ∫ x : ℝ in 3 / 5..1,
    fourCellOddP11MatchedFactorUpperTail x ^ 2
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hslo : (707 / 500 : ℝ) < Real.sqrt 2 := by nlinarith
  have hshi : Real.sqrt 2 < (283 / 200 : ℝ) := by nlinarith
  have hlog := strict_log_two_bounds
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hklo : (49 / 50 : ℝ) < k := by
    dsimp only [k]
    calc
      (49 / 50 : ℝ) < (707 / 500 : ℝ) * (6931 / 10000 : ℝ) := by
        norm_num
      _ < Real.sqrt 2 * (6931 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hslo (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hlog.1 (Real.sqrt_pos.2 (by norm_num))
  have hkhi : k < (51 / 50 : ℝ) := by
    dsimp only [k]
    calc
      Real.sqrt 2 * Real.log 2 < (283 / 200 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hshi hlog0
      _ < (283 / 200 : ℝ) * (6932 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_left hlog.2 (by norm_num)
      _ < (51 / 50 : ℝ) := by norm_num
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold fourCellOddEndpointStripEvenMass
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg
      (by norm_num) (fun _ _ ↦ sq_nonneg _))
  have hO : 0 ≤ O := by
    dsimp only [O]
    unfold fourCellOddEndpointStripOddMass
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg
      (by norm_num) (fun _ _ ↦ sq_nonneg _))
  have hsum := fourCellEndpointHalfMass_eq_evenMass_add_oddMass
    fourCellOddP11MatchedFactorUpperTail
    contDiff_fourCellOddP11MatchedFactorUpperTail.continuous
  rw [fourCellEndpointHalfMass_eq_upperStripMass_local
    fourCellOddP11MatchedFactorUpperTail
    contDiff_fourCellOddP11MatchedFactorUpperTail.continuous] at hsum
  have hEU : E + O = U := by simpa only [E, O, U] using hsum.symm
  have hU : U < (23 / 102 : ℝ) := by
    dsimp only [U]
    rw [fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_eq]
    norm_num
  have hprime : k * E + (2 - k) * O ≤ (51 / 50 : ℝ) * (E + O) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkhi.le) hE,
      mul_nonneg (sub_nonneg.mpr hklo.le) hO]
  rw [hEU] at hprime
  dsimp only [k, E, O] at hprime ⊢
  nlinarith

/-- The complete packet core is below `31/20`.  Its four inputs are the
coupled raw-strip bound, the complete prime diagonal, the exact polynomial
endpoint-potential pair, and one global regular-envelope charge. -/
theorem fourCellOddCoreLocalQuadratic_matchedFactorUpperTail_lt :
    fourCellOddCoreLocalQuadratic
        fourCellOddP11MatchedFactorUpperTail < (31 / 20 : ℝ) := by
  have hraw := matchedFactorUpperTail_rawStripCancellationReserve_lt_one
  have hprime :=
    matchedFactorUpperTail_primeMass_lt_twenty_three_hundredths
  have hpotential :=
    ninetyThree_hundredths_mul_endpointPotentialPair_upperTail_lt
  have hcharge :=
    seven_tenths_lt_matchedFactorUpperTail_scalarRegularCharge
  have hpotentialFold :=
    integral_zero_one_endpointPotential_polynomial_sq_eq_half_pair
      fourCellOddP11MatchedFactorUpperTailPolynomial
      (by simpa only [fourCellOddP11MatchedFactorUpperTail] using
        odd_fourCellOddP11MatchedFactorUpperTail)
  unfold fourCellOddCoreLocalQuadratic
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddStripReducedRemainder
  rw [show (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        fourCellOddP11MatchedFactorUpperTail x ^ 2) =
      (1 / 2 : ℝ) * endpointPotentialPolynomialPair
        fourCellOddP11MatchedFactorUpperTailPolynomial
        fourCellOddP11MatchedFactorUpperTailPolynomial by
    simpa only [fourCellOddP11MatchedFactorUpperTail] using hpotentialFold]
  linarith

/-- On the fixed packet the complete core is strictly smaller than twice
the exact scalar weight. -/
theorem fourCellOddCoreLocalQuadratic_matchedFactorUpperTail_lt_two_weight :
    fourCellOddCoreLocalQuadratic fourCellOddP11MatchedFactorUpperTail <
      2 * fourCellOddP1ExactTailWeight
        fourCellOddP11MatchedFactorUpperTail := by
  have hcore := fourCellOddCoreLocalQuadratic_matchedFactorUpperTail_lt
  have hweight :=
    thirtyNine_fiftieths_lt_fourCellOddP1ExactTailWeight_upperTail
  nlinarith

/-- Every universal tail-reserve factor is strictly below two.  This is the
upper half of the matched-factor no-go and uses one fixed structural packet,
not a truncated spectral minimum. -/
theorem factor_lt_two_of_fourCellOddP11TailReserveAtFactor
    (κ : ℝ) (htail : FourCellOddP11TailReserveAtFactor κ) :
    κ < 2 := by
  rcases fourCellOddP11MatchedFactorUpperTail_moments with
    ⟨h1, h3, h5, h7, h9⟩
  have hreserve := htail fourCellOddP11MatchedFactorUpperTail
    contDiff_fourCellOddP11MatchedFactorUpperTail
    odd_fourCellOddP11MatchedFactorUpperTail h1 h3 h5 h7 h9
  have hstrict :=
    fourCellOddCoreLocalQuadratic_matchedFactorUpperTail_lt_two_weight
  have hweight :=
    thirtyNine_fiftieths_lt_fourCellOddP1ExactTailWeight_upperTail
  by_contra hk
  have hk' : 2 ≤ κ := le_of_not_gt hk
  have hscale :
      2 * fourCellOddP1ExactTailWeight fourCellOddP11MatchedFactorUpperTail ≤
        κ * fourCellOddP1ExactTailWeight
          fourCellOddP11MatchedFactorUpperTail := by
    exact mul_le_mul_of_nonneg_right hk'
      ((by norm_num : (0 : ℝ) ≤ 39 / 50).trans hweight.le)
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorUpperTailCoreStructural
