import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11FiveModeThreeHalvesStructural
import ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural

noncomputable section

open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEigen
open ShiftedLegendreOrthogonality
open ShiftedLegendrePolynomialGap
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Exact first `P₁₁` core row

The five mixed entries in the six-mode odd Galerkin block have a common
structural form.  Their global raw and scalar-mass crosses vanish by exact
Legendre orthogonality.  What remains is an explicitly evaluated endpoint
row and one smooth regular-kernel moment.  The latter is kept intact and is
bounded by the already proved infinite-dimensional Cauchy estimate.
-/

/-- The only unevaluated term in the mixed `Pₘ`--`P₁₁` core row. -/
def fourCellOddP11CoreRegularMoment (u : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        u fourCellOddP11DirectTail t

private def p11EndpointStripOddShiftedPolynomial : ℝ[X] := -(
  (5088276 / 48828125 : ℝ) • shiftedLegendreReal 1 +
    (8502676 / 48828125 : ℝ) • shiftedLegendreReal 3 +
    (15968084 / 48828125 : ℝ) • shiftedLegendreReal 5 +
    (25716 / 1953125 : ℝ) • shiftedLegendreReal 7 +
    (2964 / 48828125 : ℝ) • shiftedLegendreReal 9 +
    (1 / 48828125 : ℝ) • shiftedLegendreReal 11)

set_option maxHeartbeats 2000000 in
private theorem centeredPullback_endpointStripOdd_P11_eq_shiftedPolynomial
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd fourCellOddP11DirectTail) t =
      p11EndpointStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback fourCellOddP11DirectTail
    p11EndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

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
    shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) = 0 := by
  rw [shiftedLogEnergyBilinear_apply,
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
    shiftedLogEnergyBilinear
        (shiftedLegendreReal n) (shiftedLegendreReal n) =
      2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) := by
  rw [shiftedLogEnergyBilinear_apply,
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
    shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) =
      if m = n then 2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1)
      else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, shiftedLogEnergyBilinear_legendre_self]
  · rw [if_neg hmn, shiftedLogEnergyBilinear_legendre_ne hmn]

private def fiveModeEndpointStripOddShiftedPolynomial
    (c d e f g : ℝ) : ℝ[X] := -(
  (c / 5 + 84 * d / 125 + 276 * e / 625 -
      9804 * f / 78125 - 303036 * g / 1953125) •
        shiftedLegendreReal 1 +
    (d / 125 + 84 * e / 625 + 35252 * f / 78125 +
      1126916 * g / 1953125) • shiftedLegendreReal 3 +
    (e / 3125 + 1012 * f / 78125 + 195844 * g / 1953125) •
      shiftedLegendreReal 5 +
    (f / 78125 + 372 * g / 390625) • shiftedLegendreReal 7 +
    (g / 1953125) • shiftedLegendreReal 9)

set_option maxHeartbeats 5000000 in
private theorem centeredPullback_fiveModeEndpointStripOdd_eq_shiftedPolynomial
    (c d e f g t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)) t =
      (fiveModeEndpointStripOddShiftedPolynomial c d e f g).eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP7
    factorTwoCenteredP9 fiveModeEndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose]
  ring

private theorem centeredRawLogBilinear_eq_four_mul_shiftedPair_of_polynomials
    (q r : ℝ → ℝ) (p s : ℝ[X]) (hr : Continuous r)
    (hqmode : ∀ t : ℝ, centeredPullback q t = p.eval t)
    (hrmode : ∀ t : ℝ, centeredPullback r t = s.eval t) :
    centeredRawLogBilinear q r =
      4 * shiftedLogEnergyBilinear s p := by
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q r hr hqmode,
    shiftedLogEnergyBilinear_apply,
    ← integral_unitInterval_eq_intervalIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hrmode]

set_option maxHeartbeats 10000000 in
/-- Exact singular endpoint row against the first tail mode. -/
theorem fourCellOddEndpointStripOddRawPolarization_fiveMode_P11_eq
    (c d e f g : ℝ) :
    fourCellOddEndpointStripOddRawPolarization
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        fourCellOddP11DirectTail =
      (13568736 / 1220703125 : ℝ) * c +
      (3472766864 / 91552734375 : ℝ) * d +
      (393505908856 / 11444091796875 : ℝ) * e +
      (18263940974568 / 667572021484375 : ℝ) * f +
      (2221708644118996 / 50067901611328125 : ℝ) * g := by
  have hlow := contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  have htail := contDiff_fourCellOddP11DirectTail
  have htailStrip : Continuous
      (fourCellOddEndpointStripOdd fourCellOddP11DirectTail) := by
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fun_prop
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear
      _ _ hlow htail,
    centeredRawLogBilinear_eq_four_mul_shiftedPair_of_polynomials
      (fourCellOddEndpointStripOdd
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g))
      (fourCellOddEndpointStripOdd fourCellOddP11DirectTail)
      (fiveModeEndpointStripOddShiftedPolynomial c d e f g)
      p11EndpointStripOddShiftedPolynomial
      htailStrip
      (centeredPullback_fiveModeEndpointStripOdd_eq_shiftedPolynomial
        c d e f g)
      centeredPullback_endpointStripOdd_P11_eq_shiftedPolynomial]
  unfold fiveModeEndpointStripOddShiftedPolynomial
    p11EndpointStripOddShiftedPolynomial
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    shiftedLogEnergyBilinear_legendre_eq]
  norm_num [harmonic, Finset.sum_range_succ]
  ring

set_option maxHeartbeats 10000000 in
private theorem fourCellOddEndpointStripEvenMassBilinear_fiveMode_P11_eq
    (c d e f g : ℝ) :
    fourCellOddEndpointStripEvenMassBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        fourCellOddP11DirectTail =
      (-(8247648 / 1220703125 : ℝ)) * c -
      (27796288 / 6103515625 : ℝ) * d -
      (7238485664 / 762939453125 : ℝ) * e -
      (30904212608 / 3814697265625 : ℝ) * f +
      (4121778714144 / 476837158203125 : ℝ) * g := by
  have hlow :=
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).continuous
  have htail := contDiff_fourCellOddP11DirectTail.continuous
  rw [fourCellOddEndpointStripEvenMassBilinear_eq_integral
    _ _ hlow htail]
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP7
    factorTwoCenteredP9 fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num
  have hlinear (a : ℝ) :
      (∫ x : ℝ in 3 / 5..1, a * x) = a * (8 / 25 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    norm_num
  rw [hlinear c]
  ring

set_option maxHeartbeats 10000000 in
private theorem fourCellOddEndpointStripOddMassBilinear_fiveMode_P11_eq
    (c d e f g : ℝ) :
    fourCellOddEndpointStripOddMassBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        fourCellOddP11DirectTail =
      (3392184 / 1220703125 : ℝ) * c +
      (287372792 / 30517578125 : ℝ) * d +
      (5704438328 / 762939453125 : ℝ) * e +
      (55320193912 / 19073486328125 : ℝ) * f +
      (2278454711736 / 476837158203125 : ℝ) * g := by
  have hlow :=
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).continuous
  have htail := contDiff_fourCellOddP11DirectTail.continuous
  rw [fourCellOddEndpointStripOddMassBilinear_eq_integral
    _ _ hlow htail]
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP7
    factorTwoCenteredP9 fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num
  have hlinear (a : ℝ) :
      (∫ x : ℝ in 3 / 5..1, a * x) = a * (8 / 25 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    norm_num
  rw [hlinear c]
  ring

private def fiveModeCenteredLegendrePolynomial
    (c d e f g : ℝ) : ℝ[X] := -(
  c • centeredShiftedLegendreReal 1 +
    d • centeredShiftedLegendreReal 3 +
    e • centeredShiftedLegendreReal 5 +
    f • centeredShiftedLegendreReal 7 +
    g • centeredShiftedLegendreReal 9)

set_option maxHeartbeats 2000000 in
private theorem fiveModeCenteredLegendrePolynomial_eval
    (c d e f g x : ℝ) :
    (fiveModeCenteredLegendrePolynomial c d e f g).eval x =
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x := by
  unfold fiveModeCenteredLegendrePolynomial
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP7
    factorTwoCenteredP9
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

private theorem endpointPotentialPolynomialPair_fiveMode_P11_eq
    (c d e f g : ℝ) :
    endpointPotentialPolynomialPair
        (fiveModeCenteredLegendrePolynomial c d e f g)
        (-(centeredShiftedLegendreReal 11)) =
      c / 65 + d / 60 + e / 51 + f / 38 + g / 21 := by
  have hoff : ∀ {m : ℕ}, m < 11 → Even (m + 11) →
      endpointPotentialPolynomialPair
          (centeredShiftedLegendreReal m)
          (centeredShiftedLegendreReal 11) =
        2 / (((11 : ℝ) - m) * ((11 : ℝ) + m + 1)) := by
    intro m hm heven
    simpa only [endpointPotentialPolynomialPair] using
      integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
        hm heven
  unfold fiveModeCenteredLegendrePolynomial
  simp only [endpointPotentialPolynomialPair_neg_left,
    endpointPotentialPolynomialPair_neg_right,
    endpointPotentialPolynomialPair_add_left,
    endpointPotentialPolynomialPair_smul_left]
  rw [hoff (m := 1) (by omega) (by norm_num),
    hoff (m := 3) (by omega) (by norm_num),
    hoff (m := 5) (by omega) (by norm_num),
    hoff (m := 7) (by omega) (by norm_num),
    hoff (m := 9) (by omega) (by norm_num)]
  norm_num
  ring

private theorem even_yoshidaEndpointPotential :
    Function.Even yoshidaEndpointPotential := by
  intro x
  unfold yoshidaEndpointPotential
  rw [neg_sq]

/-- Exact positive-half endpoint-potential cross in the first tail row. -/
theorem integral_endpointPotential_fiveMode_mul_P11_eq
    (c d e f g : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x *
        fourCellOddP11DirectTail x) =
      c / 130 + d / 120 + e / 102 + f / 76 + g / 42 := by
  let p := fiveModeCenteredLegendrePolynomial c d e f g
  let q := -(centeredShiftedLegendreReal 11)
  have hInt : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * q.eval x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotentialPolynomialPair p q
  have hpodd : Function.Odd (fun x : ℝ ↦ p.eval x) := by
    intro x
    dsimp only [p]
    rw [fiveModeCenteredLegendrePolynomial_eval,
      fiveModeCenteredLegendrePolynomial_eval,
      odd_fourCellOddOneThreeFiveSevenNineLowProfile]
  have hqodd : Function.Odd (fun x : ℝ ↦ q.eval x) := by
    intro x
    dsimp only [q]
    simp only [Polynomial.eval_neg]
    rw [eval_centeredShiftedLegendreReal_neg]
    norm_num
  have heven : Function.Even (fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * q.eval x) := by
    intro x
    change yoshidaEndpointPotential (-x) * p.eval (-x) * q.eval (-x) =
      yoshidaEndpointPotential x * p.eval x * q.eval x
    rw [even_yoshidaEndpointPotential x]
    have hp' := hpodd x
    have hq' := hqodd x
    change p.eval (-x) = -p.eval x at hp'
    change q.eval (-x) = -q.eval x at hq'
    rw [hp', hq']
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x * q.eval x)
    hInt heven
  have hpair := endpointPotentialPolynomialPair_fiveMode_P11_eq c d e f g
  change endpointPotentialPolynomialPair p q = _ at hpair
  unfold endpointPotentialPolynomialPair at hpair
  rw [hpair] at hfold
  have hloweval (x : ℝ) : p.eval x =
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x := by
    exact fiveModeCenteredLegendrePolynomial_eval c d e f g x
  have htaileval (x : ℝ) : q.eval x = fourCellOddP11DirectTail x := by
    dsimp only [q]
    unfold fourCellOddP11DirectTail
    simp
  have hhalf : (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * p.eval x * q.eval x) =
        c / 130 + d / 120 + e / 102 + f / 76 + g / 42 := by
    linarith
  calc
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x *
        fourCellOddP11DirectTail x) =
        ∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * p.eval x * q.eval x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change yoshidaEndpointPotential x *
          fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x *
            fourCellOddP11DirectTail x =
        yoshidaEndpointPotential x * p.eval x * q.eval x
      rw [hloweval, htaileval]
    _ = _ := hhalf

/-- Common exact formula for the five retained coordinates against `P₁₁`.
The last term is the sole smooth-kernel remainder. -/
theorem fourCellOddCoreLocalBilinear_fiveMode_P11_eq
    (c d e f g : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        fourCellOddP11DirectTail =
      (93 / 6500 : ℝ) * c +
      (4502146249 / 292968750000 : ℝ) * d +
      (12448527116141 / 778198242187500 : ℝ) * e +
      (1683915269078387 / 101470947265625000 : ℝ) * f +
      (905665116028339 / 28610229492187500 : ℝ) * g +
      (Real.sqrt 2 * Real.log 2) *
        ((-(11639832 / 1220703125 : ℝ)) * c -
          (426354232 / 30517578125 : ℝ) * d -
          (12942923992 / 762939453125 : ℝ) * e -
          (209841256952 / 19073486328125 : ℝ) * f +
          (1843324002408 / 476837158203125 : ℝ) * g) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) := by
  rcases fourCellOddP11DirectTail_moments with
    ⟨h1, h3, h5, h7, h9⟩
  have hrow := fourCellOddCoreLocalBilinear_fiveMode_P11Plus_fullyReduced
    fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
    odd_fourCellOddP11DirectTail h1 h3 h5 h7 h9 c d e f g
  change fourCellOddCoreLocalBilinear
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
      fourCellOddP11DirectTail =
    -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
      fourCellOddP11DirectTail +
    fourCellOddRetainedPrimePotentialBilinear
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
      fourCellOddP11DirectTail -
    2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) at hrow
  unfold fourCellOddRetainedPrimePotentialBilinear at hrow
  rw [fourCellOddEndpointStripOddRawPolarization_fiveMode_P11_eq,
    fourCellOddEndpointStripEvenMassBilinear_fiveMode_P11_eq,
    fourCellOddEndpointStripOddMassBilinear_fiveMode_P11_eq,
    integral_endpointPotential_fiveMode_mul_P11_eq] at hrow
  rw [hrow]
  ring

/-- Structural square bound for the sole smooth remainder in every retained
coordinate.  No kernel sampling or tail truncation is used. -/
theorem fourCellOddP11CoreRegularMoment_fiveMode_sq_le
    (c d e f g : ℝ) :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 *
        factorTwoIntrinsicEnergy
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) *
        (2 / 23 : ℝ) := by
  rcases fourCellOddP11DirectTail_moments with
    ⟨h1, h3, h5, h7, h9⟩
  have hsigned :=
    fourCellOddSignedMassRegularBilinear_fiveMode_tail_sq_le_energy_mul
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
      odd_fourCellOddP11DirectTail h1 h3 h5 h7 h9 c d e f g
  have hregular :=
    fourCellOddSignedMassRegularBilinear_fiveMode_tail_eq_regular
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
      odd_fourCellOddP11DirectTail h1 h3 h5 h7 h9 c d e f g
  change fourCellOddSignedMassRegularBilinear
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
      fourCellOddP11DirectTail =
    2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) at hregular
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
    (Or.inr odd_fourCellOddP11DirectTail)
  have htailEnergy :
      factorTwoIntrinsicEnergy fourCellOddP11DirectTail = (2 / 23 : ℝ) := by
    unfold factorTwoIntrinsicEnergy
    rw [hfold, integral_zero_one_fourCellOddP11DirectTail_sq]
    norm_num
  rw [hregular, htailEnergy] at hsigned
  exact hsigned

private theorem fiveMode_one_eq_centeredP1 :
    fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_three_eq_centeredP3 :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0 = centeredP3 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_five_eq_centeredP5 :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0 =
      factorTwoCenteredP5 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_seven_eq_centeredP7 :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0 =
      factorTwoCenteredP7 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_nine_eq_centeredP9 :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1 =
      factorTwoCenteredP9 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem factorTwoIntrinsicEnergy_centeredP1_eq :
    factorTwoIntrinsicEnergy centeredP1 = (2 / 3 : ℝ) := by
  unfold factorTwoIntrinsicEnergy
  rw [integral_centeredP1_sq]

private theorem factorTwoIntrinsicEnergy_centeredP3_eq :
    factorTwoIntrinsicEnergy centeredP3 = (2 / 7 : ℝ) := by
  unfold factorTwoIntrinsicEnergy
  rw [integral_centeredP3_sq]

private theorem factorTwoIntrinsicEnergy_centeredP5_eq :
    factorTwoIntrinsicEnergy factorTwoCenteredP5 = (2 / 11 : ℝ) := by
  simpa only [factorTwoIntrinsicEnergy] using integral_factorTwoCenteredP5_sq

/-- The five exact off-diagonal entries of the augmented Galerkin block. -/
theorem fourCellOddCoreLocalBilinear_P1_P11_eq :
    fourCellOddCoreLocalBilinear centeredP1 fourCellOddP11DirectTail =
      (93 / 6500 : ℝ) -
      (11639832 / 1220703125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment centeredP1 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_P11_eq 1 0 0 0 0
  rw [fiveMode_one_eq_centeredP1] at h
  rw [h]
  ring

theorem fourCellOddCoreLocalBilinear_P3_P11_eq :
    fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail =
      (4502146249 / 292968750000 : ℝ) -
      (426354232 / 30517578125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment centeredP3 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_P11_eq 0 1 0 0 0
  rw [fiveMode_three_eq_centeredP3] at h
  rw [h]
  ring

theorem fourCellOddCoreLocalBilinear_P5_P11_eq :
    fourCellOddCoreLocalBilinear factorTwoCenteredP5
        fourCellOddP11DirectTail =
      (12448527116141 / 778198242187500 : ℝ) -
      (12942923992 / 762939453125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP5 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_P11_eq 0 0 1 0 0
  rw [fiveMode_five_eq_centeredP5] at h
  rw [h]
  ring

theorem fourCellOddCoreLocalBilinear_P7_P11_eq :
    fourCellOddCoreLocalBilinear factorTwoCenteredP7
        fourCellOddP11DirectTail =
      (1683915269078387 / 101470947265625000 : ℝ) -
      (209841256952 / 19073486328125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP7 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_P11_eq 0 0 0 1 0
  rw [fiveMode_seven_eq_centeredP7] at h
  rw [h]
  ring

theorem fourCellOddCoreLocalBilinear_P9_P11_eq :
    fourCellOddCoreLocalBilinear factorTwoCenteredP9
        fourCellOddP11DirectTail =
      (905665116028339 / 28610229492187500 : ℝ) +
      (1843324002408 / 476837158203125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) -
      2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP9 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_P11_eq 0 0 0 0 1
  rw [fiveMode_nine_eq_centeredP9] at h
  rw [h]
  ring

/-- Rational square radii for the five smooth corrections. -/
theorem fourCellOddP11CoreRegularMoment_P1_sq_le :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment centeredP1) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 69 : ℝ) := by
  have h := fourCellOddP11CoreRegularMoment_fiveMode_sq_le 1 0 0 0 0
  rw [fiveMode_one_eq_centeredP1,
    factorTwoIntrinsicEnergy_centeredP1_eq] at h
  calc
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
        (2 / 3 : ℝ) * (2 / 23 : ℝ) := h
    _ = _ := by ring

theorem fourCellOddP11CoreRegularMoment_P3_sq_le :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment centeredP3) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 161 : ℝ) := by
  have h := fourCellOddP11CoreRegularMoment_fiveMode_sq_le 0 1 0 0 0
  rw [fiveMode_three_eq_centeredP3,
    factorTwoIntrinsicEnergy_centeredP3_eq] at h
  calc
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
        (2 / 7 : ℝ) * (2 / 23 : ℝ) := h
    _ = _ := by ring

theorem fourCellOddP11CoreRegularMoment_P5_sq_le :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment factorTwoCenteredP5) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 253 : ℝ) := by
  have h := fourCellOddP11CoreRegularMoment_fiveMode_sq_le 0 0 1 0 0
  rw [fiveMode_five_eq_centeredP5,
    factorTwoIntrinsicEnergy_centeredP5_eq] at h
  calc
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
        (2 / 11 : ℝ) * (2 / 23 : ℝ) := h
    _ = _ := by ring

theorem fourCellOddP11CoreRegularMoment_P7_sq_le :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment factorTwoCenteredP7) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 345 : ℝ) := by
  have h := fourCellOddP11CoreRegularMoment_fiveMode_sq_le 0 0 0 1 0
  rw [fiveMode_seven_eq_centeredP7, factorTwoCenteredP7_energy] at h
  calc
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
        (2 / 15 : ℝ) * (2 / 23 : ℝ) := h
    _ = _ := by ring

theorem fourCellOddP11CoreRegularMoment_P9_sq_le :
    (2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment factorTwoCenteredP9) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 437 : ℝ) := by
  have h := fourCellOddP11CoreRegularMoment_fiveMode_sq_le 0 0 0 0 1
  rw [fiveMode_nine_eq_centeredP9, factorTwoCenteredP9_energy] at h
  calc
    _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
        (2 / 19 : ℝ) * (2 / 23 : ℝ) := h
    _ = _ := by ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
