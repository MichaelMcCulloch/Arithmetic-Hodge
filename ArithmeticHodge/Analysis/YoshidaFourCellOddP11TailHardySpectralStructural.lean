import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import ArithmeticHodge.Analysis.ShiftedLegendrePolynomialGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge
import ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailConcentrationClosureStructural

set_option autoImplicit false

open Filter MeasureTheory Polynomial Real Set Topology
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural

noncomputable section

open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open ShiftedLegendreLogEigen
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointPotentialBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11TailConcentrationClosureStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellRawParityFoldStructural

/-!
# A global spectral probe for the proposed odd tail Hardy inequality

The remaining Hardy residual was stated with the endpoint potential only on
`[3/5,1]`.  For an odd profile the potential on `[0,1]` is one half of the
global even potential, whose matrix is already available in exact centered
Legendre coordinates.  On `[0,3/5]` the potential is at most `1/4`.

Consequently a negative value of the quadratic form below is an exact
counterexample to `FourCellOddP11TailHardyConcentration`.  This bridge is
useful for adversarial work because it replaces the truncated singular
integral by a global spectral form; it introduces no finite-mode assumption.
-/

/-- Legendre-friendly upper majorant of the retained Hardy residual.  The
lower-mass coefficient is `73077/20000 - (93/100)(1/4) = 68427/20000`.
The global potential has coefficient `93/200` because odd parity folds it
into twice its positive-half value. -/
def fourCellOddP11GlobalHardyProbe (r : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve r -
    (68427 / 20000 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) +
    (2813 / 20000 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    (93 / 200 : ℝ) *
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2)

/-- The actual upper-strip potential is bounded below by the global odd
potential minus the certified lower-strip loss. -/
theorem globalPotential_sub_quarterLowerMass_le_upperPotential
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    (1 / 2 : ℝ) *
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2) -
        (1 / 4 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) ≤
      ∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * r x ^ 2 := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf r hr (Or.inr hodd)
  have hsplit := positiveHalfPotential_eq_lower_add_upper r hr
  have hlower := lowerPotential_le_oneQuarter_lowerMass r hr
  linarith

/-- The global spectral probe really is an upper bound for the proposed
Hardy residual.  Thus negativity of the probe is stronger than negativity
of the original residual. -/
theorem tailHardyResidual_le_globalHardyProbe
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    fourCellOddP11TailHardyResidual r ≤
      fourCellOddP11GlobalHardyProbe r := by
  have hpotential :=
    globalPotential_sub_quarterLowerMass_le_upperPotential r hr hodd
  unfold fourCellOddP11TailHardyResidual
    fourCellOddP11RetainedHardySurplus
    fourCellOddP11GlobalHardyProbe
  linarith

/-- A single genuine `P₁₁+` profile with negative global probe refutes
the remaining Hardy premise.  This is the exact adversarial target for a
structural Legendre or endpoint-concentration construction. -/
theorem not_tailHardyConcentration_of_globalProbe_neg
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (hneg : fourCellOddP11GlobalHardyProbe r < 0) :
    ¬ FourCellOddP11TailHardyConcentration := by
  intro hHardy
  have hresidual := hHardy r hr hodd h1 h3 h5 h7 h9
  have hprobe := tailHardyResidual_le_globalHardyProbe r hr.continuous hodd
  linarith

/-- Conversely, the proposed universal Hardy statement forces the global
probe to be nonnegative on every profile in the exact `P₁₁+` sector.
This convenient contrapositive-free form lets a spectral calculation target
one named scalar. -/
theorem globalHardyProbe_nonneg_of_tailHardyConcentration
    (hHardy : FourCellOddP11TailHardyConcentration)
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    0 ≤ fourCellOddP11GlobalHardyProbe r := by
  have hresidual := hHardy r hr hodd h1 h3 h5 h7 h9
  exact hresidual.trans
    (tailHardyResidual_le_globalHardyProbe r hr.continuous hodd)

/-!
## Removing the reciprocal strip weight

On `[3/5,1]` the elementary tangent-line inequality
`2 - x \le 1 / x` is exact to second order at the endpoint.  Replacing the
reciprocal by this affine minorant preserves the direction needed for a
counterexample and leaves only polynomial interval integrals.
-/

/-- Affine version of the global Hardy probe.  Unlike the original probe,
all its strip-mass integrands are polynomial whenever `r` is polynomial. -/
def fourCellOddP11AffineHardyProbe (r : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve r -
    (68427 / 20000 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, (2 - x) * r x ^ 2) +
    (2813 / 20000 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    (93 / 200 : ℝ) *
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2)

/-- The reciprocal upper-strip mass dominates its endpoint tangent-line
minorant. -/
theorem upperStripAffineMass_le_weightedMass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 3 / 5..1, (2 - x) * r x ^ 2) ≤
      ∫ x : ℝ in 3 / 5..1, r x ^ 2 / x := by
  have haffine : IntervalIntegrable (fun x : ℝ ↦ (2 - x) * r x ^ 2)
      volume (3 / 5) 1 := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      (2 - x) * r x ^ 2)).intervalIntegrable _ _
  have hweighted : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2 / x)
      volume (3 / 5) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (hr.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simpa only [id_eq] using (by linarith [hx.1] : x ≠ 0)
  apply intervalIntegral.integral_mono_on (by norm_num) haffine hweighted
  intro x hx
  have hxpos : 0 < x := by linarith [hx.1]
  rw [div_eq_mul_inv]
  have hinv : 2 - x ≤ x⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hxpos]
    nlinarith [sq_nonneg (x - 1)]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right hinv (sq_nonneg (r x))

/-- The affine probe is an upper bound for the reciprocal probe.  Hence a
negative affine value is already a structural countercertificate. -/
theorem globalHardyProbe_le_affineHardyProbe
    (r : ℝ → ℝ) (hr : Continuous r) :
    fourCellOddP11GlobalHardyProbe r ≤
      fourCellOddP11AffineHardyProbe r := by
  have hmass := upperStripAffineMass_le_weightedMass r hr
  unfold fourCellOddP11GlobalHardyProbe fourCellOddP11AffineHardyProbe
  linarith

/-- A negative affine probe on a genuine `P₁₁+` profile refutes the retained
Hardy concentration premise without evaluating a reciprocal integral. -/
theorem not_tailHardyConcentration_of_affineProbe_neg
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (hneg : fourCellOddP11AffineHardyProbe r < 0) :
    ¬ FourCellOddP11TailHardyConcentration := by
  apply not_tailHardyConcentration_of_globalProbe_neg r hr hodd h1 h3 h5 h7 h9
  exact (globalHardyProbe_le_affineHardyProbe r hr.continuous).trans_lt hneg

/-- For an odd `C¹` profile, the raw reserve is exactly the global centered
logarithmic energy minus the reflection-odd energy removed on the endpoint
strip.  This exposes both spectral pieces without estimating either one. -/
theorem rawStripCancellationReserve_eq_global_sub_strip
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddRawStripCancellationReserve r =
      (1 / 4 : ℝ) * centeredRawLogEnergy r -
        (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy r := by
  have hfold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd r
    (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)) hodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfold]
  ring

/-- Exact polynomial normal form of the affine probe.  The only nonlocal
objects left are two logarithmic energies and the global endpoint-potential
pair; all interval terms are ordinary polynomial moments. -/
theorem affineHardyProbe_polynomial_eq
    (p : ℝ[X]) (hodd : Function.Odd fun x : ℝ ↦ p.eval x) :
    fourCellOddP11AffineHardyProbe (fun x : ℝ ↦ p.eval x) =
      (1 / 4 : ℝ) * centeredRawLogEnergy (fun x : ℝ ↦ p.eval x) -
        (1 / 2 : ℝ) *
          fourCellOddEndpointStripOddRawEnergy (fun x : ℝ ↦ p.eval x) -
        (68427 / 20000 : ℝ) *
          (∫ x : ℝ in 0..3 / 5, (p.eval x) ^ 2) -
        (6 / 5 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, (2 - x) * (p.eval x) ^ 2) +
        (2813 / 20000 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, (p.eval x) ^ 2) -
        (93 / 200 : ℝ) * endpointPotentialPolynomialPair p p := by
  rw [fourCellOddP11AffineHardyProbe,
    rawStripCancellationReserve_eq_global_sub_strip
      (fun x : ℝ ↦ p.eval x) (p.contDiff_aeval (𝕜 := ℝ) 1) hodd]
  unfold endpointPotentialPolynomialPair
  congr 2
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- A small rational component box suffices for negativity of the affine
probe.  These five bounds are independent structural targets: raw reserve,
lower mass, affine upper mass, ordinary upper mass, and global potential. -/
theorem affineHardyProbe_neg_of_component_box
    (r : ℝ → ℝ)
    (hraw : fourCellOddRawStripCancellationReserve r ≤ 11 / 100)
    (hlower : (195 / 1000000 : ℝ) ≤
      ∫ x : ℝ in 0..3 / 5, r x ^ 2)
    (haffine : (2448 / 100000 : ℝ) ≤
      ∫ x : ℝ in 3 / 5..1, (2 - x) * r x ^ 2)
    (hupper : (∫ x : ℝ in 3 / 5..1, r x ^ 2) ≤
      (2411 / 100000 : ℝ))
    (hpotential : (17945 / 100000 : ℝ) ≤
      ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2) :
    fourCellOddP11AffineHardyProbe r < 0 := by
  unfold fourCellOddP11AffineHardyProbe
  norm_num at hraw hlower haffine hupper hpotential ⊢
  linarith

/-! The diagonal endpoint-potential recurrence also admits a compact closed
form.  This is useful below because it separates the single transcendental
constant `log 2` from rational harmonic data at every degree. -/

theorem endpointPotentialLegendreDiagonal_closed (n : ℕ) :
    endpointPotentialLegendreDiagonal n =
      (4 * ((harmonic (2 * n) : ℝ) - (harmonic n : ℝ)) +
          2 / (2 * (n : ℝ) + 1) - 2 * Real.log 2) /
        (2 * (n : ℝ) + 1) := by
  induction n with
  | zero =>
      rw [endpointPotentialLegendreDiagonal_zero]
      norm_num [harmonic]
  | succ n ih =>
      have hrec := endpointPotentialLegendreDiagonal_succ n
      rw [ih] at hrec
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        harmonic_succ (2 * n + 1), harmonic_succ (2 * n),
        harmonic_succ n]
      push_cast at hrec ⊢
      field_simp at hrec ⊢
      nlinarith

private theorem endpointPotentialPolynomialPair_finset_sum_left
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℝ[X]) (q : ℝ[X]) :
    endpointPotentialPolynomialPair (∑ i ∈ s, p i) q =
      ∑ i ∈ s, endpointPotentialPolynomialPair (p i) q := by
  induction s using Finset.induction_on with
  | empty => simp [endpointPotentialPolynomialPair]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        endpointPotentialPolynomialPair_add_left, ih]

private theorem endpointPotentialPolynomialPair_finset_sum_right
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ℝ[X]) (q : ι → ℝ[X]) :
    endpointPotentialPolynomialPair p (∑ i ∈ s, q i) =
      ∑ i ∈ s, endpointPotentialPolynomialPair p (q i) := by
  induction s using Finset.induction_on with
  | empty => simp [endpointPotentialPolynomialPair]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        endpointPotentialPolynomialPair_add_right, ih]

/-- Coefficient-wise exact integral of a real polynomial on an arbitrary
interval.  This packages all ordinary moment calculations into one finite
algebraic functional. -/
def polynomialIntervalIntegral (p : ℝ[X]) (a b : ℝ) : ℝ :=
  p.sum fun n c ↦
    c * ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1 : ℝ))

theorem integral_polynomial_eval_eq_intervalFunctional
    (p : ℝ[X]) (a b : ℝ) :
    (∫ x : ℝ in a..b, p.eval x) = polynomialIntervalIntegral p a b := by
  unfold polynomialIntervalIntegral
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul,
      YoshidaEndpointOcticPotential.integral_pow_nat]
  · intro n hn
    exact (by fun_prop : Continuous (fun x : ℝ ↦ p.coeff n * x ^ n)).intervalIntegrable _ _

/-!
## Endpoint-concentration no-go

A pure endpoint packet does not furnish the sought counterdirection.  In the
canonical logarithmic scaling, the retained raw-strip reserve contributes
`1/2`, while the full endpoint potential contributes only `93/200`.  The
remaining scalar terms are lower order, leaving the strictly positive
coefficient `7/200`.

The theorem below isolates that coefficient algebraically.  It deliberately
makes no model-specific assertion that a given family has these asymptotics;
once those five limits are known, however, positivity is forced and no
pointwise or finite-mode calculation can reverse it.
-/

/-- Under the canonical endpoint-packet asymptotics, the normalized global
Hardy probe converges to the positive gap `7/200`.  Thus a counterexample must
use a finite-scale correlation (in practice, the `3/5` strip boundary), not
mere concentration at the two endpoints. -/
theorem globalHardyProbe_normalized_endpointLimit
    (r : ℕ → ℝ → ℝ) (scale : ℕ → ℝ)
    (hscale : ∀ n, scale n ≠ 0)
    (hraw : Tendsto (fun n ↦
      fourCellOddRawStripCancellationReserve (r n) / scale n)
      atTop (nhds (1 / 2 : ℝ)))
    (hlower : Tendsto (fun n ↦
      (∫ x : ℝ in 0..3 / 5, r n x ^ 2) / scale n)
      atTop (nhds 0))
    (hweighted : Tendsto (fun n ↦
      (∫ x : ℝ in 3 / 5..1, r n x ^ 2 / x) / scale n)
      atTop (nhds 0))
    (hupper : Tendsto (fun n ↦
      (∫ x : ℝ in 3 / 5..1, r n x ^ 2) / scale n)
      atTop (nhds 0))
    (hpotential : Tendsto (fun n ↦
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * r n x ^ 2) / scale n)
      atTop (nhds 1)) :
    Tendsto (fun n ↦
      fourCellOddP11GlobalHardyProbe (r n) / scale n)
      atTop (nhds (7 / 200 : ℝ)) := by
  have hlimit :=
    (((hraw.sub (hlower.const_mul (68427 / 20000 : ℝ))).sub
      (hweighted.const_mul (6 / 5 : ℝ))).add
      (hupper.const_mul (2813 / 20000 : ℝ))).sub
      (hpotential.const_mul (93 / 200 : ℝ))
  convert hlimit using 1
  · funext n
    unfold fourCellOddP11GlobalHardyProbe
    field_simp [hscale n]
  · norm_num

/-- Consequently the normalized probe is eventually strictly positive in
every canonical endpoint-packet regime. -/
theorem eventually_globalHardyProbe_normalized_pos_of_endpointLimit
    (r : ℕ → ℝ → ℝ) (scale : ℕ → ℝ)
    (hscale : ∀ n, scale n ≠ 0)
    (hraw : Tendsto (fun n ↦
      fourCellOddRawStripCancellationReserve (r n) / scale n)
      atTop (nhds (1 / 2 : ℝ)))
    (hlower : Tendsto (fun n ↦
      (∫ x : ℝ in 0..3 / 5, r n x ^ 2) / scale n)
      atTop (nhds 0))
    (hweighted : Tendsto (fun n ↦
      (∫ x : ℝ in 3 / 5..1, r n x ^ 2 / x) / scale n)
      atTop (nhds 0))
    (hupper : Tendsto (fun n ↦
      (∫ x : ℝ in 3 / 5..1, r n x ^ 2) / scale n)
      atTop (nhds 0))
    (hpotential : Tendsto (fun n ↦
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * r n x ^ 2) / scale n)
      atTop (nhds 1)) :
    ∀ᶠ n in atTop,
      0 < fourCellOddP11GlobalHardyProbe (r n) / scale n := by
  have hlimit := globalHardyProbe_normalized_endpointLimit r scale hscale
    hraw hlower hweighted hupper hpotential
  exact (tendsto_order.1 hlimit).1 0 (by norm_num)

/-!
## A strip-boundary representer candidate

The negative numerical direction is not an arbitrary dense vector.  Its
coefficients lie very close to the six-dimensional span generated by value
and normal-derivative representers at the strip boundary `3/5`, together
with the corresponding endpoint rows.  The rational profile below records
that structure directly.  No list of mode coefficients is expanded.
-/

/-- Exact bridge from a centered polynomial profile to the diagonal
unit-interval logarithmic form. -/
private theorem centeredRawLogEnergy_eq_four_mul_shiftedPair
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

private theorem shiftedLogEnergyBilinear_legendre_eq (m n : ℕ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) =
      if m = n then
        2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1)
      else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl,
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
      shiftedLogKernel_shiftedLegendreReal]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (fun x : ℝ ↦
        (shiftedLegendreReal m).eval x *
          (2 * (harmonic m : ℝ) * (shiftedLegendreReal m).eval x)) =
        fun x ↦ (2 * (harmonic m : ℝ)) *
          ((shiftedLegendreReal m).eval x ^ 2) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      integral_shiftedLegendreReal_sq_closed]
    ring
  · rw [if_neg hmn,
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
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

private theorem shiftedLogEnergyBilinear_oddPacket
    (N : ℕ) (a : ℕ → ℝ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (∑ k ∈ Finset.range N,
          a k • (-(shiftedLegendreReal (11 + 2 * k))))
        (∑ k ∈ Finset.range N,
          a k • (-(shiftedLegendreReal (11 + 2 * k)))) =
      ∑ k ∈ Finset.range N,
        a k ^ 2 *
          (2 * (harmonic (11 + 2 * k) : ℝ) /
            (2 * ((11 + 2 * k : ℕ) : ℝ) + 1)) := by
  classical
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, map_neg, LinearMap.neg_apply,
    shiftedLogEnergyBilinear_legendre_eq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · simp
    ring
  · intro j hj hjk
    have hdegree : 11 + 2 * j ≠ 11 + 2 * k := by omega
    rw [if_neg hdegree]
    ring
  · exact fun hnot ↦ (hnot hk).elim

/-- The classical-sign centered Legendre polynomial.  The project's shifted
convention differs by a minus sign in odd degree. -/
def fourCellOddP11BoundaryClassicalMode (n : ℕ) : ℝ[X] :=
  -(centeredShiftedLegendreReal n)

/-- Exact endpoint-potential matrix entry for two degrees in the odd packet.
The diagonal uses the recurrence above; the off-diagonal is the Green
spectral-gap kernel. -/
def fourCellOddP11BoundaryEndpointEntry (i j : ℕ) : ℝ :=
  if i = j then endpointPotentialLegendreDiagonal (11 + 2 * i)
  else if i < j then
    2 / ((((11 + 2 * j : ℕ) : ℝ) - (11 + 2 * i : ℕ)) *
      (((11 + 2 * j : ℕ) : ℝ) + (11 + 2 * i : ℕ) + 1))
  else
    2 / ((((11 + 2 * i : ℕ) : ℝ) - (11 + 2 * j : ℕ)) *
      (((11 + 2 * i : ℕ) : ℝ) + (11 + 2 * j : ℕ) + 1))

private theorem endpointPotentialPolynomialPair_boundaryClassicalMode
    (i j : ℕ) :
    endpointPotentialPolynomialPair
        (fourCellOddP11BoundaryClassicalMode (11 + 2 * i))
        (fourCellOddP11BoundaryClassicalMode (11 + 2 * j)) =
      fourCellOddP11BoundaryEndpointEntry i j := by
  have heven : Even ((11 + 2 * i) + (11 + 2 * j)) := by
    use 11 + i + j
    omega
  unfold fourCellOddP11BoundaryClassicalMode
  rw [endpointPotentialPolynomialPair_neg_left,
    endpointPotentialPolynomialPair_neg_right]
  simp only [neg_neg]
  by_cases hij : i = j
  · subst j
    rw [fourCellOddP11BoundaryEndpointEntry, if_pos rfl]
    rfl
  · rw [fourCellOddP11BoundaryEndpointEntry, if_neg hij]
    by_cases hlt : i < j
    · rw [if_pos hlt]
      unfold endpointPotentialPolynomialPair
      exact integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
        (by omega) heven
    · rw [if_neg hlt, endpointPotentialPolynomialPair_comm]
      unfold endpointPotentialPolynomialPair
      exact integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
        (by omega) (by simpa [Nat.add_comm] using heven)

/-- Rational six-representer coefficient at odd degree `n`. -/
def fourCellOddP11BoundaryRepresenterCoeff (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) - (n : ℝ) / 800 +
    ((1 / 3 : ℝ) - (n : ℝ) / 100) *
      (fourCellOddP11BoundaryClassicalMode n).eval (3 / 5) +
    ((1 / 120 : ℝ) - 3 * (n : ℝ) / 40000) *
      (fourCellOddP11BoundaryClassicalMode n).derivative.eval (3 / 5)

/-- Odd strip-boundary packet from degree eleven through degree 141.  Its
definition is one uniform spectral formula, not a coefficient table. -/
def fourCellOddP11BoundaryRepresenterPolynomial : ℝ[X] :=
  ∑ k ∈ Finset.range 66,
    fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) •
      fourCellOddP11BoundaryClassicalMode (11 + 2 * k)

/-- Exact Green-matrix formula for the packet's global endpoint-potential
pair.  Diagonal entries are supplied by the closed harmonic formula and all
off-diagonal entries by the Legendre Green identity. -/
theorem endpointPotentialPolynomialPair_boundaryRepresenter_eq :
    endpointPotentialPolynomialPair
        fourCellOddP11BoundaryRepresenterPolynomial
        fourCellOddP11BoundaryRepresenterPolynomial =
      ∑ i ∈ Finset.range 66, ∑ j ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * i) *
          fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * j) *
            fourCellOddP11BoundaryEndpointEntry i j := by
  unfold fourCellOddP11BoundaryRepresenterPolynomial
  rw [endpointPotentialPolynomialPair_finset_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [endpointPotentialPolynomialPair_smul_left,
    endpointPotentialPolynomialPair_finset_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [endpointPotentialPolynomialPair_smul_right,
    endpointPotentialPolynomialPair_boundaryClassicalMode]
  ring

/-- The same packet in unit-interval shifted Legendre coordinates. -/
def fourCellOddP11BoundaryRepresenterShiftedPolynomial : ℝ[X] :=
  ∑ k ∈ Finset.range 66,
    fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) •
      (-(shiftedLegendreReal (11 + 2 * k)))

/-- Shifted-coordinate polynomial of the reflection-odd endpoint-strip
pullback.  The two affine arguments are `3/5 + (2/5)t` and
`1 - (2/5)t`; this retains the strip involution exactly. -/
def fourCellOddP11BoundaryStripOddShiftedPolynomial : ℝ[X] :=
  (1 / 2 : ℝ) •
    (fourCellOddP11BoundaryRepresenterPolynomial.comp
        ((2 / 5 : ℝ) • X + C (3 / 5)) -
      fourCellOddP11BoundaryRepresenterPolynomial.comp
        ((-(2 / 5 : ℝ)) • X + C 1))

def fourCellOddP11BoundaryRepresenter : ℝ → ℝ := fun x ↦
  fourCellOddP11BoundaryRepresenterPolynomial.eval x

def fourCellOddP11BoundaryRepresenterSquarePolynomial : ℝ[X] :=
  fourCellOddP11BoundaryRepresenterPolynomial ^ 2

def fourCellOddP11BoundaryRepresenterAffineSquarePolynomial : ℝ[X] :=
  (C 2 - X) * fourCellOddP11BoundaryRepresenterSquarePolynomial

theorem integral_lower_boundaryRepresenter_sq_eq :
    (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11BoundaryRepresenter x ^ 2) =
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterSquarePolynomial 0 (3 / 5) := by
  rw [← integral_polynomial_eval_eq_intervalFunctional]
  apply intervalIntegral.integral_congr
  intro x hx
  unfold fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterSquarePolynomial
  simp only [Polynomial.eval_pow]

theorem integral_upper_boundaryRepresenter_sq_eq :
    (∫ x : ℝ in 3 / 5..1,
      fourCellOddP11BoundaryRepresenter x ^ 2) =
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterSquarePolynomial (3 / 5) 1 := by
  rw [← integral_polynomial_eval_eq_intervalFunctional]
  apply intervalIntegral.integral_congr
  intro x hx
  unfold fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterSquarePolynomial
  simp only [Polynomial.eval_pow]

theorem integral_affineUpper_boundaryRepresenter_sq_eq :
    (∫ x : ℝ in 3 / 5..1,
      (2 - x) * fourCellOddP11BoundaryRepresenter x ^ 2) =
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterAffineSquarePolynomial (3 / 5) 1 := by
  rw [← integral_polynomial_eval_eq_intervalFunctional]
  apply intervalIntegral.integral_congr
  intro x hx
  unfold fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterAffineSquarePolynomial
    fourCellOddP11BoundaryRepresenterSquarePolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

theorem integral_endpointPotential_boundaryRepresenter_sq_eq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        fourCellOddP11BoundaryRepresenter x ^ 2) =
      ∑ i ∈ Finset.range 66, ∑ j ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * i) *
          fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * j) *
            fourCellOddP11BoundaryEndpointEntry i j := by
  rw [← endpointPotentialPolynomialPair_boundaryRepresenter_eq]
  unfold endpointPotentialPolynomialPair fourCellOddP11BoundaryRepresenter
  apply intervalIntegral.integral_congr
  intro x hx
  ring

theorem centeredPullback_boundaryRepresenter_eq (t : ℝ) :
    centeredPullback fourCellOddP11BoundaryRepresenter t =
      fourCellOddP11BoundaryRepresenterShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterPolynomial
    fourCellOddP11BoundaryRepresenterShiftedPolynomial
    fourCellOddP11BoundaryClassicalMode
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul,
    Polynomial.eval_neg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_centeredShiftedLegendreReal]
  congr 3
  ring

theorem centeredPullback_boundaryStripOdd_eq (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd fourCellOddP11BoundaryRepresenter) t =
      fourCellOddP11BoundaryStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryStripOddShiftedPolynomial
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]
  ring_nf

/-- Exact all-degree harmonic formula for the packet's global raw energy.
The proof uses logarithmic-energy diagonalization and degree injectivity;
none of the sixty-six Legendre modes is expanded. -/
theorem centeredRawLogEnergy_boundaryRepresenter_eq :
    centeredRawLogEnergy fourCellOddP11BoundaryRepresenter =
      ∑ k ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) ^ 2 *
          (8 * (harmonic (11 + 2 * k) : ℝ) /
            (2 * ((11 + 2 * k : ℕ) : ℝ) + 1)) := by
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair
      fourCellOddP11BoundaryRepresenter
      fourCellOddP11BoundaryRepresenterShiftedPolynomial
      centeredPullback_boundaryRepresenter_eq,
    fourCellOddP11BoundaryRepresenterShiftedPolynomial,
    shiftedLogEnergyBilinear_oddPacket]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Exact logarithmic form of the strip-odd subtraction after its affine
pullback.  This keeps the strip operator as one compact polynomial rather
than expanding its shifted-Legendre coordinates. -/
theorem endpointStripOddRawEnergy_boundaryRepresenter_eq :
    fourCellOddEndpointStripOddRawEnergy
        fourCellOddP11BoundaryRepresenter =
      (4 / 5 : ℝ) *
        ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
          fourCellOddP11BoundaryStripOddShiftedPolynomial
          fourCellOddP11BoundaryStripOddShiftedPolynomial := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair
      (fourCellOddEndpointStripOdd fourCellOddP11BoundaryRepresenter)
      fourCellOddP11BoundaryStripOddShiftedPolynomial
      centeredPullback_boundaryStripOdd_eq]
  ring

theorem contDiff_fourCellOddP11BoundaryRepresenter :
    ContDiff ℝ 1 fourCellOddP11BoundaryRepresenter := by
  unfold fourCellOddP11BoundaryRepresenter
  exact fourCellOddP11BoundaryRepresenterPolynomial.contDiff_aeval
    (𝕜 := ℝ) 1

theorem odd_fourCellOddP11BoundaryRepresenter :
    Function.Odd fourCellOddP11BoundaryRepresenter := by
  intro x
  unfold fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterPolynomial
    fourCellOddP11BoundaryClassicalMode
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul,
    Polynomial.eval_neg, smul_eq_mul, eval_centeredShiftedLegendreReal_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hdegree : Odd (11 + 2 * k) := by
    rw [show 11 + 2 * k = 2 * (k + 5) + 1 by omega]
    exact odd_two_mul_add_one _
  rw [Odd.neg_one_pow hdegree]
  ring

/-- Exact structural formula for the complete raw reserve of the packet.
The global term is diagonal in the original Legendre coordinates, while the
single compact shifted polynomial retains every strip-boundary correlation. -/
theorem rawStripCancellationReserve_boundaryRepresenter_eq :
    fourCellOddRawStripCancellationReserve
        fourCellOddP11BoundaryRepresenter =
      (∑ k ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) ^ 2 *
          (2 * (harmonic (11 + 2 * k) : ℝ) /
            (2 * ((11 + 2 * k : ℕ) : ℝ) + 1))) -
      (2 / 5 : ℝ) *
        ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
          fourCellOddP11BoundaryStripOddShiftedPolynomial
          fourCellOddP11BoundaryStripOddShiftedPolynomial := by
  rw [rawStripCancellationReserve_eq_global_sub_strip
      fourCellOddP11BoundaryRepresenter
      contDiff_fourCellOddP11BoundaryRepresenter
      odd_fourCellOddP11BoundaryRepresenter,
    centeredRawLogEnergy_boundaryRepresenter_eq,
    endpointStripOddRawEnergy_boundaryRepresenter_eq,
    Finset.mul_sum]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro k hk
    ring
  · ring

/-- Fully algebraic scalar left after the structural reductions.  It contains
one diagonal harmonic sum, one compact shifted strip form, three coefficient
functionals, and the exact endpoint Green matrix. -/
def fourCellOddP11BoundaryAffineCertificate : ℝ :=
  (∑ k ∈ Finset.range 66,
      fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) ^ 2 *
        (2 * (harmonic (11 + 2 * k) : ℝ) /
          (2 * ((11 + 2 * k : ℕ) : ℝ) + 1))) -
    (2 / 5 : ℝ) *
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        fourCellOddP11BoundaryStripOddShiftedPolynomial
        fourCellOddP11BoundaryStripOddShiftedPolynomial -
    (68427 / 20000 : ℝ) *
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterSquarePolynomial 0 (3 / 5) -
    (6 / 5 : ℝ) *
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterAffineSquarePolynomial (3 / 5) 1 +
    (2813 / 20000 : ℝ) *
      polynomialIntervalIntegral
        fourCellOddP11BoundaryRepresenterSquarePolynomial (3 / 5) 1 -
    (93 / 200 : ℝ) *
      (∑ i ∈ Finset.range 66, ∑ j ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * i) *
          fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * j) *
            fourCellOddP11BoundaryEndpointEntry i j)

/-- Exact identification of the analytic affine probe with the single
structural certificate scalar. -/
theorem affineHardyProbe_boundaryRepresenter_eq :
    fourCellOddP11AffineHardyProbe fourCellOddP11BoundaryRepresenter =
      fourCellOddP11BoundaryAffineCertificate := by
  unfold fourCellOddP11AffineHardyProbe
    fourCellOddP11BoundaryAffineCertificate
  rw [rawStripCancellationReserve_boundaryRepresenter_eq,
    integral_lower_boundaryRepresenter_sq_eq,
    integral_affineUpper_boundaryRepresenter_sq_eq,
    integral_upper_boundaryRepresenter_sq_eq,
    integral_endpointPotential_boundaryRepresenter_sq_eq]

/-- Every centered Legendre coordinate below degree eleven annihilates the
boundary-representer packet.  This is an all-degree orthogonality argument;
the rational coefficient formula is never expanded. -/
theorem integral_boundaryRepresenter_mul_centeredMode_eq_zero
    (m : ℕ) (hm : m < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11BoundaryRepresenter x *
        (centeredShiftedLegendreReal m).eval x) = 0 := by
  have hterm (k : ℕ) :
      (∫ x : ℝ in -1..1,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) *
          (-(centeredShiftedLegendreReal (11 + 2 * k)).eval x *
            (centeredShiftedLegendreReal m).eval x)) = 0 := by
    have horth := centeredPolynomialPair_legendre_eq_zero
      (m := 11 + 2 * k) (n := m) (by omega)
    unfold centeredPolynomialPair at horth
    rw [intervalIntegral.integral_const_mul]
    rw [show (fun x : ℝ ↦
        -(centeredShiftedLegendreReal (11 + 2 * k)).eval x *
          (centeredShiftedLegendreReal m).eval x) = fun x ↦
        -((centeredShiftedLegendreReal (11 + 2 * k)).eval x *
          (centeredShiftedLegendreReal m).eval x) by
      funext x
      ring,
      intervalIntegral.integral_neg, horth]
    ring
  unfold fourCellOddP11BoundaryRepresenter
    fourCellOddP11BoundaryRepresenterPolynomial
    fourCellOddP11BoundaryClassicalMode
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul,
    Polynomial.eval_neg, smul_eq_mul]
  rw [show (fun x : ℝ ↦
      (∑ k ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) *
          -(centeredShiftedLegendreReal (11 + 2 * k)).eval x) *
          (centeredShiftedLegendreReal m).eval x) = fun x ↦
      ∑ k ∈ Finset.range 66,
        fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) *
          (-(centeredShiftedLegendreReal (11 + 2 * k)).eval x *
            (centeredShiftedLegendreReal m).eval x) by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring,
    intervalIntegral.integral_finset_sum]
  · exact Finset.sum_eq_zero (fun k hk ↦ hterm k)
  · intro k hk
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      fourCellOddP11BoundaryRepresenterCoeff (11 + 2 * k) *
        (-(centeredShiftedLegendreReal (11 + 2 * k)).eval x *
          (centeredShiftedLegendreReal m).eval x))).intervalIntegrable _ _

private theorem boundary_centeredP1_eq_neg_mode_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [ShiftedLegendreCenteredLowModes.eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem boundary_centeredP3_eq_neg_mode_three :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem boundary_centeredP5_eq_neg_mode_five :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5,
    Polynomial.smul_eq_C_mul]
  ring

private theorem boundary_centeredP7_eq_neg_mode_seven :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem boundary_centeredP9_eq_neg_mode_nine :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

/-- The six-representer packet is a genuine `P₁₁+` profile. -/
theorem fourCellOddP11BoundaryRepresenter_moments :
    centeredOddP1Coefficient fourCellOddP11BoundaryRepresenter = 0 ∧
    centeredOddP3Coefficient fourCellOddP11BoundaryRepresenter = 0 ∧
    centeredOddP5Coefficient fourCellOddP11BoundaryRepresenter = 0 ∧
    centeredOddP7Coefficient fourCellOddP11BoundaryRepresenter = 0 ∧
    centeredOddP9Coefficient fourCellOddP11BoundaryRepresenter = 0 := by
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient centeredOddP9Coefficient
  rw [boundary_centeredP1_eq_neg_mode_one,
    boundary_centeredP3_eq_neg_mode_three,
    boundary_centeredP5_eq_neg_mode_five,
    boundary_centeredP7_eq_neg_mode_seven,
    boundary_centeredP9_eq_neg_mode_nine]
  have h1 := integral_boundaryRepresenter_mul_centeredMode_eq_zero 1 (by omega)
  have h3 := integral_boundaryRepresenter_mul_centeredMode_eq_zero 3 (by omega)
  have h5 := integral_boundaryRepresenter_mul_centeredMode_eq_zero 5 (by omega)
  have h7 := integral_boundaryRepresenter_mul_centeredMode_eq_zero 7 (by omega)
  have h9 := integral_boundaryRepresenter_mul_centeredMode_eq_zero 9 (by omega)
  repeat' first
    | rw [show (fun x : ℝ ↦ fourCellOddP11BoundaryRepresenter x *
          -(centeredShiftedLegendreReal 1).eval x) = fun x ↦
        -(fourCellOddP11BoundaryRepresenter x *
          (centeredShiftedLegendreReal 1).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h1]
    | rw [show (fun x : ℝ ↦ fourCellOddP11BoundaryRepresenter x *
          -(centeredShiftedLegendreReal 3).eval x) = fun x ↦
        -(fourCellOddP11BoundaryRepresenter x *
          (centeredShiftedLegendreReal 3).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h3]
    | rw [show (fun x : ℝ ↦ fourCellOddP11BoundaryRepresenter x *
          -(centeredShiftedLegendreReal 5).eval x) = fun x ↦
        -(fourCellOddP11BoundaryRepresenter x *
          (centeredShiftedLegendreReal 5).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h5]
    | rw [show (fun x : ℝ ↦ fourCellOddP11BoundaryRepresenter x *
          -(centeredShiftedLegendreReal 7).eval x) = fun x ↦
        -(fourCellOddP11BoundaryRepresenter x *
          (centeredShiftedLegendreReal 7).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h7]
    | rw [show (fun x : ℝ ↦ fourCellOddP11BoundaryRepresenter x *
          -(centeredShiftedLegendreReal 9).eval x) = fun x ↦
        -(fourCellOddP11BoundaryRepresenter x *
          (centeredShiftedLegendreReal 9).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h9]
  norm_num

/-- Strict negativity of the one named algebraic certificate is the sole
remaining obligation needed to refute the retained Hardy mechanism. -/
theorem not_tailHardyConcentration_of_boundaryAffineCertificate_neg
    (hneg : fourCellOddP11BoundaryAffineCertificate < 0) :
    ¬ FourCellOddP11TailHardyConcentration := by
  rcases fourCellOddP11BoundaryRepresenter_moments with
    ⟨h1, h3, h5, h7, h9⟩
  apply not_tailHardyConcentration_of_affineProbe_neg
    fourCellOddP11BoundaryRepresenter
    contDiff_fourCellOddP11BoundaryRepresenter
    odd_fourCellOddP11BoundaryRepresenter h1 h3 h5 h7 h9
  rw [affineHardyProbe_boundaryRepresenter_eq]
  exact hneg

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural
