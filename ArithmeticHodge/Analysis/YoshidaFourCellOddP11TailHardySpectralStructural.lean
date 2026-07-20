import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailConcentrationClosureStructural

set_option autoImplicit false

open Filter MeasureTheory Polynomial Real Set Topology

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural

noncomputable section

open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialLegendreDiagonalStructural
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

/-- The classical-sign centered Legendre polynomial.  The project's shifted
convention differs by a minus sign in odd degree. -/
def fourCellOddP11BoundaryClassicalMode (n : ℕ) : ℝ[X] :=
  -(centeredShiftedLegendreReal n)

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

def fourCellOddP11BoundaryRepresenter : ℝ → ℝ := fun x ↦
  fourCellOddP11BoundaryRepresenterPolynomial.eval x

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
  rw [eval_centeredShiftedLegendreReal_one]
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

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural
