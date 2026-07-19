import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural

noncomputable section

open YoshidaEndpointPotentialBound
open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaEndpointPotentialOddCoercivity
open YoshidaEndpointOcticOddCoercivity
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointPullbackLipschitz
open YoshidaFourCellOddPolarPotentialStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFactorTwoPhaseIntrinsicRankResidualBound
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaRegularKernelBound
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection

/-!
# Sharp rank control for the odd four-cell strip operator

The previous pointwise polar payment used the deliberately loose estimate
`sinh (a x / 2) <= x / 3`.  At the production halfwidth one instead has the
rational bound `sinh (a x / 2) <= 7 x / 25`.  Combined with the quadratic
part of the endpoint potential, this lowers the cost of the complete odd
rank from `8 / 9` to `343 / 625` of one positive-half potential copy.
-/

/-- The exact positive base of the strip operator before subtracting its one
negative hyperbolic rank.  No regular-row, prime, or raw-energy term has been
estimated in this definition. -/
def fourCellOddStripCapacityBase (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w (-1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth

/-- Exact rank-one normal form of the retained strip operator. -/
theorem fourCellOddStripCapacityLowerOperator_eq_base_sub_rank
    (w : ℝ → ℝ) :
    fourCellOddStripCapacityLowerOperator w =
      fourCellOddStripCapacityBase w -
        8 * fourCellOperatorHalfWidth *
          fourCellPositiveSinhMoment w
            (fourCellOperatorHalfWidth / 2) ^ 2 := by
  unfold fourCellOddStripCapacityLowerOperator
    fourCellOddStripCapacityBase
  ring

/-- The rational diagonal allocation selected by the exact-row Schur
problem: a small scalar mass plus `7 / 50` of the endpoint potential. -/
def fourCellOddStripBlendedAllocation (w : ℝ → ℝ) : ℝ :=
  (3 / 200 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) +
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2)

/-- The exact raw/prime part of the odd strip base.  This is the global
positive-half raw form with only the adverse endpoint-strip prime channel
replaced by its sharp local gap. -/
def fourCellOddStripRetainedPrimeRawCapacity (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w (-1)

/-- The standard sharp odd raw/potential reserve, written entirely on the
positive half interval.  Its coefficient `14 / 5` is the half-interval form
of the structural `7 / 5` centered coercivity theorem. -/
def fourCellOddHalfCoreReserve (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    2 * (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    (14 / 5 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2)

/-- The known centered odd coercivity supplies a nonnegative core reserve
without a cutoff or a finite-dimensional computation. -/
theorem fourCellOddHalfCoreReserve_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddHalfCoreReserve w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hcoercive :=
    seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_endpointPotential
      w hw.continuous (by simpa only [f] using hfmem)
        (by simpa only [f] using henergy) hodd
        (intervalIntegrable_endpointPotential_mul_sq w hw.continuous)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  rw [hraw, hpotential, hmass] at hcoercive
  unfold fourCellOddHalfCoreReserve
  linarith

/-- Quantitative form of the centered odd core estimate.  Unlike the bare
`7 / 5` coercivity theorem, it retains the exact positive `P₁/P₃` Schur
quadratic after the whole infinite odd tail has been absorbed by its uniform
`53 / 60` reserve. -/
theorem oddOneThreeSchurQuadratic_le_centeredCore
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    schurS11 * centeredOddP1Coefficient w ^ 2 +
        2 * schurS13 * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        schurS33 * centeredOddP3Coefficient w ^ 2 ≤
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
        (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hlog := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hmass0 := integral_centeredOddOneThreeResidual_sq w hwcont
  have hmass :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        (2 / 3 : ℝ) * a ^ 2 + (2 / 7 : ℝ) * b ^ 2 +
          ∫ x : ℝ in -1..1, v x ^ 2 := by
    dsimp only [a, b, v]
    linarith
  have hpot := integral_octic_mul_sq_decomposition w hwcont
  have hgram := integral_combinedOcticResidual_sq w
  have htail := octic_residual_tail_nonneg w
  have hcompletion := tailReserve_completion w hwcont
  have hQ11 : rawLowQ11 =
      (1 - 7 / 5 : ℝ) * (2 / 3 : ℝ) + 13771 / 41580 := by
    norm_num [rawLowQ11]
  have hQ33 : rawLowQ33 =
      (11 / 6 - 7 / 5 : ℝ) * (2 / 7 : ℝ) + 23161 / 180180 := by
    norm_num [rawLowQ33]
  have hQ13 : rawLowQ13 = (8 / 65 : ℝ) := by
    rfl
  have hδ : tailReserve = 137 / 60 - 7 / 5 := by
    norm_num [tailReserve]
  have hSchurEq :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 =
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 -
        (residualGramC11 * a ^ 2 +
          2 * residualGramC13 * a * b + residualGramC33 * b ^ 2) /
            tailReserve := by
    unfold schurS11 schurS13 schurS33
    ring
  have hsecond :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 ≤
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
        tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
        2 * (∫ x : ℝ in -1..1, v x * r x) +
        ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 := by
    rw [hSchurEq]
    dsimp only [a, b, v, r] at hgram hcompletion htail ⊢
    rw [hgram] at hcompletion
    norm_num [tailReserve] at hcompletion ⊢
    linarith
  have hfirst :
      rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
          tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x * r x) +
          ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 ≤
        centeredRawLogEnergy w / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) -
          (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
    dsimp only [a, b, v, r] at hlog hmass hpot ⊢
    rw [hQ11, hQ13, hQ33, hδ]
    linarith
  have hocticInt : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (-1 : ℝ) ≤ 1) hocticInt hpotential
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply octic_le_endpointPotential
    rw [abs_lt]
    exact hx
  linarith [hsecond.trans hfirst]

/-- Positive-half form of the retained low-mode Schur reserve.  This is the
quantitative reserve available for absorbing the coupled four-cell local
width defect. -/
theorem oddOneThreeSchurQuadratic_le_fourCellOddHalfCoreReserve
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    schurS11 * centeredOddP1Coefficient w ^ 2 +
        2 * schurS13 * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        schurS33 * centeredOddP3Coefficient w ^ 2 ≤
      fourCellOddHalfCoreReserve w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hcenter := oddOneThreeSchurQuadratic_le_centeredCore
    w hw.continuous (by simpa only [f] using hfmem)
      (by simpa only [f] using henergy) hodd
      (intervalIntegrable_endpointPotential_mul_sq w hw.continuous)
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw.continuous (Or.inr hodd)
  rw [hraw, hpotential, hmass] at hcenter
  unfold fourCellOddHalfCoreReserve
  linarith

/-! ## Odd ground-state transform for the coupled raw kernels -/

/-- After writing an odd profile as `w x = x * u x`, the same-sign and
reflected raw kernels have an exact ground-state transform on the ordered
positive triangle.  The linear odd mode is the ground state, while every
deviation from it remains in the explicit positive square on the right. -/
theorem fourCellOddRawGroundStateKernel_eq
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    (x * u - y * v) ^ 2 / (x - y) +
        (x * u + y * v) ^ 2 / (x + y) =
      2 * x * u ^ 2 +
        (2 * x * y ^ 2 / ((x - y) * (x + y))) * (u - v) ^ 2 := by
  have hsub : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hsum : x + y ≠ 0 := by
    have hx : 0 < x := hy.trans_lt hxy
    positivity
  field_simp [hsub, hsum]
  ring

/-- The positive-square consequence of the odd raw ground-state transform.
This is the pointwise source of the sharp linear-mode raw gap. -/
theorem two_mul_oddGroundState_le_coupledRawKernel
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    2 * x * u ^ 2 ≤
      (x * u - y * v) ^ 2 / (x - y) +
        (x * u + y * v) ^ 2 / (x + y) := by
  rw [fourCellOddRawGroundStateKernel_eq hy hxy]
  have hx : 0 ≤ x := (hy.trans_lt hxy).le
  have hsub : 0 ≤ x - y := (sub_pos.mpr hxy).le
  have hsum : 0 ≤ x + y := add_nonneg hx hy
  have hcoefficient :
      0 ≤ 2 * x * y ^ 2 / ((x - y) * (x + y)) := by
    exact div_nonneg (by positivity) (mul_nonneg hsub hsum)
  nlinarith [mul_nonneg hcoefficient (sq_nonneg (u - v))]

/-! ## A signed regular-kernel reserve on the wider four-cell range -/

private def fourCellRegularLowerPolynomial (r : ℝ) : ℝ :=
  31 * r ^ 7 - 49 * r ^ 6 + 27 * r ^ 5 - 53 * r ^ 4 +
    37 * r ^ 3 - 43 * r ^ 2 + r + 1

private theorem fourCellRegularLowerPolynomial_nonpos
    {r : ℝ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8 / 5) :
    fourCellRegularLowerPolynomial r ≤ 0 := by
  let u : ℝ := (5 / 3 : ℝ) * (r - 1)
  have hu0 : 0 ≤ u := by
    have hr : 0 ≤ r - 1 := sub_nonneg.mpr hr1
    dsimp only [u]
    positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    linarith
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rw [show fourCellRegularLowerPolynomial r =
      -(48 * (1 - u) ^ 7 +
        (2064 / 5 : ℝ) * u * (1 - u) ^ 6 +
        (37296 / 25 : ℝ) * u ^ 2 * (1 - u) ^ 5 +
        2904 * u ^ 3 * (1 - u) ^ 4 +
        (2011008 / 625 : ℝ) * u ^ 4 * (1 - u) ^ 3 +
        (6041808 / 3125 : ℝ) * u ^ 5 * (1 - u) ^ 2 +
        (7870008 / 15625 : ℝ) * u ^ 6 * (1 - u) +
        (788043 / 78125 : ℝ) * u ^ 7) by
    dsimp only [u, fourCellRegularLowerPolynomial]
    ring]
  apply neg_nonpos.mpr
  positivity

/-- The regular kernel remains at least `1 / 5` on every argument produced
by the four-cell positive-half fold.  The proof is structural: the two-term
logarithm lower bound leaves one polynomial, whose Bernstein coefficients
on `1 ≤ exp (t/2) ≤ 8/5` are all negative. -/
theorem one_fifth_le_yoshidaRegularKernel_fourCellRange
    {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 5 * Real.log 2 / 4) :
    (1 / 5 : ℝ) ≤ yoshidaRegularKernel t := by
  by_cases ht : t = 0
  · norm_num [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let u : ℝ := t / 2
    let r : ℝ := Real.exp u
    have hu0 : 0 ≤ u := by
      dsimp only [u]
      linarith
    have hu7 : u ≤ 7 / 16 := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hu1 : u ≤ 1 := hu7.trans (by norm_num)
    have hexp := Real.exp_bound' hu0 hu1 (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at hexp
    have hexp8 : Real.exp u ≤ 8 / 5 := by
      calc
        Real.exp u ≤
            1 + u + u ^ 2 / 2 + u ^ 3 / 6 + 5 * u ^ 4 / 96 := by
          linarith
        _ ≤ 1 + (7 / 16 : ℝ) + (7 / 16 : ℝ) ^ 2 / 2 +
            (7 / 16 : ℝ) ^ 3 / 6 +
              5 * (7 / 16 : ℝ) ^ 4 / 96 := by
          gcongr
        _ ≤ 8 / 5 := by norm_num
    have hrpos : 0 < r := by
      dsimp only [r]
      positivity
    have hr1lt : 1 < r := by
      dsimp only [r, u]
      exact Real.one_lt_exp_iff.mpr (by linarith)
    have hr1 : 1 ≤ r := hr1lt.le
    have hr8 : r ≤ 8 / 5 := by
      simpa only [r] using hexp8
    have hrSq : r ^ 2 = Real.exp t := by
      dsimp only [r, u]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hrSqOne : 1 < r ^ 2 := by
      nlinarith [sq_nonneg (r - 1)]
    have hrFourthOne : 1 < r ^ 4 := by
      nlinarith [sq_nonneg (r ^ 2 - 1)]
    let z : ℝ := (r ^ 2 - 1) / (r ^ 2 + 1)
    have hzden : 0 < r ^ 2 + 1 := by positivity
    have hzpos : 0 < z := by
      dsimp only [z]
      exact div_pos (sub_pos.2 hrSqOne) hzden
    have hz0 : 0 ≤ z := hzpos.le
    have hz1 : z < 1 := by
      dsimp only [z]
      rw [div_lt_one hzden]
      linarith
    have hratio : (1 + z) / (1 - z) = r ^ 2 := by
      dsimp only [z]
      field_simp [ne_of_gt hzden]
      ring
    have hseries := Real.sum_range_le_log_div hz0 hz1 2
    norm_num [Finset.sum_range_succ] at hseries
    rw [hratio, hrSq, Real.log_exp] at hseries
    let A : ℝ := z + z ^ 3 / 3
    have hApos : 0 < A := by
      dsimp only [A]
      positivity
    have hAt : 2 * A ≤ t := by
      dsimp only [A]
      linarith
    have hrecip : 1 / (2 * t) ≤ 1 / (4 * A) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * t)
        (by positivity : 0 < 4 * A)]
      nlinarith
    have hP := fourCellRegularLowerPolynomial_nonpos hr1 hr8
    let D : ℝ := 80 * (r + 1) * (r ^ 2 + 1) *
      (r ^ 2 - r + 1) * (r ^ 2 + r + 1)
    have hminus : 0 < r ^ 2 - r + 1 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    have hplus : 0 < r ^ 2 + r + 1 := by nlinarith
    have hmulMinus : r * (r - 1) + 1 ≠ 0 := by nlinarith
    have hmulPlus : r * (r + 1) + 1 ≠ 0 := by nlinarith
    have hDpos : 0 < D := by
      dsimp only [D]
      positivity
    have hAformula : A =
        4 * (r - 1) * (r + 1) * (r ^ 2 - r + 1) *
          (r ^ 2 + r + 1) / (3 * (r ^ 2 + 1) ^ 3) := by
      dsimp only [A, z]
      field_simp [ne_of_gt hzden]
      ring
    have hremainder :
        0 ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 := by
      rw [show r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 =
          -fourCellRegularLowerPolynomial r / D by
        rw [hAformula]
        dsimp only [D]
        unfold fourCellRegularLowerPolynomial
        field_simp [ne_of_gt hrpos, ne_of_gt hzden,
          ne_of_gt (sub_pos.2 hrFourthOne), ne_of_gt hApos,
          ne_of_gt (sub_pos.2 hr1lt)]
        field_simp [hmulMinus, hmulPlus]
        ring]
      exact div_nonneg (neg_nonneg.mpr hP) hDpos.le
    have hkernel : yoshidaRegularKernel t =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) := by
      rw [yoshidaRegularKernel, if_neg ht, Real.sinh_eq, Real.exp_neg,
        ← hrSq]
      change r / (2 * ((r ^ 2 - (r ^ 2)⁻¹) / 2)) - 1 / (2 * t) =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t)
      field_simp [ne_of_gt hrpos, ne_of_gt (sub_pos.2 hrFourthOne)]
    rw [hkernel]
    calc
      (1 / 5 : ℝ) ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) := by
        linarith
      _ ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) :=
        sub_le_sub_left hrecip _

/-! ## Exact `P₁/P₃` local-width block -/

theorem fourCellOddEndpointStripEven_oddStructuralLow
    (c d z : ℝ) :
    fourCellOddEndpointStripEven
        (factorTwoOddStructuralLowProfile c d) z =
      (2 / 25 : ℝ) * (10 * c + d + 3 * d * z ^ 2) := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripOdd_oddStructuralLow
    (c d z : ℝ) :
    fourCellOddEndpointStripOdd
        (factorTwoOddStructuralLowProfile c d) z =
      z * (10 * c + 33 * d + d * z ^ 2) / 50 := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripEvenMass_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripEvenMass
        (factorTwoOddStructuralLowProfile c d) =
      (32 / 125 : ℝ) * c ^ 2 +
        2 * (32 / 625 : ℝ) * c * d +
        (192 / 15625 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripEvenMass
  simp_rw [fourCellOddEndpointStripEven_oddStructuralLow]
  rw [show (fun z : ℝ ↦
      ((2 / 25 : ℝ) * (10 * c + d + 3 * d * z ^ 2)) ^ 2) =
      fun z ↦
        ((4 / 625 : ℝ) * (10 * c + d) ^ 2) * z ^ 0 +
          ((24 / 625 : ℝ) * (10 * c + d) * d) * z ^ 2 +
          ((36 / 625 : ℝ) * d ^ 2) * z ^ 4 by
    funext z
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow_nat]
  norm_num
  ring

theorem fourCellOddEndpointStripOddMass_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripOddMass
        (factorTwoOddStructuralLowProfile c d) =
      (2 / 375 : ℝ) * c ^ 2 +
        2 * (56 / 3125 : ℝ) * c * d +
        (6586 / 109375 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripOddMass
  simp_rw [fourCellOddEndpointStripOdd_oddStructuralLow]
  rw [show (fun z : ℝ ↦
      (z * (10 * c + 33 * d + d * z ^ 2) / 50) ^ 2) =
      fun z ↦
        (((10 * c + 33 * d) ^ 2 / 2500 : ℝ)) * z ^ 2 +
          (((10 * c + 33 * d) * d / 1250 : ℝ)) * z ^ 4 +
          ((d ^ 2 / 2500 : ℝ)) * z ^ 6 by
    funext z
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow_nat]
  norm_num
  ring

theorem fourCellOddEndpointStripOdd_oddStructuralLow_eq_lowProfile
    (c d : ℝ) :
    fourCellOddEndpointStripOdd
        (factorTwoOddStructuralLowProfile c d) =
      factorTwoOddStructuralLowProfile
        (c / 5 + 84 * d / 125) (d / 125) := by
  funext z
  rw [fourCellOddEndpointStripOdd_oddStructuralLow]
  unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem fourCellOddEndpointStripOddRawEnergy_oddStructuralLow
    (c d : ℝ) :
    fourCellOddEndpointStripOddRawEnergy
        (factorTwoOddStructuralLowProfile c d) =
      (8 / 375 : ℝ) * c ^ 2 +
        2 * (224 / 3125 : ℝ) * c * d +
        (79036 / 328125 : ℝ) * d ^ 2 := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [fourCellOddEndpointStripOdd_oddStructuralLow_eq_lowProfile,
    centeredRawLogEnergy_factorTwoOddStructuralLowProfile]
  ring

theorem integral_zero_one_oddStructuralLow_sq
    (c d : ℝ) :
    (∫ x : ℝ in 0..1,
      factorTwoOddStructuralLowProfile c d x ^ 2) =
      (1 / 3 : ℝ) * c ^ 2 + (1 / 7 : ℝ) * d ^ 2 := by
  have hfull := integral_oddStructuralLow_sq c d
  have hhalf := integral_sq_eq_two_mul_positiveHalf
    (factorTwoOddStructuralLowProfile c d)
    (continuous_factorTwoOddStructuralLowProfile c d)
    (Or.inr (odd_factorTwoOddStructuralLowProfile c d))
  linarith

theorem integral_zero_one_endpointPotential_oddStructuralLow
    (c d : ℝ) :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        factorTwoOddStructuralLowProfile c d x ^ 2) =
      (4 / 9 - (1 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        (1 / 5 : ℝ) * c * d +
        (289 / 1470 - (1 / 7 : ℝ) * Real.log 2) * d ^ 2 := by
  have hfull := integral_endpointPotential_oddStructuralLow c d
  have hhalf := endpointPotential_eq_two_mul_positiveHalf
    (factorTwoOddStructuralLowProfile c d)
    (continuous_factorTwoOddStructuralLowProfile c d)
    (Or.inr (odd_factorTwoOddStructuralLowProfile c d))
  linarith

/-- The residual after extracting the known sharp odd core.  It contains
exactly the endpoint-strip prime modification, the wider scalar shift, the
retained regular completion, and the diagonal allocation used by the odd
rank Schur estimate.  No sign is asserted: these terms have to remain
coupled. -/
def fourCellOddStripCoreDefect (w : ℝ → ℝ) : ℝ :=
  fourCellOddStripRetainedPrimeRawCapacity w -
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth

/-- Correlation normal form of the same coupled defect.  It keeps the exact
wide regular kernel as one signed autocorrelation row, which is the useful
form for a direct comparison with the raw logarithmic reserve. -/
def fourCellOddStripCorrelationCoreDefect (w : ℝ → ℝ) : ℝ :=
  fourCellOddStripRetainedPrimeRawCapacity w -
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- Algebraic `(1,1)` entry of the exact local defect on `span(P₁,P₃)`,
before the wide regular autocorrelation is added. -/
def fourCellOddLowLocalAlgebraic11 : ℝ :=
  -(1 / 2 : ℝ) * (8 / 375) +
    Real.sqrt 2 * Real.log 2 * (32 / 125) +
    (2 - Real.sqrt 2 * Real.log 2) * (2 / 375) +
    ((14 / 5 : ℝ) -
      2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (1 / 3) -
    (7 / 50 : ℝ) * (4 / 9 - (1 / 3) * Real.log 2)

/-- Algebraic polarized `(1,3)` entry of the exact local low block. -/
def fourCellOddLowLocalAlgebraic13 : ℝ :=
  -(1 / 2 : ℝ) * (224 / 3125) +
    Real.sqrt 2 * Real.log 2 * (32 / 625) +
    (2 - Real.sqrt 2 * Real.log 2) * (56 / 3125) -
    (7 / 50 : ℝ) * (1 / 10)

/-- Algebraic `(3,3)` entry of the exact local defect on `span(P₁,P₃)`.
-/
def fourCellOddLowLocalAlgebraic33 : ℝ :=
  -(1 / 2 : ℝ) * (79036 / 328125) +
    Real.sqrt 2 * Real.log 2 * (192 / 15625) +
    (2 - Real.sqrt 2 * Real.log 2) * (6586 / 109375) +
    ((14 / 5 : ℝ) -
      2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (1 / 7) -
    (7 / 50 : ℝ) * (289 / 1470 - (1 / 7) * Real.log 2)

/-- Exact algebraic quadratic part of the local defect on the intrinsic odd
two-mode block. -/
def fourCellOddLowLocalAlgebraicQuadratic (c d : ℝ) : ℝ :=
  fourCellOddLowLocalAlgebraic11 * c ^ 2 +
    2 * fourCellOddLowLocalAlgebraic13 * c * d +
    fourCellOddLowLocalAlgebraic33 * d ^ 2

/-- Local normal form of the four-cell defect.  The global raw form cancels
exactly: only the removed strip-odd raw energy and its two retained prime
masses remain, together with the width scalar, allocation, and exact regular
correlation. -/
def fourCellOddStripLocalWidthDefect (w : ℝ → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    ((14 / 5 : ℝ) -
        2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) - 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    (7 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- Exact `P₁/P₃` normal form of the local four-cell defect.  Every
strip, potential, and scalar term is now an explicit `2 × 2` quadratic;
the only nonalgebraic entries left are the three wide regular-kernel moments.
-/
theorem fourCellOddStripLocalWidthDefect_oddStructuralLow_eq
    (c d : ℝ) :
    fourCellOddStripLocalWidthDefect
        (factorTwoOddStructuralLowProfile c d) =
      fourCellOddLowLocalAlgebraicQuadratic c d -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              (c ^ 2 * oddStructuralCorrelation11 t +
                2 * c * d * oddStructuralCorrelation13 t +
                d ^ 2 * oddStructuralCorrelation33 t)) := by
  unfold fourCellOddStripLocalWidthDefect
    fourCellOddLowLocalAlgebraicQuadratic
    fourCellOddLowLocalAlgebraic11 fourCellOddLowLocalAlgebraic13
    fourCellOddLowLocalAlgebraic33
  rw [fourCellOddEndpointStripOddRawEnergy_oddStructuralLow,
    fourCellOddEndpointStripEvenMass_oddStructuralLow,
    fourCellOddEndpointStripOddMass_oddStructuralLow,
    integral_zero_one_oddStructuralLow_sq,
    integral_zero_one_endpointPotential_oddStructuralLow]
  simp_rw [centeredEndpointCorrelation_oddStructuralLow]
  ring

/-- The endpoint-strip parity split cancels every nonlocal raw term outside
the strip from the core defect. -/
theorem fourCellOddStripCorrelationCoreDefect_eq_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellOddStripCorrelationCoreDefect w =
      fourCellOddStripLocalWidthDefect w := by
  have hstrip := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  unfold fourCellOddStripCorrelationCoreDefect
    fourCellOddStripLocalWidthDefect
    fourCellOddStripRetainedPrimeRawCapacity
  rw [hstrip]
  ring

/-- Exact conversion from the completed regular squares/row to the signed
autocorrelation row, valid on the odd form domain. -/
theorem fourCellOddStripCoreDefect_eq_correlation
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellOddStripCoreDefect w =
      fourCellOddStripCorrelationCoreDefect w := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha3 : fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
    have h := five_mul_log_two_div_four_lt_log_three
    unfold fourCellOperatorHalfWidth
    linarith
  have hregular :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_odd
      w hw hodd fourCellOperatorHalfWidth ha0 ha3
  unfold fourCellOddStripCoreDefect
    fourCellOddStripCorrelationCoreDefect
  linarith

/-- Exact decomposition of the outstanding base inequality into the known
nonnegative odd core and one genuinely coupled four-cell defect. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect
    (w : ℝ → ℝ) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w + fourCellOddStripCoreDefect w := by
  unfold fourCellOddStripCapacityBase
    fourCellOddStripBlendedAllocation fourCellOddHalfCoreReserve
    fourCellOddStripCoreDefect fourCellOddStripRetainedPrimeRawCapacity
  ring

/-- On odd profiles the outstanding base difference is the nonnegative
centered core plus the exact prime/width autocorrelation defect. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_correlationDefect
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w +
        fourCellOddStripCorrelationCoreDefect w := by
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect,
    fourCellOddStripCoreDefect_eq_correlation w hw hodd]

/-- Fully reduced structural form of the remaining odd base inequality. -/
theorem fourCellOddStripCapacityBase_sub_blended_eq_core_add_localWidthDefect
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddStripCapacityBase w -
        fourCellOddStripBlendedAllocation w =
      fourCellOddHalfCoreReserve w +
        fourCellOddStripLocalWidthDefect w := by
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_correlationDefect
      w hw.continuous hodd,
    fourCellOddStripCorrelationCoreDefect_eq_localWidthDefect w hw]

/-- The exact remaining odd base theorem is a coupled defect absorption:
the sharp centered reserve must dominate the negative part of the four-cell
width/prime defect. -/
theorem fourCellOddStripCapacityBase_ge_blended_of_core_defect
    (w : ℝ → ℝ)
    (hdefect : -fourCellOddStripCoreDefect w ≤
      fourCellOddHalfCoreReserve w) :
    fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w := by
  rw [← sub_nonneg]
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_defect]
  linarith

/-- Pointwise multiplication weight behind the blended allocation. -/
def fourCellOddStripSchurWeight (x : ℝ) : ℝ :=
  (3 / 200 : ℝ) + (7 / 50 : ℝ) * yoshidaEndpointPotential x

/-- A low-degree rational majorant for the dual Schur density. -/
def fourCellOddStripSchurPolynomial (x : ℝ) : ℝ :=
  (1 / 10 : ℝ) * x + (10 / 3 : ℝ) * x ^ 2 -
    (11 / 2 : ℝ) * x ^ 3 + (249 / 100 : ℝ) * x ^ 4

private def fourCellOddStripSchurQuarticDenominator (x : ℝ) : ℝ :=
  (3 / 200 : ℝ) + (7 / 100 : ℝ) * x ^ 2 +
    (7 / 200 : ℝ) * x ^ 4

private def fourCellOddStripSchurProductGapQuotient (x : ℝ) : ℝ :=
  (167328 * x ^ 7 - 369600 * x ^ 6 + 558656 * x ^ 5 -
      732480 * x ^ 4 + 519712 * x ^ 3 - 144960 * x ^ 2 +
      4125 * x + 2880) / 1920000

private theorem fourCellOddStripSchurProductGapQuotient_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ fourCellOddStripSchurProductGapQuotient x := by
  rcases le_total x (1 / 3 : ℝ) with hx | hx
  · let t : ℝ := 3 * x
    have ht0 : 0 ≤ t := by dsimp only [t]; positivity
    have ht1 : t ≤ 1 := by dsimp only [t]; linarith
    have htcomp : 0 ≤ 1 - t := by linarith
    have hbern : fourCellOddStripSchurProductGapQuotient x =
        (3 / 2000 : ℝ) * (1 - t) ^ 7 +
        (4307 / 384000 : ℝ) * t * (1 - t) ^ 6 +
        (15787 / 576000 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
        (1623787 / 51840000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
        (237497 / 12960000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
        (2600099 / 466560000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
        (222727 / 233280000 : ℝ) * t ^ 6 * (1 - t) +
        (54061 / 466560000 : ℝ) * t ^ 7 := by
      unfold fourCellOddStripSchurProductGapQuotient
      dsimp only [t]
      ring
    rw [hbern]
    positivity
  · rcases le_total x (2 / 3 : ℝ) with hx' | hx'
    · let t : ℝ := 3 * x - 1
      have ht0 : 0 ≤ t := by dsimp only [t]; linarith
      have ht1 : t ≤ 1 := by dsimp only [t]; linarith
      have htcomp : 0 ≤ 1 - t := by linarith
      have hbern : fourCellOddStripSchurProductGapQuotient x =
          (54061 / 466560000 : ℝ) * (1 - t) ^ 7 +
          (173 / 259200 : ℝ) * t * (1 - t) ^ 6 +
          (71831 / 18662400 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
          (976823 / 77760000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
          (9220427 / 466560000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
          (1781893 / 116640000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
          (2555657 / 466560000 : ℝ) * t ^ 6 * (1 - t) +
          (172301 / 233280000 : ℝ) * t ^ 7 := by
        unfold fourCellOddStripSchurProductGapQuotient
        dsimp only [t]
        ring
      rw [hbern]
      positivity
    · let t : ℝ := 3 * x - 2
      have ht0 : 0 ≤ t := by dsimp only [t]; linarith
      have ht1 : t ≤ 1 := by dsimp only [t]; linarith
      have htcomp : 0 ≤ 1 - t := by linarith
      have hbern : fourCellOddStripSchurProductGapQuotient x =
          (172301 / 233280000 : ℝ) * (1 - t) ^ 7 +
          (756257 / 155520000 : ℝ) * t * (1 - t) ^ 6 +
          (337891 / 29160000 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
          (1734811 / 155520000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
          (23563 / 8640000 : ℝ) * t ^ 4 * (1 - t) ^ 3 +
          (18527 / 17280000 : ℝ) * t ^ 5 * (1 - t) ^ 2 +
          (7121 / 1440000 : ℝ) * t ^ 6 * (1 - t) +
          (1887 / 640000 : ℝ) * t ^ 7 := by
        unfold fourCellOddStripSchurProductGapQuotient
        dsimp only [t]
        ring
      rw [hbern]
      positivity

private theorem fourCellOddStripSchur_productGap_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ fourCellOddStripSchurPolynomial x *
        fourCellOddStripSchurQuarticDenominator x -
      (49 / 1024 : ℝ) * x ^ 2 := by
  have hq := fourCellOddStripSchurProductGapQuotient_nonneg hx0 hx1
  have hid : fourCellOddStripSchurPolynomial x *
        fourCellOddStripSchurQuarticDenominator x -
      (49 / 1024 : ℝ) * x ^ 2 =
        x * fourCellOddStripSchurProductGapQuotient x := by
    unfold fourCellOddStripSchurPolynomial
      fourCellOddStripSchurQuarticDenominator
      fourCellOddStripSchurProductGapQuotient
    ring
  rw [hid]
  exact mul_nonneg hx0 hq

private theorem fourCellOddStripSchurQuarticDenominator_pos
    (x : ℝ) : 0 < fourCellOddStripSchurQuarticDenominator x := by
  unfold fourCellOddStripSchurQuarticDenominator
  positivity

/-- The rational density forced by the Taylor and quartic envelopes is
bounded pointwise by the explicit Schur polynomial. -/
theorem fourCellOddStripSchur_rationalDensity_le_polynomial
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (49 / 1024 : ℝ) * x ^ 2 /
        fourCellOddStripSchurQuarticDenominator x ≤
      fourCellOddStripSchurPolynomial x := by
  rw [div_le_iff₀ (fourCellOddStripSchurQuarticDenominator_pos x)]
  have hgap := fourCellOddStripSchur_productGap_nonneg hx0 hx1
  linarith

theorem integral_fourCellOddStripSchurPolynomial :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurPolynomial x) =
      2557 / 9000 := by
  unfold fourCellOddStripSchurPolynomial
  have h1 : IntervalIntegrable (fun x : ℝ ↦ (1 / 10 : ℝ) * x)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (1 / 10 : ℝ) * x))
      |>.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ (10 / 3 : ℝ) * x ^ 2)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (10 / 3 : ℝ) * x ^ 2))
      |>.intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ ↦ (11 / 2 : ℝ) * x ^ 3)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (11 / 2 : ℝ) * x ^ 3))
      |>.intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ ↦ (249 / 100 : ℝ) * x ^ 4)
      volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (249 / 100 : ℝ) * x ^ 4))
      |>.intervalIntegrable _ _
  have hi1 : (∫ x : ℝ in 0..1, (1 / 10 : ℝ) * x) = 1 / 20 := by
    rw [show (fun x : ℝ ↦ (1 / 10 : ℝ) * x) =
        fun x ↦ (1 / 10 : ℝ) * x ^ 1 by
      funext x
      ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [intervalIntegral.integral_add ((h1.add h2).sub h3) h4,
    intervalIntegral.integral_sub (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  rw [hi1]
  norm_num

theorem integral_fourCellOddStripSchurPolynomial_lt_two_sevenths :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurPolynomial x) <
      (2 / 7 : ℝ) := by
  rw [integral_fourCellOddStripSchurPolynomial]
  norm_num

private theorem fourCellOddStripSchurQuarticDenominator_le_weight
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    fourCellOddStripSchurQuarticDenominator x ≤
      fourCellOddStripSchurWeight x := by
  have hquartic := quartic_le_endpointPotential
    (show |x| < 1 by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2])
  unfold fourCellOddStripSchurQuarticDenominator
    fourCellOddStripSchurWeight yoshidaEndpointQuartic at *
  nlinarith

private theorem fourCellOddStripSchurWeight_pos_of_mem_Ioo
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < fourCellOddStripSchurWeight x := by
  exact (fourCellOddStripSchurQuarticDenominator_pos x).trans_le
    (fourCellOddStripSchurQuarticDenominator_le_weight hx)

/-- The integral of the pointwise Schur weight against a profile square is
exactly the blended allocation. -/
theorem integral_fourCellOddStripSchurWeight_mul_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1, fourCellOddStripSchurWeight x * w x ^ 2) =
      fourCellOddStripBlendedAllocation w := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2) volume 0 1 :=
    (hw.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  rw [show (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2) =
      fun x ↦ (3 / 200 : ℝ) * (w x ^ 2) +
        (7 / 50 : ℝ) *
          (yoshidaEndpointPotential x * w x ^ 2) by
    funext x
    unfold fourCellOddStripSchurWeight
    ring]
  rw [intervalIntegral.integral_add
      (hmass.const_mul (3 / 200)) (hpotential.const_mul (7 / 50)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

/-- Exact two-obligation Schur closure.  This is stronger than merely
replacing the rank by a multiple of the potential: the scalar and potential
pieces must remain coupled in both hypotheses. -/
theorem fourCellOddStripCapacityLowerOperator_nonneg_of_blendedSchur
    (w : ℝ → ℝ)
    (hbase : fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w)
    (hrank : 8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      fourCellOddStripBlendedAllocation w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  rw [fourCellOddStripCapacityLowerOperator_eq_base_sub_rank]
  linarith

private theorem sinh_le_mul_exp_self {z : ℝ} :
    Real.sinh z ≤ z * Real.exp z := by
  have hbase := Real.add_one_le_exp (-2 * z)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos z).le
  have hprod : Real.exp z * (1 - 2 * z) ≤ Real.exp (-z) := by
    calc
      Real.exp z * (1 - 2 * z) = Real.exp z * (-2 * z + 1) := by ring
      _ ≤ Real.exp z * Real.exp (-2 * z) := hmul
      _ = Real.exp (-z) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.sinh_eq]
  nlinarith [Real.exp_pos z]

private theorem fourCellOperatorHalfWidth_lt_seven_sixteenths :
    fourCellOperatorHalfWidth < (7 / 16 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  norm_num at hlog ⊢
  linarith

/-- Rational pointwise envelope for the production odd representer. -/
theorem fourCell_sinh_weight_le_seven_twenty_fifths
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ≤ (7 / 25 : ℝ) * x := by
  let z := fourCellOperatorHalfWidth * x / 2
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hz : z ≤ (7 / 32 : ℝ) := by
    dsimp only [z]
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  have hzOne : z < 1 := lt_of_le_of_lt hz (by norm_num)
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzOne
  have hden : 1 / (1 - z) ≤ (32 / 25 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
    nlinarith
  have hexpBound : Real.exp z ≤ (32 / 25 : ℝ) := hexp.trans hden
  have hsinh := sinh_le_mul_exp_self (z := z)
  have hzLinear : z ≤ (7 / 32 : ℝ) * x := by
    dsimp only [z]
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  calc
    Real.sinh z ≤ z * Real.exp z := hsinh
    _ ≤ z * (32 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpBound hz0
    _ ≤ ((7 / 32 : ℝ) * x) * (32 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_right hzLinear (by norm_num)
    _ = (7 / 25 : ℝ) * x := by ring

/-- Taylor-sharp linear envelope needed by the blended mass--potential
Schur weight.  Unlike the potential-only estimate, its constant is within
one percent of the exact production slope. -/
theorem fourCell_sinh_weight_le_seven_thirty_seconds
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ≤ (7 / 32 : ℝ) * x := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let c : ℝ := 1733 / 8000
  let z : ℝ := lambda * x
  have hlog := strict_log_two_bounds.2
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda_lt : lambda < c := by
    dsimp only [lambda, c]
    unfold fourCellOperatorHalfWidth
    norm_num at hlog ⊢
    linarith
  have hc0 : 0 ≤ c := by norm_num [c]
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hzLinear : z ≤ c * x := by
    dsimp only [z]
    exact mul_le_mul_of_nonneg_right hlambda_lt.le hx0
  have hcx : c * x ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hc0
  have hzc : z ≤ c := hzLinear.trans hcx
  have hzone : z < 1 := hzc.trans_lt (by norm_num [c])
  have hexp := Real.exp_bound_div_one_sub_of_interval hz0 hzone
  have hden : 1 / (1 - z) ≤ (32 / 25 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - z)]
    dsimp only [c] at hzc
    norm_num at hzc ⊢
    linarith
  have hexpBound : Real.exp z ≤ (32 / 25 : ℝ) := hexp.trans hden
  have hcoshExp : Real.cosh z ≤ Real.exp z := by
    rw [Real.cosh_eq]
    have hneg : Real.exp (-z) ≤ Real.exp z := by
      rw [Real.exp_le_exp]
      linarith
    linarith
  have hcosh : Real.cosh z ≤ (32 / 25 : ℝ) := hcoshExp.trans hexpBound
  have htaylor := abs_sinh_sub_cubic_le z
  have htaylorUpper :
      Real.sinh z ≤ z + z ^ 3 / 6 + Real.cosh z * z ^ 5 / 120 := by
    have hle := (le_abs_self (Real.sinh z - z - z ^ 3 / 6)).trans htaylor
    have hle' : Real.sinh z - z - z ^ 3 / 6 ≤
        Real.cosh z * z ^ 5 / 120 := by
      simpa [abs_of_nonneg hz0] using hle
    linarith
  have hzsq : z ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ hz0 hc0).2 hzc
  have hzfour : z ^ 4 ≤ c ^ 4 := by
    nlinarith [sq_nonneg (z ^ 2), sq_nonneg (c ^ 2)]
  have hzthree : z ^ 3 ≤ c ^ 2 * z := by
    nlinarith
  have hzfive : z ^ 5 ≤ c ^ 4 * z := by
    nlinarith
  have hzfactor :
      Real.sinh z ≤ z *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := by
    calc
      Real.sinh z ≤ z + z ^ 3 / 6 + Real.cosh z * z ^ 5 / 120 :=
        htaylorUpper
      _ ≤ z + (c ^ 2 * z) / 6 + (32 / 25 : ℝ) *
          (c ^ 4 * z) / 120 := by
        gcongr
      _ = z *
          (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := by ring
  have hfactor0 : 0 ≤
      1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120 := by positivity
  have hrat : c *
      (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) <
        (7 / 32 : ℝ) := by
    norm_num [c]
  rw [show fourCellOperatorHalfWidth * x / 2 = z by
    dsimp only [z, lambda]
    ring]
  calc
    Real.sinh z ≤ z *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) := hzfactor
    _ ≤ (c * x) *
        (1 + c ^ 2 / 6 + (32 / 25 : ℝ) * c ^ 4 / 120) :=
      mul_le_mul_of_nonneg_right hzLinear hfactor0
    _ ≤ (7 / 32 : ℝ) * x := by
      nlinarith

/-- Pointwise dual-density domination for the blended Schur weight. -/
theorem fourCellOddStripSchur_sinhDensity_le_polynomial
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x ≤
      fourCellOddStripSchurPolynomial x := by
  have hsinh0 : 0 ≤ Real.sinh (fourCellOperatorHalfWidth * x / 2) := by
    rw [Real.sinh_nonneg_iff]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    exact div_nonneg (mul_nonneg ha0 hx.1.le) (by norm_num)
  have hsinh := fourCell_sinh_weight_le_seven_thirty_seconds
    hx.1.le hx.2.le
  have hsinhSq :
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
        (49 / 1024 : ℝ) * x ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ hsinh0 (mul_nonneg (by norm_num) hx.1.le)).2 hsinh
    nlinarith
  have hden := fourCellOddStripSchurQuarticDenominator_le_weight hx
  have hden0 := fourCellOddStripSchurQuarticDenominator_pos x
  have hweight0 := fourCellOddStripSchurWeight_pos_of_mem_Ioo hx
  calc
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x ≤
      ((49 / 1024 : ℝ) * x ^ 2) /
        fourCellOddStripSchurWeight x :=
      div_le_div_of_nonneg_right hsinhSq hweight0.le
    _ ≤ ((49 / 1024 : ℝ) * x ^ 2) /
        fourCellOddStripSchurQuarticDenominator x := by
      exact div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ ≤ fourCellOddStripSchurPolynomial x :=
      fourCellOddStripSchur_rationalDensity_le_polynomial hx.1.le hx.2.le

/-- The exact dual norm of the sinh representer in the blended weight is
strictly smaller than `2 / 7`. -/
theorem integral_fourCellOddStripSchur_sinhDensity_lt_two_sevenths :
    (∫ x : ℝ in 0..1,
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
        fourCellOddStripSchurWeight x) < (2 / 7 : ℝ) := by
  let F : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let P : ℝ → ℝ := fourCellOddStripSchurPolynomial
  have hPint : IntervalIntegrable P volume 0 1 := by
    exact (by
      dsimp only [P]
      unfold fourCellOddStripSchurPolynomial
      fun_prop : Continuous P) |>.intervalIntegrable _ _
  have hFmeas : AEStronglyMeasurable F
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hPset : IntegrableOn P (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hPint
  have hFset : IntegrableOn F (Ioc (0 : ℝ) 1) := by
    apply hPset.mono' hFmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne
          (volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ)] with x hx hx1
    have hxoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have hle := fourCellOddStripSchur_sinhDensity_le_polynomial hxoo
    have hF0 : 0 ≤ F x := by
      dsimp only [F]
      exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo hxoo).le
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simpa only [F, P] using hle
  have hFint : IntervalIntegrable F volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hFset
  have hmono : (∫ x : ℝ in 0..1, F x) ≤ ∫ x : ℝ in 0..1, P x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hFint hPint
    intro x hx
    exact fourCellOddStripSchur_sinhDensity_le_polynomial hx
  dsimp only [F, P] at hmono ⊢
  exact hmono.trans_lt
    integral_fourCellOddStripSchurPolynomial_lt_two_sevenths

private theorem intervalIntegrable_fourCellOddStripSchur_sinhDensity :
    IntervalIntegrable
      (fun x : ℝ ↦
        Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
          fourCellOddStripSchurWeight x) volume 0 1 := by
  let F : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let P : ℝ → ℝ := fourCellOddStripSchurPolynomial
  have hPint : IntervalIntegrable P volume 0 1 := by
    exact (by
      dsimp only [P]
      unfold fourCellOddStripSchurPolynomial
      fun_prop : Continuous P) |>.intervalIntegrable _ _
  have hFmeas : AEStronglyMeasurable F
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hPset : IntegrableOn P (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hPint
  have hFset : IntegrableOn F (Ioc (0 : ℝ) 1) := by
    apply hPset.mono' hFmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne
          (volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ)] with x hx hx1
    have hxoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have hle := fourCellOddStripSchur_sinhDensity_le_polynomial hxoo
    have hF0 : 0 ≤ F x := by
      dsimp only [F]
      exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo hxoo).le
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simpa only [F, P] using hle
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hFset

private theorem intervalIntegrable_fourCellOddStripSchurWeight_mul_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2)
      volume 0 1 := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2) volume 0 1 :=
    (hw.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  apply (hmass.const_mul (3 / 200)).add
    (hpotential.const_mul (7 / 50)) |>.congr
  intro x _hx
  unfold fourCellOddStripSchurWeight
  ring

/-- Weighted Cauchy--Schwarz with the exact blended diagonal allocation. -/
theorem fourCellPositiveSinhMoment_sq_le_blendedDual_mul_allocation
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (∫ x : ℝ in 0..1,
        Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
          fourCellOddStripSchurWeight x) *
        fourCellOddStripBlendedAllocation w := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let W : ℝ → ℝ := fourCellOddStripSchurWeight
  let G : ℝ → ℝ := fun x ↦
    Real.sinh (fourCellOperatorHalfWidth * x / 2)
  have hW : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.Measure.ae_ne μ (1 : ℝ)] with x hx hx1
    exact fourCellOddStripSchurWeight_pos_of_mem_Ioo
      ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  have hdualMeas : AEStronglyMeasurable
      (fun x ↦ G x / Real.sqrt (W x)) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G, W, μ]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hdual : MemLp (fun x ↦ G x / Real.sqrt (W x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hdualMeas]
    have hset : IntegrableOn
        (fun x : ℝ ↦
          Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
            fourCellOddStripSchurWeight x) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        intervalIntegrable_fourCellOddStripSchur_sinhDensity
    have hset' : Integrable
        (fun x : ℝ ↦ G x ^ 2 / W x) μ := by
      simpa only [μ, G, W] using hset
    apply hset'.congr
    filter_upwards [hW] with x hx
    rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hx.le]
  have hprimalMeas : AEStronglyMeasurable
      (fun x ↦ Real.sqrt (W x) * w x) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [W, μ]
    unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
    fun_prop
  have hprimal : MemLp (fun x ↦ Real.sqrt (W x) * w x) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hprimalMeas]
    have hset : IntegrableOn
        (fun x : ℝ ↦ fourCellOddStripSchurWeight x * w x ^ 2)
        (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        (intervalIntegrable_fourCellOddStripSchurWeight_mul_sq w hw)
    have hset' : Integrable (fun x : ℝ ↦ W x * w x ^ 2) μ := by
      simpa only [μ, W] using hset
    apply hset'.congr
    filter_upwards [hW] with x hx
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hx.le]
  have hcauchy := sq_integral_mul_le_weighted μ W G w
    hW hdual hprimal
  dsimp only [μ] at hcauchy
  repeat rw [← intervalIntegral.integral_of_le (by norm_num)] at hcauchy
  have hmomentEq : (∫ x : ℝ in 0..1, G x * w x) =
      fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) := by
    unfold fourCellPositiveSinhMoment
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [G]
    congr 2
    ring
  have hweightEq : (∫ x : ℝ in 0..1, W x * w x ^ 2) =
      fourCellOddStripBlendedAllocation w := by
    simpa only [W] using integral_fourCellOddStripSchurWeight_mul_sq w hw
  rw [hmomentEq, hweightEq] at hcauchy
  simpa only [G, W] using hcauchy

/-- The complete negative sinh rank is dominated by the blended allocation,
with strict slack in the scalar dual norm. -/
theorem eight_mul_fourCell_sinhMoment_sq_le_blendedAllocation
    (w : ℝ → ℝ) (hw : Continuous w) :
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      fourCellOddStripBlendedAllocation w := by
  let I : ℝ := ∫ x : ℝ in 0..1,
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 /
      fourCellOddStripSchurWeight x
  let D : ℝ := fourCellOddStripBlendedAllocation w
  have hmoment :=
    fourCellPositiveSinhMoment_sq_le_blendedDual_mul_allocation w hw
  change fourCellPositiveSinhMoment w
    (fourCellOperatorHalfWidth / 2) ^ 2 ≤ I * D at hmoment
  have hI : I < (2 / 7 : ℝ) := by
    simpa only [I] using
      integral_fourCellOddStripSchur_sinhDensity_lt_two_sevenths
  have ha : 8 * fourCellOperatorHalfWidth < (7 / 2 : ℝ) := by
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  have hD : 0 ≤ D := by
    dsimp only [D, fourCellOddStripBlendedAllocation]
    have hm : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (w x))
    have hp : 0 ≤
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1, yoshidaEndpointPotential]
      · have hquartic := quartic_le_endpointPotential
            (show |x| < 1 by
              rw [abs_lt]
              constructor
              · linarith [hx.1]
              · exact lt_of_le_of_ne hx.2 hx1)
        have hV : 0 ≤ yoshidaEndpointPotential x := by
          unfold yoshidaEndpointQuartic at hquartic
          nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
        exact mul_nonneg hV (sq_nonneg _)
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hx1 : x = 1
    · rw [hx1]
      unfold fourCellOddStripSchurWeight yoshidaEndpointPotential
      norm_num
      exact div_nonneg (sq_nonneg _) (by norm_num)
    · exact div_nonneg (sq_nonneg _)
        (fourCellOddStripSchurWeight_pos_of_mem_Ioo
          ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩).le
  have hcoef : 8 * fourCellOperatorHalfWidth * I ≤ 1 := by
    nlinarith
  have ha0 : 0 ≤ 8 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  calc
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      8 * fourCellOperatorHalfWidth * (I * D) :=
        mul_le_mul_of_nonneg_left hmoment ha0
    _ = (8 * fourCellOperatorHalfWidth * I) * D := by ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hcoef hD
    _ = D := one_mul D

/-- After the rank is discharged structurally, odd strip positivity has one
remaining obligation: the exact non-rank base must dominate the fixed
blended diagonal allocation. -/
theorem fourCellOddStripCapacityLowerOperator_nonneg_of_base_ge_blended
    (w : ℝ → ℝ) (hw : Continuous w)
    (hbase : fourCellOddStripBlendedAllocation w ≤
      fourCellOddStripCapacityBase w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  exact fourCellOddStripCapacityLowerOperator_nonneg_of_blendedSchur
    w hbase (eight_mul_fourCell_sinhMoment_sq_le_blendedAllocation w hw)

private theorem fourCell_sinh_sq_le_ninety_eight_six_twenty_fifths_potential
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
      (98 / 625 : ℝ) * yoshidaEndpointPotential x := by
  have hsinh0 : 0 ≤ Real.sinh (fourCellOperatorHalfWidth * x / 2) := by
    rw [Real.sinh_nonneg_iff]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    exact div_nonneg (mul_nonneg ha0 hx.1.le) (by norm_num)
  have hsinh := fourCell_sinh_weight_le_seven_twenty_fifths hx.1.le hx.2.le
  have hsinhSq :
      Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 ≤
        ((7 / 25 : ℝ) * x) ^ 2 :=
    (sq_le_sq₀ hsinh0 (mul_nonneg (by norm_num) hx.1.le)).2 hsinh
  have hquartic := quartic_le_endpointPotential
    (show |x| < 1 by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
  unfold yoshidaEndpointQuartic at hquartic
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

private theorem sq_intervalIntegral_zero_one_le_integral_sq
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : ℝ in 0..1, f x) ^ 2 ≤ ∫ x : ℝ in 0..1, f x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have honeMeas : AEStronglyMeasurable (fun _x : ℝ ↦ (1 : ℝ)) μ := by
    fun_prop
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have honeLp : MemLp (fun _x : ℝ ↦ (1 : ℝ)) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm honeMeas]
    have hcompact : IntegrableOn (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (by fun_prop : Continuous (fun _x : ℝ ↦ ‖(1 : ℝ)‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ
    (fun _x : ℝ ↦ (1 : ℝ)) (fun _x : ℝ ↦ (1 : ℝ)) f
    (by simp) (by simpa using honeLp) (by simpa using hfLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa [μ] using h

/-- The squared representer, including the profile, costs at most
`98 / 625` of the endpoint potential. -/
theorem integral_fourCell_sinh_sq_mul_le_ninety_eight_six_twenty_fifths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      (98 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2)
      volume 0 1 := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2))
        |>.intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := hpotentialFull.mono_set (by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1)
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (98 / 625 : ℝ) *
        (yoshidaEndpointPotential x * w x ^ 2)) volume 0 1 :=
    hpotential.const_mul (98 / 625)
  have hmono :
      (∫ x : ℝ in 0..1,
        (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) ≤
      ∫ x : ℝ in 0..1,
        (98 / 625 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hright
    intro x hx
    have hweight :=
      fourCell_sinh_sq_le_ninety_eight_six_twenty_fifths_potential hx
    have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg (w x))
    calc
      (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2 =
          Real.sinh (fourCellOperatorHalfWidth * x / 2) ^ 2 * w x ^ 2 := by
            ring
      _ ≤ ((98 / 625 : ℝ) * yoshidaEndpointPotential x) * w x ^ 2 := hmul
      _ = (98 / 625 : ℝ) * (yoshidaEndpointPotential x * w x ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Sharp rational structural payment of the complete odd hyperbolic rank.
This retains `907 / 625` of the two positive-half potential copies. -/
theorem eight_mul_fourCell_sinhMoment_sq_le_three_hundred_forty_three_six_twenty_fifths_potential
    (w : ℝ → ℝ) (hw : Continuous w) :
    8 * fourCellOperatorHalfWidth *
        fourCellPositiveSinhMoment w
          (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (343 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hcauchy := sq_intervalIntegral_zero_one_le_integral_sq
    (fun x : ℝ ↦
      Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) (by fun_prop)
  have hweighted :=
    integral_fourCell_sinh_sq_mul_le_ninety_eight_six_twenty_fifths_potential
      w hw
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : 8 * fourCellOperatorHalfWidth ≤ (7 / 2 : ℝ) := by
    nlinarith [fourCellOperatorHalfWidth_lt_seven_sixteenths]
  unfold fourCellPositiveSinhMoment at hcauchy ⊢
  calc
    8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          Real.sinh (fourCellOperatorHalfWidth / 2 * x) * w x) ^ 2 ≤
      8 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in 0..1,
          (Real.sinh (fourCellOperatorHalfWidth * x / 2) * w x) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            convert hcauchy using 1
            all_goals ring
    _ ≤ 8 * fourCellOperatorHalfWidth *
        ((98 / 625 : ℝ) *
          ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ (343 / 625 : ℝ) *
        ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
      have hpotentialNonneg : 0 ≤
          ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
        apply intervalIntegral.integral_nonneg (by norm_num)
        intro x hx
        have hV : 0 ≤ yoshidaEndpointPotential x := by
          by_cases hx1 : x = 1
          · simp [hx1, yoshidaEndpointPotential]
          · have hquartic := quartic_le_endpointPotential
                (show |x| < 1 by
                  rw [abs_lt]
                  constructor
                  · linarith [hx.1]
                  · exact lt_of_le_of_ne hx.2 hx1)
            unfold yoshidaEndpointQuartic at hquartic
            nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
        exact mul_nonneg hV (sq_nonneg _)
      nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityClosureStructural
