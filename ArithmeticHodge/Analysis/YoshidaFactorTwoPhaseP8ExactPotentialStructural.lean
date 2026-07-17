import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ExactPotentialStructural

open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP8StructuralReserve
open UnitIntervalLogEnergyAffine

noncomputable section

/-!
# Exact endpoint-potential reserve on centered `P8`

The cutoff-eight spectral gap leaves substantially more phase reserve on the
pure `P8` line than on an arbitrary cutoff-eight residual.  The extra reserve
comes from the exact endpoint-potential mass of this one retained mode.  No
phase point is sampled and no finite matrix is enumerated.
-/

/-! ## The missing degree-sixteen endpoint-potential moment -/

private theorem integral_pow_mul_log_one_sub_local (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) =
      ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
          (-(1 : ℝ) / (k + 1) ^ 2) := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ n * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) =
        ∫ x : ℝ in 0..1, g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ∫ x : ℝ in 0..1, g x := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := g)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = ∫ x : ℝ in 0..1,
        ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
            (x ^ k * Real.log x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      rw [show (1 - x) ^ n =
          ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (-1 : ℝ) ^ k * x ^ k by
        rw [show 1 - x = -x + 1 by ring, add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [one_pow]
        rw [neg_pow]
        ring]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Finset.range (n + 1),
        ∫ x : ℝ in 0..1,
          ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
            (x ^ k * Real.log x) := by
      apply intervalIntegral.integral_finset_sum
      intro k hk
      exact (intervalIntegral.intervalIntegrable_log'.continuousOn_mul
        (continuous_pow k).continuousOn).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul,
        integral_pow_mul_log_zero_one]
      ring

private theorem integral_inv_one_add_local :
    (∫ x : ℝ in 0..1, 1 / (1 + x)) = Real.log 2 := by
  let F : ℝ → ℝ := fun x ↦ Real.log (1 + x)
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (1 / (1 + x)) x := by
    have hadd : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log hx).comp x hadd
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 / (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num

private theorem integral_pow_mul_log_one_add_eq_quotient_local (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) =
      Real.log 2 / (n + 1) -
        (1 / (n + 1 : ℝ)) *
          ∫ x : ℝ in 0..1, x ^ (n + 1) / (1 + x) := by
  let u : ℝ → ℝ := fun x ↦ Real.log (1 + x)
  let u' : ℝ → ℝ := fun x ↦ 1 / (1 + x)
  let v : ℝ → ℝ := fun x ↦ x ^ (n + 1) / (n + 1)
  let v' : ℝ → ℝ := fun x ↦ x ^ n
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp only [v, v']
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (n + 1) using 1
    · simp only [id_eq, Nat.cast_add, Nat.cast_one]
      field_simp
      rw [Nat.add_sub_cancel]
  have huOn : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hadd : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    simpa only [u, u', Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log hne).comp x hadd
  have hvOn : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x :=
    fun x _hx ↦ hv x
  have huI : IntervalIntegrable u' volume 0 1 := by
    dsimp only [u']
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hvI : IntervalIntegrable v' volume 0 1 := by
    dsimp only [v']
    exact (continuous_pow n).intervalIntegrable 0 1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    huOn hvOn huI hvI
  have hleft :
      (∫ x : ℝ in 0..1, u x * v' x) =
        ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [u, v']
    ring
  rw [hleft] at hparts
  dsimp only [u, u', v, v'] at hparts
  norm_num only [one_pow, zero_pow (Nat.succ_ne_zero n), Nat.cast_add,
    Nat.cast_one, zero_div, mul_zero, Real.log_one, zero_mul, zero_sub] at hparts
  have hfactor :
      (∫ x : ℝ in 0..1,
          1 / (1 + x) * (x ^ (n + 1) / (n + 1))) =
        (1 / (n + 1 : ℝ)) *
          ∫ x : ℝ in 0..1, x ^ (n + 1) / (1 + x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hfactor] at hparts
  convert hparts using 1
  all_goals ring

private theorem integral_pow_seventeen_div_one_add :
    (∫ x : ℝ in 0..1, x ^ 17 / (1 + x)) =
      1768477 / 2450448 - Real.log 2 := by
  let q : ℕ → ℝ → ℝ := fun k x ↦ (-1 : ℝ) ^ k * x ^ (16 - k)
  have hqI (k : ℕ) : IntervalIntegrable (q k) volume 0 1 := by
    dsimp only [q]
    exact (continuous_const.mul (continuous_pow (16 - k))).intervalIntegrable 0 1
  have hinv : IntervalIntegrable (fun x : ℝ ↦ 1 / (1 + x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hsumI : IntervalIntegrable
      (fun x : ℝ ↦ ∑ k ∈ Finset.range 17, q k x) volume 0 1 := by
    exact IntervalIntegrable.sum (Finset.range 17) (fun k _hk ↦ hqI k)
  calc
    (∫ x : ℝ in 0..1, x ^ 17 / (1 + x)) =
        ∫ x : ℝ in 0..1,
          (∑ k ∈ Finset.range 17, q k x) - 1 / (1 + x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      have hne : 1 + x ≠ 0 := by linarith [hxu.1]
      dsimp only [q]
      norm_num [Finset.sum_range_succ]
      field_simp [hne]
      ring
    _ = (∑ k ∈ Finset.range 17,
          ∫ x : ℝ in 0..1, q k x) -
        ∫ x : ℝ in 0..1, 1 / (1 + x) := by
      rw [intervalIntegral.integral_sub hsumI hinv,
        intervalIntegral.integral_finset_sum fun k hk ↦ hqI k]
    _ = 1768477 / 2450448 - Real.log 2 := by
      rw [integral_inv_one_add_local]
      dsimp only [q]
      simp_rw [intervalIntegral.integral_const_mul,
        YoshidaEndpointOcticPotential.integral_pow_nat]
      norm_num [Finset.sum_range_succ]

private theorem integral_sixteenth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 16 * Real.log (1 - x)) =
      -42142223 / 208288080 := by
  rw [integral_pow_mul_log_one_sub_local]
  norm_num [Finset.sum_range_succ, Nat.choose]

private theorem integral_sixteenth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 16 * Real.log (1 + x)) =
      (2 / 17 : ℝ) * Real.log 2 - 1768477 / 41657616 := by
  rw [integral_pow_mul_log_one_add_eq_quotient_local,
    integral_pow_seventeen_div_one_add]
  ring

private theorem integral_endpointPotential_mul_pow_of_even_local
    (n : ℕ) (hn : Even n) :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ n) =
      -((∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) +
        ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ n
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    rw [hn.neg_pow]
    congr 1
    congr 3
    ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ n * Real.log (1 - x) + x ^ n * Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hsubI : IntervalIntegrable
      (fun x : ℝ ↦ x ^ n * Real.log (1 - x)) volume 0 1 := by
    let g : ℝ → ℝ := fun y ↦ (1 - y) ^ n * Real.log y
    have hg : IntervalIntegrable g volume 0 1 := by
      have hpoly : Continuous (fun y : ℝ ↦ (1 - y) ^ n) := by fun_prop
      have hbase : IntervalIntegrable
          (fun y : ℝ ↦ (1 - y) ^ n * Real.log y) volume 0 1 :=
        (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
          |>.continuousOn_mul hpoly.continuousOn
      simpa only [g] using hbase
    have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
        volume 0 1 := by
      simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
    apply hreflect.congr
    intro x _hx
    dsimp only [g]
    ring
  have haddI : IntervalIntegrable
      (fun x : ℝ ↦ x ^ n * Real.log (1 + x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow n).mul hlog).continuousWithinAt
  have hrRight : IntervalIntegrable r volume 0 1 := by
    have hsum := hsubI.add haddI
    have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
    simpa only [r] using hscaled
  have hqRight : IntervalIntegrable q volume 0 1 := by
    have hrev : r =ᵐ[volume] q := by
      filter_upwards [hpoint] with x hx
      exact hx.symm
    apply hrRight.congr_ae
    exact hrev.filter_mono (ae_mono Measure.restrict_le_self)
  have hqLeft : IntervalIntegrable q volume (-1) 0 := by
    have hneg : IntervalIntegrable (fun x : ℝ ↦ q (-x)) volume (-1) 0 := by
      simpa only [zero_sub, sub_zero] using (hqRight.comp_sub_left 0).symm
    apply hneg.congr
    intro x _hx
    exact hqEven x
  have hfold : (∫ x : ℝ in -1..1, q x) =
      2 * ∫ x : ℝ in 0..1, q x := by
    have hreflect : (∫ x : ℝ in 0..1, q (-x)) =
        ∫ x : ℝ in -1..0, q x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := q) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, q x) =
          (∫ x : ℝ in -1..0, q x) + ∫ x : ℝ in 0..1, q x :=
        (intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight).symm
      _ = (∫ x : ℝ in 0..1, q x) + ∫ x : ℝ in 0..1, q x := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hqEven x
      _ = _ := by ring
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * x ^ n) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ n * Real.log (1 - x) +
                x ^ n * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ n * Real.log (1 - x) +
              x ^ n * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add hsubI haddI]
  rw [hsplit]
  ring

/-- Exact degree-sixteen moment of the logarithmic endpoint potential. -/
theorem integral_endpointPotential_mul_pow_sixteen :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 16) =
      3186538 / 13018005 - (2 / 17 : ℝ) * Real.log 2 := by
  rw [integral_endpointPotential_mul_pow_of_even_local 16 (by decide),
    integral_sixteenth_mul_log_one_sub,
    integral_sixteenth_mul_log_one_add]
  ring

private theorem intervalIntegrable_endpointPotential_mul_even_pow (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n))
      volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ n) (continuous_id.pow n)
  apply h.congr
  intro x _hx
  ring

/-! ## Exact endpoint-potential mass and ratio -/

/-- Exact endpoint-potential mass on centered `P8`. -/
theorem integral_endpointPotential_mul_factorTwoCenteredP8_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP8 x ^ 2) =
        1696405 / 10414404 - (2 / 17 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP8 x ^ 2) =
    fun x ↦
      (41409225 / 16384 : ℝ) * (yoshidaEndpointPotential x * x ^ 16) -
        (19324305 / 2048 : ℝ) * (yoshidaEndpointPotential x * x ^ 14) +
      (58369311 / 4096 : ℝ) * (yoshidaEndpointPotential x * x ^ 12) -
        (22837815 / 2048 : ℝ) * (yoshidaEndpointPotential x * x ^ 10) +
      (39372795 / 8192 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (2288055 / 2048 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
      (518175 / 4096 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (11025 / 2048 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
      (1225 / 16384 : ℝ) * yoshidaEndpointPotential x by
    funext x
    rw [factorTwoCenteredP8_eq]
    ring]
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 0
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 2
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 3
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 4
  have h10 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 10) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 5
  have h12 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 12) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 6
  have h14 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 14) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 7
  have h16 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 16) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 8
  rw [intervalIntegral.integral_add
      (((((((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ))).add
        (h12.const_mul (58369311 / 4096 : ℝ))).sub
        (h10.const_mul (22837815 / 2048 : ℝ))).add
        (h8.const_mul (39372795 / 8192 : ℝ))).sub
        (h6.const_mul (2288055 / 2048 : ℝ))).add
        (h4.const_mul (518175 / 4096 : ℝ)) |>.sub
        (h2.const_mul (11025 / 2048 : ℝ)))
      (h0.const_mul (1225 / 16384 : ℝ)),
    intervalIntegral.integral_sub
      ((((((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ))).add
        (h12.const_mul (58369311 / 4096 : ℝ))).sub
        (h10.const_mul (22837815 / 2048 : ℝ))).add
        (h8.const_mul (39372795 / 8192 : ℝ))).sub
        (h6.const_mul (2288055 / 2048 : ℝ)) |>.add
        (h4.const_mul (518175 / 4096 : ℝ)))
      (h2.const_mul (11025 / 2048 : ℝ)),
    intervalIntegral.integral_add
      (((((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ))).add
        (h12.const_mul (58369311 / 4096 : ℝ))).sub
        (h10.const_mul (22837815 / 2048 : ℝ))).add
        (h8.const_mul (39372795 / 8192 : ℝ)) |>.sub
        (h6.const_mul (2288055 / 2048 : ℝ)))
      (h4.const_mul (518175 / 4096 : ℝ)),
    intervalIntegral.integral_sub
      ((((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ))).add
        (h12.const_mul (58369311 / 4096 : ℝ))).sub
        (h10.const_mul (22837815 / 2048 : ℝ)) |>.add
        (h8.const_mul (39372795 / 8192 : ℝ)))
      (h6.const_mul (2288055 / 2048 : ℝ)),
    intervalIntegral.integral_add
      (((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ))).add
        (h12.const_mul (58369311 / 4096 : ℝ)) |>.sub
        (h10.const_mul (22837815 / 2048 : ℝ)))
      (h8.const_mul (39372795 / 8192 : ℝ)),
    intervalIntegral.integral_sub
      ((h16.const_mul (41409225 / 16384 : ℝ)).sub
        (h14.const_mul (19324305 / 2048 : ℝ)) |>.add
        (h12.const_mul (58369311 / 4096 : ℝ)))
      (h10.const_mul (22837815 / 2048 : ℝ)),
    intervalIntegral.integral_add
      (h16.const_mul (41409225 / 16384 : ℝ) |>.sub
        (h14.const_mul (19324305 / 2048 : ℝ)))
      (h12.const_mul (58369311 / 4096 : ℝ)),
    intervalIntegral.integral_sub
      (h16.const_mul (41409225 / 16384 : ℝ))
      (h14.const_mul (19324305 / 2048 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_sixteen,
    integral_endpointPotential_mul_pow_fourteen,
    integral_endpointPotential_mul_pow_twelve,
    integral_endpointPotential_mul_pow_ten,
    integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

/-- The exact endpoint-potential coefficient relative to the `P8` energy. -/
theorem factorTwoCenteredP8_potential_ratio :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP8 =
      (1696405 / 1225224 - Real.log 2) *
        factorTwoIntrinsicEnergy factorTwoCenteredP8 := by
  unfold factorTwoIntrinsicPotentialEnergy
  rw [integral_endpointPotential_mul_factorTwoCenteredP8_sq,
    factorTwoCenteredP8_energy]
  ring

theorem factorTwoCenteredP8_raw_reserve :
    (harmonic 8 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP8 ≤
      centeredRawLogEnergy factorTwoCenteredP8 / 4 :=
  harmonic_mul_intrinsicEnergy_le_raw_div_four factorTwoCenteredP8
    continuous_factorTwoCenteredP8 locallyLipschitzOn_factorTwoCenteredP8
    8 factorTwoCenteredP8_momentsVanishBelow

/-! ## Uniform phase reserve -/

private theorem zero_locallyLipschitzOn :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
  have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
  change LocallyLipschitzOn (Icc (-1) 1) (fun _ : ℝ ↦ (0 : ℝ))
  exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)

private theorem factorTwoEndpointChannelPhase_even_zero_b_independent
    (e : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointChannelPhase e 0 a b =
      factorTwoEndpointChannelPhase e 0 a 0 := by
  have hAlt : factorTwoCenteredAlternatingCoupling e (0 : ℝ → ℝ) = 0 := by
    have h := factorTwoCenteredAlternatingCoupling_smul_right
      0 e (fun _ : ℝ ↦ 1)
    norm_num at h
    exact h
  unfold factorTwoEndpointChannelPhase
  rw [hAlt]
  ring

private theorem projected_self_phase_variable_le_702_div_1000
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (Real.log 2 / Real.sqrt 2) * a ≤ 702 / 1000 := by
  let d := factorTwoIntrinsicSelfRegularHalfWidth
  let alpha := Real.log 2 / Real.sqrt 2
  have hlogLower := strict_log_two_fine_bounds.1
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hdUpper : d < (211 / 1000 : ℝ) := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    positivity
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have halphaUpper : alpha < (491 / 1000 : ℝ) := by
    dsimp only [alpha]
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith [Real.log_two_lt_d9]
  have habs : |a| ≤ 1 := by
    nlinarith [sq_abs a, abs_nonneg a]
  have haAbs : alpha * a ≤ alpha * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) halpha0
  have hsum : d + alpha < (702 / 1000 : ℝ) := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hsum.le (abs_nonneg a)
  dsimp only [d, alpha] at hscaled ⊢
  nlinarith

private theorem P8_projected_loss_budget
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a 0 +
        Real.log 2 / 2 + (33 / 100 : ℝ) ≤
      (harmonic 8 : ℝ) +
        (1 / 2 : ℝ) * (1696405 / 1225224 - Real.log 2) := by
  have hphase := projected_self_phase_variable_le_702_div_1000 a ha
  have hbeta := log_three_div_sqrt_three_kernel_bounds.2
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlog := strict_log_two_fine_bounds.2
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at hphase ⊢
  linarith

/-- The complete pure `P8` phase retains `33/100` of its `L²` energy. -/
theorem thirty_three_hundredths_energy_le_P8_phase
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (33 / 100 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP8 ≤
      factorTwoEndpointChannelPhase factorTwoCenteredP8 0 a b := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hab0 : a ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by simpa using ha
  have hraw := factorTwoCenteredP8_raw_reserve
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    factorTwoCenteredP8 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP8 (by fun_prop)
    locallyLipschitzOn_factorTwoCenteredP8 zero_locallyLipschitzOn
    a 0 hab0
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    factorTwoCenteredP8 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP8 (by fun_prop)
    even_factorTwoCenteredP8 (by intro x; simp)
    factorTwoCenteredP8_p0_zero a 0 hab0
  have hbudget := P8_projected_loss_budget a ha
  have henergy := factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP8
  have hbudgetScaled := mul_le_mul_of_nonneg_right hbudget henergy
  have hzeroRaw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicPotentialEnergy
    simp
  have hzeroEnergy : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicEnergy
    simp
  rw [factorTwoCenteredP8_potential_ratio] at hprotected
  rw [hzeroRaw, hzeroPotential, hzeroEnergy] at hprotected
  rw [hzeroEnergy] at hremainder
  norm_num only [zero_div, add_zero, mul_zero, sub_zero] at hprotected hremainder
  have hphase :
      (33 / 100 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP8 ≤
        factorTwoEndpointChannelPhase factorTwoCenteredP8 0 a 0 := by
    rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
      factorTwoCenteredP8 (0 : ℝ → ℝ)
        continuous_factorTwoCenteredP8 (by fun_prop) a 0]
    nlinarith
  rw [factorTwoEndpointChannelPhase_even_zero_b_independent
    factorTwoCenteredP8 a b]
  exact hphase

/-- After arbitrary real scaling, the exact `P8` reserve is `33/850 c²`. -/
theorem thirty_three_eight_hundred_fiftieths_sq_le_scaled_P8_phase
    (c a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (33 / 850 : ℝ) * c ^ 2 ≤
      factorTwoEndpointChannelPhase (c • factorTwoCenteredP8) 0 a b := by
  have hbase := thirty_three_hundredths_energy_le_P8_phase a b hab
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  have hphaseScale := factorTwoEndpointChannelPhase_smul
    factorTwoCenteredP8 (0 : ℝ → ℝ) c a b
  simp only [smul_zero] at hphaseScale
  rw [factorTwoCenteredP8_energy] at hscaled
  rw [hphaseScale]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ExactPotentialStructural
