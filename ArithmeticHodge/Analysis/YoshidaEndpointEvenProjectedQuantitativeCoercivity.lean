import ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedQuantitativeCoercivity

noncomputable section

open TwoByTwoSchur
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenProjectedBaseIntegrable
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedGapMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopeFinal
open YoshidaEndpointEvenProjectedRemainderIntegrable
open YoshidaEndpointEvenProjectedRemainderMajorant
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenProjectedWeightedLp
open YoshidaEndpointEvenResidualRegularity
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural

/-- The strict two-by-two reserve already present in the projected-dual
argument dominates a scalar multiple of the Euclidean low-coordinate norm.
This is a structural two-dimensional estimate, not a large Gram
certificate. -/
theorem fixedProjectedGap_sub_remainder_quadratic_ge
    (c b : ℝ) :
    (1 / 3000 : ℝ) * (c ^ 2 + b ^ 2) ≤
      (fixedProjectedGapGram00 -
          fixedProjectedPolynomialRemainderGram00) * c ^ 2 +
        2 * (fixedProjectedGapGram02 -
          fixedProjectedPolynomialRemainderGram02) * c * b +
        (fixedProjectedGapGram22 -
          fixedProjectedPolynomialRemainderGram22) * b ^ 2 := by
  let d00 : ℝ := fixedProjectedGapGram00 -
    fixedProjectedPolynomialRemainderGram00
  let d02 : ℝ := fixedProjectedGapGram02 -
    fixedProjectedPolynomialRemainderGram02
  let d22 : ℝ := fixedProjectedGapGram22 -
    fixedProjectedPolynomialRemainderGram22
  have h00 : (14463 / 50000 : ℝ) < d00 := by
    simpa only [d00] using fixedProjectedGap_sub_remainder00_gt
  have h22 : (11789 / 50000 : ℝ) < d22 := by
    simpa only [d22] using fixedProjectedGap_sub_remainder22_gt
  have h02 : (26073 / 100000 : ℝ) < d02 ∧
      d02 < (26077 / 100000 : ℝ) := by
    simpa only [d02] using fixedProjectedGap_sub_remainder02_bounds
  have h02pos : 0 < d02 :=
    (by norm_num : (0 : ℝ) < 26073 / 100000).trans h02.1
  have h02sq : d02 ^ 2 < (26077 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h02.2 h02pos.le (by norm_num)
  have hfirst : 0 < d00 - (1 / 3000 : ℝ) := by
    norm_num at h00 ⊢
    linarith
  have hprod :
      ((14463 / 50000 : ℝ) - 1 / 3000) *
          ((11789 / 50000 : ℝ) - 1 / 3000) <
        (d00 - 1 / 3000) * (d22 - 1 / 3000) := by
    apply mul_lt_mul
    · linarith
    · linarith
    · norm_num
    · linarith
  have hdet : 0 <
      (d00 - 1 / 3000) * (d22 - 1 / 3000) - d02 ^ 2 := by
    norm_num at hprod h02sq ⊢
    linarith
  have hquad := quadratic_add_tail_nonneg
    (d00 - 1 / 3000) d02 (d22 - 1 / 3000)
    0 0 0 c b hfirst hdet (by norm_num)
  dsimp only [d00, d02, d22] at hquad ⊢
  nlinarith

/-- The fixed projected weighted-dual estimate retains the preceding
`1 / 3000` reserve.  The earlier nonnegative theorem discarded this strict
matrix slack at its last step. -/
theorem fixedProjectedWeightedDual_add_reserve_le_exactLowGram
    (c b : ℝ) :
    (∫ x : ℝ in -1..1,
        (c * fixedProjectedTailRepresenter0 x +
          b * fixedProjectedTailRepresenter2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) +
        (1 / 3000 : ℝ) * (c ^ 2 + b ^ 2) ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  have hbase := intervalIntegrable_fixedProjectedDualBaseIntegrand c b
  have htrue := intervalIntegrable_fixedProjectedTrueRemainderIntegrand c b
  have hatanh := intervalIntegrable_fixedProjectedAtanhRemainderIntegrand c b
  have hpoly := intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand c b
  have hdecomp := fixedProjectedDual_integral_decomposition
    c b hbase htrue
  have htrueLe := fixedProjectedTrueRemainder_integral_le_atanh
    c b htrue hatanh
  have hatanhLe := fixedProjectedAtanhRemainder_integral_le_polynomial
    c b hatanh hpoly
  have hpolyEq := integral_fixedProjectedPolynomialRemainder_eq_gram
    c b
    intervalIntegrable_fixedProjectedPolynomialRemainderGram00Integrand
    intervalIntegrable_fixedProjectedPolynomialRemainderGram02Integrand
    intervalIntegrable_fixedProjectedPolynomialRemainderGram22Integrand
  have hgapEq := exactLowGram_sub_baseIntegral_eq_gapGram
    c b
    (intervalIntegrable_fixedProjectedDualBaseIntegrand 1 0)
    intervalIntegrable_fixedProjectedDualBaseCrossIntegrand
    (intervalIntegrable_fixedProjectedDualBaseIntegrand 0 1)
  have hreserve := fixedProjectedGap_sub_remainder_quadratic_ge c b
  unfold fixedProjectedDualIntegrand at hdecomp
  rw [hpolyEq] at hatanhLe
  linarith

/-- A convenient uniform upper bound for the exact two-dimensional clean
low Gram. -/
theorem exactEvenLowGram_quadratic_le_three_quarters
    (c b : ℝ) :
    yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 ≤
      (3 / 4 : ℝ) * (c ^ 2 + b ^ 2) := by
  have h00 : yoshidaEndpointEvenLowGram00 < (3668 / 10000 : ℝ) :=
    intrinsicEven_cleanGram00_lt_step01
  have h02 := intrinsicEven_cleanGram02_bounds
  have h22 : yoshidaEndpointEvenLowGram22 < (3271 / 10000 : ℝ) :=
    intrinsicEven_cleanGram22_lt_step01
  have h02nonneg : 0 ≤ yoshidaEndpointEvenLowGram02 := by
    linarith [h02.1]
  have hcrossBase : 2 * c * b ≤ c ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (c - b)]
  have hcross := mul_le_mul_of_nonneg_left hcrossBase h02nonneg
  have h00scaled := mul_le_mul_of_nonneg_right h00.le (sq_nonneg c)
  have h22scaled := mul_le_mul_of_nonneg_right h22.le (sq_nonneg b)
  have h02scaled := mul_le_mul_of_nonneg_right h02.2.le
    (add_nonneg (sq_nonneg c) (sq_nonneg b))
  calc
    yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2 ≤
        (3668 / 10000 : ℝ) * c ^ 2 +
          yoshidaEndpointEvenLowGram02 * (c ^ 2 + b ^ 2) +
          (3271 / 10000 : ℝ) * b ^ 2 := by
            nlinarith
    _ ≤ (3668 / 10000 : ℝ) * c ^ 2 +
          (3403 / 10000 : ℝ) * (c ^ 2 + b ^ 2) +
          (3271 / 10000 : ℝ) * b ^ 2 := by
            linarith
    _ ≤ (3 / 4 : ℝ) * (c ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg c, sq_nonneg b]

/-- Quantitative projected Schur closure.  A fixed fraction of both the
two low Legendre coordinates and the weighted orthogonal residual survives
completion of the square. -/
theorem fixedProjected_low_tail_quantitative
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (c b : ℝ) :
    (1 / 6000 : ℝ) * (c ^ 2 + b ^ 2) +
        (1 / 4500 : ℝ) *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailWeight x * r x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic
        (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1) 1)
  let W : ℝ → ℝ := yoshidaEndpointEvenTailWeight
  let G : ℝ → ℝ := fun x ↦
    c * fixedProjectedTailRepresenter0 x +
      b * fixedProjectedTailRepresenter2 x
  let D : ℝ := ∫ x : ℝ in -1..1, G x ^ 2 / W x
  let H : ℝ := ∫ x : ℝ in -1..1, W x * r x ^ 2
  let X : ℝ := ∫ x : ℝ in -1..1, G x * r x
  let Q : ℝ := yoshidaEndpointEvenLowGram00 * c ^ 2 +
    2 * yoshidaEndpointEvenLowGram02 * c * b +
    yoshidaEndpointEvenLowGram22 * b ^ 2
  let S : ℝ := c ^ 2 + b ^ 2
  have hW : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact yoshidaEndpointEvenTailWeight_pos_on_Icc
      (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  have hmeasureIntegral (g : ℝ → ℝ) :
      (∫ x, g x ∂μ) = ∫ x : ℝ in -1..1, g x := by
    dsimp only [μ]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hdualLp : MemLp (fun x : ℝ ↦ G x / Real.sqrt (W x)) 2 μ := by
    simpa only [G, W, μ] using
      fixedProjectedTailRepresenter_div_sqrt_memLp_two c b
  have hprimal : MemLp (fun x : ℝ ↦ Real.sqrt (W x) * r x) 2 μ := by
    simpa only [W, μ] using sqrt_tailWeight_mul_memLp_two r hr
  have hcauchy := sq_integral_mul_le_weighted μ W G r
    hW hdualLp hprimal
  rw [hmeasureIntegral (fun x ↦ G x * r x),
    hmeasureIntegral (fun x ↦ G x ^ 2 / W x),
    hmeasureIntegral (fun x ↦ W x * r x ^ 2)] at hcauchy
  change X ^ 2 ≤ D * H at hcauchy
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    exact div_nonneg (sq_nonneg _) (yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc).le
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    exact mul_nonneg (yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc).le
      (sq_nonneg _)
  have hdualReserve : D + (1 / 3000 : ℝ) * S ≤ Q := by
    simpa only [D, W, G, S, Q] using
      fixedProjectedWeightedDual_add_reserve_le_exactLowGram c b
  have hQupper : Q ≤ (3 / 4 : ℝ) * S := by
    simpa only [Q, S] using exactEvenLowGram_quadratic_le_three_quarters c b
  have hscaledCross :
      (4499 * 4500 * X) ^ 2 ≤
        (4500 ^ 2 * D) * (4499 ^ 2 * H) := by
    nlinarith
  have hscaledLow : 0 ≤ 4500 ^ 2 * D := by positivity
  have hscaledTail : 0 ≤ 4499 ^ 2 * H := by positivity
  have hcomplete := scalar_low_tail_nonneg
    (4500 ^ 2 * D) (4499 ^ 2 * H) (4499 * 4500 * X)
    hscaledLow hscaledTail hscaledCross
  have hcore :
      (1 / 6000 : ℝ) * S + (1 / 4500 : ℝ) * H ≤
        Q + 2 * X + H := by
    norm_num at hcomplete ⊢
    linarith
  have htail := weighted_tail_mass_le_cleanQuadratic
    r hr hre hzero htwo hlocal
  change H ≤ yoshidaEndpointOddCleanQuadratic r at htail
  have hcross0 := intervalIntegrable_yoshidaEndpointEvenTailRepresenter0_mul r hr
  have hcross2 := intervalIntegrable_yoshidaEndpointEvenTailRepresenter2_mul r hr
  have hprojected0 : IntervalIntegrable
      (fun x ↦ fixedProjectedTailRepresenter0 x * r x)
      volume (-1) 1 := by
    simpa only [fixedProjectedTailRepresenter0,
      yoshidaEndpointEvenTailRepresenter0] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP0 r hr (73 / 48) (35 / 48) hcross0
  have hprojected2 : IntervalIntegrable
      (fun x ↦ fixedProjectedTailRepresenter2 x * r x)
      volume (-1) 1 := by
    simpa only [fixedProjectedTailRepresenter2,
      yoshidaEndpointEvenTailRepresenter2] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP2 r hr (7 / 48) (1 / 2) hcross2
  have hpair0 :
      (∫ x : ℝ in -1..1, fixedProjectedTailRepresenter0 x * r x) =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter0 x * r x := by
    simpa only [fixedProjectedTailRepresenter0,
      yoshidaEndpointEvenTailRepresenter0] using
      integral_projectedTailRepresenter_mul_eq
        centeredEvenP0 r hr hzero htwo (73 / 48) (35 / 48) hcross0
  have hpair2 :
      (∫ x : ℝ in -1..1, fixedProjectedTailRepresenter2 x * r x) =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter2 x * r x := by
    simpa only [fixedProjectedTailRepresenter2,
      yoshidaEndpointEvenTailRepresenter2] using
      integral_projectedTailRepresenter_mul_eq
        centeredEvenP2 r hr hzero htwo (7 / 48) (1 / 2) hcross2
  have hX : X =
      c * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailRepresenter0 x * r x) +
      b * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailRepresenter2 x * r x) := by
    dsimp only [X, G]
    rw [show (fun x : ℝ ↦
        (c * fixedProjectedTailRepresenter0 x +
          b * fixedProjectedTailRepresenter2 x) * r x) =
        fun x ↦ c * (fixedProjectedTailRepresenter0 x * r x) +
          b * (fixedProjectedTailRepresenter2 x * r x) by
      funext x
      ring,
      intervalIntegral.integral_add
        (hprojected0.const_mul c) (hprojected2.const_mul b),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hpair0, hpair2]
  have hform := yoshidaEndpointOddCleanQuadratic_fixed_low_tail_expansion
    r hr hre hzero htwo hlocal c b
  rw [hform]
  dsimp only [S, H, Q] at hcore ⊢
  nlinarith [hX, htail]

/-- The complete continuous even clean endpoint form has an explicit global
`L²` gap.  The small constant comes from retaining the strict projected-dual
matrix reserve and then completing the low/tail square with a rational
margin. -/
theorem one_over_twelve_thousand_energy_le_even_clean
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    (1 / 12000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  let c : ℝ := centeredEvenP0Coefficient w
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  let H : ℝ := ∫ x : ℝ in -1..1,
    yoshidaEndpointEvenTailWeight x * r x ^ 2
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredEvenZeroTwoResidual w hw
  have hre : Function.Even r := by
    simpa only [r] using centeredEvenZeroTwoResidual_even w hweven
  have hzero : centeredEvenP0Coefficient r = 0 := by
    simpa only [r] using
      centeredEvenP0Coefficient_zeroTwoResidual_eq_zero w hw
  have htwo : centeredEvenP2Coefficient r = 0 := by
    simpa only [r] using
      centeredEvenP2Coefficient_zeroTwoResidual_eq_zero w hw
  have hlocalR : LocallyLipschitzOn (Icc (-1) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredEvenZeroTwoResidual w hlocal
  have hquant := fixedProjected_low_tail_quantitative
    r hr hre hzero htwo hlocalR c b
  have hdecomp :
      (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) = w := by
    simpa only [c, b, r] using low_add_zeroTwoResidual_eq w
  rw [hdecomp] at hquant
  change (1 / 6000 : ℝ) * (c ^ 2 + b ^ 2) +
      (1 / 4500 : ℝ) * H ≤
    yoshidaEndpointOddCleanQuadratic w at hquant
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * r x ^ 2)
      volume (-1) 1 := intervalIntegrable_endpointPotential_mul_sq r hr
  have hpotentialNonneg :
      0 ≤ ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * r x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  have hrSq : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (-1) 1 := (hr.pow 2).intervalIntegrable (-1) 1
  have hweight : H = (41 / 60 : ℝ) * R +
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * r x ^ 2 := by
    dsimp only [H, R]
    rw [show (fun x : ℝ ↦
        yoshidaEndpointEvenTailWeight x * r x ^ 2) =
      fun x ↦ (41 / 60 : ℝ) * r x ^ 2 +
        yoshidaEndpointPotential x * r x ^ 2 by
          funext x
          unfold yoshidaEndpointEvenTailWeight
          ring,
      intervalIntegral.integral_add
        (hrSq.const_mul (41 / 60 : ℝ)) hpotential,
      intervalIntegral.integral_const_mul]
  have hHlower : (41 / 60 : ℝ) * R ≤ H := by
    rw [hweight]
    linarith
  have hHscaled := mul_le_mul_of_nonneg_left hHlower
    (by norm_num : (0 : ℝ) ≤ 1 / 4500)
  have hmass := integral_centeredEvenZeroTwoResidual_sq w hw
  change R = (∫ x : ℝ in -1..1, w x ^ 2) -
      2 * c ^ 2 - (2 / 5 : ℝ) * b ^ 2 at hmass
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedQuantitativeCoercivity
