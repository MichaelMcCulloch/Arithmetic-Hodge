import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCoshMixedStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCapacityCauchyStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open YoshidaConstantBounds
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellEvenCoshMixedStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelLowerStructural
open YoshidaRegularKernelBound

/-!
# Structural Cauchy for the even endpoint-capacity form

The endpoint potential and the adverse dyadic translation are retained as a
single quadratic form.  Its universal positivity on the even sector supplies
the exact Cauchy inequality for its polarization, without estimating the
singular potential row and the prime row separately.
-/

/-- The retained even endpoint-capacity quadratic: endpoint potential minus
the exact dyadic translation. -/
def fourCellEvenEndpointCapacityQuadratic (w : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

/-- The exact polarization of `fourCellEvenEndpointCapacityQuadratic`. -/
def fourCellEvenEndpointCapacityPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x * v x) -
    Real.sqrt 2 * Real.log 2 *
      factorTwoCenteredCorrelationBilinear u v (8 / 5)

private theorem upperStripPotential_le_fullPotential_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    2 * (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  have hgFull : IntervalIntegrable g volume (-1) 1 := by
    simpa only [g] using intervalIntegrable_endpointPotential_mul_sq w hw
  have hgEven : Function.Even g := by
    intro x
    dsimp only [g, yoshidaEndpointPotential]
    rw [heven x]
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    g hgFull hgEven
  have hleft : IntervalIntegrable g volume 0 (3 / 5) := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable g volume (3 / 5) 1 := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤ ∫ x : ℝ in 0..3 / 5, g x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  dsimp only [g] at hfold hsplit hleftNonneg ⊢
  linarith

/-- The retained endpoint-capacity quadratic is nonnegative on every
continuous even profile. -/
theorem fourCellEvenEndpointCapacityQuadratic_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    0 ≤ fourCellEvenEndpointCapacityQuadratic w := by
  let S : ℝ := ∫ x : ℝ in 3 / 5..1,
    yoshidaEndpointPotential x * w x ^ 2
  let V : ℝ := ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * w x ^ 2
  let P : ℝ := Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hprime : P ≤ (99 / 50 : ℝ) * S := by
    simpa only [P, S] using
      fourCell_dyadicPairing_le_endpointStripPotential w hw heven
  have hstrip : 2 * S ≤ V := by
    simpa only [S, V] using
      upperStripPotential_le_fullPotential_of_even w hw heven
  have hS : 0 ≤ S := by
    dsimp only [S]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  unfold fourCellEvenEndpointCapacityQuadratic
  change 0 ≤ V - P
  nlinarith

/-- Exact quadratic expansion of the retained endpoint-capacity form. -/
theorem fourCellEvenEndpointCapacityQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellEvenEndpointCapacityQuadratic (u + v) =
      fourCellEvenEndpointCapacityQuadratic u +
        2 * fourCellEvenEndpointCapacityPolarization u v +
      fourCellEvenEndpointCapacityQuadratic v := by
  have hpotential := integral_endpointPotential_add_sq u v hu hv
  have hprime := centeredEndpointCorrelation_add u v hu hv (8 / 5)
  unfold fourCellEvenEndpointCapacityQuadratic
    fourCellEvenEndpointCapacityPolarization
  simp only [Pi.add_apply]
  rw [hpotential,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    hprime]
  ring

/-- Homogeneity of the retained endpoint-capacity quadratic. -/
theorem fourCellEvenEndpointCapacityQuadratic_smul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEvenEndpointCapacityQuadratic (c • w) =
      c ^ 2 * fourCellEvenEndpointCapacityQuadratic w := by
  have hpotential :
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * (c • w) x ^ 2) =
        c ^ 2 *
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * (c • w) x ^ 2) =
        fun x ↦ c ^ 2 * (yoshidaEndpointPotential x * w x ^ 2) by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  have hprime : fourCellEndpointPairing (c • w) =
      c ^ 2 * fourCellEndpointPairing w := by
    rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation,
      fourCellEndpointPairing_eq_centeredEndpointCorrelation,
      ← factorTwoCenteredCorrelationBilinear_self,
      ← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  unfold fourCellEvenEndpointCapacityQuadratic
  rw [hpotential, hprime]
  ring

/-- Linearity of the retained polarization in its second real argument. -/
theorem fourCellEvenEndpointCapacityPolarization_smul_right
    (c : ℝ) (u v : ℝ → ℝ) :
    fourCellEvenEndpointCapacityPolarization u (c • v) =
      c * fourCellEvenEndpointCapacityPolarization u v := by
  have hpotential :
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * u x * (c • v) x) =
        c *
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x * v x := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * u x * (c • v) x) =
        fun x ↦ c * (yoshidaEndpointPotential x * u x * v x) by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  have hprime :
      factorTwoCenteredCorrelationBilinear u (c • v) (8 / 5) =
        c * factorTwoCenteredCorrelationBilinear u v (8 / 5) := by
    simpa only [one_smul, one_mul] using
      factorTwoCenteredCorrelationBilinear_smul_smul 1 c u v (8 / 5)
  unfold fourCellEvenEndpointCapacityPolarization
  rw [hpotential, hprime]
  ring

private theorem sq_le_mul_of_forall_quadratic_nonneg
    (a b c : ℝ) (hc : 0 ≤ c)
    (hquad : ∀ t : ℝ, 0 ≤ a + 2 * b * t + c * t ^ 2) :
    b ^ 2 ≤ a * c := by
  by_cases hc0 : c = 0
  · subst c
    have hb : b = 0 := by
      by_contra hb0
      let t : ℝ := -(a + 1) / (2 * b)
      have hq := hquad t
      have ht : 2 * b * t = -(a + 1) := by
        dsimp only [t]
        field_simp [hb0]
      simp only [zero_mul] at hq
      rw [ht] at hq
      linarith
    rw [hb]
    norm_num
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hq := hquad (-b / c)
    have heq :
        a + 2 * b * (-b / c) + c * (-b / c) ^ 2 =
          (a * c - b ^ 2) / c := by
      field_simp [ne_of_gt hcpos]
      ring
    rw [heq] at hq
    have hmul := mul_nonneg hq hc
    have hcancel : ((a * c - b ^ 2) / c) * c =
        a * c - b ^ 2 := by
      field_simp [ne_of_gt hcpos]
    rw [hcancel] at hmul
    linarith

/-- Structural Cauchy--Schwarz for the complete retained endpoint-capacity
form.  It follows from nonnegativity of the whole scalar pencil, so the prime
and potential pieces are never separated. -/
theorem fourCellEvenEndpointCapacityPolarization_sq_le_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hevenU : Function.Even u) (hevenV : Function.Even v) :
    fourCellEvenEndpointCapacityPolarization u v ^ 2 ≤
      fourCellEvenEndpointCapacityQuadratic u *
        fourCellEvenEndpointCapacityQuadratic v := by
  let a := fourCellEvenEndpointCapacityQuadratic u
  let b := fourCellEvenEndpointCapacityPolarization u v
  let c := fourCellEvenEndpointCapacityQuadratic v
  have hc : 0 ≤ c := by
    simpa only [c] using
      fourCellEvenEndpointCapacityQuadratic_nonnegative v hv hevenV
  apply sq_le_mul_of_forall_quadratic_nonneg a b c hc
  intro t
  have htv : Continuous (t • v) := by
    change Continuous (fun x ↦ t * v x)
    exact continuous_const.mul hv
  have hcont : Continuous (u + t • v) := hu.add htv
  have heven : Function.Even (u + t • v) := by
    intro x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hevenU x, hevenV x]
  have hnonneg :=
    fourCellEvenEndpointCapacityQuadratic_nonnegative
      (u + t • v) hcont heven
  rw [fourCellEvenEndpointCapacityQuadratic_add u (t • v) hu htv,
    fourCellEvenEndpointCapacityPolarization_smul_right,
    fourCellEvenEndpointCapacityQuadratic_smul] at hnonneg
  dsimp only [a, b, c]
  nlinarith only [hnonneg]

/-! ## The complementary scalar and smooth-kernel form -/

/-- The scalar mass and smooth regular-kernel diagonal which is subtracted
from the raw-plus-endpoint core in the polar-free even operator. -/
def fourCellEvenSignedMassRegularQuadratic (w : ℝ → ℝ) : ℝ :=
  (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in -1..1, w x ^ 2) +
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- The exact polarization of the scalar-mass and smooth regular-kernel
diagonal. -/
def fourCellEvenSignedMassRegularPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in -1..1, u x * v x) +
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t)

private theorem intervalIntegrable_fourCellRegularKernel_mul_continuous
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1.le
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- The complete smooth regular correlation has the generic sharp quarter
mass bound.  No parity or sign is imposed on the profile. -/
theorem abs_fourCellEvenRegularCorrelation_le_quarter_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    |(∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)| ≤
      (1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hKC := intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t| ≤
        (1 / 4 : ℝ) * |C t| := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    rw [abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg _)
  have habsInt := hKC.abs
  have hmajorInt : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 4 : ℝ) * |C t|) volume 0 2 :=
    (hC.abs.intervalIntegrable _ _).const_mul (1 / 4)
  have hmono :
      (∫ t : ℝ in 0..2,
          |yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t|) ≤
        ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habsInt hmajorInt
    exact hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2)
    (f := fun t ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      (μ := volume)
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy w hw
  rw [intervalIntegral.integral_const_mul] at hmono
  simp only [Real.norm_eq_abs] at hnorm
  linarith

private theorem one_lt_fourCellScalar :
    (1 : ℝ) < Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  have hfive : 0 < Real.log (5 / 4 : ℝ) :=
    Real.log_pos (by norm_num)
  rw [hwidth]
  linarith [strict_log_log_two_bounds.1,
    strict_euler_gamma_bounds.1, strict_log_pi_bounds.1]

private theorem fourCellOperatorHalfWidth_le_one_half :
    fourCellOperatorHalfWidth ≤ (1 / 2 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  nlinarith

/-- The scalar-mass plus smooth regular-kernel form is positive on every
continuous real profile. -/
theorem fourCellEvenSignedMassRegularQuadratic_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w) :
    0 ≤ fourCellEvenSignedMassRegularQuadratic w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hRabs : |R| ≤ (1 / 4 : ℝ) * M := by
    simpa only [R, M] using
      abs_fourCellEvenRegularCorrelation_le_quarter_mass w hw
  have hRlower : -(1 / 4 : ℝ) * M ≤ R := by
    linarith [neg_abs_le R]
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hregular := mul_le_mul_of_nonneg_left hRlower ha0
  have hS : 1 < S := by simpa only [S] using one_lt_fourCellScalar
  have ha := fourCellOperatorHalfWidth_le_one_half
  unfold fourCellEvenSignedMassRegularQuadratic
  dsimp only [M, R, S] at hregular hS ⊢
  nlinarith

/-- Exact quadratic expansion of the scalar-mass and smooth-kernel form. -/
theorem fourCellEvenSignedMassRegularQuadratic_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellEvenSignedMassRegularQuadratic (u + v) =
      fourCellEvenSignedMassRegularQuadratic u +
        2 * fourCellEvenSignedMassRegularPolarization u v +
      fourCellEvenSignedMassRegularQuadratic v := by
  have hmass := integral_add_sq u v hu hv
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous (factorTwoCenteredCorrelationBilinear u v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hIu := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (centeredEndpointCorrelation u) hCu
  have hIv := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (centeredEndpointCorrelation v) hCv
  have hIb := intervalIntegrable_fourCellRegularKernel_mul_continuous
    (factorTwoCenteredCorrelationBilinear u v) hB
  unfold fourCellEvenSignedMassRegularQuadratic
    fourCellEvenSignedMassRegularPolarization
  simp only [Pi.add_apply]
  rw [hmass]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (u + v) t) =
      fun t ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation u t +
        (2 * (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) +
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation v t) by
    funext t
    rw [centeredEndpointCorrelation_add u v hu hv t]
    ring,
    intervalIntegral.integral_add hIu ((hIb.const_mul 2).add hIv),
    intervalIntegral.integral_add (hIb.const_mul 2) hIv,
    intervalIntegral.integral_const_mul]
  ring

/-- Homogeneity of the scalar-mass and smooth-kernel form. -/
theorem fourCellEvenSignedMassRegularQuadratic_smul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEvenSignedMassRegularQuadratic (c • w) =
      c ^ 2 * fourCellEvenSignedMassRegularQuadratic w := by
  have hmass :
      (∫ x : ℝ in -1..1, (c • w) x ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [show (fun x : ℝ ↦ (c • w) x ^ 2) =
        fun x ↦ c ^ 2 * w x ^ 2 by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  have hcorr (t : ℝ) : centeredEndpointCorrelation (c • w) t =
      c ^ 2 * centeredEndpointCorrelation w t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      ← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  unfold fourCellEvenSignedMassRegularQuadratic
  rw [hmass]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (c • w) t) =
      fun t ↦ c ^ 2 *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t) by
    funext t
    rw [hcorr]
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Linearity of the scalar-mass and smooth-kernel polarization in its
second real argument. -/
theorem fourCellEvenSignedMassRegularPolarization_smul_right
    (c : ℝ) (u v : ℝ → ℝ) :
    fourCellEvenSignedMassRegularPolarization u (c • v) =
      c * fourCellEvenSignedMassRegularPolarization u v := by
  have hmass :
      (∫ x : ℝ in -1..1, u x * (c • v) x) =
        c * ∫ x : ℝ in -1..1, u x * v x := by
    rw [show (fun x : ℝ ↦ u x * (c • v) x) =
        fun x ↦ c * (u x * v x) by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul]
  have hcorr (t : ℝ) :
      factorTwoCenteredCorrelationBilinear u (c • v) t =
        c * factorTwoCenteredCorrelationBilinear u v t := by
    simpa only [one_smul, one_mul] using
      factorTwoCenteredCorrelationBilinear_smul_smul 1 c u v t
  unfold fourCellEvenSignedMassRegularPolarization
  rw [hmass]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear u (c • v) t) =
      fun t ↦ c *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) by
    funext t
    rw [hcorr]
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Structural Cauchy--Schwarz for the positive scalar-mass and smooth
regular-kernel form. -/
theorem fourCellEvenSignedMassRegularPolarization_sq_le_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellEvenSignedMassRegularPolarization u v ^ 2 ≤
      fourCellEvenSignedMassRegularQuadratic u *
        fourCellEvenSignedMassRegularQuadratic v := by
  apply sq_le_mul_of_forall_quadratic_nonneg
    (fourCellEvenSignedMassRegularQuadratic u)
    (fourCellEvenSignedMassRegularPolarization u v)
    (fourCellEvenSignedMassRegularQuadratic v)
    (fourCellEvenSignedMassRegularQuadratic_nonnegative v hv)
  intro t
  have htv : Continuous (t • v) := by
    change Continuous (fun x ↦ t * v x)
    exact continuous_const.mul hv
  have hnonneg := fourCellEvenSignedMassRegularQuadratic_nonnegative
    (u + t • v) (hu.add htv)
  rw [fourCellEvenSignedMassRegularQuadratic_add u (t • v) hu htv,
    fourCellEvenSignedMassRegularPolarization_smul_right,
    fourCellEvenSignedMassRegularQuadratic_smul] at hnonneg
  nlinarith only [hnonneg]

private theorem log_five_four_lt_4463_div_20000 :
    Real.log (5 / 4 : ℝ) < 4463 / 20000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_lt_eight_fifths :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      (8 / 5 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_lt_4463_div_20000,
    strict_log_log_two_bounds.2, strict_euler_gamma_bounds.2,
    strict_log_pi_bounds.2]

private theorem two_mul_integral_centeredCorrelation_eq_mean_sq_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    2 * (∫ t : ℝ in 0..2, centeredEndpointCorrelation w t) =
      (∫ x : ℝ in -1..1, w x) ^ 2 := by
  have h := two_mul_integral_cosh_mul_centeredCorrelation_of_even
    w hw heven 0
  simpa only [zero_mul, Real.cosh_zero, one_mul, centeredCoshMoment] using h

/-- The constant/even correlation polarization has integral exactly equal
to the ordinary centered mean. -/
theorem integral_factorTwoCenteredCorrelationBilinear_one_even
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t) =
      ∫ x : ℝ in -1..1, v x := by
  let u : ℝ → ℝ := fun _ ↦ 1
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u v
  have hu : Continuous u := continuous_const
  have hueven : Function.Even u := by intro x; rfl
  have huvEven : Function.Even (u + v) := hueven.add heven
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hCuInt : IntervalIntegrable (centeredEndpointCorrelation u)
      volume 0 2 := hCu.intervalIntegrable _ _
  have hCvInt : IntervalIntegrable (centeredEndpointCorrelation v)
      volume 0 2 := hCv.intervalIntegrable _ _
  have hBInt : IntervalIntegrable (fun t : ℝ ↦ 2 * B t)
      volume 0 2 := (hB.const_mul 2).intervalIntegrable _ _
  have hCuBInt : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointCorrelation u t + 2 * B t)
      volume 0 2 := hCuInt.add hBInt
  have hexpand :
      (∫ t : ℝ in 0..2, centeredEndpointCorrelation (u + v) t) =
        (∫ t : ℝ in 0..2, centeredEndpointCorrelation u t) +
          2 * (∫ t : ℝ in 0..2, B t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t := by
    rw [show (fun t : ℝ ↦ centeredEndpointCorrelation (u + v) t) =
        fun t ↦ centeredEndpointCorrelation u t + 2 * B t +
          centeredEndpointCorrelation v t by
      funext t
      dsimp only [B]
      rw [centeredEndpointCorrelation_add u v hu hv t]]
    calc
      _ = (∫ t : ℝ in 0..2,
            centeredEndpointCorrelation u t + 2 * B t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t :=
        intervalIntegral.integral_add hCuBInt hCvInt
      _ = ((∫ t : ℝ in 0..2, centeredEndpointCorrelation u t) +
            ∫ t : ℝ in 0..2, 2 * B t) +
          ∫ t : ℝ in 0..2, centeredEndpointCorrelation v t := by
        rw [intervalIntegral.integral_add hCuInt hBInt]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have huMean : (∫ x : ℝ in -1..1, u x) = 2 := by
    norm_num [u]
  have huvMean :
      (∫ x : ℝ in -1..1, (u + v) x) =
        2 + ∫ x : ℝ in -1..1, v x := by
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_add
      (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _), huMean]
  have hsum := two_mul_integral_centeredCorrelation_eq_mean_sq_of_even
    (u + v) (hu.add hv) huvEven
  have hleft := two_mul_integral_centeredCorrelation_eq_mean_sq_of_even
    u hu hueven
  have hright := two_mul_integral_centeredCorrelation_eq_mean_sq_of_even
    v hv heven
  rw [huvMean] at hsum
  rw [huMean] at hleft
  dsimp only [B, u] at hexpand ⊢
  linarith

private theorem abs_fourCellRegularBilinear_one_even_sub_fifth_mean_le
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v) :
    |(∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t) -
      (1 / 5 : ℝ) * (∫ x : ℝ in -1..1, v x)| ≤
      (1 / 20 : ℝ) *
        ∫ t : ℝ in 0..2,
          |factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t| := by
  let B : ℝ → ℝ :=
    factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v
  let delta : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) - 1 / 5
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation
      (fun _ : ℝ ↦ 1) v continuous_const hv).add
      (continuous_factorTwoCenteredCrossCorrelation
        v (fun _ : ℝ ↦ 1) hv continuous_const)).div_const 2
  have hBint : IntervalIntegrable B volume 0 2 :=
    hB.intervalIntegrable _ _
  have hKB := intervalIntegrable_fourCellRegularKernel_mul_continuous B hB
  have hconst : IntervalIntegrable (fun t : ℝ ↦ (1 / 5 : ℝ) * B t)
      volume 0 2 := hBint.const_mul (1 / 5)
  have hdeltaB : IntervalIntegrable (fun t : ℝ ↦ delta t * B t)
      volume 0 2 := by
    apply hKB.sub hconst |>.congr
    intro t _ht
    dsimp only [delta]
    ring
  have hmean : (∫ t : ℝ in 0..2, B t) =
      ∫ x : ℝ in -1..1, v x := by
    simpa only [B] using
      integral_factorTwoCenteredCorrelationBilinear_one_even v hv heven
  have hrewrite :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * B t) -
        (1 / 5 : ℝ) * (∫ x : ℝ in -1..1, v x) =
      ∫ t : ℝ in 0..2, delta t * B t := by
    rw [show (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * B t) =
      fun t ↦ delta t * B t + (1 / 5 : ℝ) * B t by
      funext t
      dsimp only [delta]
      ring,
      intervalIntegral.integral_add hdeltaB hconst,
      intervalIntegral.integral_const_mul, hmean]
    ring
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |delta t * B t| ≤ (1 / 20 : ℝ) * |B t| := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    have hdelta0 : 0 ≤ delta t := by dsimp only [delta]; linarith
    have hdelta1 : delta t ≤ (1 / 20 : ℝ) := by
      dsimp only [delta]
      linarith
    rw [abs_mul, abs_of_nonneg hdelta0]
    exact mul_le_mul_of_nonneg_right hdelta1 (abs_nonneg _)
  have habsInt := hdeltaB.abs
  have hmajorInt : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 20 : ℝ) * |B t|) volume 0 2 :=
    (hB.abs.intervalIntegrable _ _).const_mul (1 / 20)
  have hmono :
      (∫ t : ℝ in 0..2, |delta t * B t|) ≤
        ∫ t : ℝ in 0..2, (1 / 20 : ℝ) * |B t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habsInt hmajorInt
    exact hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ delta t * B t)
      (μ := volume)
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hrewrite]
  simp only [Real.norm_eq_abs] at hnorm
  dsimp only [B]
  linarith

/-- On the zero-wide-cosh hyperplane, the only remaining scalar/regular
constant row has a small uniform `L²` norm. -/
theorem fourCellEvenSignedMassRegularPolarization_one_sq_le_mass
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v)
    (hzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenSignedMassRegularPolarization (fun _ : ℝ ↦ 1) v ^ 2 ≤
      (17 / 1000 : ℝ) * (∫ x : ℝ in -1..1, v x ^ 2) := by
  let m : ℝ := ∫ x : ℝ in -1..1, v x
  let M : ℝ := ∫ x : ℝ in -1..1, v x ^ 2
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t|
  let J : ℝ :=
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t) -
      (1 / 5 : ℝ) * m
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let C : ℝ := S + 2 * fourCellOperatorHalfWidth / 5
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hmean0 :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      v hv heven hzero
  have hmean : m ^ 2 ≤ (1 / 1000 : ℝ) * M := by
    unfold centeredEvenP0Coefficient at hmean0
    dsimp only [m, M]
    nlinarith
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have hI : I ^ 2 ≤ 2 * M := by
    have h :=
      integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        (fun _ : ℝ ↦ 1) v continuous_const hv
    have hone : factorTwoIntrinsicEnergy (fun _ : ℝ ↦ 1) = 2 := by
      norm_num [factorTwoIntrinsicEnergy]
    rw [hone] at h
    simpa only [I, M, factorTwoIntrinsicEnergy] using h
  have hJ : |J| ≤ (1 / 20 : ℝ) * I := by
    simpa only [J, I, m] using
      abs_fourCellRegularBilinear_one_even_sub_fifth_mean_le
        v hv heven
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    linarith [one_lt_fourCellScalar]
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    positivity
  have hCupper : C ≤ (9 / 5 : ℝ) := by
    dsimp only [C, S]
    have ha := fourCellOperatorHalfWidth_le_one_half
    linarith [fourCellScalar_lt_eight_fifths]
  have hCsq : C ^ 2 ≤ (81 / 25 : ℝ) := by
    nlinarith [sq_nonneg ((9 / 5 : ℝ) - C)]
  have hx : (C * m) ^ 2 ≤ (81 / 25000 : ℝ) * M := by
    have hmul := mul_le_mul_of_nonneg_right hCsq (sq_nonneg m)
    nlinarith [hmul, hmean]
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha1 : 2 * fourCellOperatorHalfWidth ≤ 1 := by
    linarith [fourCellOperatorHalfWidth_le_one_half]
  have hyabs : |2 * fourCellOperatorHalfWidth * J| ≤ I / 20 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc
      2 * fourCellOperatorHalfWidth * |J| ≤ 1 * |J| :=
        mul_le_mul_of_nonneg_right ha1 (abs_nonneg J)
      _ ≤ (1 / 20 : ℝ) * I := by simpa using hJ
      _ = I / 20 := by ring
  have hy : (2 * fourCellOperatorHalfWidth * J) ^ 2 ≤
      (1 / 200 : ℝ) * M := by
    have hsq : (2 * fourCellOperatorHalfWidth * J) ^ 2 ≤
        (I / 20) ^ 2 := by
      rw [← sq_abs (2 * fourCellOperatorHalfWidth * J)]
      exact (sq_le_sq₀ (abs_nonneg _)
        (div_nonneg hI0 (by norm_num))).2 hyabs
    nlinarith [hsq, hI]
  have hrow :
      fourCellEvenSignedMassRegularPolarization (fun _ : ℝ ↦ 1) v =
        C * m + 2 * fourCellOperatorHalfWidth * J := by
    unfold fourCellEvenSignedMassRegularPolarization
    rw [show (fun x : ℝ ↦ 1 * v x) = v by
      funext x
      ring]
    dsimp only [C, S, J, m]
    ring
  change fourCellEvenSignedMassRegularPolarization
      (fun _ : ℝ ↦ 1) v ^ 2 ≤ (17 / 1000 : ℝ) * M
  rw [hrow]
  have hsplit := sq_nonneg (C * m - 2 * fourCellOperatorHalfWidth * J)
  nlinarith [hx, hy, hsplit]

/-- The fixed constant row is exactly the difference between the two
positive endpoint and scalar/regular polarizations. -/
theorem fourCellEvenZeroCoshConstantRow_eq_capacity_sub_signed
    (v : ℝ → ℝ) :
    fourCellEvenZeroCoshConstantRow v =
      fourCellEvenEndpointCapacityPolarization (fun _ : ℝ ↦ 1) v -
        fourCellEvenSignedMassRegularPolarization (fun _ : ℝ ↦ 1) v := by
  unfold fourCellEvenZeroCoshConstantRow
    fourCellEvenEndpointCapacityPolarization
    fourCellEvenSignedMassRegularPolarization
  ring

/-- The singular part of the constant Schur row is exactly the retained
endpoint-capacity polarization against the unit profile. -/
theorem fourCellEvenEndpointCapacityPolarization_one
    (v : ℝ → ℝ) :
    fourCellEvenEndpointCapacityPolarization (fun _ : ℝ ↦ 1) v =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x) -
        Real.sqrt 2 * Real.log 2 *
          factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v (8 / 5) := by
  unfold fourCellEvenEndpointCapacityPolarization
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- Cauchy control of the complete singular constant row. -/
theorem fourCellEvenEndpointCapacityPolarization_one_sq_le
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v) :
    fourCellEvenEndpointCapacityPolarization (fun _ : ℝ ↦ 1) v ^ 2 ≤
      fourCellEvenEndpointCapacityQuadratic (fun _ : ℝ ↦ 1) *
        fourCellEvenEndpointCapacityQuadratic v := by
  exact fourCellEvenEndpointCapacityPolarization_sq_le_mul
    (fun _ : ℝ ↦ 1) v continuous_const hv (by intro x; rfl) heven

/-- The full constant row is the positive endpoint-capacity polarization
minus only the scalar-mass and smooth regular-kernel rows. -/
theorem fourCellEvenZeroCoshConstantRow_eq_capacity_sub_scalar_sub_regular
    (v : ℝ → ℝ) :
    fourCellEvenZeroCoshConstantRow v =
      fourCellEvenEndpointCapacityPolarization (fun _ : ℝ ↦ 1) v -
        (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) *
          (∫ x : ℝ in -1..1, v x) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear
                (fun _ : ℝ ↦ 1) v t) := by
  unfold fourCellEvenZeroCoshConstantRow
    fourCellEvenEndpointCapacityPolarization
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCapacityCauchyStructural
