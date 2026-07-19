import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCoshMixedStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCapacityCauchyStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellEvenCoshMixedStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
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
