import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelLowerStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenFiniteSevenTailAssemblyStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
open YoshidaFourCellEvenEndpointSeedUniversalClosureStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelLowerStructural
open YoshidaRegularKernelBound

/-!
# Exact finite-seven / `P14+` tail assembly

The finite-seven certificate controls the bordered diagonal of the six
cosh-quotient modes.  The cutoff-fourteen theorem controls the complete
endpoint row by that finite diagonal plus a tail charge.  This file records
the exact scalar left after those two results are put together.

No entry enclosure is asserted here.  In particular, the theorem below
shows that the current `1 / 16` tail charge cannot simply be discarded: the
fixed endpoint seed diagonal is strictly smaller than `1 / 16`.  A final
assembly therefore has to retain the actual low--tail polarization or sharpen
the tail-row charge (for example by the exact cosh-border Schur complement).
-/

/-- The fixed endpoint-seed diagonal, abbreviated only to make the assembly
identities readable. -/
def fourCellEvenFiniteSevenSeedDiagonal : ℝ :=
  fourCellEvenExactBracket fourCellEvenEndpointCoshSeed

/-- The canonical finite profile through degree twelve. -/
def fourCellEvenFiniteSevenCanonicalLow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreLowProjection w hw 14

/-- The genuine `P14+` residual. -/
def fourCellEvenFiniteSevenCanonicalTail
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreHigherResidual w hw 14

/-- The finite bordered diagonal before choosing quotient coordinates. -/
def fourCellEvenFiniteSevenCanonicalLowBorder
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalLow w hw) -
    (251 / 250 : ℝ) *
      fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2

/-- The exact part of the global determinant not contained in the finite
border after spending the existing `1 / 16` tail-row budget. -/
def fourCellEvenFiniteSevenCanonicalTailCoupling
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  2 * fourCellEvenFiniteSevenSeedDiagonal *
      fourCellEvenFiniteSevenPolarFreePolarization
        (fourCellEvenFiniteSevenCanonicalLow w hw)
        (fourCellEvenFiniteSevenCanonicalTail w hw) +
    (fourCellEvenFiniteSevenSeedDiagonal - (1 / 16 : ℝ)) *
      fourCellEvenPolarFreeOperator
        (fourCellEvenFiniteSevenCanonicalTail w hw)

/-- Lossless low--mixed--tail expansion of the polar-free operator at the
canonical cutoff fourteen.  This uses only the definition of polarization;
no bilinearity or analytic estimate is hidden in the identity. -/
theorem fourCellEvenPolarFreeOperator_eq_finiteSevenLow_add_mixed_add_tail
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenPolarFreeOperator w =
      fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalLow w hw) +
        2 * fourCellEvenFiniteSevenPolarFreePolarization
          (fourCellEvenFiniteSevenCanonicalLow w hw)
          (fourCellEvenFiniteSevenCanonicalTail w hw) +
        fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalTail w hw) := by
  have hsplit := centeredLegendreLowProjection_add_higherResidual w hw 14
  unfold fourCellEvenFiniteSevenPolarFreePolarization
    fourCellEvenFiniteSevenCanonicalLow
    fourCellEvenFiniteSevenCanonicalTail
  rw [hsplit]
  ring

/-- Exact determinant accounting after the current universal endpoint-row
bound is inserted.  This is the structural assembly identity: the first
summand is the finite seven-coordinate border and the second is the sole
remaining low--tail coupling. -/
theorem finiteSevenCanonicalLowBorder_add_tailCoupling_eq_global_sub_budget
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw =
      fourCellEvenFiniteSevenSeedDiagonal *
          fourCellEvenPolarFreeOperator w -
        ((251 / 250 : ℝ) *
            fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
          (1 / 16 : ℝ) *
            fourCellEvenPolarFreeOperator
              (fourCellEvenFiniteSevenCanonicalTail w hw)) := by
  have hsplit :=
    fourCellEvenPolarFreeOperator_eq_finiteSevenLow_add_mixed_add_tail w hw
  unfold fourCellEvenFiniteSevenCanonicalLowBorder
    fourCellEvenFiniteSevenCanonicalTailCoupling
  rw [hsplit]
  ring

/-- The exact remaining structural condition after the six-mode matrix is
identified with the canonical low border.  Under this one condition, the
existing cutoff-fourteen row theorem gives the desired universal endpoint
Schur determinant. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_tailAssembly
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hassembly : 0 ≤
      fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hrow :=
    fourCellEvenEndpointSeedRow_sq_le_251_div_250_lowThroughTwelve_add_one_sixteenth_tailPolarFree
      w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator
          (fourCellEvenFiniteSevenCanonicalTail w hw) := by
    simpa only [fourCellEvenFiniteSevenCanonicalTail] using hrow
  have hid :=
    finiteSevenCanonicalLowBorder_add_tailCoupling_eq_global_sub_budget w hw
  linarith only [hrow', hassembly, hid]

/-- Direct handoff from the named six-coordinate certificate.  The equality
`hmatrix` is the exact quotient-coordinate synthesis identity; `hcoupling`
is the genuinely infinite low--tail reserve.  Thus the twenty-one entry boxes
and the operator assembly are kept as logically independent obligations. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_finiteSeven
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hbox : fourCellEvenFiniteSevenTrueBorderEntryBox)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ)
    (hmatrix :
      fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
          x₂ x₄ x₆ x₈ x₁₀ x₁₂ =
        fourCellEvenFiniteSevenCanonicalLowBorder w hw)
    (hcoupling : 0 ≤ fourCellEvenFiniteSevenCanonicalTailCoupling w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  have hfinite :=
    finiteSevenTrueBorderMatrixQuadratic_nonnegative_of_entryBox hbox
      x₂ x₄ x₆ x₈ x₁₀ x₁₂
  have hassembly : 0 ≤
      fourCellEvenFiniteSevenCanonicalLowBorder w hw +
        fourCellEvenFiniteSevenCanonicalTailCoupling w hw := by
    rw [← hmatrix]
    exact add_nonneg hfinite hcoupling
  exact
    fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_tailAssembly
      w hw hlocal heven hzero hassembly

/-! ## The current `1/16` budget is not a closable pure-tail allocation -/

private theorem finiteSeven_integral_polynomial_five
    (a₀ a₁ a₂ a₃ a₄ a₅ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
          a₃ * (r ^ 4 - l ^ 4) / 4 +
            a₄ * (r ^ 5 - l ^ 5) / 5 +
              a₅ * (r ^ 6 - l ^ 6) / 6 := by
  rw [show (fun x : ℝ ↦
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5) =
      fun x ↦ a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 +
        a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 by
    funext x
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem finiteSeven_cosh_le_fortyOne_fortieths
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 32 : ℝ)) :
    Real.cosh u ≤ (41 / 40 : ℝ) := by
  have huSqRaw : u ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hv : u ^ 2 / 2 ≤ (49 / 2048 : ℝ) := by
    norm_num at huSqRaw ⊢
    linarith
  have hv1 : u ^ 2 / 2 < 1 := hv.trans_lt (by norm_num)
  have hexp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hfrac : 1 / (1 - u ^ 2 / 2) ≤ (41 / 40 : ℝ) := by
    rw [div_le_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans (hexp.trans hfrac)

private theorem finiteSeven_cosh_le_one_add_fortyOne_eightieths_sq
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 32 : ℝ)) :
    Real.cosh u ≤ 1 + (41 / 80 : ℝ) * u ^ 2 := by
  let v : ℝ := u ^ 2 / 2
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have huSqRaw : u ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hv : v ≤ (49 / 2048 : ℝ) := by
    dsimp only [v]
    norm_num at huSqRaw ⊢
    linarith
  have hv1 : v < 1 := hv.trans_lt (by norm_num)
  have hexp : Real.exp v ≤ 1 / (1 - v) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hlinear : 1 / (1 - v) ≤ 1 + (41 / 40 : ℝ) * v := by
    rw [div_le_iff₀ (sub_pos.mpr hv1)]
    have hvSharp : 41 * v ≤ 1 := by
      calc
        41 * v ≤ 41 * (49 / 2048 : ℝ) :=
          mul_le_mul_of_nonneg_left hv (by norm_num)
        _ ≤ 1 := by norm_num
    nlinarith only [hv0, hvSharp]
  calc
    Real.cosh u ≤ Real.exp (u ^ 2 / 2) := Real.cosh_le_exp_half_sq u
    _ = Real.exp v := by rfl
    _ ≤ 1 / (1 - v) := hexp
    _ ≤ 1 + (41 / 40 : ℝ) * v := hlinear
    _ = 1 + (41 / 80 : ℝ) * u ^ 2 := by
      dsimp only [v]
      ring

private theorem endpointSeed_coshMoment_le_sixtySeven_hundredths :
    fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
        (fourCellOperatorHalfWidth / 2) ≤ (67 / 100 : ℝ) := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda : lambda ≤ (7 / 32 : ℝ) := by
    dsimp only [lambda]
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x ≤
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hz0 : 0 ≤ lambda * x := mul_nonneg hlambda0 hx0
    have hz : lambda * x ≤ (7 / 32 : ℝ) := by
      calc
        lambda * x ≤ lambda * 1 :=
          mul_le_mul_of_nonneg_left hx1 hlambda0
        _ ≤ (7 / 32 : ℝ) := by simpa using hlambda
    have hcosh :=
      finiteSeven_cosh_le_one_add_fortyOne_eightieths_sq hz0 hz
    have hseed : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg x]
    unfold fourCellEvenEndpointCoshSeed
    have hmul := mul_le_mul_of_nonneg_right hcosh hseed
    nlinarith only [hmul]
  have hint :
      (∫ x : ℝ in 0..1,
          Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x) ≤
        ∫ x : ℝ in 0..1,
          (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
            (1 - x ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((Continuous.mul (by fun_prop)
        fourCellEvenEndpointCoshSeed_continuous).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun x : ℝ ↦
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2))).intervalIntegrable 0 1)
      hpoint
  have hlambdaSq : lambda ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlambda0 hlambda 2
  unfold fourCellPositiveCoshMoment
  change (∫ x : ℝ in 0..1,
      Real.cosh (lambda * x) * fourCellEvenEndpointCoshSeed x) ≤ _
  calc
    _ ≤ ∫ x : ℝ in 0..1,
        (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
          (1 - x ^ 2) := hint
    _ = (2 / 3 : ℝ) + (41 / 600 : ℝ) * lambda ^ 2 := by
      rw [show (fun x : ℝ ↦
          (1 + (41 / 80 : ℝ) * lambda ^ 2 * x ^ 2) *
            (1 - x ^ 2)) =
        fun x ↦ (1 : ℝ) + 0 * x +
          ((41 / 80 : ℝ) * lambda ^ 2 - 1) * x ^ 2 +
          0 * x ^ 3 + (-(41 / 80 : ℝ) * lambda ^ 2) * x ^ 4 +
          0 * x ^ 5 by
        funext x
        ring,
        finiteSeven_integral_polynomial_five]
      ring
    _ ≤ (2 / 3 : ℝ) + (41 / 600) * (7 / 32 : ℝ) ^ 2 := by
      have hscaled : (41 / 600 : ℝ) * lambda ^ 2 ≤
          (41 / 600 : ℝ) * (7 / 32) ^ 2 :=
        mul_le_mul_of_nonneg_left hlambdaSq (by norm_num)
      simpa only [add_comm] using add_le_add_left hscaled (2 / 3 : ℝ)
    _ ≤ (67 / 100 : ℝ) := by norm_num

private theorem log_five_four_gt_2231_div_10000 :
    (2231 / 10000 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_gt_15783_div_10000 :
    (15783 / 10000 : ℝ) <
      Real.log (2 * fourCellOperatorHalfWidth) +
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
  rw [hwidth]
  linarith [log_five_four_gt_2231_div_10000,
    strict_log_log_two_bounds.1, strict_euler_gamma_bounds.1,
    strict_log_pi_bounds.1]

private theorem finiteSeven_centeredEndpointCorrelation_endpointCoshSeed
    (t : ℝ) :
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t =
      16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
        t ^ 5 / 30 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellEvenEndpointCoshSeed (t + x) *
        fourCellEvenEndpointCoshSeed x) =
      fun x ↦
        (1 - t ^ 2) + (-2 * t) * x + (t ^ 2 - 2) * x ^ 2 +
          (2 * t) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 by
    funext x
    unfold fourCellEvenEndpointCoshSeed
    ring,
    finiteSeven_integral_polynomial_five]
  ring

private theorem endpointSeed_regularCorrelation_ge_eight_fortyFifths :
    (8 / 45 : ℝ) ≤
      ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t := by
  -- The kernel is at least `1/5` on the four-cell range, while the exact
  -- autocorrelation mass of `1 - x^2` is `8/9`.
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  have hC : Continuous C := by
    rw [show C = fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30 by
      funext t
      exact finiteSeven_centeredEndpointCorrelation_endpointCoshSeed t]
    fun_prop
  have hCnonneg : ∀ t ∈ Icc (0 : ℝ) 2, 0 ≤ C t := by
    intro t ht
    dsimp only [C]
    rw [finiteSeven_centeredEndpointCorrelation_endpointCoshSeed]
    have hcube : 0 ≤ (2 - t) ^ 3 :=
      pow_nonneg (sub_nonneg.mpr ht.2) 3
    have hquad : 0 ≤ t ^ 2 + 6 * t + 4 := by
      nlinarith [sq_nonneg t, ht.1]
    have hfactor :
        30 * (16 / 15 - (4 / 3 : ℝ) * t ^ 2 +
          (2 / 3 : ℝ) * t ^ 3 - t ^ 5 / 30) =
            (2 - t) ^ 3 * (t ^ 2 + 6 * t + 4) := by ring
    nlinarith [mul_nonneg hcube hquad]
  have hmono :
      (∫ t : ℝ in 0..2, (1 / 5 : ℝ) * C t) ≤
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const.mul hC).intervalIntegrable 0 2)
      (intervalIntegrable_boundedLag_mul_continuous
        (fun t : ℝ ↦ yoshidaRegularKernel (fourCellOperatorHalfWidth * t))
        C (measurable_yoshidaRegularKernel.comp
          (measurable_const.mul measurable_id)) hC (1 / 4) (by
            intro t ht
            have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
              unfold fourCellOperatorHalfWidth
              positivity
            have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
              mul_nonneg ha0 ht.1
            have harg4 : fourCellOperatorHalfWidth * t ≤
                5 * Real.log 2 / 4 := by
              calc
                fourCellOperatorHalfWidth * t ≤
                    fourCellOperatorHalfWidth * 2 :=
                  mul_le_mul_of_nonneg_left ht.2 ha0
                _ = 5 * Real.log 2 / 4 := by
                  unfold fourCellOperatorHalfWidth
                  ring
            have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
            rw [abs_of_nonneg hk0]
            exact yoshidaRegularKernel_le_quarter harg0))
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (one_fifth_le_yoshidaRegularKernel_fourCellRange
        (mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1)
        (by
          calc
            fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
              mul_le_mul_of_nonneg_left ht.2
                (by unfold fourCellOperatorHalfWidth; positivity)
            _ = 5 * Real.log 2 / 4 := by
              unfold fourCellOperatorHalfWidth
              ring))
      (hCnonneg t ht)
  have hCint : (∫ t : ℝ in 0..2, C t) = 8 / 9 := by
    dsimp only [C]
    simp_rw [finiteSeven_centeredEndpointCorrelation_endpointCoshSeed]
    rw [show (fun t : ℝ ↦
        16 / 15 - (4 / 3 : ℝ) * t ^ 2 + (2 / 3 : ℝ) * t ^ 3 -
          t ^ 5 / 30) =
      fun t ↦ (16 / 15) + 0 * t + (-4 / 3) * t ^ 2 +
        (2 / 3) * t ^ 3 + 0 * t ^ 4 + (-1 / 30) * t ^ 5 by
      funext t
      ring,
      finiteSeven_integral_polynomial_five]
    norm_num
  rw [intervalIntegral.integral_const_mul, hCint] at hmono
  norm_num at hmono
  simpa only [C] using hmono

/-- The fixed seed diagonal is strictly below the `1 / 16` tail allocation.
This is a structural inequality, proved from a global kernel lower bound and
elementary hyperbolic/logarithmic bounds; it is not one of the twenty-one
finite entry boxes. -/
theorem fourCellEvenFiniteSevenSeedDiagonal_lt_one_sixteenth :
    fourCellEvenFiniteSevenSeedDiagonal < (1 / 16 : ℝ) := by
  let L : ℝ := Real.log 2
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  let H : ℝ := fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
    (fourCellOperatorHalfWidth / 2)
  have hL := strict_log_two_bounds
  have hL0 : (6931 / 10000 : ℝ) ≤ L := by
    dsimp only [L]
    exact hL.1.le
  have hL1 : L ≤ (6932 / 10000 : ℝ) := by
    dsimp only [L]
    exact hL.2.le
  have hS : (15783 / 10000 : ℝ) ≤ S := by
    dsimp only [S]
    exact fourCellScalar_gt_15783_div_10000.le
  have hR : (8 / 45 : ℝ) ≤ R := by
    simpa only [R] using endpointSeed_regularCorrelation_ge_eight_fortyFifths
  have hH : H ≤ (67 / 100 : ℝ) := by
    simpa only [H] using endpointSeed_coshMoment_le_sixtySeven_hundredths
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    unfold fourCellPositiveCoshMoment
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg (Real.cosh_pos _).le
      (by
        unfold fourCellEvenEndpointCoshSeed
        nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)])
  have hHSq : H ^ 2 ≤ (67 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hH0 hH 2
  have hLnonneg : 0 ≤ L := by
    dsimp only [L]
    exact (Real.log_pos (by norm_num)).le
  have hRnonneg : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 8 / 45).trans hR
  have hnegLog : -(16 / 15 : ℝ) * L ≤
      -(16 / 15) * (6931 / 10000 : ℝ) := by
    nlinarith only [hL0]
  have hnegScalar : -S * (16 / 15 : ℝ) ≤
      -(15783 / 10000 : ℝ) * (16 / 15) := by
    nlinarith only [hS]
  have hLR : (6931 / 10000 : ℝ) * (8 / 45) ≤ L * R := by
    exact mul_le_mul hL0 hR (by norm_num) hLnonneg
  have hnegRegular : -(5 / 4 : ℝ) * (L * R) ≤
      -(5 / 4) * ((6931 / 10000 : ℝ) * (8 / 45)) := by
    nlinarith only [hLR]
  have hPolar : 5 * L * H ^ 2 ≤
      5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 := by
    calc
      5 * L * H ^ 2 ≤ 5 * (6932 / 10000 : ℝ) * H ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1 (by norm_num)) (sq_nonneg H)
      _ ≤ 5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 :=
        mul_le_mul_of_nonneg_left hHSq (by norm_num)
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hprimeProduct :
      (7 / 5 : ℝ) * (6931 / 10000) ≤ Real.sqrt 2 * L := by
    exact mul_le_mul hsqrt hL0 (by norm_num) (Real.sqrt_nonneg 2)
  have hnegPrime :
      -(Real.sqrt 2 * L) * (1616 / 46875 : ℝ) ≤
        -((7 / 5 : ℝ) * (6931 / 10000)) * (1616 / 46875) := by
    exact mul_le_mul_of_nonneg_right (neg_le_neg hprimeProduct) (by norm_num)
  unfold fourCellEvenFiniteSevenSeedDiagonal
  rw [fourCellEvenExactBracket_endpointCoshSeed_formula]
  change 248 / 225 - (16 / 15 : ℝ) * L - S * (16 / 15) -
      (5 * L / 4) * R + 5 * L * H ^ 2 -
        Real.sqrt 2 * L * (1616 / 46875) < _
  have hrat :
      248 / 225 - (16 / 15 : ℝ) * (6931 / 10000) -
          (15783 / 10000 : ℝ) * (16 / 15) -
          (5 / 4 : ℝ) * ((6931 / 10000) * (8 / 45)) +
          5 * (6932 / 10000 : ℝ) * (67 / 100) ^ 2 -
          ((7 / 5 : ℝ) * (6931 / 10000)) * (1616 / 46875) <
        (1 / 16 : ℝ) := by norm_num
  nlinarith only [hnegLog, hnegScalar, hnegRegular, hPolar, hnegPrime, hrat]

/-- Consequently, the existing `1 / 16` upper-bound allocation is already
too large on a hypothetical positive pure tail.  This does *not* refute the
actual endpoint determinant; it proves that composing the current two upper
bounds while dropping the mixed/exact tail structure cannot close it. -/
theorem one_sixteenth_tailBudget_strictly_exceeds_seedDiagonal
    {T : ℝ} (hT : 0 < T) :
    fourCellEvenFiniteSevenSeedDiagonal * T < (1 / 16 : ℝ) * T := by
  exact mul_lt_mul_of_pos_right
    fourCellEvenFiniteSevenSeedDiagonal_lt_one_sixteenth hT

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenFiniteSevenTailAssemblyStructural
