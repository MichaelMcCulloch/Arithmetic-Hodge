import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentBoundStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Quantitative regular-moment bound for the old Galerkin residual

The exact polynomial moment below is the finite Legendre cancellation.
The difference between the true kernel and its sixth-order polynomial is
then controlled by the uniform seven-eighths envelope and one correlation
`L¹` estimate.
-/

/-- Exact sixth-order kernel moment against the five-mode--`P11`
correlation.  The `P3` coefficient is absent because that moment vanishes
identically. -/
def fourCellOddFiveModeP11PolynomialMoment
    (_c _d e f g : ℝ) : ℝ :=
  let a := fourCellOperatorHalfWidth
  (-e * (31 * a ^ 5 / 2698531355520) +
    f * (a ^ 3 / 320932800 + 31 * a ^ 5 / 1022170968000) -
    g * (a / 220248 + a ^ 3 / 133722000 +
      31 * a ^ 5 / 849188188800))

set_option maxHeartbeats 3000000 in
private theorem integral_regularKernelPolynomial6_mul_correlation_basis_one :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial 1 0 0 0 0 t) =
      fourCellOddFiveModeP11PolynomialMoment 1 0 0 0 0 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddFiveModeP11CorrelationPolynomial
    fourCellOddFiveModeP11PolynomialMoment
  norm_num
  simp only [mul_add, add_mul, sub_eq_add_neg]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num
  ring

set_option maxHeartbeats 3000000 in
private theorem integral_regularKernelPolynomial6_mul_correlation_basis_three :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial 0 1 0 0 0 t) =
      fourCellOddFiveModeP11PolynomialMoment 0 1 0 0 0 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddFiveModeP11CorrelationPolynomial
    fourCellOddFiveModeP11PolynomialMoment
  norm_num
  simp only [mul_add, add_mul, sub_eq_add_neg]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num
  ring

set_option maxHeartbeats 3000000 in
private theorem integral_regularKernelPolynomial6_mul_correlation_basis_five :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial 0 0 1 0 0 t) =
      fourCellOddFiveModeP11PolynomialMoment 0 0 1 0 0 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddFiveModeP11CorrelationPolynomial
    fourCellOddFiveModeP11PolynomialMoment
  norm_num
  simp only [mul_add, add_mul, sub_eq_add_neg]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num
  unfold fourCellOperatorHalfWidth
  ring

set_option maxHeartbeats 3000000 in
private theorem integral_regularKernelPolynomial6_mul_correlation_basis_seven :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial 0 0 0 1 0 t) =
      fourCellOddFiveModeP11PolynomialMoment 0 0 0 1 0 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddFiveModeP11CorrelationPolynomial
    fourCellOddFiveModeP11PolynomialMoment
  norm_num
  simp only [mul_add, add_mul, sub_eq_add_neg]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num
  unfold fourCellOperatorHalfWidth
  ring

set_option maxHeartbeats 3000000 in
private theorem integral_regularKernelPolynomial6_mul_correlation_basis_nine :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial 0 0 0 0 1 t) =
      fourCellOddFiveModeP11PolynomialMoment 0 0 0 0 1 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    fourCellOddFiveModeP11CorrelationPolynomial
    fourCellOddFiveModeP11PolynomialMoment
  norm_num
  simp only [mul_add, add_mul, sub_eq_add_neg]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num
  unfold fourCellOperatorHalfWidth
  ring

set_option maxHeartbeats 2000000 in
theorem integral_regularKernelPolynomial6_mul_fiveModeP11Correlation
    (c d e f g : ℝ) :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
          fourCellOddP11DirectTail t) =
      fourCellOddFiveModeP11PolynomialMoment c d e f g := by
  simp_rw [factorTwoCenteredCorrelationBilinear_fiveMode_P11_eq]
  let F1 : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
      fourCellOddFiveModeP11CorrelationPolynomial 1 0 0 0 0 t
  let F3 : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
      fourCellOddFiveModeP11CorrelationPolynomial 0 1 0 0 0 t
  let F5 : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
      fourCellOddFiveModeP11CorrelationPolynomial 0 0 1 0 0 t
  let F7 : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
      fourCellOddFiveModeP11CorrelationPolynomial 0 0 0 1 0 t
  let F9 : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
      fourCellOddFiveModeP11CorrelationPolynomial 0 0 0 0 1 t
  have h1 : IntervalIntegrable F1 volume 0 2 :=
    (by
      dsimp only [F1]
      unfold yoshidaRegularKernelPolynomial6
        fourCellOddFiveModeP11CorrelationPolynomial
      fun_prop : Continuous F1).intervalIntegrable 0 2
  have h3 : IntervalIntegrable F3 volume 0 2 :=
    (by
      dsimp only [F3]
      unfold yoshidaRegularKernelPolynomial6
        fourCellOddFiveModeP11CorrelationPolynomial
      fun_prop : Continuous F3).intervalIntegrable 0 2
  have h5 : IntervalIntegrable F5 volume 0 2 :=
    (by
      dsimp only [F5]
      unfold yoshidaRegularKernelPolynomial6
        fourCellOddFiveModeP11CorrelationPolynomial
      fun_prop : Continuous F5).intervalIntegrable 0 2
  have h7 : IntervalIntegrable F7 volume 0 2 :=
    (by
      dsimp only [F7]
      unfold yoshidaRegularKernelPolynomial6
        fourCellOddFiveModeP11CorrelationPolynomial
      fun_prop : Continuous F7).intervalIntegrable 0 2
  have h9 : IntervalIntegrable F9 volume 0 2 :=
    (by
      dsimp only [F9]
      unfold yoshidaRegularKernelPolynomial6
        fourCellOddFiveModeP11CorrelationPolynomial
      fun_prop : Continuous F9).intervalIntegrable 0 2
  have hc := h1.const_mul c
  have hd := h3.const_mul d
  have he := h5.const_mul e
  have hf := h7.const_mul f
  have hg := h9.const_mul g
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        fourCellOddFiveModeP11CorrelationPolynomial c d e f g t) =
      fun t ↦
        c * F1 t + d * F3 t + e * F5 t + f * F7 t + g * F9 t by
    funext t
    dsimp only [F1, F3, F5, F7, F9]
    unfold fourCellOddFiveModeP11CorrelationPolynomial
    ring]
  rw [intervalIntegral.integral_add (((hc.add hd).add he).add hf) hg,
    intervalIntegral.integral_add ((hc.add hd).add he) hf,
    intervalIntegral.integral_add (hc.add hd) he,
    intervalIntegral.integral_add hc hd]
  repeat rw [intervalIntegral.integral_const_mul]
  dsimp only [F1, F3, F5, F7, F9]
  rw [integral_regularKernelPolynomial6_mul_correlation_basis_one,
    integral_regularKernelPolynomial6_mul_correlation_basis_three,
    integral_regularKernelPolynomial6_mul_correlation_basis_five,
    integral_regularKernelPolynomial6_mul_correlation_basis_seven,
    integral_regularKernelPolynomial6_mul_correlation_basis_nine]
  unfold fourCellOddFiveModeP11PolynomialMoment
  ring

end


end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentBoundStructural
