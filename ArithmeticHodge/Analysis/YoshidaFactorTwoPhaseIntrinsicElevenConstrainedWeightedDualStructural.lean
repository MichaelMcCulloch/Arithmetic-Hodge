import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural

open TwoByTwoSchur
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# The constrained weighted dual at the eleventh gap

The cutoff-eleven phase reserve is a multiplication operator: its even and
odd weights are respectively `21/110 + V/2` and `1/11 + V/2`, where `V` is
the endpoint potential.  A tail with eleven vanishing Legendre moments pairs
trivially with every transported polynomial of degree below eleven.  Thus a
low-to-tail representer may first be reduced modulo that finite polynomial
space and only then charged to the multiplication reserve by weighted
Cauchy--Schwarz.

The final theorem isolates the genuinely finite statement still required:
one must choose the two degree-`< 11` polynomial selectors so that their
weighted dual integral is bounded by the retained low quadratic form.  No
tail basis is truncated or enumerated here.
-/

/-- Uniform even multiplication weight retained by the eleventh-gap phase
reserve. -/
def factorTwoIntrinsicElevenEvenWeight (x : ℝ) : ℝ :=
  (21 / 110 : ℝ) + (1 / 2 : ℝ) * yoshidaEndpointPotential x

/-- Uniform odd multiplication weight retained by the eleventh-gap phase
reserve. -/
def factorTwoIntrinsicElevenOddWeight (x : ℝ) : ℝ :=
  (1 / 11 : ℝ) + (1 / 2 : ℝ) * yoshidaEndpointPotential x

/-- The residual representer left after subtracting a transported low
polynomial. -/
def factorTwoIntrinsicElevenSelectorResidual
    (F : ℝ → ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  F x - centeredPolynomialLift p x

/-- Weighted dual cost of one polynomial selector. -/
def factorTwoIntrinsicElevenSelectorDual
    (W F : ℝ → ℝ) (p : ℝ[X]) : ℝ :=
  ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenSelectorResidual F p x ^ 2 / W x

/-- Sum of the even and odd constrained weighted-dual costs. -/
def factorTwoIntrinsicElevenConstrainedSelectorDual
    (FE FO : ℝ → ℝ) (pE pO : ℝ[X]) : ℝ :=
  factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenEvenWeight FE pE +
    factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenOddWeight FO pO

/-- The exact multiplication reserve used by the constrained dual. -/
def factorTwoIntrinsicElevenWeightedReserve
    (e o : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1,
      factorTwoIntrinsicElevenEvenWeight x * e x ^ 2) +
    ∫ x : ℝ in -1..1,
      factorTwoIntrinsicElevenOddWeight x * o x ^ 2

/-- The two parity representer pairings, before the finite selector is
chosen. -/
def factorTwoIntrinsicElevenMixedPairing
    (FE FO e o : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1, FE x * e x) +
    ∫ x : ℝ in -1..1, FO x * o x

theorem factorTwoIntrinsicElevenEvenWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenEvenWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenEvenWeight
  nlinarith

theorem factorTwoIntrinsicElevenOddWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenOddWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenOddWeight
  nlinarith

/-- The multiplication reserve is exactly the rational gap-eleven reserve,
not merely bounded by it. -/
theorem factorTwoIntrinsicElevenWeightedReserve_eq
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    factorTwoIntrinsicElevenWeightedReserve e o =
      (21 / 110 : ℝ) * factorTwoIntrinsicEnergy e +
        (1 / 11 : ℝ) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) := by
  have heMass : IntervalIntegrable
      (fun x : ℝ ↦ (21 / 110 : ℝ) * e x ^ 2) volume (-1) 1 :=
    ((hec.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hoMass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 11 : ℝ) * o x ^ 2) volume (-1) 1 :=
    ((hoc.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hePotential : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        (yoshidaEndpointPotential x * e x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq e hec).const_mul _
  have hoPotential : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        (yoshidaEndpointPotential x * o x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq o hoc).const_mul _
  have heExpand :
      (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenEvenWeight x * e x ^ 2) =
        (21 / 110 : ℝ) * factorTwoIntrinsicEnergy e +
          (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy e := by
    unfold factorTwoIntrinsicElevenEvenWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (21 / 110 : ℝ) * e x ^ 2 +
            (1 / 2 : ℝ) *
              (yoshidaEndpointPotential x * e x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add heMass hePotential,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hoExpand :
      (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenOddWeight x * o x ^ 2) =
        (1 / 11 : ℝ) * factorTwoIntrinsicEnergy o +
          (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy o := by
    unfold factorTwoIntrinsicElevenOddWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (1 / 11 : ℝ) * o x ^ 2 +
            (1 / 2 : ℝ) *
              (yoshidaEndpointPotential x * o x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hoMass hoPotential,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicElevenWeightedReserve
  rw [heExpand, hoExpand]
  ring

theorem factorTwoIntrinsicElevenWeightedReserve_nonneg
    (e o : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicElevenWeightedReserve e o := by
  have he : 0 ≤ ∫ x : ℝ in -1..1,
      factorTwoIntrinsicElevenEvenWeight x * e x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenEvenWeight_pos_on_Icc hx).le (sq_nonneg _)
  have ho : 0 ≤ ∫ x : ℝ in -1..1,
      factorTwoIntrinsicElevenOddWeight x * o x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenOddWeight_pos_on_Icc hx).le (sq_nonneg _)
  unfold factorTwoIntrinsicElevenWeightedReserve
  positivity

/-- The weighted reserve sits below the complete infinite-dimensional tail
phase form. -/
theorem factorTwoIntrinsicElevenWeightedReserve_le_phase
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicElevenWeightedReserve e o ≤
      factorTwoEndpointChannelPhase e o a b := by
  rw [factorTwoIntrinsicElevenWeightedReserve_eq e o hec hoc]
  exact factorTwoEndpointChannelPhase_gap_eleven_reserve
    e o hec hoc he ho he0 helocal holocal heLow hoLow a b hab

/-- Exact subtraction of one degree-`< 11` selector. -/
theorem intervalIntegral_representer_mul_tail_eq_selectorResidual
    (F r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 11)
    (p : ℝ[X]) (hp : p.natDegree < 11)
    (hresidualTail : IntervalIntegrable
      (fun x : ℝ ↦
        factorTwoIntrinsicElevenSelectorResidual F p x * r x)
      volume (-1) 1) :
    (∫ x : ℝ in -1..1, F x * r x) =
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenSelectorResidual F p x * r x := by
  have hpoly := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hlow hp
  have hpolyTail : IntervalIntegrable
      (fun x : ℝ ↦ centeredPolynomialLift p x * r x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredPolynomialLift
    fun_prop
  calc
    (∫ x : ℝ in -1..1, F x * r x) =
        ∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenSelectorResidual F p x * r x +
            centeredPolynomialLift p x * r x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      unfold factorTwoIntrinsicElevenSelectorResidual
      ring
    _ = (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenSelectorResidual F p x * r x) +
          ∫ x : ℝ in -1..1, centeredPolynomialLift p x * r x := by
      rw [intervalIntegral.integral_add hresidualTail hpolyTail]
    _ = _ := by rw [hpoly, add_zero]

/-- Interval form of the weighted Cauchy inequality.  The `MemLp`
hypotheses are deliberately explicit: in the final application they are
regularity obligations on the chosen finite representers, not estimates on
an enumerated tail basis. -/
theorem sq_intervalIntegral_mul_le_weighted
    (W G r : ℝ → ℝ)
    (hW : ∀ᵐ x ∂(volume.restrict (Ioc (-1 : ℝ) 1)), 0 < W x)
    (hdual : MemLp (fun x ↦ G x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimal : MemLp (fun x ↦ Real.sqrt (W x) * r x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
      (∫ x : ℝ in -1..1, G x ^ 2 / W x) *
        ∫ x : ℝ in -1..1, W x * r x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have h := YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
    μ W G r (by simpa only [μ] using hW)
      (by simpa only [μ] using hdual) (by simpa only [μ] using hprimal)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ] using h

/-- One-channel constrained weighted Cauchy after exact moment subtraction. -/
theorem sq_representerPairing_le_selectorDual_mul_reserve
    (W F r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 11)
    (p : ℝ[X]) (hp : p.natDegree < 11)
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x)
    (hdual : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual F p x /
          Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimal : MemLp (fun x ↦ Real.sqrt (W x) * r x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    (∫ x : ℝ in -1..1, F x * r x) ^ 2 ≤
      factorTwoIntrinsicElevenSelectorDual W F p *
        ∫ x : ℝ in -1..1, W x * r x ^ 2 := by
  have hWae : ∀ᵐ x ∂(volume.restrict (Ioc (-1 : ℝ) 1)), 0 < W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hW x ⟨hx.1.le, hx.2⟩
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hscaled : Integrable (fun x : ℝ ↦
      (factorTwoIntrinsicElevenSelectorResidual F p x /
          Real.sqrt (W x)) *
        (Real.sqrt (W x) * r x)) μ := by
    have h := hdual.integrable_mul hprimal
    simpa only [μ, Pi.mul_apply] using h
  have hscaledEq : ∀ᵐ x ∂μ,
      (factorTwoIntrinsicElevenSelectorResidual F p x /
          Real.sqrt (W x)) *
          (Real.sqrt (W x) * r x) =
        factorTwoIntrinsicElevenSelectorResidual F p x * r x := by
    filter_upwards [show ∀ᵐ x ∂μ, 0 < W x by
      simpa only [μ] using hWae] with x hx
    have hsqrt : Real.sqrt (W x) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    field_simp [hsqrt]
  have hresidualMeasure : Integrable
      (fun x : ℝ ↦
        factorTwoIntrinsicElevenSelectorResidual F p x * r x) μ :=
    hscaled.congr hscaledEq
  have hresidualTail : IntervalIntegrable
      (fun x : ℝ ↦
        factorTwoIntrinsicElevenSelectorResidual F p x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μ] using hresidualMeasure
  have hcauchy := sq_intervalIntegral_mul_le_weighted W
    (factorTwoIntrinsicElevenSelectorResidual F p) r hWae hdual hprimal
  rw [intervalIntegral_representer_mul_tail_eq_selectorResidual
    F r hr hlow p hp hresidualTail]
  simpa only [factorTwoIntrinsicElevenSelectorDual] using hcauchy

/-- The selector dual is nonnegative whenever its multiplication weight is
positive on the endpoint interval. -/
theorem factorTwoIntrinsicElevenSelectorDual_nonneg
    (W F : ℝ → ℝ) (p : ℝ[X])
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x) :
    0 ≤ factorTwoIntrinsicElevenSelectorDual W F p := by
  unfold factorTwoIntrinsicElevenSelectorDual
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact div_nonneg (sq_nonneg _) (hW x hx).le

/-- The exact two-channel Schur estimate.  It uses closure of positive
`2 × 2` matrices, so the even and odd channels are added without a triangle
inequality or a square-root loss. -/
theorem factorTwoIntrinsicElevenMixedPairing_sq_le
    (FE FO e o : ℝ → ℝ)
    (hec : Continuous e) (hoc : Continuous o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (pE pO : ℝ[X]) (hpE : pE.natDegree < 11)
    (hpO : pO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FE pE x /
          Real.sqrt (factorTwoIntrinsicElevenEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimalE : MemLp (fun x ↦
        Real.sqrt (factorTwoIntrinsicElevenEvenWeight x) * e x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FO pO x /
          Real.sqrt (factorTwoIntrinsicElevenOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimalO : MemLp (fun x ↦
        Real.sqrt (factorTwoIntrinsicElevenOddWeight x) * o x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    factorTwoIntrinsicElevenMixedPairing FE FO e o ^ 2 ≤
      factorTwoIntrinsicElevenConstrainedSelectorDual FE FO pE pO *
        factorTwoIntrinsicElevenWeightedReserve e o := by
  let IE : ℝ := ∫ x : ℝ in -1..1, FE x * e x
  let IO : ℝ := ∫ x : ℝ in -1..1, FO x * o x
  let DE : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenEvenWeight FE pE
  let DO : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenOddWeight FO pO
  let RE : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenEvenWeight x * e x ^ 2
  let RO : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenOddWeight x * o x ^ 2
  have hIE : IE ^ 2 ≤ DE * RE := by
    dsimp only [IE, DE, RE]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenEvenWeight FE e hec heLow pE hpE
      (fun x hx ↦ factorTwoIntrinsicElevenEvenWeight_pos_on_Icc hx)
      hdualE hprimalE
  have hIO : IO ^ 2 ≤ DO * RO := by
    dsimp only [IO, DO, RO]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenOddWeight FO o hoc hoLow pO hpO
      (fun x hx ↦ factorTwoIntrinsicElevenOddWeight_pos_on_Icc hx)
      hdualO hprimalO
  have hDE : 0 ≤ DE := by
    dsimp only [DE]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenEvenWeight_pos_on_Icc hx)
  have hDO : 0 ≤ DO := by
    dsimp only [DO]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenOddWeight_pos_on_Icc hx)
  have hRE : 0 ≤ RE := by
    dsimp only [RE]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenEvenWeight_pos_on_Icc hx).le (sq_nonneg _)
  have hRO : 0 ≤ RO := by
    dsimp only [RO]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenOddWeight_pos_on_Icc hx).le (sq_nonneg _)
  have hsum := determinant_bound_add
    DE RE (2 * IE) DO RO (2 * IO)
    hDE hRE hDO hRO (by nlinarith) (by nlinarith)
  dsimp only [factorTwoIntrinsicElevenMixedPairing,
    factorTwoIntrinsicElevenConstrainedSelectorDual,
    factorTwoIntrinsicElevenWeightedReserve]
  dsimp only [IE, IO, DE, DO, RE, RO] at hsum
  nlinarith

/-- Handoff theorem for the remaining finite selector inequality.  Once the
two degree-`< 11` selectors have dual cost at most the retained low form, the
complete infinite tail is absorbed by the phase. -/
theorem factorTwoIntrinsicElevenMixedPairing_sq_le_low_mul_phase_of_finiteSelector
    (FE FO e o : ℝ → ℝ)
    (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (pE pO : ℝ[X]) (hpE : pE.natDegree < 11)
    (hpO : pO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FE pE x /
          Real.sqrt (factorTwoIntrinsicElevenEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimalE : MemLp (fun x ↦
        Real.sqrt (factorTwoIntrinsicElevenEvenWeight x) * e x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FO pO x /
          Real.sqrt (factorTwoIntrinsicElevenOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hprimalO : MemLp (fun x ↦
        Real.sqrt (factorTwoIntrinsicElevenOddWeight x) * o x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (low : ℝ) (hlow : 0 ≤ low)
    (hfiniteSelector :
      factorTwoIntrinsicElevenConstrainedSelectorDual FE FO pE pO ≤ low) :
    factorTwoIntrinsicElevenMixedPairing FE FO e o ^ 2 ≤
      low * factorTwoEndpointChannelPhase e o a b := by
  have hmixed := factorTwoIntrinsicElevenMixedPairing_sq_le
    FE FO e o hec hoc heLow hoLow pE pO hpE hpO
      hdualE hprimalE hdualO hprimalO
  have hreserve := factorTwoIntrinsicElevenWeightedReserve_le_phase
    e o hec hoc he ho he0 helocal holocal heLow hoLow a b hab
  have hreserve0 := factorTwoIntrinsicElevenWeightedReserve_nonneg e o
  have hproduct :
      factorTwoIntrinsicElevenConstrainedSelectorDual FE FO pE pO *
          factorTwoIntrinsicElevenWeightedReserve e o ≤
        low * factorTwoEndpointChannelPhase e o a b :=
    mul_le_mul hfiniteSelector hreserve hreserve0 hlow
  exact hmixed.trans hproduct

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
