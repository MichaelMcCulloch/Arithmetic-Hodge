import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

open TwoByTwoSchur
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# The retained constrained dual at cutoff eleven

Retaining `1 / 64` of the singular Gram changes the multiplication weights.
The even and odd weights below encode exactly the reserve left by
`factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four`.
The two-channel theorem charges the retained representer row to that reserve
without a triangle inequality.
-/

/-- Even multiplication weight after retaining `1 / 64` of the singular
Gram. -/
def factorTwoIntrinsicElevenRetainedEvenWeight (x : ℝ) : ℝ :=
  (13 / 100 : ℝ) + (63 / 128 : ℝ) * yoshidaEndpointPotential x

/-- Odd multiplication weight after retaining `1 / 64` of the singular
Gram. -/
def factorTwoIntrinsicElevenRetainedOddWeight (x : ℝ) : ℝ :=
  (1 / 30 : ℝ) + (63 / 128 : ℝ) * yoshidaEndpointPotential x

/-- Sum of the two retained constrained selector costs. -/
def factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
    (FE FO : ℝ → ℝ) (pE pO : ℝ[X]) : ℝ :=
  factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenRetainedEvenWeight FE pE +
    factorTwoIntrinsicElevenSelectorDual
      factorTwoIntrinsicElevenRetainedOddWeight FO pO

theorem factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenRetainedEvenWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenRetainedEvenWeight
  nlinarith

theorem factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoIntrinsicElevenRetainedOddWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold factorTwoIntrinsicElevenRetainedOddWeight
  nlinarith

theorem intervalIntegrable_retainedEvenWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenWeight x * r x ^ 2)
      volume (-1) 1 := by
  have hmass : IntervalIntegrable
      (fun x : ℝ ↦ (13 / 100 : ℝ) * r x ^ 2) volume (-1) 1 :=
    ((hr.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * r x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq r hr).const_mul _
  apply (hmass.add hpotential).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedEvenWeight
  ring

theorem intervalIntegrable_retainedOddWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddWeight x * r x ^ 2)
      volume (-1) 1 := by
  have hmass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 30 : ℝ) * r x ^ 2) volume (-1) 1 :=
    ((hr.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * r x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq r hr).const_mul _
  apply (hmass.add hpotential).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedOddWeight
  ring

private theorem measurable_retainedEvenWeight :
    Measurable factorTwoIntrinsicElevenRetainedEvenWeight := by
  unfold factorTwoIntrinsicElevenRetainedEvenWeight yoshidaEndpointPotential
  fun_prop

private theorem measurable_retainedOddWeight :
    Measurable factorTwoIntrinsicElevenRetainedOddWeight := by
  unfold factorTwoIntrinsicElevenRetainedOddWeight yoshidaEndpointPotential
  fun_prop

/-- Continuity of a residual profile automatically supplies the retained
even primal `L²` hypothesis. -/
theorem sqrt_retainedEvenWeight_mul_memLp_two
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) * r x)
      (volume.restrict (Ioc (-1) 1)) :=
    (measurable_retainedEvenWeight.sqrt.mul hr.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hweight : Integrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenWeight x * r x ^ 2)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_retainedEvenWeight_mul_sq r hr)
  apply hweight.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hweightPos.le]

/-- Continuity of a residual profile automatically supplies the retained odd
primal `L²` hypothesis. -/
theorem sqrt_retainedOddWeight_mul_memLp_two
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) * r x)
      (volume.restrict (Ioc (-1) 1)) :=
    (measurable_retainedOddWeight.sqrt.mul hr.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hweight : Integrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddWeight x * r x ^ 2)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_retainedOddWeight_mul_sq r hr)
  apply hweight.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hweightPos.le]

/-- The two retained multiplication integrals are exactly the algebraic
reserve carried by the gap-eleven tail theorem. -/
theorem factorTwoIntrinsicElevenRetainedWeightedReserve_eq_integrals
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    factorTwoIntrinsicElevenRetainedWeightedReserve e o =
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2) +
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2 := by
  have heMass : IntervalIntegrable
      (fun x : ℝ ↦ (13 / 100 : ℝ) * e x ^ 2) volume (-1) 1 :=
    ((hec.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hoMass : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 30 : ℝ) * o x ^ 2) volume (-1) 1 :=
    ((hoc.pow 2).intervalIntegrable (-1) 1).const_mul _
  have hePotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * e x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq e hec).const_mul _
  have hoPotential : IntervalIntegrable
      (fun x : ℝ ↦ (63 / 128 : ℝ) *
        (yoshidaEndpointPotential x * o x ^ 2)) volume (-1) 1 :=
    (intervalIntegrable_endpointPotential_mul_sq o hoc).const_mul _
  have heExpand :
      (∫ x : ℝ in -1..1,
          factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2) =
        (13 / 100 : ℝ) * factorTwoIntrinsicEnergy e +
          (63 / 128 : ℝ) * factorTwoIntrinsicPotentialEnergy e := by
    unfold factorTwoIntrinsicElevenRetainedEvenWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (13 / 100 : ℝ) * e x ^ 2 +
            (63 / 128 : ℝ) *
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
          factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2) =
        (1 / 30 : ℝ) * factorTwoIntrinsicEnergy o +
          (63 / 128 : ℝ) * factorTwoIntrinsicPotentialEnergy o := by
    unfold factorTwoIntrinsicElevenRetainedOddWeight factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy
    calc
      _ = ∫ x : ℝ in -1..1,
          (1 / 30 : ℝ) * o x ^ 2 +
            (63 / 128 : ℝ) *
              (yoshidaEndpointPotential x * o x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hoMass hoPotential,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicElevenRetainedWeightedReserve
  rw [heExpand, hoExpand]
  ring

theorem factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
    (FE FO : ℝ → ℝ) (pE pO : ℝ[X]) :
    0 ≤ factorTwoIntrinsicElevenRetainedConstrainedSelectorDual FE FO pE pO := by
  unfold factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
  exact add_nonneg
    (factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx))
    (factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx))

/-- Sharp two-channel weighted Cauchy estimate for the retained row.  The
primal `L²` hypotheses are discharged from continuity; only the two concrete
dual residuals remain as regularity obligations. -/
theorem factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (FE FO e o : ℝ → ℝ)
    (hec : Continuous e) (hoc : Continuous o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (pE pO : ℝ[X]) (hpE : pE.natDegree < 11)
    (hpO : pO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FE pE x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual FO pO x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    factorTwoIntrinsicElevenMixedPairing FE FO e o ^ 2 ≤
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual FE FO pE pO *
        factorTwoIntrinsicElevenRetainedWeightedReserve e o := by
  let IE : ℝ := ∫ x : ℝ in -1..1, FE x * e x
  let IO : ℝ := ∫ x : ℝ in -1..1, FO x * o x
  let DE : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenRetainedEvenWeight FE pE
  let DO : ℝ := factorTwoIntrinsicElevenSelectorDual
    factorTwoIntrinsicElevenRetainedOddWeight FO pO
  let RE : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenRetainedEvenWeight x * e x ^ 2
  let RO : ℝ := ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenRetainedOddWeight x * o x ^ 2
  have hIE : IE ^ 2 ≤ DE * RE := by
    dsimp only [IE, DE, RE]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenRetainedEvenWeight FE e hec heLow pE hpE
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      hdualE (sqrt_retainedEvenWeight_mul_memLp_two e hec)
  have hIO : IO ^ 2 ≤ DO * RO := by
    dsimp only [IO, DO, RO]
    exact sq_representerPairing_le_selectorDual_mul_reserve
      factorTwoIntrinsicElevenRetainedOddWeight FO o hoc hoLow pO hpO
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      hdualO (sqrt_retainedOddWeight_mul_memLp_two o hoc)
  have hDE : 0 ≤ DE := by
    dsimp only [DE]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
  have hDO : 0 ≤ DO := by
    dsimp only [DO]
    exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
  have hRE : 0 ≤ RE := by
    dsimp only [RE]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx).le
      (sq_nonneg _)
  have hRO : 0 ≤ RO := by
    dsimp only [RO]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx).le
      (sq_nonneg _)
  have hsum := determinant_bound_add
    DE RE (2 * IE) DO RO (2 * IO)
    hDE hRE hDO hRO (by nlinarith) (by nlinarith)
  rw [factorTwoIntrinsicElevenRetainedWeightedReserve_eq_integrals e o hec hoc]
  dsimp only [factorTwoIntrinsicElevenMixedPairing,
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual]
  dsimp only [IE, IO, DE, DO, RE, RO] at hsum
  nlinarith

/-- Final retained cutoff-eleven Schur handoff.  The only quantitative input
left is a finite selector whose retained dual cost fits below the exact low
complement. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
              pE pO a b) qE x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedOddMixedRepresenter
              pE pO a b) qO x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 64 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO hdualE hdualO
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 64 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_one_div_sixty_four_potentialPole_eq_pairing
      pE pO eR oR heRc hoRc heRlocal hoRlocal heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_sixty_four
    pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
      heGap hoGap hpE hpO a b lowComplement hab hlowComplement
      hlowRetains hremaining

/-- Asymmetric retained-selector handoff with low fraction `1 / 1024`, tail
fraction `1 / 64`, and pole-row coefficient `1 / 256`.  The only quantitative
input is the finite selector cost below the corrected low complement. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_asymmetricRetainedSelector
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (qE qO : ℝ[X]) (hqE : qE.natDegree < 11)
    (hqO : qO.natDegree < 11)
    (hdualE : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              (1 / 256 : ℝ) pE pO a b) qE x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hdualO : MemLp (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
              (1 / 256 : ℝ) pE pO a b) qO x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hfiniteSelector :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
          (1 / 2048 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let lowComplement : ℝ :=
    factorTwoEndpointChannelPhase
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b -
      (1 / 2048 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b
  have hfiniteSelector' :
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 256 : ℝ) pE pO a b)
          qE qO ≤ lowComplement := by
    simpa only [lowComplement] using hfiniteSelector
  have hdualNonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 256 : ℝ) pE pO a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        (1 / 256 : ℝ) pE pO a b)
      qE qO
  have hlowComplement : 0 ≤ lowComplement :=
    hdualNonneg.trans hfiniteSelector'
  have hlowRetains :
      (1 / 1024 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b := by
    dsimp only [lowComplement]
    ring_nf
    exact le_rfl
  have hpairing := factorTwoIntrinsicElevenMixedPairing_sq_le_retained
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 256 : ℝ) pE pO a b)
    (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
      (1 / 256 : ℝ) pE pO a b)
    eR oR heRc hoRc heGap hoGap qE qO hqE hqO hdualE hdualO
  have hreserve0 :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 256 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR := by
    rw [factorTwoEndpointLowTailMixed_sub_potentialPole_eq_pairing
      (1 / 256 : ℝ) pE pO eR oR heRc hoRc heRlocal hoRlocal
      heGap hoGap hpE hpO a b]
    exact hpairing.trans
      (mul_le_mul_of_nonneg_right hfiniteSelector' hreserve0)
  exact
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_one_thousand_twenty_four
      pE pO eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap hpE hpO a b lowComplement hab hlowComplement
        hlowRetains hremaining

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
