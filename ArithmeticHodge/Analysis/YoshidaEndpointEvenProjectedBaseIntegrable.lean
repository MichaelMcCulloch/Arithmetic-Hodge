import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedGapMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedBaseIntegrable

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedGapMoments
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound

noncomputable section

theorem intervalIntegrable_fixedProjectedDualBaseIntegrand (c b : ℝ) :
    IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1 := by
  let p : ℝ → ℝ := fun x ↦ fixedEvenLowProfile c b x
  have hp : Continuous p := by
    dsimp only [p, fixedEvenLowProfile]
    unfold centeredEvenP0 centeredEvenP2
    fun_prop
  have hV : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * p x * p x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul p p hp hp
  have hR0 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * p x)
      volume (-1) 1 :=
    intervalIntegrable_regularRepresenter_mul centeredEvenP0 p
      (by unfold centeredEvenP0; fun_prop) hp
  have hR2 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * p x)
      volume (-1) 1 :=
    intervalIntegrable_regularRepresenter_mul centeredEvenP2 p
      (by unfold centeredEvenP2; fun_prop) hp
  have hregular : IntervalIntegrable
      (fun x ↦ (-2 * yoshidaEndpointA) *
        (c * (yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x * p x) +
          b * (yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x * p x)))
      volume (-1) 1 :=
    ((hR0.const_mul c).add (hR2.const_mul b)).const_mul
      (-2 * yoshidaEndpointA)
  have hrest : IntervalIntegrable
      (fun x ↦
        4 * yoshidaEndpointA * p x *
            (c * yoshidaEndpointCoshMoment centeredEvenP0 +
              b * yoshidaEndpointCoshMoment centeredEvenP2) *
              Real.cosh (yoshidaEndpointA * x / 2) -
          2 * p x * fixedProjectionPolynomial c b x -
          (41 / 60 : ℝ) * p x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [p, fixedEvenLowProfile, fixedProjectionPolynomial]
    unfold centeredEvenP0 centeredEvenP2
    fun_prop
  apply (hV.add (hregular.add hrest)).congr
  intro x _hx
  dsimp only [p]
  unfold fixedProjectedDualBaseIntegrand
    fixedProjectedBoundedRemainder
  ring

theorem intervalIntegrable_fixedProjectedDualBaseCrossIntegrand :
    IntervalIntegrable fixedProjectedDualBaseCrossIntegrand
      volume (-1) 1 := by
  have h11 := intervalIntegrable_fixedProjectedDualBaseIntegrand 1 1
  have h10 := intervalIntegrable_fixedProjectedDualBaseIntegrand 1 0
  have h01 := intervalIntegrable_fixedProjectedDualBaseIntegrand 0 1
  apply (((h11.sub h10).sub h01).const_mul (1 / 2 : ℝ)).congr
  intro x _hx
  unfold fixedProjectedDualBaseCrossIntegrand
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedBaseIntegrable
