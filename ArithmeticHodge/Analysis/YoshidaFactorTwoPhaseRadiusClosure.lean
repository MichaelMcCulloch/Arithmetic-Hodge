import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRadiusClosure

noncomputable section

open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaOddSpectralMassBridge

/-!
# Closure of the factor-two phase radius

The alternating radius is now unconditional.  Substituting its sharp
`625 / 64` square bound into the existing tail phase theorem leaves only the
two symmetric perturbation radii as analytic hypotheses.
-/

private theorem continuous_clipped_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (r : YoshidaClippedPeriodicCore a)
    (hneg : (r : YoshidaClippedSmooth a) (-a) = 0)
    (hpos : (r : YoshidaClippedSmooth a) a = 0) :
    Continuous (((r : YoshidaClippedSmooth a) : ℝ → ℂ)) := by
  let S : Set ℝ := Icc (-a) a
  have hfront : ∀ x ∈ frontier S,
      ((r : YoshidaClippedSmooth a) : ℝ → ℂ) x = 0 := by
    intro x hx
    have hx' : x ∈ ({-a, a} : Set ℝ) := by
      simpa only [S, frontier_Icc (by linarith : -a ≤ a)] using hx
    rcases hx' with (rfl | rfl)
    · exact hneg
    · exact hpos
  have hpiece : Continuous (S.piecewise
      (((r : YoshidaClippedSmooth a) : ℝ → ℂ)) 0) := by
    apply continuous_piecewise hfront
    · simpa only [S, isClosed_Icc.closure_eq] using
        (r : YoshidaClippedSmooth a).property.1.continuousOn
    · exact continuousOn_const
  have heq : (((r : YoshidaClippedSmooth a) : ℝ → ℂ)) =
      S.piecewise (((r : YoshidaClippedSmooth a) : ℝ → ℂ)) 0 := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.piecewise, hx, if_true]
    · rw [yoshidaClippedSmooth_eq_zero_outside
        (r : YoshidaClippedSmooth a) (by simpa only [S] using hx)]
      simp only [Set.piecewise, hx, if_false, Pi.zero_apply]
  rw [heq]
  exact hpiece

private theorem continuous_centeredRescale_re_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (r : YoshidaClippedPeriodicCore a)
    (hneg : (r : YoshidaClippedSmooth a) (-a) = 0)
    (hpos : (r : YoshidaClippedSmooth a) a = 0) :
    Continuous (centeredRescale a (fun x ↦
      ((r : YoshidaClippedSmooth a) x).re)) := by
  have hr := continuous_clipped_of_endpoints_zero ha r hneg hpos
  unfold centeredRescale
  exact (Complex.continuous_re.comp hr).comp
    (continuous_const.mul continuous_id)

/-- With the alternating radius discharged, phase-uniform endpoint-tail
positivity requires only the two symmetric `3/2` operator bounds. -/
theorem endpoint_tail_phase_uniform_of_symmetric_bounds
    (re ro : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaEndpointA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule
      yoshidaEndpointA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (heNeg : (re : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hePos : (re : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hoNeg : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hoPos : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hPe :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      |factorTwoCenteredSymmetricPerturbation e| ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, e x ^ 2)
    (hPo :
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      |factorTwoCenteredSymmetricPerturbation o| ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, o x ^ 2)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaEndpointA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    let o := centeredRescale yoshidaEndpointA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    0 ≤ yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
      a * (factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o) +
      b * factorTwoCenteredAlternatingCoupling e o := by
  dsimp only at hPe hPo ⊢
  let e : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let o : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  have hec : Continuous e := by
    simpa only [e] using
      continuous_centeredRescale_re_of_endpoints_zero
        yoshidaEndpointA_pos re heNeg hePos
  have hoc : Continuous o := by
    simpa only [o] using
      continuous_centeredRescale_re_of_endpoints_zero
        yoshidaEndpointA_pos ro hoNeg hoPos
  have heven : Function.Even e := by
    intro x
    dsimp only [e, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      evenTail_pointwise_even yoshidaEndpointA_pos 199 re heTail
        (yoshidaEndpointA * x)]
  have hood : Function.Odd o := by
    intro x
    dsimp only [o, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      oddTail_pointwise_odd yoshidaEndpointA_pos 10 ro hoTail
        (yoshidaEndpointA * x)]
    rfl
  have hJ := factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
    e o hec hoc heven hood
  have hJ' :
      let e' := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      let o' := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
      factorTwoCenteredAlternatingCoupling e' o' ^ 2 ≤
        (625 / 64 : ℝ) *
          (∫ x : ℝ in -1..1, e' x ^ 2) *
          (∫ x : ℝ in -1..1, o' x ^ 2) := by
    simpa only [e, o, mul_assoc] using hJ
  exact endpoint_tail_phase_uniform_of_complete_bounds
    re ro heTail hoTail heReal hoReal heNeg hePos hoNeg hoPos hPe hPo hJ'
    a b hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRadiusClosure
