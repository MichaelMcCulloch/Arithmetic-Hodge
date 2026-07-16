import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTail

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTailCoerciveStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseDirectionalClosure
open YoshidaFactorTwoPhaseDirectionalTail
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseEvenSchurClosure
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseOddSymmetricBound
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaEvenHomogeneousCoercivity
open YoshidaOddSpectralMassBridge
open YoshidaWeightedTailBounds

/-!
# Structural coercivity of the endpoint-adapted phase tail

The tail phase pencil retains a fixed fraction of its clean diagonal.  The
proof spends only `199 / 200` of the two spectral coercivities and closes the
remaining directional pencil by the same exact two-by-two determinant used
for tail positivity.  The two determinant margins are explicit rational
completions of squares; no mode enumeration or phase-disk subdivision occurs.
-/

/-- The one-sided directional tail budget remains positive after retaining
`1 / 200` of both clean diagonal terms. -/
theorem phase_uniform_of_directional_tail_bounds_clean_reserve
    (Ee Eo Qe Qo Pe Po J a b : ℝ)
    (hEe : 0 ≤ Ee) (hEo : 0 ≤ Eo)
    (hQe : (102 / 25 : ℝ) * Ee ≤ Qe)
    (hQo : (38 / 25 : ℝ) * Eo ≤ Qo)
    (hPeLower : -(3 : ℝ) * Ee ≤ Pe)
    (hPeUpper : Pe ≤ Ee)
    (hPoLower : -Eo ≤ Po)
    (hPoUpper : Po ≤ (3 / 2 : ℝ) * Eo)
    (hJ : J ^ 2 ≤ (625 / 64 : ℝ) * Ee * Eo)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 200 : ℝ) * (Qe + Qo) ≤
      Qe + Qo + a * (Pe + Po) + b * J := by
  have hQeScaled : (10149 / 2500 : ℝ) * Ee ≤
      (199 / 200 : ℝ) * Qe := by
    nlinarith
  have hQoScaled : (3781 / 2500 : ℝ) * Eo ≤
      (199 / 200 : ℝ) * Qo := by
    nlinarith
  have hscaled : 0 ≤
      (199 / 200 : ℝ) * Qe + (199 / 200 : ℝ) * Qo +
        a * (Pe + Po) + b * J := by
    by_cases ha : 0 ≤ a
    · let Re : ℝ := (10149 / 2500 : ℝ) - 3 * a
      let Ro : ℝ := (3781 / 2500 : ℝ) - a
      have ha1 : a ≤ 1 := by
        nlinarith [sq_nonneg b]
      have hRe : 0 ≤ Re := by
        dsimp only [Re]
        nlinarith
      have hRo : 0 ≤ Ro := by
        dsimp only [Ro]
        nlinarith
      have hdiagE : Re * Ee ≤
          (199 / 200 : ℝ) * Qe + a * Pe := by
        dsimp only [Re]
        nlinarith
      have hdiagO : Ro * Eo ≤
          (199 / 200 : ℝ) * Qo + a * Po := by
        dsimp only [Ro]
        nlinarith
      have hbudget : (625 / 256 : ℝ) * b ^ 2 ≤ Re * Ro := by
        have hb : b ^ 2 ≤ 1 - a ^ 2 := by
          nlinarith
        have hpoly :
            (625 / 256 : ℝ) * (1 - a ^ 2) ≤ Re * Ro := by
          dsimp only [Re, Ro]
          nlinarith [sq_nonneg
            ((1393 / 128 : ℝ) * a - (5373 / 625 : ℝ))]
        exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans hpoly
      let AE : ℝ := Re * Ee
      let AO : ℝ := Ro * Eo
      let C : ℝ := b * J / 2
      have hAE : 0 ≤ AE := mul_nonneg hRe hEe
      have hAO : 0 ≤ AO := mul_nonneg hRo hEo
      have hC : C ^ 2 ≤ AE * AO := by
        have hJscaled := mul_le_mul_of_nonneg_left hJ (sq_nonneg b)
        have hEprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
        have hbudgetScaled :=
          mul_le_mul_of_nonneg_right hbudget hEprod
        dsimp only [C, AE, AO]
        calc
          (b * J / 2) ^ 2 = (b ^ 2 * J ^ 2) / 4 := by ring
          _ ≤ (b ^ 2 * ((625 / 64 : ℝ) * Ee * Eo)) / 4 :=
            (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
              hJscaled
          _ = ((625 / 256 : ℝ) * b ^ 2) * (Ee * Eo) := by ring
          _ ≤ (Re * Ro) * (Ee * Eo) := hbudgetScaled
          _ = (Re * Ee) * (Ro * Eo) := by ring
      have hbase : 0 ≤ AE + 2 * C + AO := by
        have hp := (real_quadratic_pencil_nonneg_iff AE AO C).2
          ⟨hAE, hAO, hC⟩ 1 1
        simpa only [one_pow, mul_one] using hp
      have hbase' : 0 ≤ Re * Ee + b * J + Ro * Eo := by
        calc
          0 ≤ AE + 2 * C + AO := hbase
          _ = Re * Ee + b * J + Ro * Eo := by
            dsimp only [AE, AO, C]
            ring
      linarith
    · have ha0 : a ≤ 0 := le_of_not_ge ha
      let x : ℝ := -a
      let Re : ℝ := (10149 / 2500 : ℝ) - x
      let Ro : ℝ := (3781 / 2500 : ℝ) - (3 / 2 : ℝ) * x
      have hx0 : 0 ≤ x := by
        dsimp only [x]
        linarith
      have hx1 : x ≤ 1 := by
        dsimp only [x]
        nlinarith [sq_nonneg b]
      have hRe : 0 ≤ Re := by
        dsimp only [Re]
        nlinarith
      have hRo : 0 ≤ Ro := by
        dsimp only [Ro]
        nlinarith
      have hdiagE : Re * Ee ≤
          (199 / 200 : ℝ) * Qe + a * Pe := by
        dsimp only [Re, x]
        nlinarith
      have hdiagO : Ro * Eo ≤
          (199 / 200 : ℝ) * Qo + a * Po := by
        dsimp only [Ro, x]
        nlinarith
      have hbudget : (625 / 256 : ℝ) * b ^ 2 ≤ Re * Ro := by
        have hb : b ^ 2 ≤ 1 - x ^ 2 := by
          dsimp only [x]
          nlinarith
        have hpoly :
            (625 / 256 : ℝ) * (1 - x ^ 2) ≤ Re * Ro := by
          dsimp only [Re, Ro]
          nlinarith [sq_nonneg
            ((1009 / 128 : ℝ) * x - (38009 / 5000 : ℝ))]
        exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans hpoly
      let AE : ℝ := Re * Ee
      let AO : ℝ := Ro * Eo
      let C : ℝ := b * J / 2
      have hAE : 0 ≤ AE := mul_nonneg hRe hEe
      have hAO : 0 ≤ AO := mul_nonneg hRo hEo
      have hC : C ^ 2 ≤ AE * AO := by
        have hJscaled := mul_le_mul_of_nonneg_left hJ (sq_nonneg b)
        have hEprod : 0 ≤ Ee * Eo := mul_nonneg hEe hEo
        have hbudgetScaled :=
          mul_le_mul_of_nonneg_right hbudget hEprod
        dsimp only [C, AE, AO]
        calc
          (b * J / 2) ^ 2 = (b ^ 2 * J ^ 2) / 4 := by ring
          _ ≤ (b ^ 2 * ((625 / 64 : ℝ) * Ee * Eo)) / 4 :=
            (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
              hJscaled
          _ = ((625 / 256 : ℝ) * b ^ 2) * (Ee * Eo) := by ring
          _ ≤ (Re * Ro) * (Ee * Eo) := hbudgetScaled
          _ = (Re * Ee) * (Ro * Eo) := by ring
      have hbase : 0 ≤ AE + 2 * C + AO := by
        have hp := (real_quadratic_pencil_nonneg_iff AE AO C).2
          ⟨hAE, hAO, hC⟩ 1 1
        simpa only [one_pow, mul_one] using hp
      have hbase' : 0 ≤ Re * Ee + b * J + Ro * Eo := by
        calc
          0 ≤ AE + 2 * C + AO := hbase
          _ = Re * Ee + b * J + Ro * Eo := by
            dsimp only [AE, AO, C]
            ring
      linarith
  linarith

/-- Real endpoint-zero Fourier tails retain `1 / 200` of their clean channel
uniformly on the closed phase disk. -/
theorem endpoint_tail_phase_uniform_clean_reserve
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
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaEndpointA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    let o := centeredRescale yoshidaEndpointA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    (1 / 200 : ℝ) * (yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  dsimp only
  let e : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let o : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
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
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (o x))
  have hQe : (102 / 25 : ℝ) * Ee ≤
      yoshidaEndpointOddCleanQuadratic e := by
    simpa only [e, Ee] using evenTail_endpoint_clean_coercive
      re heTail heReal heNeg hePos
  have hQo : (38 / 25 : ℝ) * Eo ≤
      yoshidaEndpointOddCleanQuadratic o := by
    simpa only [o, Eo] using oddTail_endpoint_clean_coercive
      ro hoTail hoReal hoNeg hoPos
  have hPeLower : -(3 : ℝ) * Ee ≤
      factorTwoCenteredSymmetricPerturbation e := by
    simpa only [Ee] using
      neg_three_energy_le_even_symmetricPerturbation e hec heven
  have hPeUpper : factorTwoCenteredSymmetricPerturbation e ≤ Ee := by
    simpa only [Ee] using even_symmetricPerturbation_le_energy e hec heven
  have hPoLower : -Eo ≤ factorTwoCenteredSymmetricPerturbation o := by
    simpa only [Eo] using neg_energy_le_odd_symmetricPerturbation o hoc hood
  have hPoUpper : factorTwoCenteredSymmetricPerturbation o ≤
      (3 / 2 : ℝ) * Eo := by
    simpa only [Eo] using
      odd_symmetricPerturbation_le_three_halves_energy o hoc hood
  have hJ : factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
      (625 / 64 : ℝ) * Ee * Eo := by
    simpa only [Ee, Eo, mul_assoc] using
      factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
        e o hec hoc heven hood
  have h := phase_uniform_of_directional_tail_bounds_clean_reserve
    Ee Eo
    (yoshidaEndpointOddCleanQuadratic e)
    (yoshidaEndpointOddCleanQuadratic o)
    (factorTwoCenteredSymmetricPerturbation e)
    (factorTwoCenteredSymmetricPerturbation o)
    (factorTwoCenteredAlternatingCoupling e o)
    a b hEe hEo hQe hQo hPeLower hPeUpper hPoLower hPoUpper hJ hphase
  simpa only [factorTwoEndpointChannelPhase,
    factorTwoEndpointChannelCleanSum, factorTwoEndpointChannelSymmetricSum]
    using h

/-- The production aliases `yoshidaA` and `yoshidaEndpointA` give the same
endpoint-zero coercive tail theorem. -/
theorem tail_phase_uniform_clean_reserve
    (re ro : YoshidaClippedPeriodicCore yoshidaA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (heNeg : (re : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hePos : (re : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hoNeg : (ro : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoPos : (ro : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaA) x).re)
    let o := centeredRescale yoshidaA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaA) x).re)
    (1 / 200 : ℝ) * (yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have h := endpoint_tail_phase_uniform_clean_reserve
    re ro
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heTail)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoTail)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heReal)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoReal)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heNeg)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hePos)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoNeg)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoPos)
    a b hphase
  simpa only [YoshidaWeightedTailBounds.yoshidaA,
    YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using h

/-- Correcting the even endpoint trace preserves the same `1 / 200` clean
reserve for arbitrary real production Fourier tails. -/
theorem endpointAdapted_tail_phase_uniform_clean_reserve
    (re ro : YoshidaClippedPeriodicCore yoshidaA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaA (fun x ↦
      (((endpointAdaptedEvenTail re :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re)
    let o := centeredRescale yoshidaA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaA) x).re)
    (1 / 200 : ℝ) * (yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have heTail0 := endpointAdaptedEvenTail_mem_tail re heTail
  have heReal0 := endpointAdaptedEvenTail_real re heReal
  have heNeg0 := endpointAdaptedEvenTail_apply_neg re heTail heReal
  have hePos0 := endpointAdaptedEvenTail_apply_pos re heReal
  obtain ⟨hoNeg0, hoPos0⟩ := oddTail_endpoints_zero ro hoTail
  exact tail_phase_uniform_clean_reserve
    (endpointAdaptedEvenTail re) ro heTail0 hoTail heReal0 hoReal
    heNeg0 hePos0 hoNeg0 hoPos0 a b hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTailCoerciveStructural
