import ArithmeticHodge.Analysis.Contour.RectangleFiniteResidues
import ArithmeticHodge.Analysis.MultiplicativeWeilCriticalGammaPair
import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteXiContour
import ArithmeticHodge.Analysis.MultiplicativeWeilGammaArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilZetaPrimeIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical Bombieri boundary identities

The reflected left xi boundary is rewritten as a direct-plus-transpose right
boundary. Its prime part converges to `-primeSum`, while rectangular residue
shifts isolate the two polar Mellin values at zero and one.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ContDiff Distributions Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The polar and real-gamma part of `xi'/xi` after removing `zeta'/zeta`. -/
def bombieriArchPolar (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
    Complex.digamma (s / 2) / 2

/-- Right vertical integral of the Bombieri Mellin weight against `xi'/xi`. -/
def bombieriXiRightVertical
    (f : BombieriTest) (sigma T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T,
    mellin (f : ℝ → ℂ) (sigma + t * I) *
      logDeriv xiFunction (sigma + t * I)

/-- Left vertical integral on the side reflected from `Re(s)=sigma`. -/
def bombieriXiLeftVertical
    (f : BombieriTest) (sigma T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T,
    mellin (f : ℝ → ℂ) ((1 - sigma) + t * I) *
      logDeriv xiFunction ((1 - sigma) + t * I)

/-- After reflecting the left edge, the oriented difference of the two raw
vertical integrals is the right-line integral with the direct-plus-transpose
Mellin weight.  The surrounding factors of `I` are exactly those in
`rectIntegral`. -/
theorem bombieriXi_oriented_vertical_eq_right_pair
    (f : BombieriTest) (sigma T : ℝ) (hsigma : 1 < sigma) :
    I * bombieriXiRightVertical f sigma T -
        I * bombieriXiLeftVertical f sigma T =
      I * ∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
            logDeriv xiFunction (sigma + t * I) := by
  let L : ℝ → ℂ := fun t ↦
    mellin (f : ℝ → ℂ) ((1 - sigma) + t * I) *
      logDeriv xiFunction ((1 - sigma) + t * I)
  have hsymm : (∫ t : ℝ in -T..T, L t) =
      ∫ t : ℝ in -T..T, L (-t) := by
    have h := intervalIntegral.integral_comp_neg L
      (a := -T) (b := T)
    simpa only [neg_neg] using h.symm
  have hleft : bombieriXiLeftVertical f sigma T =
      -(∫ t : ℝ in -T..T,
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I) *
          logDeriv xiFunction (sigma + t * I)) := by
    rw [bombieriXiLeftVertical]
    change (∫ t : ℝ in -T..T, L t) = _
    rw [hsymm]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    have hs : ((1 : ℂ) - (sigma : ℂ) + ((-t : ℝ) : ℂ) * I) =
        1 - ((sigma : ℂ) + t * I) := by
      push_cast
      ring
    have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
        transpose (f : ℝ → ℂ) := by
      funext x
      exact transposeLinearMap_apply f x
    have hM : mellin (f : ℝ → ℂ)
        (1 - ((sigma : ℂ) + t * I)) =
          mellin (transposeLinearMap f : ℝ → ℂ)
            ((sigma : ℂ) + t * I) := by
      rw [hfun, mellin_transpose]
    have hxi : logDeriv xiFunction
        (1 - ((sigma : ℂ) + t * I)) =
          -logDeriv xiFunction ((sigma : ℂ) + t * I) := by
      have hx := xi_logDeriv_one_sub_add ((sigma : ℂ) + t * I)
      simp only [logDeriv_apply]
      linear_combination hx
    dsimp only [L]
    rw [hs, hM, hxi]
    ring
  rw [hleft, bombieriXiRightVertical]
  let A : ℝ → ℂ := fun t ↦
    mellin (f : ℝ → ℂ) (sigma + t * I) *
      logDeriv xiFunction (sigma + t * I)
  let B : ℝ → ℂ := fun t ↦
    mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I) *
      logDeriv xiFunction (sigma + t * I)
  have hline : Continuous (fun t : ℝ ↦ ((sigma : ℂ) + t * I)) := by
    fun_prop
  have hlog : Continuous (fun t : ℝ ↦
      logDeriv xiFunction ((sigma : ℂ) + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hsne : xiFunction ((sigma : ℂ) + t * I) ≠ 0 :=
      xiFunction_ne_zero_of_one_le_re (by simp; linarith)
    have hld : ContinuousAt (logDeriv xiFunction)
        ((sigma : ℂ) + t * I) :=
      (Contour.analyticAt_logDeriv_of_analyticAt
        (differentiable_xiFunction.analyticAt _) hsne).continuousAt
    exact ContinuousAt.comp'
      (f := fun u : ℝ ↦ (sigma : ℂ) + u * I) hld hline.continuousAt
  have hAcont : Continuous A := by
    exact ((bombieriMellin_differentiable f).continuous.comp hline).mul hlog
  have hBcont : Continuous B := by
    exact ((bombieriMellin_differentiable (transposeLinearMap f)).continuous.comp hline).mul hlog
  have hadd : (∫ t : ℝ in -T..T, A t) + (∫ t : ℝ in -T..T, B t) =
      ∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
            logDeriv xiFunction (sigma + t * I) := by
    rw [← intervalIntegral.integral_add
      (hAcont.intervalIntegrable (-T) T)
      (hBcont.intervalIntegrable (-T) T)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [A, B]
    ring
  change I * (∫ t : ℝ in -T..T, A t) -
      I * -(∫ t : ℝ in -T..T, B t) = _
  rw [← hadd]
  ring

/-- On a right vertical line, the paired xi logarithmic derivative has the
exact zeta plus polar/gamma decomposition used by the explicit formula. -/
theorem bombieriXi_oriented_vertical_eq_explicit_right_pair
    (f : BombieriTest) (sigma T : ℝ) (hsigma : 1 < sigma) :
    I * bombieriXiRightVertical f sigma T -
        I * bombieriXiLeftVertical f sigma T =
      I * ∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
          (deriv riemannZeta (sigma + t * I) /
              riemannZeta (sigma + t * I) +
            bombieriArchPolar (sigma + t * I)) := by
  rw [bombieriXi_oriented_vertical_eq_right_pair f sigma T hsigma]
  apply congrArg (fun x : ℂ ↦ I * x)
  apply intervalIntegral.integral_congr
  intro t _
  let s : ℂ := (sigma : ℂ) + t * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s]; linarith)
  have h := zeta_logDeriv_from_xi_explicit s hs1 hs0 hzeta
  have hxi : logDeriv xiFunction s =
      deriv riemannZeta s / riemannZeta s + bombieriArchPolar s := by
    rw [logDeriv_apply, h]
    simp only [bombieriArchPolar]
    ring
  change (mellin (f : ℝ → ℂ) s +
      mellin (transposeLinearMap f : ℝ → ℂ) s) *
        logDeriv xiFunction s = _
  rw [hxi]

/-- The full right-line prime component has the negative sign required by
Bombieri's functional. -/
theorem bombieriOuterPrimeIntegral
    (f : BombieriTest) (sigma : ℝ) (hsigma : 1 < sigma) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (mellin (f : ℝ → ℂ) (sigma + t * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
              (deriv riemannZeta (sigma + t * I) /
                riemannZeta (sigma + t * I)) =
      -primeSum f := by
  have h := bombieriPrimeSum_integral f sigma hsigma
  let N : ℝ → ℂ := fun t ↦
    (mellin (f : ℝ → ℂ) (sigma + t * I) +
      mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
        (-(deriv riemannZeta (sigma + t * I) /
          riemannZeta (sigma + t * I)))
  have hint : (∫ t : ℝ,
      (mellin (f : ℝ → ℂ) (sigma + t * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
          (deriv riemannZeta (sigma + t * I) /
            riemannZeta (sigma + t * I))) = -(∫ t : ℝ, N t) := by
    rw [← MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [N]
    ring
  rw [hint]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * -(∫ t : ℝ, N t) = _
  have hN : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, N t) =
      primeSum f := by
    simpa only [N] using h
  rw [← hN]
  ring

/-- Finite symmetric truncations of the right-line prime component converge
to `-primeSum f`. -/
theorem bombieriOuterPrimeIntervalIntegral_tendsto
    (f : BombieriTest) (sigma : ℝ) (hsigma : 1 < sigma)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ in -T n..T n,
          (mellin (f : ℝ → ℂ) (sigma + t * I) +
            mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
              (deriv riemannZeta (sigma + t * I) /
                riemannZeta (sigma + t * I)))
      atTop (nhds (-primeSum f)) := by
  let P : ℝ → ℂ := fun t ↦
    (mellin (f : ℝ → ℂ) (sigma + t * I) +
      mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
        (deriv riemannZeta (sigma + t * I) /
          riemannZeta (sigma + t * I))
  have hP : Integrable P := by
    have hneg := bombieriPrimeSum_integrand_integrable f sigma hsigma
    refine hneg.neg.congr ?_
    filter_upwards [] with t
    simp only [P, Pi.neg_apply]
    ring
  have hinterval : Tendsto (fun n ↦ ∫ t : ℝ in -T n..T n, P t)
      atTop (nhds (∫ t : ℝ, P t)) :=
    intervalIntegral_tendsto_integral hP
      (tendsto_neg_atTop_atBot.comp hT) hT
  have hscaled := hinterval.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have heval : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, P t) = -primeSum f := by
    simpa only [P] using bombieriOuterPrimeIntegral f sigma hsigma
  rw [heval] at hscaled
  simpa only [P] using hscaled

private def bombieriArchPolarRegular (s : ℂ) : ℂ :=
  1 / s - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2

private theorem bombieriArchPolarRegular_differentiableAt
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ bombieriArchPolarRegular s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hhalf : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s :=
    analyticAt_id.div_const (c := 2)
  have hhalfRe : 0 < (s / 2).re := by
    simpa using half_pos hs
  have hGammaAnalytic : AnalyticAt ℂ Complex.Gamma (s / 2) := by
    have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
      intro z hz
      exact (Complex.differentiableAt_Gamma z (fun m hm ↦ by
        have hre := congrArg Complex.re hm
        simp only [neg_re, natCast_re] at hre
        have hzpos : 0 < z.re := hz
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith)).differentiableWithinAt
    have hopen : IsOpen {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const continuous_re
    exact (hdiff.analyticOnNhd hopen) (s / 2) hhalfRe
  have hGammaNe : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hhalfRe
  have hpsi : AnalyticAt ℂ Complex.digamma (s / 2) := by
    simpa only [Complex.digamma_def] using
      Contour.analyticAt_logDeriv_of_analyticAt
        hGammaAnalytic hGammaNe
  have hpsiComp : AnalyticAt ℂ (fun z : ℂ ↦ Complex.digamma (z / 2)) s :=
    hpsi.comp' (f := fun z : ℂ ↦ z / 2) hhalf
  unfold bombieriArchPolarRegular
  exact (((differentiableAt_const (c := (1 : ℂ))).div differentiableAt_id hs0).sub
    (differentiableAt_const (c := (Real.log Real.pi : ℂ) / 2))).add
      (hpsiComp.differentiableAt.div_const 2)

/-- The archimedean/polar factor is differentiable in the positive half-plane
away from its simple pole at one. -/
theorem bombieriArchPolar_differentiableAt
    {s : ℂ} (hspos : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ bombieriArchPolar s := by
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [show bombieriArchPolar = fun z ↦
      bombieriArchPolarRegular z + 1 / (z - 1) by
    funext z
    simp only [bombieriArchPolar, bombieriArchPolarRegular]
    ring]
  exact (bombieriArchPolarRegular_differentiableAt hspos).add
    ((differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.sub_const 1) hden)


/-- Moving the archimedean/polar factor from `Re(s)=sigma` to the critical
line crosses exactly the simple pole at `s=1`, with residue `M f(1)`. -/
theorem rectIntegral_bombieriMellin_mul_archPolar
    (f : BombieriTest) (sigma T : ℝ)
    (hsigma : 1 < sigma) (hT : 0 < T) :
    rectIntegral
        (fun s ↦ mellin (f : ℝ → ℂ) s * bombieriArchPolar s)
        (((1 / 2 : ℝ) : ℂ) - T * I)
        ((sigma : ℂ) + T * I) =
      2 * (Real.pi : ℂ) * I * mellin (f : ℝ → ℂ) 1 := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) - T * I
  let w : ℂ := (sigma : ℂ) + T * I
  let M : ℂ → ℂ := mellin (f : ℝ → ℂ)
  let G : ℂ → ℂ := fun s ↦ M s * bombieriArchPolarRegular s
  have hrew : z.re < w.re := by simp [z, w]; linarith
  have himw : z.im < w.im := by simp [z, w]; linarith
  have hG : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]),
      DifferentiableAt ℂ G s := by
    intro s hsrect
    have hscoords := hsrect
    rw [mem_reProdIm, uIcc_of_le hrew.le, uIcc_of_le himw.le] at hscoords
    have hspos : 0 < s.re := by
      have hzre : z.re = 1 / 2 := by simp [z]
      linarith [hscoords.1.1]
    exact (bombieriMellin_differentiable f s).mul
      (bombieriArchPolarRegular_differentiableAt hspos)
  have hM : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]),
      DifferentiableAt ℂ M s := by
    intro s _
    exact bombieriMellin_differentiable f s
  have hres := Contour.rectIntegral_finite_simple_residues_add_remainder
    (G := G) (H := M) (a := fun _ : ℂ ↦ 1) (S := {1})
    (z := z) (w := w) hrew himw hG hM (by
      intro rho hrho
      simp only [Finset.mem_singleton] at hrho
      subst rho
      simp [z, w, hsigma, hT]
      norm_num)
  have hfun : (fun s ↦ M s * bombieriArchPolar s) =
      fun s ↦ G s + ∑ rho ∈ ({1} : Finset ℂ),
        (1 : ℂ) * M s * (s - rho)⁻¹ := by
    funext s
    simp only [Finset.sum_singleton, G, bombieriArchPolar,
      bombieriArchPolarRegular]
    ring
  rw [hfun]
  simpa only [Finset.sum_singleton, one_mul, M, z, w] using hres

/-- The same contour shift for the transpose contributes the other polar
Mellin value `M f(0)`. -/
theorem rectIntegral_bombieriTransposeMellin_mul_archPolar
    (f : BombieriTest) (sigma T : ℝ)
    (hsigma : 1 < sigma) (hT : 0 < T) :
    rectIntegral
        (fun s ↦ mellin (transposeLinearMap f : ℝ → ℂ) s *
          bombieriArchPolar s)
        (((1 / 2 : ℝ) : ℂ) - T * I)
        ((sigma : ℂ) + T * I) =
      2 * (Real.pi : ℂ) * I * mellin (f : ℝ → ℂ) 0 := by
  rw [rectIntegral_bombieriMellin_mul_archPolar
    (transposeLinearMap f) sigma T hsigma hT]
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  rw [hfun, mellin_transpose]
  norm_num

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

