import ArithmeticHodge.Analysis.MultiplicativeWeilContourExhaustion
import ArithmeticHodge.Analysis.MultiplicativeWeilDistinctZeroSum
import ArithmeticHodge.Analysis.MultiplicativeWeilSelectedContourExhaustion
import ArithmeticHodge.Analysis.MultiplicativeWeilVerticalBoundary
import ArithmeticHodge.Analysis.MultiplicativeWeilXiHorizontalVanishing

/-!
# Bombieri contour-limit assembly

The normalized outer boundary is split into horizontal, prime, and
archimedean/polar components.  Once the single right-line arch-polar limit is
available, the selected contour exhaustion yields the full distinct and
enumerated Bombieri zero-sum formulas.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Set Topology
open scoped Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The normalized explicit integrand on a symmetric outer rectangle. -/
def bombieriExplicitOuterBoundary
    (f : BombieriTest) (sigma T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    rectIntegral
      (fun s ↦ mellin (f : ℝ → ℂ) s *
        (deriv riemannZeta s / riemannZeta s + bombieriArchPolar s))
      (((1 - sigma : ℝ) : ℂ) - T * I)
      ((sigma : ℂ) + T * I)

/-- The normalized truncated prime contribution on the right vertical line. -/
def bombieriRightPrimeBoundary
    (f : BombieriTest) (sigma T : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) (sigma + t * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
      (deriv riemannZeta (sigma + t * I) /
        riemannZeta (sigma + t * I)))

/-- The normalized truncated archimedean and polar contribution on the right line. -/
def bombieriRightArchPolarBoundary
    (f : BombieriTest) (sigma T : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) (sigma + t * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
      bombieriArchPolar (sigma + t * I))

/-- The remaining analytic input after the proved prime, residue, and
horizontal calculations. -/
def BombieriArchPolarRightLineLimit : Prop :=
  ∀ (f : BombieriTest) (sigma : ℝ), 1 < sigma →
    ∀ T : ℕ → ℝ, Tendsto T atTop atTop →
      Tendsto (fun n ↦ bombieriRightArchPolarBoundary f sigma (T n))
        atTop (nhds
          (mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
            bombieriArchTerm f))

private theorem bombieriRightExplicitInterval_eq_prime_add_arch
    (f : BombieriTest) (sigma T : ℝ) (hsigma : 1 < sigma) :
    (∫ t : ℝ in -T..T,
      (mellin (f : ℝ → ℂ) (sigma + t * I) +
        mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
      (deriv riemannZeta (sigma + t * I) /
          riemannZeta (sigma + t * I) +
        bombieriArchPolar (sigma + t * I))) =
      (∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
        (deriv riemannZeta (sigma + t * I) /
          riemannZeta (sigma + t * I))) +
      (∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
        bombieriArchPolar (sigma + t * I)) := by
  let line : ℝ → ℂ := fun t ↦ (sigma : ℂ) + t * I
  let pair : ℝ → ℂ := fun t ↦
    mellin (f : ℝ → ℂ) (line t) +
      mellin (transposeLinearMap f : ℝ → ℂ) (line t)
  let P : ℝ → ℂ := fun t ↦ pair t *
    (deriv riemannZeta (line t) / riemannZeta (line t))
  let A : ℝ → ℂ := fun t ↦ pair t * bombieriArchPolar (line t)
  let Q : ℝ → ℂ := fun t ↦ pair t *
    (deriv riemannZeta (line t) / riemannZeta (line t) +
      bombieriArchPolar (line t))
  have hline : Continuous line := by
    dsimp only [line]
    fun_prop
  have hpair : Continuous pair := by
    exact ((bombieriMellin_differentiable f).continuous.comp hline).add
      ((bombieriMellin_differentiable (transposeLinearMap f)).continuous.comp hline)
  have hxi : Continuous (fun t ↦ logDeriv xiFunction (line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : xiFunction (line t) ≠ 0 :=
      xiFunction_ne_zero_of_one_le_re (by simp [line]; linarith)
    exact ContinuousAt.comp'
      (Contour.analyticAt_logDeriv_of_analyticAt
        (differentiable_xiFunction.analyticAt _) hne).continuousAt
      hline.continuousAt
  have hQ : IntervalIntegrable Q volume (-T) T := by
    apply ((hpair.mul hxi).intervalIntegrable (-T) T).congr
    intro t _
    let s := line t
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [s, line] at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [s, line] at hre
      linarith
    have hne : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp [s, line]; linarith)
    have h := zeta_logDeriv_from_xi_explicit s hs1 hs0 hne
    simp only [Q, pair]
    change pair t * logDeriv xiFunction s = pair t *
      (deriv riemannZeta s / riemannZeta s + bombieriArchPolar s)
    congr 1
    rw [logDeriv_apply, h]
    simp only [bombieriArchPolar]
    ring
  have hP : IntervalIntegrable P volume (-T) T := by
    have hneg := bombieriPrimeSum_integrand_integrable f sigma hsigma
    have hPglobal : Integrable P := by
      refine hneg.neg.congr ?_
      filter_upwards [] with t
      simp only [P, pair, line, Pi.neg_apply]
      ring
    exact hPglobal.intervalIntegrable
  have hA : IntervalIntegrable A volume (-T) T := by
    apply (hQ.sub hP).congr
    intro t _
    simp only [Q, P, A]
    ring
  change (∫ t : ℝ in -T..T, Q t) =
    (∫ t : ℝ in -T..T, P t) + ∫ t : ℝ in -T..T, A t
  rw [← intervalIntegral.integral_add hP hA]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Q, P, A]
  ring

theorem bombieriExplicitOuterBoundary_eq_components
    (f : BombieriTest) (sigma T : ℝ) (hsigma : 1 < sigma) :
    bombieriExplicitOuterBoundary f sigma T =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (bombieriHorizontalLower f (logDeriv xiFunction)
            (1 - sigma) sigma T -
          bombieriHorizontalUpper f (logDeriv xiFunction)
            (1 - sigma) sigma T) +
      bombieriRightPrimeBoundary f sigma T +
      bombieriRightArchPolarBoundary f sigma T := by
  let z : ℂ := ((1 - sigma : ℝ) : ℂ) - T * I
  let w : ℂ := (sigma : ℂ) + T * I
  have hrewrite :
      rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s * logDeriv xiFunction s) z w =
        rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s *
            (deriv riemannZeta s / riemannZeta s + bombieriArchPolar s)) z w := by
    rw [ArithmeticHodge.Analysis.rectIntegral_weighted_xi_logDeriv_eq_zeta_gamma_polar]
    apply congrArg (fun F : ℂ → ℂ ↦ rectIntegral F z w)
    funext s
    simp only [bombieriArchPolar]
    ring
  unfold bombieriExplicitOuterBoundary
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectIntegral
        (fun s ↦ mellin (f : ℝ → ℂ) s *
          (deriv riemannZeta s / riemannZeta s + bombieriArchPolar s)) z w = _
  rw [← hrewrite]
  rw [show z = (((1 - sigma : ℝ) : ℂ) - T * I) by rfl,
    show w = ((sigma : ℂ) + T * I) by rfl,
    rectIntegral_bombieri_horizontal_decomposition]
  let R : ℂ := ∫ y : ℝ in -T..T,
    mellin (f : ℝ → ℂ) (sigma + y * I) *
      logDeriv xiFunction (sigma + y * I)
  let L : ℂ := ∫ y : ℝ in -T..T,
    mellin (f : ℝ → ℂ) ((1 - sigma : ℝ) + y * I) *
      logDeriv xiFunction ((1 - sigma : ℝ) + y * I)
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      ((bombieriHorizontalLower f (logDeriv xiFunction) (1 - sigma) sigma T -
          bombieriHorizontalUpper f (logDeriv xiFunction) (1 - sigma) sigma T +
        I * R) - I * L) = _
  have hvertical : I * R - I * L =
      I * ∫ t : ℝ in -T..T,
        (mellin (f : ℝ → ℂ) (sigma + t * I) +
          mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
          (deriv riemannZeta (sigma + t * I) /
              riemannZeta (sigma + t * I) +
            bombieriArchPolar (sigma + t * I)) := by
    have hcast : (((1 - sigma : ℝ) : ℂ)) = 1 - (sigma : ℂ) := by
      push_cast
      rfl
    simpa only [R, L, bombieriXiRightVertical, bombieriXiLeftVertical,
      hcast] using
      bombieriXi_oriented_vertical_eq_explicit_right_pair f sigma T hsigma
  rw [show
      (bombieriHorizontalLower f (logDeriv xiFunction) (1 - sigma) sigma T -
          bombieriHorizontalUpper f (logDeriv xiFunction) (1 - sigma) sigma T +
        I * R) - I * L =
        (bombieriHorizontalLower f (logDeriv xiFunction) (1 - sigma) sigma T -
          bombieriHorizontalUpper f (logDeriv xiFunction) (1 - sigma) sigma T) +
        (I * R - I * L) by ring]
  rw [hvertical]
  rw [bombieriRightExplicitInterval_eq_prime_add_arch f sigma T hsigma]
  have hscale : (2 * (Real.pi : ℂ) * I)⁻¹ * I =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) := by
    push_cast
    field_simp [Real.pi_ne_zero, I_ne_zero]
  unfold bombieriRightPrimeBoundary bombieriRightArchPolarBoundary
  let H : ℂ :=
    bombieriHorizontalLower f (logDeriv xiFunction) (1 - sigma) sigma T -
      bombieriHorizontalUpper f (logDeriv xiFunction) (1 - sigma) sigma T
  let P : ℂ := ∫ t : ℝ in -T..T,
    (mellin (f : ℝ → ℂ) (sigma + t * I) +
      mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
    (deriv riemannZeta (sigma + t * I) / riemannZeta (sigma + t * I))
  let A : ℂ := ∫ t : ℝ in -T..T,
    (mellin (f : ℝ → ℂ) (sigma + t * I) +
      mellin (transposeLinearMap f : ℝ → ℂ) (sigma + t * I)) *
    bombieriArchPolar (sigma + t * I)
  change (2 * (Real.pi : ℂ) * I)⁻¹ * (H + I * (P + A)) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * H +
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * P +
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * A
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ * (H + I * (P + A)) =
        (2 * (Real.pi : ℂ) * I)⁻¹ * H +
          ((2 * (Real.pi : ℂ) * I)⁻¹ * I) * (P + A) := by ring
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ * H +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (P + A) := by rw [hscale]
    _ = _ := by ring

/-- One quantitatively selected contour sequence has both its boundary
evaluation and its zero-side exhaustion aligned. -/
theorem exists_bombieri_selected_outer_contour_tendsto_functional
    (harch : BombieriArchPolarRightLineLimit)
    (f : BombieriTest) (sigma : ℝ) (hsigma : 1 < sigma) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      (Tendsto (fun n ↦ bombieriExplicitOuterBoundary f sigma (T n))
        atTop (nhds (bombieriFunctional f))) ∧
      Tendsto (fun n ↦ bombieriExplicitOuterBoundary f sigma (T n))
        atTop
        (nhds (∑' rho : NontrivialZetaZero,
          (analyticOrderNatAt riemannZeta rho.val : ℂ) *
            mellin (f : ℝ → ℂ) rho.val)) := by
  obtain ⟨T, hT, _hfree, htop, hbottom, hzero⟩ :=
    exists_bombieri_selected_outer_contour_exhaustion f sigma hsigma
  have hhorizontal : Tendsto
      (fun n ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        (bombieriHorizontalLower f (logDeriv xiFunction)
            (1 - sigma) sigma (T n) -
          bombieriHorizontalUpper f (logDeriv xiFunction)
            (1 - sigma) sigma (T n))) atTop (nhds 0) := by
    simpa using (hbottom.sub htop).const_mul ((2 * (Real.pi : ℂ) * I)⁻¹)
  have hprime := bombieriOuterPrimeIntervalIntegral_tendsto
    f sigma hsigma T hT
  have harch' := harch f sigma hsigma T hT
  have hcomponents := (hhorizontal.add hprime).add harch'
  have hfunctional : Tendsto
      (fun n ↦ bombieriExplicitOuterBoundary f sigma (T n))
      atTop (nhds (bombieriFunctional f)) := by
    have hlimit :
        (0 : ℂ) + (-primeSum f) +
            (mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 +
              bombieriArchTerm f) = bombieriFunctional f := by
      rw [bombieriFunctional_apply]
      ring
    rw [hlimit] at hcomponents
    apply hcomponents.congr'
    exact Filter.Eventually.of_forall fun n ↦
      (bombieriExplicitOuterBoundary_eq_components
        f sigma (T n) hsigma).symm
  have hzero' : Tendsto
      (fun n ↦ bombieriExplicitOuterBoundary f sigma (T n))
      atTop
      (nhds (∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          mellin (f : ℝ → ℂ) rho.val)) := by
    apply hzero.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      unfold bombieriExplicitOuterBoundary
      apply congrArg (fun x : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ * x)
      apply congrArg (fun F : ℂ → ℂ ↦
        rectIntegral F
          (((1 - sigma : ℝ) : ℂ) - (T n : ℂ) * I)
          ((sigma : ℂ) + (T n : ℂ) * I))
      funext s
      simp only [bombieriArchPolar]
      ring
  exact ⟨T, hT, hfunctional, hzero'⟩

/-- The sole remaining archimedean/polar right-line limit implies the full
distinct-zero Bombieri explicit formula. -/
theorem bombieriDistinctZeroSumFormula_of_archPolarRightLineLimit
    (harch : BombieriArchPolarRightLineLimit) :
    BombieriDistinctZeroSumFormula := by
  intro f
  obtain ⟨T, _hT, hfunctional, hzero⟩ :=
    exists_bombieri_selected_outer_contour_tendsto_functional
      harch f 2 (by norm_num)
  exact tendsto_nhds_unique hfunctional hzero

/-- Consequently every exhaustive exact-multiplicity enumeration satisfies
the existing Bombieri zero-sum interface. -/
theorem bombieriZeroSumFormula_of_archPolarRightLineLimit
    (harch : BombieriArchPolarRightLineLimit)
    (zeros : ZetaZeroEnumeration) :
    BombieriZeroSumFormula zeros :=
  (bombieriZeroSumFormula_iff_distinct zeros).2
    (bombieriDistinctZeroSumFormula_of_archPolarRightLineLimit harch)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

