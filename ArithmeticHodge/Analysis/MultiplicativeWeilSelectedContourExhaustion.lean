import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteXiContour
import ArithmeticHodge.Analysis.MultiplicativeWeilXiHorizontalVanishing
import ArithmeticHodge.Analysis.XiZetaZeroEquiv

/-!
# Selected Bombieri contour exhaustion

One symmetric outer contour sequence is chosen to satisfy every condition used
later: paired zero-freeness, horizontal vanishing, and convergence of the
normalized finite contour to the distinct zero sum.
-/

set_option autoImplicit false

open Complex Filter Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A single symmetric outer contour sequence is simultaneously zero-free,
has vanishing horizontal xi terms, and exhausts the distinct zeta-zero sum. -/
theorem exists_bombieri_selected_outer_contour_exhaustion
    (f : BombieriTest) (sigma : ℝ) (hsigma : 1 < sigma) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        0 < T n ∧
        (∀ x ∈ Set.Icc (1 - sigma) sigma,
          xiFunction ((x : ℂ) + T n * I) ≠ 0) ∧
        (∀ x ∈ Set.Icc (1 - sigma) sigma,
          xiFunction ((x : ℂ) - T n * I) ≠ 0)) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalUpper f (logDeriv xiFunction)
          (1 - sigma) sigma (T n)) atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction)
          (1 - sigma) sigma (T n)) atTop (nhds 0) ∧
      Tendsto
        (fun n ↦
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            rectIntegral
              (fun s ↦ mellin (f : ℝ → ℂ) s *
                (deriv riemannZeta s / riemannZeta s +
                  1 / s + 1 / (s - 1) -
                    (Real.log Real.pi : ℂ) / 2 +
                      Complex.digamma (s / 2) / 2))
              (((1 - sigma : ℝ) : ℂ) - (T n : ℂ) * I)
              ((sigma : ℂ) + (T n : ℂ) * I))
        atTop
        (nhds (∑' rho : NontrivialZetaZero,
          (analyticOrderNatAt riemannZeta rho.val : ℂ) *
            mellin (f : ℝ → ℂ) rho.val)) := by
  have hsides : 1 - sigma < sigma := by linarith
  obtain ⟨T, hT, hfree, htop, hbottom⟩ :=
    exists_bombieri_xi_horizontal_vanishing_sequence
      f (1 - sigma) sigma hsides
  refine ⟨T, hT, hfree, htop, hbottom, ?_⟩
  have hzeros := tendsto_finite_xiMultiplicity_mellin_sum f hT
  apply hzeros.congr'
  exact Filter.Eventually.of_forall fun n => by
    exact bombieriFiniteOuterXiContour_of_horizontal_pair
      f (by linarith) hsigma (hfree n).1 (hfree n).2.1 (hfree n).2.2

end

end ArithmeticHodge.Analysis.MultiplicativeWeil


