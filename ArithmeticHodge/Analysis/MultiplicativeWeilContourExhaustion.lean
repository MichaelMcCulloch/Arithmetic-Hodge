import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteXiContour
import ArithmeticHodge.Analysis.XiContourSequence
import ArithmeticHodge.Analysis.XiZetaZeroEquiv

/-!
# Bombieri contour exhaustion

The finite outer-rectangle formula and the finite-divisor convergence theorem
assemble into a single unconditional contour exhaustion.  The remaining
explicit-formula task is to evaluate the limiting boundary integral.
-/

set_option autoImplicit false

open Complex Filter Set Topology
open scoped Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Along a paired zero-free exhaustion with fixed outer vertical sides, the
normalized explicit Bombieri boundary integrals converge to the distinct
nontrivial-zero sum with analytic multiplicity. -/
theorem exists_bombieri_outer_contour_tendsto_distinct_zero_sum
    (f : BombieriTest) (sigmaLower sigmaUpper : ℝ)
    (hlower : sigmaLower < 0) (hupper : 1 < sigmaUpper) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        (n : ℝ) < T n ∧ T n < (n : ℝ) + 1 ∧
        (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction (σ + T n * I) ≠ 0) ∧
        (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction (σ - T n * I) ≠ 0)) ∧
      Tendsto
        (fun n =>
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            rectIntegral
              (fun s ↦ mellin (f : ℝ → ℂ) s *
                (deriv riemannZeta s / riemannZeta s +
                  1 / s + 1 / (s - 1) -
                    (Real.log Real.pi : ℂ) / 2 +
                      Complex.digamma (s / 2) / 2))
              ((sigmaLower : ℂ) - (T n : ℂ) * I)
              ((sigmaUpper : ℂ) + (T n : ℂ) * I))
        atTop
        (nhds (∑' rho : NontrivialZetaZero,
          (analyticOrderNatAt riemannZeta rho.val : ℂ) *
            mellin (f : ℝ → ℂ) rho.val)) := by
  obtain ⟨T, hT, hdata⟩ := exists_xi_outer_contour_sequence
    sigmaLower sigmaUpper hlower hupper
    (mellin (f : ℝ → ℂ)) (bombieriMellin_differentiable f)
  refine ⟨T, hT, ?_, ?_⟩
  · intro n
    exact ⟨(hdata n).1, (hdata n).2.1,
      (hdata n).2.2.1, (hdata n).2.2.2.1⟩
  · have hzeros := tendsto_finite_xiMultiplicity_mellin_sum f hT
    apply hzeros.congr'
    exact Filter.Eventually.of_forall fun n => by
      exact (bombieriFiniteOuterXiContour_of_horizontal_pair
        f hlower hupper
        ((Nat.cast_nonneg n).trans_lt (hdata n).1)
        (hdata n).2.2.1 (hdata n).2.2.2.1)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
