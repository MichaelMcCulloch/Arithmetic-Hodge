import ArithmeticHodge.Arithmetic.HodgeIndex
import ArithmeticHodge.Strategy.DetailedBalance

open MeasureTheory
open scoped InnerProductSpace

namespace ArithmeticHodge

set_option autoImplicit false

-- The Arakelov class is exactly a packaging of Weil positivity.

theorem degree_zero_spec_Z_self_intersection_eq_zero_scratch
    (L : Arithmetic.MetrizedLineBundle) (hL : Arithmetic.isDegreeZero L) :
    Arithmetic.arakelovSelfIntersection L = 0 := by
  have hmetric : L.logMetric = 0 := (Arithmetic.isDegreeZero_iff L).mp hL
  simp [Arithmetic.arakelovSelfIntersection, hmetric]

theorem nonempty_arakelovIntersectionTheory_iff_weilPositivity_scratch
    (α : Type*) :
    Nonempty (Arithmetic.ArakelovIntersectionTheory α) ↔
      Analysis.WeilPositivity := by
  constructor
  · rintro ⟨inst⟩
    exact inst.arakelov_weil_bridge inst.neg_semidef
  · intro hwp
    refine ⟨{
      pairing := fun _ _ => 0
      pairing_symm := ?_
      neg_semidef := ?_
      arakelov_weil_bridge := ?_
    }⟩
    · intro x y
      rfl
    · intro x
      exact le_rfl
    · intro _
      exact hwp

theorem hodge_index_hypothesis_automatic_scratch
    [inst : Arithmetic.ArakelovIntersectionTheory Arithmetic.ArakelovChowClass] :
    ∀ α : Arithmetic.ArakelovChowClass,
      Arithmetic.arakelovPairing α α ≤ 0 := by
  intro α
  exact Arithmetic.arithmetic_hodge_index α

theorem hodge_index_conditional_iff_RH_scratch
    [inst : Arithmetic.ArakelovIntersectionTheory Arithmetic.ArakelovChowClass] :
    ((∀ α : Arithmetic.ArakelovChowClass,
        Arithmetic.arakelovPairing α α ≤ 0) → RiemannHypothesis) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact h hodge_index_hypothesis_automatic_scratch
  · intro hRH _
    exact hRH

theorem nonempty_arakelovIntersectionTheory_iff_RH_current_scratch
    (α : Type*) :
    Nonempty (Arithmetic.ArakelovIntersectionTheory α) ↔
      RiemannHypothesis := by
  exact (nonempty_arakelovIntersectionTheory_iff_weilPositivity_scratch α).trans
    Analysis.weil_criterion_equiv.symm

-- Workpacket goals whose signatures omit the claimed analytic data.

theorem symmetric_bounded_operator_exists_without_flow_scratch
    (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    ∃ D : H →L[ℂ] H,
      ∀ x y : H, ⟪D x, y⟫_ℂ = ⟪x, D y⟫_ℂ := by
  exact ⟨0, fun x y => by simp⟩

theorem inverse_error_decay_without_balance_data_scratch :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > 0, ∃ Λ₀ : ℝ, Λ₀ > 0 ∧
      ∀ Λ' ≥ Λ₀, C / Λ' < ε := by
  simpa using Strategy.approximate_detailed_balance 1 one_pos

theorem unconstrained_trace_error_witness_scratch (_f : ℝ → ℝ) :
    ∃ trace error : ℝ, error ≥ 0 ∧ trace ≥ -error := by
  exact ⟨0, 0, le_rfl, by norm_num⟩

theorem workpacket_5_aggregate_goal_iff_weilPositivity_scratch :
    (∀ (f : ℝ → ℝ), Analysis.IsAutocorrelation f → Continuous f →
      (∀ x, ‖f x‖ ≤ 1 / (1 + x ^ 2)) →
      0 ≤ Analysis.weilFunctionalFull f (Analysis.fourierCos f)) ↔
      Analysis.WeilPositivity := by
  rfl

theorem chain_strategy_C_eq_weil_criterion_backward_scratch :
    Strategy.chain_strategy_C = Analysis.weil_criterion_backward := by
  rfl

#print axioms nonempty_arakelovIntersectionTheory_iff_weilPositivity_scratch
#print axioms degree_zero_spec_Z_self_intersection_eq_zero_scratch
#print axioms hodge_index_hypothesis_automatic_scratch
#print axioms hodge_index_conditional_iff_RH_scratch
#print axioms nonempty_arakelovIntersectionTheory_iff_RH_current_scratch
#print axioms symmetric_bounded_operator_exists_without_flow_scratch
#print axioms inverse_error_decay_without_balance_data_scratch
#print axioms unconstrained_trace_error_witness_scratch
#print axioms workpacket_5_aggregate_goal_iff_weilPositivity_scratch
#print axioms chain_strategy_C_eq_weil_criterion_backward_scratch

#print axioms Arithmetic.arithmetic_hodge_index
#print axioms Arithmetic.hodge_index_implies_RH
#print axioms Strategy.regularized_trace_limit
#print axioms Strategy.workpacket_5_trace_formula_positivity
#print axioms Strategy.workpacket_6_weil_positivity_implies_rh
#print axioms Strategy.chain_strategy_C

end ArithmeticHodge
