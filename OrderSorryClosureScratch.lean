import ArithmeticHodge.Analysis.ZetaProduct

set_option autoImplicit false

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

/-!
The remaining source `sorry` tries to feed xi zeros (`hadamardZeros`) into
the subtype of zeros of `completedRiemannZeta₀`.  These two zero sets are in
fact disjoint: by definition

  xi(s) = (1/2) * s * (s - 1) * completedRiemannZeta₀(s) + 1/2.

Thus a zero of `completedRiemannZeta₀` has xi-value `1/2`, not zero.
-/

/-- A zero of the regularized completed zeta has xi-value `1/2`. -/
theorem completedZeta_zero_implies_xi_eq_half_order_scratch {z : ℂ}
    (hz : completedRiemannZeta₀ z = 0) :
    xiFunction z = 1 / 2 := by
  simp [xiFunction, hz]

/-- Consequently no xi zero is a zero of the regularized completed zeta. -/
theorem xi_zero_implies_completedZeta_ne_zero_order_scratch {z : ℂ}
    (hz : xiFunction z = 0) :
    completedRiemannZeta₀ z ≠ 0 := by
  intro hcompleted
  have hhalf := completedZeta_zero_implies_xi_eq_half_order_scratch hcompleted
  rw [hz] at hhalf
  norm_num at hhalf

/-- The two zero sets used in the source proof sketch are disjoint. -/
theorem xiZeroSet_disjoint_completedZetaZeroSet_order_scratch :
    Disjoint {z : ℂ | xiFunction z = 0}
      {z : ℂ | completedRiemannZeta₀ z = 0} := by
  rw [Set.disjoint_left]
  intro z hxi hcompleted
  exact xi_zero_implies_completedZeta_ne_zero_order_scratch hxi hcompleted

/-- No sequence consisting of xi zeros can be lifted pointwise to the
completed-zeta zero subtype.  This is the exact bridge asserted in the
source `sorry` comments. -/
theorem no_completedZetaZero_lift_of_xiZero_sequence_order_scratch
    (a : ℕ → ℂ) (ha : ∀ n, xiFunction (a n) = 0) :
    ¬ ∃ lift : ℕ → {w : ℂ // completedRiemannZeta₀ w = 0 ∧ w ≠ 0},
      ∀ n, (lift n : ℂ) = a n := by
  rintro ⟨lift, hlift⟩
  have hcompleted : completedRiemannZeta₀ (a 0) = 0 := by
    rw [← hlift 0]
    exact (lift 0).property.1
  exact xi_zero_implies_completedZeta_ne_zero_order_scratch (ha 0) hcompleted

/-- A basic warning that finite order by itself cannot provide the desired
lower zero-density bound: the complex exponential is entire and its
distinct-zero inverse-power series is vacuously summable at every exponent. -/
theorem complexExp_distinct_zero_rpow_summable_order_scratch (s : ℝ) :
    Summable (fun z : {w : ℂ // Complex.exp w = 0 ∧ w ≠ 0} =>
      ‖(z : ℂ)‖⁻¹ ^ s) := by
  let Z := {w : ℂ // Complex.exp w = 0 ∧ w ≠ 0}
  have hZ : IsEmpty Z := by
    constructor
    intro z
    exact Complex.exp_ne_zero z z.property.1
  letI : IsEmpty Z := hZ
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

#print axioms completedZeta_zero_implies_xi_eq_half_order_scratch
#print axioms xi_zero_implies_completedZeta_ne_zero_order_scratch
#print axioms xiZeroSet_disjoint_completedZetaZeroSet_order_scratch
#print axioms no_completedZetaZero_lift_of_xiZero_sequence_order_scratch
#print axioms complexExp_distinct_zero_rpow_summable_order_scratch

end ArithmeticHodge.Analysis.EntireFunction
