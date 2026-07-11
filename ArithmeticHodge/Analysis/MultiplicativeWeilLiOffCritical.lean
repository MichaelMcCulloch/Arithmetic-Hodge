import ArithmeticHodge.Analysis.MultiplicativeWeilLiAlgebra
import ArithmeticHodge.Analysis.XiZetaZeroEquiv
import ArithmeticHodge.Analysis.ZetaZeroCount

/-!
# An expanding Li base from failure of RH

The functional equation reflects any off-line zero to the left half of the
critical strip.  The exact Li modulus identity then gives a base of norm
strictly greater than one, the geometric input to Bombieri's negativity
argument.
-/

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Failure of RH supplies a nontrivial zero strictly to the left of the
critical line, after applying the functional equation if necessary. -/
theorem not_RH_exists_left_nontrivial_zero
    (hnot : ¬ RiemannHypothesis) :
    ∃ rho : NontrivialZetaZero, rho.val.re < 1 / 2 := by
  obtain ⟨z, hmult, hoff⟩ :=
    not_RH_iff_exists_xiZero_off_critical_line.mp hnot
  have hxi : xiFunction z = 0 := (xiZeroMultiplicity_pos_iff z).mp hmult
  by_cases hleft : z.re < 1 / 2
  · exact ⟨xiZeroEquivNontrivialZetaZero ⟨z, hxi⟩, hleft⟩
  · have hright : 1 / 2 < z.re := by
      have hle : 1 / 2 ≤ z.re := le_of_not_gt hleft
      exact lt_of_le_of_ne hle (Ne.symm hoff)
    let w : XiZeroSubtype := ⟨1 - z, by
      rw [xiFunction_one_sub]
      exact hxi⟩
    refine ⟨xiZeroEquivNontrivialZetaZero w, ?_⟩
    change (1 - z).re < 1 / 2
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- Therefore failure of RH produces a nontrivial zero whose Li base has
modulus strictly greater than one. -/
theorem not_RH_exists_li_base_gt_one
    (hnot : ¬ RiemannHypothesis) :
    ∃ rho : NontrivialZetaZero, 1 < ‖1 - 1 / rho.val‖ := by
  obtain ⟨rho, hleft⟩ := not_RH_exists_left_nontrivial_zero hnot
  refine ⟨rho, one_lt_norm_one_sub_inv rho.val ?_ hleft⟩
  intro hrho
  have hpos := rho.re_pos
  rw [hrho] at hpos
  simp at hpos

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
