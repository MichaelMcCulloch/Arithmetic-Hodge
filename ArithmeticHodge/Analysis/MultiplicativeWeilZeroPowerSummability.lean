import ArithmeticHodge.Analysis.MultiplicativeWeilLiSeries

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Exact-multiplicity zero enumerations inherit inverse-power summability at
every exponent strictly larger than the order one of completed zeta. -/
theorem ZetaZeroEnumeration.summable_inv_norm_rpow
    (zeros : ZetaZeroEnumeration) (p : ℝ) (hp : 1 < p) :
    Summable (fun n ↦ ‖(zeros.zero n).val‖⁻¹ ^ p) := by
  let XiZero := {z : ℂ // xiFunction z = 0 ∧ z ≠ 0}
  let toXi : NontrivialZetaZero → XiZero := fun rho ↦
    ⟨rho.val, (xiFunction_zero_iff rho.re_pos rho.re_lt_one).2 rho.is_zero,
      by
        intro hzero
        have hpos := rho.re_pos
        rw [hzero] at hpos
        norm_num at hpos⟩
  have htoXi : Function.Injective toXi := by
    intro rho sigma h
    have hv : rho.val = sigma.val :=
      congrArg (fun z : XiZero ↦ (z : ℂ)) h
    cases rho
    cases sigma
    simp_all
  have hxi : Summable (fun z : XiZero ↦
      (analyticOrderNatAt xiFunction (z : ℂ) : ℝ) *
        ‖(z : ℂ)‖⁻¹ ^ p) := by
    apply EntireFunction.summable_zero_multiplicity_rpow_of_order_lt
      xiFunction differentiable_xiFunction xiFunction_ne_const_zero
    rw [xiFunction_order]
    exact EReal.coe_lt_coe_iff.mpr hp
  have hzeta : Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt riemannZeta rho.val : ℝ) *
        ‖rho.val‖⁻¹ ^ p) := by
    have hcomp := hxi.comp_injective htoXi
    change Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt xiFunction rho.val : ℝ) *
        ‖rho.val‖⁻¹ ^ p) at hcomp
    simpa only [analyticOrderNatAt_xiFunction_eq_riemannZeta] using hcomp
  rw [summable_partition
    (fun n : ℕ ↦ Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    (s := fun rho : NontrivialZetaZero ↦ {n : ℕ | zeros.zero n = rho})]
  constructor
  · intro rho
    exact (zeros.fiberFinite rho).summable
      (fun n : ℕ ↦ ‖(zeros.zero n).val‖⁻¹ ^ p)
  · apply hzeta.congr
    intro rho
    letI : Fintype {n : ℕ | zeros.zero n = rho} :=
      (zeros.fiberFinite rho).fintype
    rw [tsum_fintype]
    have hconst : ∀ n : {n : ℕ | zeros.zero n = rho},
        ‖(zeros.zero n).val‖⁻¹ ^ p = ‖rho.val‖⁻¹ ^ p := by
      intro n
      rw [n.property]
    simp_rw [hconst]
    have hcard : Fintype.card {n : ℕ | zeros.zero n = rho} =
        analyticOrderNatAt riemannZeta rho.val := by
      rw [Fintype.card_eq_nat_card]
      exact zeros.fiberCard rho
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  · intro n
    refine ⟨zeros.zero n, rfl, ?_⟩
    intro rho hrho
    exact hrho.symm

/-- The reflected zero divisor has the same inverse-power summability. -/
theorem ZetaZeroEnumeration.summable_one_sub_inv_norm_rpow
    (zeros : ZetaZeroEnumeration) (p : ℝ) (hp : 1 < p) :
    Summable (fun n ↦ ‖1 - (zeros.zero n).val‖⁻¹ ^ p) := by
  simpa only [ZetaZeroEnumeration.oneSub,
    oneSubNontrivialZetaZero_val] using
      zeros.oneSub.summable_inv_norm_rpow p hp

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

