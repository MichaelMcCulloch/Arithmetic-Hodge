import ArithmeticHodge.Analysis.MultiplicativeWeilZeros

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private abbrev ZetaZeroFiber
    (zeros : ZetaZeroEnumeration) (rho : NontrivialZetaZero) :=
  {n : ℕ // zeros.zero n = rho}

private theorem ZetaZeroEnumeration.fiber_nonempty
    (zeros : ZetaZeroEnumeration) (rho : NontrivialZetaZero) :
    Nonempty (ZetaZeroFiber zeros rho) := by
  obtain ⟨n, hn⟩ := zeros.exhaustive rho
  exact ⟨⟨n, hn⟩⟩

private theorem ZetaZeroEnumeration.sigmaFiber_summable
    (zeros : ZetaZeroEnumeration) (G : NontrivialZetaZero → ℂ)
    (hG : Summable (fun n : ℕ ↦ G (zeros.zero n))) :
    Summable (fun p : Σ rho : NontrivialZetaZero, ZetaZeroFiber zeros rho ↦
      G p.1) := by
  let e : ℕ ≃ Σ rho : NontrivialZetaZero, ZetaZeroFiber zeros rho :=
    (Equiv.sigmaFiberEquiv zeros.zero).symm
  apply e.summable_iff.mp
  simpa only [e, Function.comp_apply, Equiv.sigmaFiberEquiv] using hG

private theorem ZetaZeroEnumeration.tsum_fiber_eq_multiplicity
    (zeros : ZetaZeroEnumeration) (G : NontrivialZetaZero → ℂ)
    (rho : NontrivialZetaZero) :
    ∑' _n : ZetaZeroFiber zeros rho, G rho =
      (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho := by
  letI : Fintype (ZetaZeroFiber zeros rho) :=
    (zeros.fiberFinite rho).fintype
  letI : Nonempty (ZetaZeroFiber zeros rho) := zeros.fiber_nonempty rho
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_eq_nat_card, zeros.fiberCard rho]

private theorem ZetaZeroEnumeration.fiberwise_sum_data
    (zeros : ZetaZeroEnumeration) (G : NontrivialZetaZero → ℂ)
    (hG : Summable (fun n : ℕ ↦ G (zeros.zero n))) :
    Summable (fun rho : NontrivialZetaZero ↦
        (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho) ∧
      ∑' n : ℕ, G (zeros.zero n) =
        ∑' rho : NontrivialZetaZero,
          (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho := by
  have hsigma := zeros.sigmaFiber_summable G hG
  have houter : Summable (fun rho : NontrivialZetaZero ↦
      ∑' _n : ZetaZeroFiber zeros rho, G rho) := by
    simpa only using hsigma.sigma
  have hfiber (rho : NontrivialZetaZero) :
      (∑' _n : ZetaZeroFiber zeros rho, G rho) =
        (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho :=
    zeros.tsum_fiber_eq_multiplicity G rho
  have hweighted : Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho) :=
    houter.congr hfiber
  refine ⟨hweighted, ?_⟩
  let e : ℕ ≃ Σ rho : NontrivialZetaZero, ZetaZeroFiber zeros rho :=
    (Equiv.sigmaFiberEquiv zeros.zero).symm
  calc
    ∑' n : ℕ, G (zeros.zero n) =
        ∑' p : Σ rho : NontrivialZetaZero, ZetaZeroFiber zeros rho, G p.1 := by
      simpa only [e, Equiv.sigmaFiberEquiv] using
        (e.tsum_eq (fun p : Σ rho : NontrivialZetaZero,
          ZetaZeroFiber zeros rho ↦ G p.1))
    _ = ∑' rho : NontrivialZetaZero,
          ∑' _n : ZetaZeroFiber zeros rho, G rho := by
      simpa only using hsigma.tsum_sigma
    _ = ∑' rho : NontrivialZetaZero,
          (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho := by
      apply tsum_congr
      exact hfiber

theorem ZetaZeroEnumeration.distinct_multiplicity_summable
    (zeros : ZetaZeroEnumeration) (G : NontrivialZetaZero → ℂ)
    (hG : Summable (fun n : ℕ ↦ G (zeros.zero n))) :
    Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho) := by
  exact (zeros.fiberwise_sum_data G hG).1

theorem ZetaZeroEnumeration.tsum_comp_zero_eq_tsum_distinct_multiplicity
    (zeros : ZetaZeroEnumeration) (G : NontrivialZetaZero → ℂ)
    (hG : Summable (fun n : ℕ ↦ G (zeros.zero n))) :
    ∑' n : ℕ, G (zeros.zero n) =
      ∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) * G rho := by
  exact (zeros.fiberwise_sum_data G hG).2

#print axioms ZetaZeroEnumeration.distinct_multiplicity_summable
#print axioms ZetaZeroEnumeration.tsum_comp_zero_eq_tsum_distinct_multiplicity

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
