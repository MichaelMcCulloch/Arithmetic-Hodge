import ArithmeticHodge.Analysis.MultiplicativeWeil
import ArithmeticHodge.Analysis.ZetaProduct

set_option autoImplicit false

open Complex Filter Topology

namespace ArithmeticHodge.Analysis

private theorem nontrivialZetaZero_countable : Countable NontrivialZetaZero := by
  let Z := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
  letI : Countable Z := (show Set.Countable Z from zetaZeros_countable).to_subtype
  let ι : NontrivialZetaZero → Z := fun ρ =>
    ⟨ρ.val, ρ.is_zero, ρ.re_pos, ρ.re_lt_one⟩
  apply Function.Injective.countable (f := ι)
  intro ρ σ h
  have hv : ρ.val = σ.val := congr_arg Subtype.val h
  cases ρ
  cases σ
  simp_all

private theorem xi_nonzero_zero_set_infinite :
    Set.Infinite {z : ℂ | xiFunction z = 0 ∧ z ≠ 0} := by
  obtain ⟨m, A, B, zeros, _hzeros_ne, hzeros, hsumm, hfactorization⟩ :=
    xi_hadamard_product
  have hm : m = 0 := by
    by_contra hm
    have h0 := hfactorization 0
    rw [xiFunction_zero_val] at h0
    simp [zero_pow hm] at h0
  apply xi_zero_set_infinite_of_genus_one_factorization A B zeros
  · exact fun n _ => hzeros n
  · exact hsumm
  · intro z
    simpa [hm] using hfactorization z

private theorem nontrivialZetaZero_infinite : Infinite NontrivialZetaZero := by
  let X := {z : ℂ | xiFunction z = 0 ∧ z ≠ 0}
  letI : Infinite X :=
    (show Set.Infinite X from xi_nonzero_zero_set_infinite).to_subtype
  let ι : X → NontrivialZetaZero := fun z =>
    let hre := xiFunction_zero_re z.property.1
    ⟨z, (xiFunction_zero_iff hre.1 hre.2).mp z.property.1, hre.1, hre.2⟩
  apply Infinite.of_injective ι
  intro ρ σ h
  apply Subtype.ext
  exact congr_arg NontrivialZetaZero.val h

private theorem riemannZeta_analyticOrderNatAt_pos (ρ : NontrivialZetaZero) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have hρ_ne_one : ρ.val ≠ 1 := by
    intro h
    have := ρ.re_lt_one
    rw [h] at this
    norm_num at this
  have hana : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
    exact hdiff.analyticOnNhd hopen
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank
      (by rw [rank_real_complex]; exact Nat.one_lt_ofNat) 1
  have htwo_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have htwo_order : analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    have hz : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr htwo_ne)
    rw [hz]
    exact ENat.zero_ne_top
  have hρ_order : analyticOrderAt riemannZeta ρ.val ≠ ⊤ :=
    hana.analyticOrderAt_ne_top_of_isPreconnected hconn.isPreconnected
      (by norm_num) hρ_ne_one htwo_order
  rw [Nat.pos_iff_ne_zero, Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
  exact ⟨analyticOrderAt_ne_zero.mpr
      ⟨hana ρ.val hρ_ne_one, ρ.is_zero⟩,
    hρ_order⟩

private noncomputable def exactMultiplicityFiberEquiv
    {α : Type*} (m : α → ℕ)
    (e : ℕ ≃ {p : α × ℕ // p.2 < m p.1}) (a : α) :
    {n : ℕ // (e n).val.1 = a} ≃ Fin (m a) where
  toFun n := ⟨(e n).val.2, by
    simpa only [n.property] using (e n).property⟩
  invFun i := ⟨e.symm ⟨(a, i), i.isLt⟩, by simp⟩
  left_inv n := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext n.property.symm rfl
  right_inv i := by
    apply Fin.ext
    simp

private theorem exists_exactMultiplicityEnumeration
    {α : Type*} [Countable α] [Infinite α]
    (m : α → ℕ) (hm : ∀ a, 0 < m a) :
    ∃ zero : ℕ → α,
      (∀ a, ∃ n, zero n = a) ∧
      (∀ a, Set.Finite {n : ℕ | zero n = a}) ∧
      (∀ a, Nat.card {n : ℕ // zero n = a} = m a) := by
  let P := {p : α × ℕ // p.2 < m p.1}
  letI : Countable P := inferInstance
  letI : Infinite P := by
    apply Infinite.of_injective (fun a : α => (⟨(a, 0), hm a⟩ : P))
    intro a b h
    exact congr_arg (fun p : P => p.val.1) h
  obtain ⟨e : ℕ ≃ P⟩ :=
    nonempty_equiv_of_countable (α := ℕ) (β := P)
  let zero : ℕ → α := fun n => (e n).val.1
  refine ⟨zero, ?_, ?_, ?_⟩
  · intro a
    exact ⟨e.symm ⟨(a, 0), hm a⟩, by simp [zero]⟩
  · intro a
    let fiberEquiv : {n : ℕ // zero n = a} ≃ Fin (m a) :=
      exactMultiplicityFiberEquiv m e a
    exact Set.finite_def.mpr
      ⟨Fintype.ofEquiv (Fin (m a)) fiberEquiv.symm⟩
  · intro a
    simpa only [zero, Nat.card_fin] using
      Nat.card_congr (exactMultiplicityFiberEquiv m e a)

namespace MultiplicativeWeil

noncomputable section

theorem nonempty_zetaZeroEnumeration : Nonempty ZetaZeroEnumeration := by
  letI : Countable NontrivialZetaZero := nontrivialZetaZero_countable
  letI : Infinite NontrivialZetaZero := nontrivialZetaZero_infinite
  obtain ⟨zero, hexhaustive, hfiberFinite, hfiberCard⟩ :=
    exists_exactMultiplicityEnumeration
      (fun ρ : NontrivialZetaZero =>
        analyticOrderNatAt riemannZeta ρ.val)
      riemannZeta_analyticOrderNatAt_pos
  exact ⟨{
    zero := zero
    exhaustive := hexhaustive
    fiberFinite := hfiberFinite
    fiberCard := hfiberCard
  }⟩

#print axioms nonempty_zetaZeroEnumeration

end

end MultiplicativeWeil

end ArithmeticHodge.Analysis
