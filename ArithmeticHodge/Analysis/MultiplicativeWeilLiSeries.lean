import ArithmeticHodge.Analysis.MultiplicativeWeilLiAlgebra
import ArithmeticHodge.Analysis.XiZetaZeroEquiv
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Reflection of a nontrivial zeta zero through the functional equation. -/
def oneSubNontrivialZetaZero
    (rho : NontrivialZetaZero) : NontrivialZetaZero :=
  xiZeroEquivNontrivialZetaZero
    ⟨1 - rho.val, by
      rw [xiFunction_one_sub]
      exact (xiFunction_zero_iff rho.re_pos rho.re_lt_one).mpr rho.is_zero⟩

@[simp]
theorem oneSubNontrivialZetaZero_val
    (rho : NontrivialZetaZero) :
    (oneSubNontrivialZetaZero rho).val = 1 - rho.val := rfl

private theorem nontrivialZetaZero_ext_val_scratch
    {rho sigma : NontrivialZetaZero} (h : rho.val = sigma.val) :
    rho = sigma := by
  cases rho with
  | mk rho hrho hpos hlt =>
      cases sigma with
      | mk sigma hsigma hpos' hlt' =>
          dsimp only at h
          subst sigma
          rfl

@[simp]
theorem oneSubNontrivialZetaZero_involutive
    (rho : NontrivialZetaZero) :
    oneSubNontrivialZetaZero
      (oneSubNontrivialZetaZero rho) = rho := by
  apply nontrivialZetaZero_ext_val_scratch
  simp

/-- `rho |-> 1-rho` as an equivalence of the nontrivial-zero subtype. -/
def oneSubNontrivialZetaZeroEquiv :
    NontrivialZetaZero ≃ NontrivialZetaZero where
  toFun := oneSubNontrivialZetaZero
  invFun := oneSubNontrivialZetaZero
  left_inv := oneSubNontrivialZetaZero_involutive
  right_inv := oneSubNontrivialZetaZero_involutive

@[simp]
theorem oneSubNontrivialZetaZero_eq_iff
    (rho sigma : NontrivialZetaZero) :
    oneSubNontrivialZetaZero rho = sigma ↔
      rho = oneSubNontrivialZetaZero sigma := by
  constructor
  · intro h
    rw [← h]
    exact (oneSubNontrivialZetaZero_involutive rho).symm
  · intro h
    rw [h]
    exact oneSubNontrivialZetaZero_involutive sigma

/-- Reflection preserves analytic zeta multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_oneSub
    (rho : NontrivialZetaZero) :
    analyticOrderNatAt riemannZeta
        (oneSubNontrivialZetaZero rho).val =
      analyticOrderNatAt riemannZeta rho.val := by
  rw [← xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta,
    ← xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta,
    oneSubNontrivialZetaZero_val,
    xiZeroMultiplicity_one_sub]

/-- Reflect an exact-multiplicity enumeration termwise.  Multiplicity
preservation is what makes this again a valid enumeration. -/
def ZetaZeroEnumeration.oneSub
    (zeros : ZetaZeroEnumeration) : ZetaZeroEnumeration where
  zero k := oneSubNontrivialZetaZero (zeros.zero k)
  exhaustive rho := by
    obtain ⟨k, hk⟩ :=
      zeros.exhaustive (oneSubNontrivialZetaZero rho)
    refine ⟨k, ?_⟩
    simp [hk]
  fiberFinite rho := by
    have hset :
        {k : ℕ | oneSubNontrivialZetaZero (zeros.zero k) = rho} =
          {k : ℕ | zeros.zero k = oneSubNontrivialZetaZero rho} := by
      ext k
      exact oneSubNontrivialZetaZero_eq_iff (zeros.zero k) rho
    rw [hset]
    exact zeros.fiberFinite (oneSubNontrivialZetaZero rho)
  fiberCard rho := by
    have hset :
        {k : ℕ | oneSubNontrivialZetaZero (zeros.zero k) = rho} =
          {k : ℕ | zeros.zero k = oneSubNontrivialZetaZero rho} := by
      ext k
      exact oneSubNontrivialZetaZero_eq_iff (zeros.zero k) rho
    calc
      Nat.card {k : ℕ //
          oneSubNontrivialZetaZero (zeros.zero k) = rho} =
          Nat.card {k : ℕ //
            zeros.zero k = oneSubNontrivialZetaZero rho} :=
        Nat.card_congr (Equiv.setCongr hset)
      _ = analyticOrderNatAt riemannZeta
          (oneSubNontrivialZetaZero rho).val :=
        zeros.fiberCard (oneSubNontrivialZetaZero rho)
      _ = analyticOrderNatAt riemannZeta rho.val :=
        analyticOrderNatAt_riemannZeta_oneSub rho

/-- Inverse-square summability transfers to the reflected zeros without
choosing a permutation of the enumeration. -/
theorem ZetaZeroEnumeration.summable_one_sub_inv_norm_sq_scratch
    (zeros : ZetaZeroEnumeration) :
    Summable (fun k : ℕ ↦
      ‖1 - (zeros.zero k).val‖⁻¹ ^ (2 : ℝ)) := by
  simpa only [ZetaZeroEnumeration.oneSub,
    oneSubNontrivialZetaZero_val] using
      (zeros.oneSub.summable_inv_norm_sq)

private theorem summable_pow_succ_of_summable_nonneg_scratch
    (a : ℕ → ℝ) (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k)
    (m : ℕ) :
    Summable (fun k ↦ (a k) ^ (m + 1)) := by
  let S : ℝ := ∑' k, a k
  have hS0 : 0 ≤ S := tsum_nonneg ha0
  have hakS (k : ℕ) : a k ≤ S :=
    ha.le_tsum k (fun j _hjk ↦ ha0 j)
  apply (ha.mul_left (S ^ m)).of_nonneg_of_le
  · intro k
    exact pow_nonneg (ha0 k) _
  · intro k
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (ha0 k) (hakS k) m) (ha0 k)

theorem liFunction_eq_finset_sum_scratch (n : ℕ) (s : ℂ) :
    liFunction n s =
      ∑ m ∈ Finset.range n,
        (Nat.choose n (m + 1) : ℂ) * (-1 : ℂ) ^ m *
          (1 / s) ^ (m + 1) := by
  have h := add_pow (-(1 / s)) 1 n
  rw [Finset.sum_range_succ'] at h
  simp only [one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_zero] at h
  rw [liFunction]
  calc
    1 - (1 - 1 / s) ^ n =
        -(∑ m ∈ Finset.range n,
          ((-(1 / s)) ^ (m + 1) *
            (Nat.choose n (m + 1) : ℂ))) := by
      rw [show (1 - 1 / s) ^ n = (-(1 / s) + 1) ^ n by ring]
      rw [h]
      ring
    _ = ∑ m ∈ Finset.range n,
        -((-(1 / s)) ^ (m + 1) *
          (Nat.choose n (m + 1) : ℂ)) := by
      rw [Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [neg_pow, pow_succ]
      ring

/-- Fixed-index Li functions are square-summable along every complex sequence
whose inverse squared norms are summable. -/
theorem summable_norm_liFunction_sq_of_inv_norm_sq_scratch
    (z : ℕ → ℂ)
    (hinv : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℝ)))
    (n : ℕ) :
    Summable (fun k ↦ ‖liFunction n (z k)‖ ^ 2) := by
  let a : ℕ → ℝ := fun k ↦ ‖z k‖⁻¹ ^ 2
  have ha : Summable a := by
    simpa only [a, Real.rpow_two] using hinv
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by
    dsimp only [a]
    positivity
  let b : ℕ → ℕ → ℝ := fun m k ↦
    (Nat.choose n (m + 1) : ℝ) * ‖z k‖⁻¹ ^ (m + 1)
  have hb0 (m k : ℕ) : 0 ≤ b m k := by
    dsimp only [b]
    positivity
  have hterm (m : ℕ) : Summable (fun k ↦ (b m k) ^ 2) := by
    have hp := summable_pow_succ_of_summable_nonneg_scratch a ha ha0 m
    have hc := hp.mul_left ((Nat.choose n (m + 1) : ℝ) ^ 2)
    apply hc.congr
    intro k
    dsimp only [a, b]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    omega
  have hfinite : Summable (fun k ↦
      ∑ m ∈ Finset.range n, (b m k) ^ 2) := by
    exact summable_sum fun m _hm ↦ hterm m
  have hmajor : Summable (fun k ↦
      (n : ℝ) * ∑ m ∈ Finset.range n, (b m k) ^ 2) :=
    hfinite.mul_left (n : ℝ)
  apply hmajor.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    have hnorm : ‖liFunction n (z k)‖ ≤
        ∑ m ∈ Finset.range n, b m k := by
      rw [liFunction_eq_finset_sum_scratch]
      apply norm_sum_le_of_le
      intro m _hm
      dsimp only [b]
      rw [norm_mul, norm_mul, norm_pow, norm_pow,
        Complex.norm_natCast]
      norm_num [norm_div]
    have hsum0 : 0 ≤ ∑ m ∈ Finset.range n, b m k := by
      exact Finset.sum_nonneg fun m _hm ↦ hb0 m k
    calc
      ‖liFunction n (z k)‖ ^ 2 ≤
          (∑ m ∈ Finset.range n, b m k) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hsum0).2 hnorm
      _ ≤ ((Finset.range n).card : ℝ) *
          ∑ m ∈ Finset.range n, (b m k) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m ∈ Finset.range n, (b m k) ^ 2 := by
        rw [Finset.card_range]

/-- The direct Li factors are square-summable over a zero enumeration. -/
theorem ZetaZeroEnumeration.summable_norm_liFunction_sq_scratch
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    Summable (fun k ↦ ‖liFunction n (zeros.zero k).val‖ ^ 2) := by
  exact summable_norm_liFunction_sq_of_inv_norm_sq_scratch
    (fun k ↦ (zeros.zero k).val) zeros.summable_inv_norm_sq n

/-- The reflected Li factors are square-summable over the same enumeration. -/
theorem ZetaZeroEnumeration.summable_norm_liFunction_one_sub_sq_scratch
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    Summable (fun k ↦
      ‖liFunction n (1 - (zeros.zero k).val)‖ ^ 2) := by
  exact summable_norm_liFunction_sq_of_inv_norm_sq_scratch
    (fun k ↦ 1 - (zeros.zero k).val)
    zeros.summable_one_sub_inv_norm_sq_scratch n

/-- Fixed-index products of the direct and reflected Li factors are
absolutely summable. -/
theorem ZetaZeroEnumeration.liFunction_product_summable_scratch
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    Summable (fun k : ℕ ↦
      liFunction n (zeros.zero k).val *
        liFunction n (1 - (zeros.zero k).val)) := by
  have hdirect := zeros.summable_norm_liFunction_sq_scratch n
  have hreflected := zeros.summable_norm_liFunction_one_sub_sq_scratch n
  apply (hdirect.add hreflected).of_norm_bounded
  intro k
  rw [norm_mul]
  have hA : 0 ≤ ‖liFunction n (zeros.zero k).val‖ := norm_nonneg _
  have hB : 0 ≤ ‖liFunction n (1 - (zeros.zero k).val)‖ := norm_nonneg _
  nlinarith [two_mul_le_add_sq
    ‖liFunction n (zeros.zero k).val‖
    ‖liFunction n (1 - (zeros.zero k).val)‖]

private theorem nontrivialZetaZero_ne_zero_scratch
    (rho : NontrivialZetaZero) : rho.val ≠ 0 := by
  intro h
  have hpos := rho.re_pos
  rw [h] at hpos
  norm_num at hpos

private theorem nontrivialZetaZero_ne_one_scratch
    (rho : NontrivialZetaZero) : rho.val ≠ 1 := by
  intro h
  have hlt := rho.re_lt_one
  rw [h] at hlt
  norm_num at hlt

/-- Fixed-index Bombieri--Li paired terms are absolutely summable
over any exact-multiplicity zeta-zero enumeration. -/
theorem ZetaZeroEnumeration.liFunction_paired_summable_scratch
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    Summable (fun k : ℕ ↦
      liFunction n (zeros.zero k).val +
        liFunction n (1 - (zeros.zero k).val)) := by
  apply (zeros.liFunction_product_summable_scratch n).congr
  intro k
  exact liFunction_mul_one_sub n (zeros.zero k).val
    (nontrivialZetaZero_ne_zero_scratch (zeros.zero k))
    (nontrivialZetaZero_ne_one_scratch (zeros.zero k))

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

