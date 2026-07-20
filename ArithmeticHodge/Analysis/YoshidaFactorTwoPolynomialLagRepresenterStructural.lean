import ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural

noncomputable section

open YoshidaFactorTwoContinuousLagRepresenterStructural

/-!
# Polynomial realization of the continuous lag representer

For polynomial lag kernel `q` and polynomial profile `p`, the symmetric
continuous-lag representer is itself a polynomial.  The construction below
is coefficientwise and keeps the sharp total-degree estimate

`deg K(q,p) <= deg q + deg p + 1`.

This is the reusable algebraic bridge needed by the degree-eighteen `P51`
main row: degrees eighteen and fifty-one give degree at most seventy before
using parity.
-/

/-- Polynomial representing the right integral for the monomial pair
`q(t) = t^m`, `p(y) = y^n`. -/
def factorTwoPolynomialLagRightMonomial (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) /
        (k + n + 1 : ℕ)) •
      (X ^ (m - k) - X ^ (m + n + 1))

/-- Polynomial representing the left integral for the monomial pair
`q(t) = t^m`, `p(y) = y^n`. -/
def factorTwoPolynomialLagLeftMonomial (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) /
        (m - k + n + 1 : ℕ)) •
      (X ^ (m + n + 1) -
        (-1 : ℝ) ^ (m - k + n + 1) • X ^ k)

/-- Polynomial representing the symmetric lag integral for two monomials. -/
def factorTwoPolynomialLagMonomial (m n : ℕ) : ℝ[X] :=
  factorTwoPolynomialLagRightMonomial m n +
    factorTwoPolynomialLagLeftMonomial m n

theorem natDegree_factorTwoPolynomialLagRightMonomial_le (m n : ℕ) :
    (factorTwoPolynomialLagRightMonomial m n).natDegree ≤ m + n + 1 := by
  unfold factorTwoPolynomialLagRightMonomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_sub_le _ _).trans
  simp only [Polynomial.natDegree_X_pow]
  have hkm : k ≤ m := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  omega

theorem natDegree_factorTwoPolynomialLagLeftMonomial_le (m n : ℕ) :
    (factorTwoPolynomialLagLeftMonomial m n).natDegree ≤ m + n + 1 := by
  unfold factorTwoPolynomialLagLeftMonomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp only [Polynomial.natDegree_X_pow]
    exact le_rfl
  · apply (Polynomial.natDegree_smul_le _ _).trans
    simp only [Polynomial.natDegree_X_pow]
    have hkm : k ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    omega

theorem natDegree_factorTwoPolynomialLagMonomial_le (m n : ℕ) :
    (factorTwoPolynomialLagMonomial m n).natDegree ≤ m + n + 1 := by
  unfold factorTwoPolynomialLagMonomial
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le (natDegree_factorTwoPolynomialLagRightMonomial_le m n)
    (natDegree_factorTwoPolynomialLagLeftMonomial_le m n)

theorem eval_factorTwoPolynomialLagRightMonomial (m n : ℕ) (x : ℝ) :
    (factorTwoPolynomialLagRightMonomial m n).eval x =
      ∫ y : ℝ in x..1,
        (X ^ m).eval (y - x) * (X ^ n).eval y := by
  rw [show (fun y : ℝ ↦
      (X ^ m).eval (y - x) * (X ^ n).eval y) =
      fun y ↦ ∑ k ∈ Finset.range (m + 1),
        (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) *
          x ^ (m - k)) * y ^ (k + n) by
    funext y
    simp only [eval_pow, eval_X, sub_pow, Finset.sum_mul, pow_add]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · unfold factorTwoPolynomialLagRightMonomial
    simp only [eval_finset_sum, eval_smul, eval_sub, eval_pow, eval_X,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have hkm : k ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    have hxpow : x ^ (m - k) * x ^ (k + n + 1) =
        x ^ (m + n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [one_pow, ← hxpow]
    ring
  · intro k hk
    exact (by fun_prop : Continuous (fun y : ℝ ↦
      (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) *
        x ^ (m - k)) * y ^ (k + n))).intervalIntegrable _ _

theorem eval_factorTwoPolynomialLagLeftMonomial (m n : ℕ) (x : ℝ) :
    (factorTwoPolynomialLagLeftMonomial m n).eval x =
      ∫ y : ℝ in -1..x,
        (X ^ m).eval (x - y) * (X ^ n).eval y := by
  rw [show (fun y : ℝ ↦
      (X ^ m).eval (x - y) * (X ^ n).eval y) =
      fun y ↦ ∑ k ∈ Finset.range (m + 1),
        (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) *
          x ^ k) * y ^ (m - k + n) by
    funext y
    simp only [eval_pow, eval_X, sub_pow, Finset.sum_mul, pow_add]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · unfold factorTwoPolynomialLagLeftMonomial
    simp only [eval_finset_sum, eval_smul, eval_sub, eval_pow, eval_X,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have hkm : k ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    have hxpow : x ^ k * x ^ (m - k + n + 1) =
        x ^ (m + n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hxpow]
    ring
  · intro k hk
    exact (by fun_prop : Continuous (fun y : ℝ ↦
      (((m.choose k : ℕ) : ℝ) * (-1 : ℝ) ^ (k + m) * x ^ k) *
        y ^ (m - k + n))).intervalIntegrable _ _

theorem eval_factorTwoPolynomialLagMonomial (m n : ℕ) (x : ℝ) :
    (factorTwoPolynomialLagMonomial m n).eval x =
      factorTwoContinuousLagK (fun t ↦ (X ^ m).eval t)
        (fun y ↦ (X ^ n).eval y) x := by
  unfold factorTwoPolynomialLagMonomial factorTwoContinuousLagK
    factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  rw [eval_add, eval_factorTwoPolynomialLagRightMonomial,
    eval_factorTwoPolynomialLagLeftMonomial]

/-- Coefficientwise polynomial realization of the symmetric continuous-lag
representer. -/
def factorTwoPolynomialLagK (q p : ℝ[X]) : ℝ[X] :=
  q.sum fun m a ↦ p.sum fun n b ↦
    (a * b) • factorTwoPolynomialLagMonomial m n

/-- Sharp total-degree bound for the polynomial lag representer. -/
theorem natDegree_factorTwoPolynomialLagK_le (q p : ℝ[X]) :
    (factorTwoPolynomialLagK q p).natDegree ≤
      q.natDegree + p.natDegree + 1 := by
  unfold factorTwoPolynomialLagK Polynomial.sum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (natDegree_factorTwoPolynomialLagMonomial_le m n).trans
  have hmq : m ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp m hm
  have hnp : n ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
  omega

private theorem eval_mul_eval_eq_double_sum
    (q p : ℝ[X]) (u v : ℝ) :
    q.eval u * p.eval v =
      ∑ m ∈ q.support, ∑ n ∈ p.support,
        q.coeff m * p.coeff n *
          ((X ^ m).eval u * (X ^ n).eval v) := by
  rw [eval_eq_sum, eval_eq_sum]
  simp only [Polynomial.sum_def]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [eval_pow, eval_X]
  ring

theorem eval_factorTwoPolynomialLagK (q p : ℝ[X]) (x : ℝ) :
    (factorTwoPolynomialLagK q p).eval x =
      factorTwoContinuousLagK q.eval p.eval x := by
  have hdouble (F G : ℕ → ℕ → ℝ) :
      (∑ m ∈ q.support, ∑ n ∈ p.support, (F m n + G m n)) =
        (∑ m ∈ q.support, ∑ n ∈ p.support, F m n) +
          ∑ m ∈ q.support, ∑ n ∈ p.support, G m n := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_add_distrib]
  have hright :
      (∫ y : ℝ in x..1, q.eval (y - x) * p.eval y) =
        ∑ m ∈ q.support, ∑ n ∈ p.support,
          q.coeff m * p.coeff n *
            (∫ y : ℝ in x..1,
              (X ^ m).eval (y - x) * (X ^ n).eval y) := by
    rw [show (fun y : ℝ ↦ q.eval (y - x) * p.eval y) =
        fun y ↦ ∑ m ∈ q.support, ∑ n ∈ p.support,
          q.coeff m * p.coeff n *
            ((X ^ m).eval (y - x) * (X ^ n).eval y) by
      funext y
      exact eval_mul_eval_eq_double_sum q p (y - x) y]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [intervalIntegral.integral_const_mul]
      · intro n hn
        exact (by fun_prop : Continuous (fun y : ℝ ↦
          q.coeff m * p.coeff n *
            ((X ^ m).eval (y - x) * (X ^ n).eval y))).intervalIntegrable _ _
    · intro m hm
      exact (by fun_prop : Continuous (fun y : ℝ ↦
        ∑ n ∈ p.support, q.coeff m * p.coeff n *
          ((X ^ m).eval (y - x) * (X ^ n).eval y))).intervalIntegrable _ _
  have hleft :
      (∫ y : ℝ in -1..x, q.eval (x - y) * p.eval y) =
        ∑ m ∈ q.support, ∑ n ∈ p.support,
          q.coeff m * p.coeff n *
            (∫ y : ℝ in -1..x,
              (X ^ m).eval (x - y) * (X ^ n).eval y) := by
    rw [show (fun y : ℝ ↦ q.eval (x - y) * p.eval y) =
        fun y ↦ ∑ m ∈ q.support, ∑ n ∈ p.support,
          q.coeff m * p.coeff n *
            ((X ^ m).eval (x - y) * (X ^ n).eval y) by
      funext y
      exact eval_mul_eval_eq_double_sum q p (x - y) y]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [intervalIntegral.integral_const_mul]
      · intro n hn
        exact (by fun_prop : Continuous (fun y : ℝ ↦
          q.coeff m * p.coeff n *
            ((X ^ m).eval (x - y) * (X ^ n).eval y))).intervalIntegrable _ _
    · intro m hm
      exact (by fun_prop : Continuous (fun y : ℝ ↦
        ∑ n ∈ p.support, q.coeff m * p.coeff n *
          ((X ^ m).eval (x - y) * (X ^ n).eval y))).intervalIntegrable _ _
  unfold factorTwoPolynomialLagK factorTwoContinuousLagK
    factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  simp only [Polynomial.sum_def, eval_finset_sum, eval_smul, smul_eq_mul]
  rw [hright, hleft]
  simp_rw [eval_factorTwoPolynomialLagMonomial]
  unfold factorTwoContinuousLagK factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  simp only [sub_eq_add_neg, add_comm]
  simpa only [mul_add] using hdouble
    (fun m n ↦ q.coeff m * p.coeff n *
      ∫ y : ℝ in -1..x, (X ^ m).eval (x - y) * (X ^ n).eval y)
    (fun m n ↦ q.coeff m * p.coeff n *
      ∫ y : ℝ in x..1, (X ^ m).eval (y - x) * (X ^ n).eval y)

/-- Function-level form of the polynomial realization theorem. -/
theorem factorTwoContinuousLagK_polynomial (q p : ℝ[X]) :
    factorTwoContinuousLagK q.eval p.eval =
      (factorTwoPolynomialLagK q p).eval := by
  funext x
  exact (eval_factorTwoPolynomialLagK q p x).symm

/-- Existential packaging useful when the concrete realizing polynomial is
not needed by a caller. -/
theorem exists_polynomial_factorTwoContinuousLagK (q p : ℝ[X]) :
    ∃ r : ℝ[X],
      r.natDegree ≤ q.natDegree + p.natDegree + 1 ∧
        factorTwoContinuousLagK q.eval p.eval = r.eval := by
  exact ⟨factorTwoPolynomialLagK q p,
    natDegree_factorTwoPolynomialLagK_le q p,
    factorTwoContinuousLagK_polynomial q p⟩

private theorem lagRightRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagRightRepresenter q p (-x) =
      -factorTwoContinuousLagLeftRepresenter q p x := by
  unfold factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y + x) * p y)
    (a := (-1 : ℝ)) (b := x)
  have heq : (fun y : ℝ ↦ q (-y + x) * p (-y)) =
      fun y ↦ -(q (x - y) * p y) := by
    funext y
    rw [hp y]
    ring_nf
  rw [heq, intervalIntegral.integral_neg] at h
  calc
    (∫ y : ℝ in -x..1, q (y - -x) * p y) =
        ∫ y : ℝ in -x..1, q (y + x) * p y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      ring_nf
    _ = _ := by simpa only [neg_neg] using h.symm

private theorem lagLeftRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagLeftRepresenter q p (-x) =
      -factorTwoContinuousLagRightRepresenter q p x := by
  unfold factorTwoContinuousLagLeftRepresenter
    factorTwoContinuousLagRightRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y - x) * p y)
    (a := (-1 : ℝ)) (b := -x)
  have heq : (fun y : ℝ ↦ q (-y - x) * p (-y)) =
      fun y ↦ -(q (-x - y) * p y) := by
    funext y
    rw [hp y]
    ring_nf
  rw [heq, intervalIntegral.integral_neg] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_neg] using h'

/-- Symmetric lag convolution preserves odd parity. -/
theorem odd_factorTwoContinuousLagK_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) :
    Function.Odd (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [lagRightRepresenter_neg_of_odd q p hp,
    lagLeftRepresenter_neg_of_odd q p hp]
  ring

/-- The numerical degree instance used by a degree-eighteen lag kernel
acting on a degree-fifty-one profile. -/
theorem exists_polynomial_factorTwoContinuousLagK_degree18_degree51
    (q p : ℝ[X]) (hq : q.natDegree ≤ 18) (hp : p.natDegree ≤ 51) :
    ∃ r : ℝ[X], r.natDegree ≤ 70 ∧
      factorTwoContinuousLagK q.eval p.eval = r.eval := by
  refine ⟨factorTwoPolynomialLagK q p, ?_,
    factorTwoContinuousLagK_polynomial q p⟩
  exact (natDegree_factorTwoPolynomialLagK_le q p).trans (by omega)

private theorem coeff_comp_neg_X (r : ℝ[X]) (n : ℕ) :
    (r.comp (-X)).coeff n = (-1 : ℝ) ^ n * r.coeff n := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial k a =>
      have hneg : (-X : ℝ[X]) ^ k = (-1 : ℝ) ^ k • X ^ k := by
        rw [neg_pow, Polynomial.smul_eq_C_mul]
        norm_cast
      rw [monomial_comp, hneg, Polynomial.smul_eq_C_mul, ← mul_assoc,
        ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
      by_cases hnk : n = k
      · simp [hnk]
        ring
      · rw [if_neg hnk, if_neg (Ne.symm hnk)]
        ring

/-- An odd polynomial whose crude degree bound is even automatically loses
that top even degree. -/
theorem natDegree_le_sixtyNine_of_le_seventy_of_odd
    (r : ℝ[X]) (hdeg : r.natDegree ≤ 70)
    (hodd : Function.Odd r.eval) :
    r.natDegree ≤ 69 := by
  have hpoly : r.comp (-X) = -r := by
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_neg, eval_X]
    exact hodd x
  have hcoeff := congrArg (fun s : ℝ[X] ↦ s.coeff 70) hpoly
  change (r.comp (-X)).coeff 70 = (-r).coeff 70 at hcoeff
  rw [coeff_comp_neg_X, coeff_neg] at hcoeff
  norm_num at hcoeff
  have hzero : r.coeff 70 = 0 := by linarith
  simpa using Polynomial.natDegree_le_pred hdeg hzero

/-- Odd degree-fifty-one profiles improve the degree-eighteen convolution
bound from seventy to sixty-nine. -/
theorem exists_polynomial_factorTwoContinuousLagK_degree18_degree51_odd
    (q p : ℝ[X]) (hq : q.natDegree ≤ 18) (hp : p.natDegree ≤ 51)
    (hpodd : Function.Odd p.eval) :
    ∃ r : ℝ[X], r.natDegree ≤ 69 ∧
      factorTwoContinuousLagK q.eval p.eval = r.eval := by
  let r := factorTwoPolynomialLagK q p
  have hr70 : r.natDegree ≤ 70 :=
    (natDegree_factorTwoPolynomialLagK_le q p).trans (by omega)
  have hrepr : factorTwoContinuousLagK q.eval p.eval = r.eval :=
    factorTwoContinuousLagK_polynomial q p
  have hrodd : Function.Odd r.eval := by
    rw [← hrepr]
    exact odd_factorTwoContinuousLagK_of_odd q.eval p.eval hpodd
  exact ⟨r, natDegree_le_sixtyNine_of_le_seventy_of_odd r hr70 hrodd,
    hrepr⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural
