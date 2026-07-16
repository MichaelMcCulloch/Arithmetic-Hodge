import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

open Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural

open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

noncomputable section

/-!
# Ninth derivatives of the reduced `P6/P7` forward representers

The logarithms occurring here are evaluated only on `[-1,1]`; their
arguments then lie in `[1,2]`.  The quantitative part below is organized
around the exact ninth derivative, whose denominator is `(9-x^2)^9`.
Thus every bound is an exact rational polynomial certificate on a compact
interval, rather than a numerical sampling argument.
-/

/-! ## Explicit centered modes and reduced representers -/

/-- The classical centered Legendre polynomial `P6`, in power basis. -/
def factorTwoForwardCenteredP6 (x : ℝ) : ℝ :=
  (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16

/-- The classical centered Legendre polynomial `P7`, in power basis. -/
def factorTwoForwardCenteredP7 (x : ℝ) : ℝ :=
  (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16

theorem factorTwoForwardCenteredP6_eq_factorTwoCenteredP6 :
    factorTwoForwardCenteredP6 = factorTwoCenteredP6 := by
  funext x
  rw [factorTwoCenteredP6_eq]
  rfl

theorem factorTwoForwardCenteredP7_eq_factorTwoCenteredP7 :
    factorTwoForwardCenteredP7 = factorTwoCenteredP7 := by
  funext x
  rw [factorTwoCenteredP7_eq]
  rfl

/-- Symmetric reduced representer attached to `P6`. -/
def factorTwoForwardKP6 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP6 (x + 2) * Real.log ((3 + x) / 2) +
    factorTwoForwardCenteredP6 (x - 2) * Real.log ((3 - x) / 2)

/-- Symmetric reduced representer attached to `P7`. -/
def factorTwoForwardKP7 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP7 (x + 2) * Real.log ((3 + x) / 2) +
    factorTwoForwardCenteredP7 (x - 2) * Real.log ((3 - x) / 2)

/-- Alternating reduced representer attached to `P6`. -/
def factorTwoForwardLP6 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP6 (x - 2) * Real.log ((3 - x) / 2) -
    factorTwoForwardCenteredP6 (x + 2) * Real.log ((3 + x) / 2)

/-- Alternating reduced representer attached to `P7`. -/
def factorTwoForwardLP7 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP7 (x - 2) * Real.log ((3 - x) / 2) -
    factorTwoForwardCenteredP7 (x + 2) * Real.log ((3 + x) / 2)

private lemma forward_log_arguments_ne_zero
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (3 + x) / 2 ≠ 0 ∧ (3 - x) / 2 ≠ 0 := by
  rcases hx with ⟨hx0, hx1⟩
  constructor <;> norm_num <;> linarith

private lemma contDiffOn_forward_log_plus :
    ContDiffOn ℝ 9 (fun x : ℝ ↦ Real.log ((3 + x) / 2))
      (Icc (-1 : ℝ) 1) := by
  apply ContDiffOn.log (by fun_prop)
  intro x hx
  exact (forward_log_arguments_ne_zero hx).1

private lemma contDiffOn_forward_log_minus :
    ContDiffOn ℝ 9 (fun x : ℝ ↦ Real.log ((3 - x) / 2))
      (Icc (-1 : ℝ) 1) := by
  apply ContDiffOn.log (by fun_prop)
  intro x hx
  exact (forward_log_arguments_ne_zero hx).2

theorem continuousOn_factorTwoForwardKP6 :
    ContinuousOn factorTwoForwardKP6 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP6
  apply ContinuousOn.add
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP6
      fun_prop
    · exact contDiffOn_forward_log_plus.continuousOn
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP6
      fun_prop
    · exact contDiffOn_forward_log_minus.continuousOn

theorem continuousOn_factorTwoForwardKP7 :
    ContinuousOn factorTwoForwardKP7 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP7
  apply ContinuousOn.add
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_plus.continuousOn
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_minus.continuousOn

theorem continuousOn_factorTwoForwardLP6 :
    ContinuousOn factorTwoForwardLP6 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardLP6
  apply ContinuousOn.sub
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_minus.continuousOn
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_plus.continuousOn

theorem continuousOn_factorTwoForwardLP7 :
    ContinuousOn factorTwoForwardLP7 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardLP7
  apply ContinuousOn.sub
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_minus.continuousOn
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_plus.continuousOn

theorem contDiffOn_factorTwoForwardKP6 :
    ContDiffOn ℝ 9 factorTwoForwardKP6 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP6
  apply ContDiffOn.add
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_plus
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_minus

theorem contDiffOn_factorTwoForwardKP7 :
    ContDiffOn ℝ 9 factorTwoForwardKP7 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP7
  apply ContDiffOn.add
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_plus
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_minus

theorem contDiffOn_factorTwoForwardLP6 :
    ContDiffOn ℝ 9 factorTwoForwardLP6 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardLP6
  apply ContDiffOn.sub
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_minus
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP6; fun_prop
    · exact contDiffOn_forward_log_plus

theorem contDiffOn_factorTwoForwardLP7 :
    ContDiffOn ℝ 9 factorTwoForwardLP7 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardLP7
  apply ContDiffOn.sub
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_minus
  · apply ContDiffOn.mul
    · unfold factorTwoForwardCenteredP7; fun_prop
    · exact contDiffOn_forward_log_plus

/-! ## Exact ninth derivative -/

private def forwardP6PlusPolynomial : ℝ[X] :=
  Polynomial.C (231 / 16) * Polynomial.X ^ 6 +
    Polynomial.C (693 / 4) * Polynomial.X ^ 5 +
      Polynomial.C (13545 / 16) * Polynomial.X ^ 4 +
        Polynomial.C (4305 / 2) * Polynomial.X ^ 3 +
          Polynomial.C (47985 / 16) * Polynomial.X ^ 2 +
            Polynomial.C (8673 / 4) * Polynomial.X +
              Polynomial.C (10159 / 16)

private def forwardP6MinusPolynomial : ℝ[X] :=
  Polynomial.C (231 / 16) * Polynomial.X ^ 6 -
    Polynomial.C (693 / 4) * Polynomial.X ^ 5 +
      Polynomial.C (13545 / 16) * Polynomial.X ^ 4 -
        Polynomial.C (4305 / 2) * Polynomial.X ^ 3 +
          Polynomial.C (47985 / 16) * Polynomial.X ^ 2 -
            Polynomial.C (8673 / 4) * Polynomial.X +
              Polynomial.C (10159 / 16)

private def forwardP7PlusPolynomial : ℝ[X] :=
  Polynomial.C (429 / 16) * Polynomial.X ^ 7 +
    Polynomial.C (3003 / 8) * Polynomial.X ^ 6 +
      Polynomial.C (35343 / 16) * Polynomial.X ^ 5 +
        Polynomial.C (56595 / 8) * Polynomial.X ^ 4 +
          Polynomial.C (212835 / 16) * Polynomial.X ^ 3 +
            Polynomial.C (117369 / 8) * Polynomial.X ^ 2 +
              Polynomial.C (140497 / 16) * Polynomial.X +
                Polynomial.C (17593 / 8)

private def forwardP7MinusPolynomial : ℝ[X] :=
  Polynomial.C (429 / 16) * Polynomial.X ^ 7 -
    Polynomial.C (3003 / 8) * Polynomial.X ^ 6 +
      Polynomial.C (35343 / 16) * Polynomial.X ^ 5 -
        Polynomial.C (56595 / 8) * Polynomial.X ^ 4 +
          Polynomial.C (212835 / 16) * Polynomial.X ^ 3 -
            Polynomial.C (117369 / 8) * Polynomial.X ^ 2 +
              Polynomial.C (140497 / 16) * Polynomial.X -
                Polynomial.C (17593 / 8)

private lemma forwardP6PlusPolynomial_eval (x : ℝ) :
    forwardP6PlusPolynomial.eval x = factorTwoForwardCenteredP6 (x + 2) := by
  simp [forwardP6PlusPolynomial, factorTwoForwardCenteredP6]
  ring

private lemma forwardP6MinusPolynomial_eval (x : ℝ) :
    forwardP6MinusPolynomial.eval x = factorTwoForwardCenteredP6 (x - 2) := by
  simp [forwardP6MinusPolynomial, factorTwoForwardCenteredP6]
  ring

private lemma forwardP7PlusPolynomial_eval (x : ℝ) :
    forwardP7PlusPolynomial.eval x = factorTwoForwardCenteredP7 (x + 2) := by
  simp [forwardP7PlusPolynomial, factorTwoForwardCenteredP7]
  ring

private lemma forwardP7MinusPolynomial_eval (x : ℝ) :
    forwardP7MinusPolynomial.eval x = factorTwoForwardCenteredP7 (x - 2) := by
  simp [forwardP7MinusPolynomial, factorTwoForwardCenteredP7]
  ring

private theorem iteratedDeriv_polynomial_eval
    (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ P.eval y) x =
      (Polynomial.derivative^[n] P).eval x := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun y : ℝ ↦ P.eval y) =
          fun y ↦ P.derivative.eval y := by
        funext y
        exact P.deriv
      rw [hderiv, ih, Function.iterate_succ_apply]

private theorem iteratedDerivWithin_polynomial_eval
    (n : ℕ) (P : ℝ[X]) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin n (fun y : ℝ ↦ P.eval y) (Icc (-1 : ℝ) 1) x =
      (Polynomial.derivative^[n] P).eval x := by
  have hP : ContDiff ℝ n (fun y : ℝ ↦ P.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      P.contDiff_aeval (𝕜 := ℝ) n
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num)) hP.contDiffAt hx]
  exact iteratedDeriv_polynomial_eval n P x

private theorem iteratedDerivWithin_forwardLogPlus
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin n (fun y : ℝ ↦ Real.log ((3 + y) / 2))
        (Icc (-1 : ℝ) 1) x =
      ((-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ)) /
        (3 + x) ^ n := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          rw [iteratedDerivWithin_succ, iteratedDerivWithin_zero]
          have harg : HasDerivAt (fun y : ℝ ↦ (3 + y) / 2) (1 / 2) x := by
            convert ((hasDerivAt_const x (3 : ℝ)).add (hasDerivAt_id x)).div_const 2
              using 1
            all_goals ring
          have hne : (3 + x) / 2 ≠ 0 := (forward_log_arguments_ne_zero hx).1
          have hlog := (Real.hasDerivAt_log hne).comp x harg
          have hd := hlog.hasDerivWithinAt.derivWithin
            ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hx)
          rw [show derivWithin (fun y : ℝ ↦ Real.log ((3 + y) / 2))
              (Icc (-1 : ℝ) 1) x = ((3 + x) / 2)⁻¹ * (1 / 2) by
            simpa only [Function.comp_apply] using hd]
          norm_num
      | succ k =>
          rw [iteratedDerivWithin_succ]
          have heq : Set.EqOn
              (fun y : ℝ ↦ iteratedDerivWithin (k + 1)
                (fun z : ℝ ↦ Real.log ((3 + z) / 2))
                (Icc (-1 : ℝ) 1) y)
              (fun y : ℝ ↦
                ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) /
                  (3 + y) ^ (k + 1))
              (Icc (-1 : ℝ) 1) := by
            intro y hy
            simpa using ih (by omega) y hy
          rw [derivWithin_congr heq (heq hx)]
          have hbase : HasDerivAt (fun y : ℝ ↦ 3 + y) 1 x := by
            convert (hasDerivAt_const x (3 : ℝ)).add (hasDerivAt_id x) using 1
            all_goals ring
          have hden : 3 + x ≠ 0 := by
            rcases hx with ⟨hx0, hx1⟩
            linarith
          have hquot :=
            (hasDerivAt_const x
              ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ))).div
              (hbase.pow (k + 1)) (pow_ne_zero _ hden)
          have hd := hquot.hasDerivWithinAt.derivWithin
            ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hx)
          simp only [Pi.pow_apply] at hd
          have hshape :
              derivWithin (fun y : ℝ ↦
                ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) /
                  (3 + y) ^ (k + 1)) (Icc (-1 : ℝ) 1) x =
                derivWithin
                  ((fun _ : ℝ ↦ (-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) /
                    (fun y : ℝ ↦ 3 + y) ^ (k + 1))
                  (Icc (-1 : ℝ) 1) x := by
            apply derivWithin_congr
            · intro y hy
              rfl
            · rfl
          rw [hshape, hd]
          simp only [Nat.add_sub_cancel]
          field_simp
          rw [Nat.factorial_succ]
          push_cast
          ring

private theorem iteratedDerivWithin_forwardLogMinus
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin n (fun y : ℝ ↦ Real.log ((3 - y) / 2))
        (Icc (-1 : ℝ) 1) x =
      -(Nat.factorial (n - 1) : ℝ) / (3 - x) ^ n := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          rw [iteratedDerivWithin_succ, iteratedDerivWithin_zero]
          have harg : HasDerivAt (fun y : ℝ ↦ (3 - y) / 2) (-1 / 2) x := by
            convert ((hasDerivAt_const x (3 : ℝ)).sub (hasDerivAt_id x)).div_const 2
              using 1
            all_goals ring
          have hne : (3 - x) / 2 ≠ 0 := (forward_log_arguments_ne_zero hx).2
          have hlog := (Real.hasDerivAt_log hne).comp x harg
          have hd := hlog.hasDerivWithinAt.derivWithin
            ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hx)
          rw [show derivWithin (fun y : ℝ ↦ Real.log ((3 - y) / 2))
              (Icc (-1 : ℝ) 1) x = ((3 - x) / 2)⁻¹ * (-1 / 2) by
            simpa only [Function.comp_apply] using hd]
          norm_num
          field_simp
      | succ k =>
          rw [iteratedDerivWithin_succ]
          have heq : Set.EqOn
              (fun y : ℝ ↦ iteratedDerivWithin (k + 1)
                (fun z : ℝ ↦ Real.log ((3 - z) / 2))
                (Icc (-1 : ℝ) 1) y)
              (fun y : ℝ ↦ -(Nat.factorial k : ℝ) / (3 - y) ^ (k + 1))
              (Icc (-1 : ℝ) 1) := by
            intro y hy
            simpa using ih (by omega) y hy
          rw [derivWithin_congr heq (heq hx)]
          have hbase : HasDerivAt (fun y : ℝ ↦ 3 - y) (-1) x := by
            convert (hasDerivAt_const x (3 : ℝ)).sub (hasDerivAt_id x) using 1
            all_goals ring
          have hden : 3 - x ≠ 0 := by
            rcases hx with ⟨hx0, hx1⟩
            linarith
          have hquot :=
            (hasDerivAt_const x (-(Nat.factorial k : ℝ))).div
              (hbase.pow (k + 1)) (pow_ne_zero _ hden)
          have hd := hquot.hasDerivWithinAt.derivWithin
            ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hx)
          simp only [Pi.pow_apply] at hd
          have hshape :
              derivWithin (fun y : ℝ ↦
                -(Nat.factorial k : ℝ) / (3 - y) ^ (k + 1))
                  (Icc (-1 : ℝ) 1) x =
                derivWithin
                  ((fun _ : ℝ ↦ -(Nat.factorial k : ℝ)) /
                    (fun y : ℝ ↦ 3 - y) ^ (k + 1))
                  (Icc (-1 : ℝ) 1) x := by
            apply derivWithin_congr
            · intro y hy
              rfl
            · rfl
          rw [hshape, hd]
          simp only [Nat.add_sub_cancel]
          field_simp
          rw [Nat.factorial_succ]
          push_cast
          ring

set_option maxHeartbeats 1000000 in
private theorem iteratedDerivWithin_nine_forwardP6PlusLog
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9
        (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y + 2) *
          Real.log ((3 + y) / 2))
        (Icc (-1 : ℝ) 1) x =
      (20790 * x ^ 6 + 436590 * x ^ 5 + 3855600 * x ^ 4 +
        18351900 * x ^ 3 + 49735350 * x ^ 2 + 72914310 * x + 45298260) /
          (3 + x) ^ 9 := by
  rw [show (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y + 2) *
      Real.log ((3 + y) / 2)) =
      (fun y : ℝ ↦ forwardP6PlusPolynomial.eval y) *
        (fun y : ℝ ↦ Real.log ((3 + y) / 2)) by
    funext y
    simp only [Pi.mul_apply]
    rw [forwardP6PlusPolynomial_eval]
  ]
  have hP : ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ forwardP6PlusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x := by
    have hP' : ContDiff ℝ 9
        (fun y : ℝ ↦ forwardP6PlusPolynomial.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        forwardP6PlusPolynomial.contDiff_aeval (𝕜 := ℝ) 9
    exact hP'.contDiffAt.contDiffWithinAt
  rw [iteratedDerivWithin_mul hx (uniqueDiffOn_Icc (by norm_num)) hP
    (contDiffOn_forward_log_plus x hx)]
  norm_num [Finset.sum_range_succ]
  have hP1 : derivWithin (fun y : ℝ ↦ forwardP6PlusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x = forwardP6PlusPolynomial.derivative.eval x := by
    simpa only [iteratedDerivWithin_one] using
      iteratedDerivWithin_polynomial_eval 1 forwardP6PlusPolynomial x hx
  have hlog1 : derivWithin (fun y : ℝ ↦ Real.log ((3 + y) / 2))
      (Icc (-1 : ℝ) 1) x = 1 / (3 + x) := by
    convert iteratedDerivWithin_forwardLogPlus 1 (by norm_num) x hx using 1 <;>
      norm_num [iteratedDerivWithin_one]
  rw [hP1, hlog1,
    iteratedDerivWithin_polynomial_eval 2 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 3 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 4 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 5 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 6 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 7 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 8 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 9 forwardP6PlusPolynomial x hx,
    iteratedDerivWithin_forwardLogPlus 9 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 8 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 7 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 6 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 5 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 4 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 3 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 2 (by norm_num) x hx]
  have hP7 : (Polynomial.derivative^[7] forwardP6PlusPolynomial).eval x = 0 := by
    norm_num [forwardP6PlusPolynomial, Function.iterate_succ_apply]
  have hP8 : (Polynomial.derivative^[8] forwardP6PlusPolynomial).eval x = 0 := by
    norm_num [forwardP6PlusPolynomial, Function.iterate_succ_apply]
  have hP9 : (Polynomial.derivative^[9] forwardP6PlusPolynomial).eval x = 0 := by
    norm_num [forwardP6PlusPolynomial, Function.iterate_succ_apply]
  rw [hP7, hP8, hP9]
  simp only [zero_mul, add_zero]
  have hden : 3 + x ≠ 0 := by
    rcases hx with ⟨hx0, hx1⟩
    linarith
  field_simp [hden]
  norm_num [forwardP6PlusPolynomial, Function.iterate_succ_apply, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
private theorem iteratedDerivWithin_nine_forwardP6MinusLog
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9
        (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y - 2) *
          Real.log ((3 - y) / 2))
        (Icc (-1 : ℝ) 1) x =
      (-20790 * x ^ 6 + 436590 * x ^ 5 - 3855600 * x ^ 4 +
        18351900 * x ^ 3 - 49735350 * x ^ 2 + 72914310 * x - 45298260) /
          (3 - x) ^ 9 := by
  rw [show (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y - 2) *
      Real.log ((3 - y) / 2)) =
      (fun y : ℝ ↦ forwardP6MinusPolynomial.eval y) *
        (fun y : ℝ ↦ Real.log ((3 - y) / 2)) by
    funext y
    simp only [Pi.mul_apply]
    rw [forwardP6MinusPolynomial_eval]
  ]
  have hP : ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ forwardP6MinusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x := by
    have hP' : ContDiff ℝ 9
        (fun y : ℝ ↦ forwardP6MinusPolynomial.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        forwardP6MinusPolynomial.contDiff_aeval (𝕜 := ℝ) 9
    exact hP'.contDiffAt.contDiffWithinAt
  rw [iteratedDerivWithin_mul hx (uniqueDiffOn_Icc (by norm_num)) hP
    (contDiffOn_forward_log_minus x hx)]
  norm_num [Finset.sum_range_succ]
  have hP1 : derivWithin (fun y : ℝ ↦ forwardP6MinusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x = forwardP6MinusPolynomial.derivative.eval x := by
    simpa only [iteratedDerivWithin_one] using
      iteratedDerivWithin_polynomial_eval 1 forwardP6MinusPolynomial x hx
  have hlog1 : derivWithin (fun y : ℝ ↦ Real.log ((3 - y) / 2))
      (Icc (-1 : ℝ) 1) x = -(1 / (3 - x)) := by
    convert iteratedDerivWithin_forwardLogMinus 1 (by norm_num) x hx using 1 <;>
      norm_num [iteratedDerivWithin_one, div_eq_mul_inv]
  rw [hP1, hlog1,
    iteratedDerivWithin_polynomial_eval 2 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 3 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 4 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 5 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 6 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 7 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 8 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 9 forwardP6MinusPolynomial x hx,
    iteratedDerivWithin_forwardLogMinus 9 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 8 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 7 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 6 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 5 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 4 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 3 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 2 (by norm_num) x hx]
  have hP7 : (Polynomial.derivative^[7] forwardP6MinusPolynomial).eval x = 0 := by
    norm_num [forwardP6MinusPolynomial, Function.iterate_succ_apply]
  have hP8 : (Polynomial.derivative^[8] forwardP6MinusPolynomial).eval x = 0 := by
    norm_num [forwardP6MinusPolynomial, Function.iterate_succ_apply]
  have hP9 : (Polynomial.derivative^[9] forwardP6MinusPolynomial).eval x = 0 := by
    norm_num [forwardP6MinusPolynomial, Function.iterate_succ_apply]
  rw [hP7, hP8, hP9]
  simp only [zero_mul, add_zero]
  have hden : 3 - x ≠ 0 := by
    rcases hx with ⟨hx0, hx1⟩
    linarith
  field_simp [hden]
  norm_num [forwardP6MinusPolynomial, Function.iterate_succ_apply, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
private theorem iteratedDerivWithin_nine_forwardP7PlusLog
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9
        (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y + 2) *
          Real.log ((3 + y) / 2))
        (Icc (-1 : ℝ) 1) x =
      (-135135 * x ^ 7 - 3108105 * x ^ 6 - 30779595 * x ^ 5 -
        170218125 * x ^ 4 - 568100925 * x ^ 3 - 1145138715 * x ^ 2 -
          1292093145 * x - 630301455) / (3 + x) ^ 9 := by
  rw [show (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y + 2) *
      Real.log ((3 + y) / 2)) =
      (fun y : ℝ ↦ forwardP7PlusPolynomial.eval y) *
        (fun y : ℝ ↦ Real.log ((3 + y) / 2)) by
    funext y
    simp only [Pi.mul_apply]
    rw [forwardP7PlusPolynomial_eval]
  ]
  have hP : ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ forwardP7PlusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x := by
    have hP' : ContDiff ℝ 9
        (fun y : ℝ ↦ forwardP7PlusPolynomial.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        forwardP7PlusPolynomial.contDiff_aeval (𝕜 := ℝ) 9
    exact hP'.contDiffAt.contDiffWithinAt
  rw [iteratedDerivWithin_mul hx (uniqueDiffOn_Icc (by norm_num)) hP
    (contDiffOn_forward_log_plus x hx)]
  norm_num [Finset.sum_range_succ]
  have hP1 : derivWithin (fun y : ℝ ↦ forwardP7PlusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x = forwardP7PlusPolynomial.derivative.eval x := by
    simpa only [iteratedDerivWithin_one] using
      iteratedDerivWithin_polynomial_eval 1 forwardP7PlusPolynomial x hx
  have hlog1 : derivWithin (fun y : ℝ ↦ Real.log ((3 + y) / 2))
      (Icc (-1 : ℝ) 1) x = 1 / (3 + x) := by
    convert iteratedDerivWithin_forwardLogPlus 1 (by norm_num) x hx using 1 <;>
      norm_num [iteratedDerivWithin_one]
  rw [hP1, hlog1,
    iteratedDerivWithin_polynomial_eval 2 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 3 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 4 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 5 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 6 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 7 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 8 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 9 forwardP7PlusPolynomial x hx,
    iteratedDerivWithin_forwardLogPlus 9 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 8 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 7 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 6 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 5 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 4 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 3 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogPlus 2 (by norm_num) x hx]
  have hP8 : (Polynomial.derivative^[8] forwardP7PlusPolynomial).eval x = 0 := by
    norm_num [forwardP7PlusPolynomial, Function.iterate_succ_apply]
  have hP9 : (Polynomial.derivative^[9] forwardP7PlusPolynomial).eval x = 0 := by
    norm_num [forwardP7PlusPolynomial, Function.iterate_succ_apply]
  rw [hP8, hP9]
  simp only [zero_mul, add_zero]
  have hden : 3 + x ≠ 0 := by
    rcases hx with ⟨hx0, hx1⟩
    linarith
  field_simp [hden]
  norm_num [forwardP7PlusPolynomial, Function.iterate_succ_apply, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
private theorem iteratedDerivWithin_nine_forwardP7MinusLog
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9
        (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y - 2) *
          Real.log ((3 - y) / 2))
        (Icc (-1 : ℝ) 1) x =
      (135135 * x ^ 7 - 3108105 * x ^ 6 + 30779595 * x ^ 5 -
        170218125 * x ^ 4 + 568100925 * x ^ 3 - 1145138715 * x ^ 2 +
          1292093145 * x - 630301455) / (3 - x) ^ 9 := by
  rw [show (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y - 2) *
      Real.log ((3 - y) / 2)) =
      (fun y : ℝ ↦ forwardP7MinusPolynomial.eval y) *
        (fun y : ℝ ↦ Real.log ((3 - y) / 2)) by
    funext y
    simp only [Pi.mul_apply]
    rw [forwardP7MinusPolynomial_eval]
  ]
  have hP : ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ forwardP7MinusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x := by
    have hP' : ContDiff ℝ 9
        (fun y : ℝ ↦ forwardP7MinusPolynomial.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        forwardP7MinusPolynomial.contDiff_aeval (𝕜 := ℝ) 9
    exact hP'.contDiffAt.contDiffWithinAt
  rw [iteratedDerivWithin_mul hx (uniqueDiffOn_Icc (by norm_num)) hP
    (contDiffOn_forward_log_minus x hx)]
  norm_num [Finset.sum_range_succ]
  have hP1 : derivWithin (fun y : ℝ ↦ forwardP7MinusPolynomial.eval y)
      (Icc (-1 : ℝ) 1) x = forwardP7MinusPolynomial.derivative.eval x := by
    simpa only [iteratedDerivWithin_one] using
      iteratedDerivWithin_polynomial_eval 1 forwardP7MinusPolynomial x hx
  have hlog1 : derivWithin (fun y : ℝ ↦ Real.log ((3 - y) / 2))
      (Icc (-1 : ℝ) 1) x = -(1 / (3 - x)) := by
    convert iteratedDerivWithin_forwardLogMinus 1 (by norm_num) x hx using 1 <;>
      norm_num [iteratedDerivWithin_one, div_eq_mul_inv]
  rw [hP1, hlog1,
    iteratedDerivWithin_polynomial_eval 2 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 3 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 4 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 5 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 6 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 7 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 8 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_polynomial_eval 9 forwardP7MinusPolynomial x hx,
    iteratedDerivWithin_forwardLogMinus 9 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 8 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 7 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 6 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 5 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 4 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 3 (by norm_num) x hx,
    iteratedDerivWithin_forwardLogMinus 2 (by norm_num) x hx]
  have hP8 : (Polynomial.derivative^[8] forwardP7MinusPolynomial).eval x = 0 := by
    norm_num [forwardP7MinusPolynomial, Function.iterate_succ_apply]
  have hP9 : (Polynomial.derivative^[9] forwardP7MinusPolynomial).eval x = 0 := by
    norm_num [forwardP7MinusPolynomial, Function.iterate_succ_apply]
  rw [hP8, hP9]
  simp only [zero_mul, add_zero]
  have hden : 3 - x ≠ 0 := by
    rcases hx with ⟨hx0, hx1⟩
    linarith
  field_simp [hden]
  norm_num [forwardP7MinusPolynomial, Function.iterate_succ_apply, Nat.choose]
  ring

/-! ## Common-denominator forms -/

/-- The common positive denominator of all four ninth derivatives. -/
def factorTwoForwardNinthDenominator (x : ℝ) : ℝ :=
  (9 - x ^ 2) ^ 9

private lemma nine_sub_sq_pos {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < 9 - x ^ 2 := by
  have hprod : 0 ≤ (x + 1) * (1 - x) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  nlinarith

theorem factorTwoForwardNinthDenominator_pos
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardNinthDenominator
  exact pow_pos (nine_sub_sq_pos hx) 9

def factorTwoForwardKP6NinthRadial (u : ℝ) : ℝ :=
  -2479289182020 + 782405942220 * u - 99223446420 * u ^ 2 +
    4073929020 * u ^ 3 + 350812980 * u ^ 4 - 50890140 * u ^ 5 +
      2392740 * u ^ 6 - 41580 * u ^ 7

def factorTwoForwardLP6NinthRadial (u : ℝ) : ℝ :=
  -1783211303160 - 479692818360 * u + 340093109160 * u ^ 2 -
    71522219160 * u ^ 3 + 7896654360 * u ^ 4 - 498272040 * u ^ 5 +
      17108280 * u ^ 6 - 249480 * u ^ 7

def factorTwoForwardKP7NinthRadial (u : ℝ) : ℝ :=
  -24812447077530 + 8264297273400 * u - 279254530800 * u ^ 2 -
    322671875400 * u ^ 3 + 77672933100 * u ^ 4 - 8737890840 * u ^ 5 +
      549612000 * u ^ 6 - 18711000 * u ^ 7 + 270270 * u ^ 8

def factorTwoForwardLP7NinthRadial (u : ℝ) : ℝ :=
  -23572802486520 + 13389144237000 * u - 3425832711000 * u ^ 2 +
    504138637800 * u ^ 3 - 45681690600 * u ^ 4 + 2534558040 * u ^ 5 -
      79417800 * u ^ 6 + 1081080 * u ^ 7

def factorTwoForwardKP6NinthNumerator (x : ℝ) : ℝ :=
  x * factorTwoForwardKP6NinthRadial (x ^ 2)

def factorTwoForwardLP6NinthNumerator (x : ℝ) : ℝ :=
  factorTwoForwardLP6NinthRadial (x ^ 2)

def factorTwoForwardKP7NinthNumerator (x : ℝ) : ℝ :=
  factorTwoForwardKP7NinthRadial (x ^ 2)

def factorTwoForwardLP7NinthNumerator (x : ℝ) : ℝ :=
  x * factorTwoForwardLP7NinthRadial (x ^ 2)

private lemma contDiffWithinAt_forwardP6PlusLog
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y + 2) *
        Real.log ((3 + y) / 2)) (Icc (-1 : ℝ) 1) x := by
  apply ContDiffWithinAt.mul
  · unfold factorTwoForwardCenteredP6
    fun_prop
  · exact contDiffOn_forward_log_plus x hx

private lemma contDiffWithinAt_forwardP6MinusLog
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y - 2) *
        Real.log ((3 - y) / 2)) (Icc (-1 : ℝ) 1) x := by
  apply ContDiffWithinAt.mul
  · unfold factorTwoForwardCenteredP6
    fun_prop
  · exact contDiffOn_forward_log_minus x hx

private lemma contDiffWithinAt_forwardP7PlusLog
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y + 2) *
        Real.log ((3 + y) / 2)) (Icc (-1 : ℝ) 1) x := by
  apply ContDiffWithinAt.mul
  · unfold factorTwoForwardCenteredP7
    fun_prop
  · exact contDiffOn_forward_log_plus x hx

private lemma contDiffWithinAt_forwardP7MinusLog
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ContDiffWithinAt ℝ 9
      (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y - 2) *
        Real.log ((3 - y) / 2)) (Icc (-1 : ℝ) 1) x := by
  apply ContDiffWithinAt.mul
  · unfold factorTwoForwardCenteredP7
    fun_prop
  · exact contDiffOn_forward_log_minus x hx

theorem iteratedDerivWithin_nine_factorTwoForwardKP6_eq
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9 factorTwoForwardKP6 (Icc (-1 : ℝ) 1) x =
      factorTwoForwardKP6NinthNumerator x /
        factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardKP6
  change iteratedDerivWithin 9
      ((fun y : ℝ ↦ factorTwoForwardCenteredP6 (y + 2) *
          Real.log ((3 + y) / 2)) +
        (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y - 2) *
          Real.log ((3 - y) / 2))) (Icc (-1 : ℝ) 1) x = _
  rw [iteratedDerivWithin_add hx (uniqueDiffOn_Icc (by norm_num))
    (contDiffWithinAt_forwardP6PlusLog hx)
    (contDiffWithinAt_forwardP6MinusLog hx),
    iteratedDerivWithin_nine_forwardP6PlusLog x hx,
    iteratedDerivWithin_nine_forwardP6MinusLog x hx]
  have hp : 3 + x ≠ 0 := by linarith [hx.1]
  have hm : 3 - x ≠ 0 := by linarith [hx.2]
  have hcore : 9 - x ^ 2 ≠ 0 := (nine_sub_sq_pos hx).ne'
  unfold factorTwoForwardKP6NinthNumerator factorTwoForwardKP6NinthRadial
    factorTwoForwardNinthDenominator
  field_simp [hp, hm, hcore]
  ring

theorem iteratedDerivWithin_nine_factorTwoForwardLP6_eq
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9 factorTwoForwardLP6 (Icc (-1 : ℝ) 1) x =
      factorTwoForwardLP6NinthNumerator x /
        factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardLP6
  change iteratedDerivWithin 9
      ((fun y : ℝ ↦ factorTwoForwardCenteredP6 (y - 2) *
          Real.log ((3 - y) / 2)) -
        (fun y : ℝ ↦ factorTwoForwardCenteredP6 (y + 2) *
          Real.log ((3 + y) / 2))) (Icc (-1 : ℝ) 1) x = _
  rw [iteratedDerivWithin_sub hx (uniqueDiffOn_Icc (by norm_num))
    (contDiffWithinAt_forwardP6MinusLog hx)
    (contDiffWithinAt_forwardP6PlusLog hx),
    iteratedDerivWithin_nine_forwardP6MinusLog x hx,
    iteratedDerivWithin_nine_forwardP6PlusLog x hx]
  have hp : 3 + x ≠ 0 := by linarith [hx.1]
  have hm : 3 - x ≠ 0 := by linarith [hx.2]
  have hcore : 9 - x ^ 2 ≠ 0 := (nine_sub_sq_pos hx).ne'
  unfold factorTwoForwardLP6NinthNumerator factorTwoForwardLP6NinthRadial
    factorTwoForwardNinthDenominator
  field_simp [hp, hm, hcore]
  ring

theorem iteratedDerivWithin_nine_factorTwoForwardKP7_eq
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9 factorTwoForwardKP7 (Icc (-1 : ℝ) 1) x =
      factorTwoForwardKP7NinthNumerator x /
        factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardKP7
  change iteratedDerivWithin 9
      ((fun y : ℝ ↦ factorTwoForwardCenteredP7 (y + 2) *
          Real.log ((3 + y) / 2)) +
        (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y - 2) *
          Real.log ((3 - y) / 2))) (Icc (-1 : ℝ) 1) x = _
  rw [iteratedDerivWithin_add hx (uniqueDiffOn_Icc (by norm_num))
    (contDiffWithinAt_forwardP7PlusLog hx)
    (contDiffWithinAt_forwardP7MinusLog hx),
    iteratedDerivWithin_nine_forwardP7PlusLog x hx,
    iteratedDerivWithin_nine_forwardP7MinusLog x hx]
  have hp : 3 + x ≠ 0 := by linarith [hx.1]
  have hm : 3 - x ≠ 0 := by linarith [hx.2]
  have hcore : 9 - x ^ 2 ≠ 0 := (nine_sub_sq_pos hx).ne'
  unfold factorTwoForwardKP7NinthNumerator factorTwoForwardKP7NinthRadial
    factorTwoForwardNinthDenominator
  field_simp [hp, hm, hcore]
  ring

theorem iteratedDerivWithin_nine_factorTwoForwardLP7_eq
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin 9 factorTwoForwardLP7 (Icc (-1 : ℝ) 1) x =
      factorTwoForwardLP7NinthNumerator x /
        factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardLP7
  change iteratedDerivWithin 9
      ((fun y : ℝ ↦ factorTwoForwardCenteredP7 (y - 2) *
          Real.log ((3 - y) / 2)) -
        (fun y : ℝ ↦ factorTwoForwardCenteredP7 (y + 2) *
          Real.log ((3 + y) / 2))) (Icc (-1 : ℝ) 1) x = _
  rw [iteratedDerivWithin_sub hx (uniqueDiffOn_Icc (by norm_num))
    (contDiffWithinAt_forwardP7MinusLog hx)
    (contDiffWithinAt_forwardP7PlusLog hx),
    iteratedDerivWithin_nine_forwardP7MinusLog x hx,
    iteratedDerivWithin_nine_forwardP7PlusLog x hx]
  have hp : 3 + x ≠ 0 := by linarith [hx.1]
  have hm : 3 - x ≠ 0 := by linarith [hx.2]
  have hcore : 9 - x ^ 2 ≠ 0 := (nine_sub_sq_pos hx).ne'
  unfold factorTwoForwardLP7NinthNumerator factorTwoForwardLP7NinthRadial
    factorTwoForwardNinthDenominator
  field_simp [hp, hm, hcore]
  ring

/-! ## Degree-nine Bernstein certificates -/

private def forwardBernsteinNine
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 u : ℝ) : ℝ :=
  c0 * (1 - u) ^ 9 +
    c1 * u * (1 - u) ^ 8 +
      c2 * u ^ 2 * (1 - u) ^ 7 +
        c3 * u ^ 3 * (1 - u) ^ 6 +
          c4 * u ^ 4 * (1 - u) ^ 5 +
            c5 * u ^ 5 * (1 - u) ^ 4 +
              c6 * u ^ 6 * (1 - u) ^ 3 +
                c7 * u ^ 7 * (1 - u) ^ 2 +
                  c8 * u ^ 8 * (1 - u) + c9 * u ^ 9

private theorem forwardBernsteinNine_nonneg
    {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : 0 ≤ c6) (hc7 : 0 ≤ c7) (hc8 : 0 ≤ c8)
    (hc9 : 0 ≤ c9) :
    0 ≤ forwardBernsteinNine c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 u := by
  unfold forwardBernsteinNine
  have hu' : 0 ≤ 1 - u := by linarith
  positivity

private theorem factorTwoForwardKP6NinthRadial_lower_certificate (u : ℝ) :
    14000 * (9 - u) ^ 9 + factorTwoForwardKP6NinthRadial u =
      forwardBernsteinNine
        2944597663980 21859898072040 71185061602620 132943588288560
        156014735698080 118211826378240 56903506168320 16247715563520
        2302444892160 87317708800 u := by
  unfold factorTwoForwardKP6NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardKP6NinthRadial_upper_certificate (u : ℝ) :
    14000 * (9 - u) ^ 9 - factorTwoForwardKP6NinthRadial u =
      forwardBernsteinNine
        7903176028020 64922291463960 237373834525380 507030418495440
        697283940013920 640275885365760 392570693383680 154980550932480
        35748280995840 3670778675200 u := by
  unfold factorTwoForwardKP6NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardLP6NinthRadial_lower_certificate (u : ℝ) :
    16000 * (9 - u) ^ 9 + factorTwoForwardLP6NinthRadial u =
      forwardBernsteinNine
        4415516520840 33061228045200 108626312864520 204787413613440
        242772539869440 186027838617600 90739657451520 26362867875840
        3845887119360 160565657600 u := by
  unfold factorTwoForwardLP6NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardLP6NinthRadial_upper_certificate (u : ℝ) :
    16000 * (9 - u) ^ 9 - factorTwoForwardLP6NinthRadial u =
      forwardBernsteinNine
        7981939127160 66118417138800 244012425567480 526611451282560
        732425946658560 680815260518400 422945142036480 169326579548160
        39640656752640 4134401638400 u := by
  unfold factorTwoForwardLP6NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardKP7NinthRadial_lower_certificate (u : ℝ) :
    130000 * (9 - u) ^ 9 + factorTwoForwardKP7NinthRadial u =
      forwardBernsteinNine
        25552216492470 187869582135630 605181903745320 1116185204191680
        1290453463595520 959448207674880 449914572011520 123162117857280
        15930650787840 367694643200 u := by
  unfold factorTwoForwardKP7NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardKP7NinthRadial_upper_certificate (u : ℝ) :
    130000 * (9 - u) ^ 9 - factorTwoForwardKP7NinthRadial u =
      forwardBernsteinNine
        75177110647530 617965034984370 2260007846014680 4826430573088320
        6633034239444480 6083651972805120 3723774423828480 1466814642462720
        337397518172160 34528914636800 u := by
  unfold factorTwoForwardKP7NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardLP7NinthRadial_lower_certificate (u : ℝ) :
    100000 * (9 - u) ^ 9 + factorTwoForwardLP7NinthRadial u =
      forwardBernsteinNine
        15169246413480 111170313058320 357062489270280 656925392229120
        758150897575680 563383728875520 264673536583680 72982418227200
        9678877655040 273195008000 u := by
  unfold factorTwoForwardLP7NinthRadial forwardBernsteinNine
  ring

private theorem factorTwoForwardLP7NinthRadial_upper_certificate (u : ℝ) :
    100000 * (9 - u) ^ 9 - factorTwoForwardLP7NinthRadial u =
      forwardBernsteinNine
        62314851386520 508702469341680 1846929625929720 3914317513370880
        5336839643224320 4854385640724480 2945856460216320 1150076628172800
        262112021544960 26570350592000 u := by
  unfold factorTwoForwardLP7NinthRadial forwardBernsteinNine
  ring

private theorem abs_factorTwoForwardKP6NinthRadial_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |factorTwoForwardKP6NinthRadial u| ≤ 14000 * (9 - u) ^ 9 := by
  have hlo : 0 ≤ 14000 * (9 - u) ^ 9 + factorTwoForwardKP6NinthRadial u := by
    rw [factorTwoForwardKP6NinthRadial_lower_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  have hup : 0 ≤ 14000 * (9 - u) ^ 9 - factorTwoForwardKP6NinthRadial u := by
    rw [factorTwoForwardKP6NinthRadial_upper_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_factorTwoForwardLP6NinthRadial_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |factorTwoForwardLP6NinthRadial u| ≤ 16000 * (9 - u) ^ 9 := by
  have hlo : 0 ≤ 16000 * (9 - u) ^ 9 + factorTwoForwardLP6NinthRadial u := by
    rw [factorTwoForwardLP6NinthRadial_lower_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  have hup : 0 ≤ 16000 * (9 - u) ^ 9 - factorTwoForwardLP6NinthRadial u := by
    rw [factorTwoForwardLP6NinthRadial_upper_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_factorTwoForwardKP7NinthRadial_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |factorTwoForwardKP7NinthRadial u| ≤ 130000 * (9 - u) ^ 9 := by
  have hlo : 0 ≤ 130000 * (9 - u) ^ 9 + factorTwoForwardKP7NinthRadial u := by
    rw [factorTwoForwardKP7NinthRadial_lower_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  have hup : 0 ≤ 130000 * (9 - u) ^ 9 - factorTwoForwardKP7NinthRadial u := by
    rw [factorTwoForwardKP7NinthRadial_upper_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_factorTwoForwardLP7NinthRadial_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |factorTwoForwardLP7NinthRadial u| ≤ 100000 * (9 - u) ^ 9 := by
  have hlo : 0 ≤ 100000 * (9 - u) ^ 9 + factorTwoForwardLP7NinthRadial u := by
    rw [factorTwoForwardLP7NinthRadial_lower_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  have hup : 0 ≤ 100000 * (9 - u) ^ 9 - factorTwoForwardLP7NinthRadial u := by
    rw [factorTwoForwardLP7NinthRadial_upper_certificate]
    apply forwardBernsteinNine_nonneg hu0 hu1 <;> norm_num
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma sq_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    x ^ 2 ≤ 1 := by
  have hprod : 0 ≤ (x + 1) * (1 - x) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  nlinarith

theorem abs_factorTwoForwardKP6NinthNumerator_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardKP6NinthNumerator x| ≤
      14000 * factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardKP6NinthNumerator
  rw [abs_mul]
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hr := abs_factorTwoForwardKP6NinthRadial_le
    (sq_nonneg x) (sq_le_one_of_mem_Icc hx)
  calc
    |x| * |factorTwoForwardKP6NinthRadial (x ^ 2)| ≤
        1 * (14000 * (9 - x ^ 2) ^ 9) :=
      mul_le_mul hxabs hr (abs_nonneg _) (by norm_num)
    _ = 14000 * factorTwoForwardNinthDenominator x := by
      unfold factorTwoForwardNinthDenominator
      ring

theorem abs_factorTwoForwardLP6NinthNumerator_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardLP6NinthNumerator x| ≤
      16000 * factorTwoForwardNinthDenominator x := by
  simpa only [factorTwoForwardLP6NinthNumerator,
    factorTwoForwardNinthDenominator] using
      abs_factorTwoForwardLP6NinthRadial_le
        (sq_nonneg x) (sq_le_one_of_mem_Icc hx)

theorem abs_factorTwoForwardKP7NinthNumerator_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardKP7NinthNumerator x| ≤
      130000 * factorTwoForwardNinthDenominator x := by
  simpa only [factorTwoForwardKP7NinthNumerator,
    factorTwoForwardNinthDenominator] using
      abs_factorTwoForwardKP7NinthRadial_le
        (sq_nonneg x) (sq_le_one_of_mem_Icc hx)

theorem abs_factorTwoForwardLP7NinthNumerator_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardLP7NinthNumerator x| ≤
      100000 * factorTwoForwardNinthDenominator x := by
  unfold factorTwoForwardLP7NinthNumerator
  rw [abs_mul]
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hr := abs_factorTwoForwardLP7NinthRadial_le
    (sq_nonneg x) (sq_le_one_of_mem_Icc hx)
  calc
    |x| * |factorTwoForwardLP7NinthRadial (x ^ 2)| ≤
        1 * (100000 * (9 - x ^ 2) ^ 9) :=
      mul_le_mul hxabs hr (abs_nonneg _) (by norm_num)
    _ = 100000 * factorTwoForwardNinthDenominator x := by
      unfold factorTwoForwardNinthDenominator
      ring

/-! ## Final ninth-derivative envelopes -/

theorem abs_iteratedDerivWithin_nine_factorTwoForwardKP6_le
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin 9 factorTwoForwardKP6 (Icc (-1 : ℝ) 1) x| ≤
      14000 := by
  rw [iteratedDerivWithin_nine_factorTwoForwardKP6_eq x hx, abs_div,
    abs_of_pos (factorTwoForwardNinthDenominator_pos hx)]
  exact (div_le_iff₀ (factorTwoForwardNinthDenominator_pos hx)).2
    (abs_factorTwoForwardKP6NinthNumerator_le hx)

theorem abs_iteratedDerivWithin_nine_factorTwoForwardLP6_le
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin 9 factorTwoForwardLP6 (Icc (-1 : ℝ) 1) x| ≤
      16000 := by
  rw [iteratedDerivWithin_nine_factorTwoForwardLP6_eq x hx, abs_div,
    abs_of_pos (factorTwoForwardNinthDenominator_pos hx)]
  exact (div_le_iff₀ (factorTwoForwardNinthDenominator_pos hx)).2
    (abs_factorTwoForwardLP6NinthNumerator_le hx)

theorem abs_iteratedDerivWithin_nine_factorTwoForwardKP7_le
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin 9 factorTwoForwardKP7 (Icc (-1 : ℝ) 1) x| ≤
      130000 := by
  rw [iteratedDerivWithin_nine_factorTwoForwardKP7_eq x hx, abs_div,
    abs_of_pos (factorTwoForwardNinthDenominator_pos hx)]
  exact (div_le_iff₀ (factorTwoForwardNinthDenominator_pos hx)).2
    (abs_factorTwoForwardKP7NinthNumerator_le hx)

theorem abs_iteratedDerivWithin_nine_factorTwoForwardLP7_le
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin 9 factorTwoForwardLP7 (Icc (-1 : ℝ) 1) x| ≤
      100000 := by
  rw [iteratedDerivWithin_nine_factorTwoForwardLP7_eq x hx, abs_div,
    abs_of_pos (factorTwoForwardNinthDenominator_pos hx)]
  exact (div_le_iff₀ (factorTwoForwardNinthDenominator_pos hx)).2
    (abs_factorTwoForwardLP7NinthNumerator_le hx)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural
