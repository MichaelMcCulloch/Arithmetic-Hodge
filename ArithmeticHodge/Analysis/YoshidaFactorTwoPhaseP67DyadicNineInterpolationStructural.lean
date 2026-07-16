import ArithmeticHodge.Analysis.FiniteRepeatedRolle
import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardLegendreRemainderStructural
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open ArithmeticHodge.Analysis.FiniteRepeatedRolle

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67DyadicNineInterpolationStructural

noncomputable section

/-!
# A structural nine-node interpolation grid

These symmetric dyadic nodes are fixed once for all four forward-Hankel
representers.  They approximate the ninth Chebyshev roots, but every fact
used below is exact: strict ordering, containment in `[-1,1]`, the monic
nodal polynomial, and its uniform-measure `L²` mass.
-/

/-- A symmetric dyadic approximation to the nine Chebyshev roots. -/
def factorTwoDyadicNineNode : Fin 9 → ℝ := ![
  -63 / 64,
  -55 / 64,
  -41 / 64,
  -11 / 32,
  0,
  11 / 32,
  41 / 64,
  55 / 64,
  63 / 64
]

theorem factorTwoDyadicNineNode_strictMono :
    StrictMono factorTwoDyadicNineNode := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;>
    norm_num [factorTwoDyadicNineNode, Matrix.cons_val_two]

theorem factorTwoDyadicNineNode_mem_Icc (i : Fin 9) :
    factorTwoDyadicNineNode i ∈ Icc (-1 : ℝ) 1 := by
  fin_cases i <;> norm_num [factorTwoDyadicNineNode]

/-- The monic nodal polynomial of the dyadic interpolation grid. -/
def factorTwoDyadicNineNodalPolynomial : ℝ[X] :=
  ∏ i : Fin 9, (Polynomial.X - Polynomial.C (factorTwoDyadicNineNode i))

theorem factorTwoDyadicNineNodalPolynomial_eval (x : ℝ) :
    factorTwoDyadicNineNodalPolynomial.eval x =
      x ^ 9 - (9159 / 4096 : ℝ) * x ^ 7 +
        (27961839 / 16777216 : ℝ) * x ^ 5 -
          (31683823501 / 68719476736 : ℝ) * x ^ 3 +
            (2442078171225 / 70368744177664 : ℝ) * x := by
  norm_num [factorTwoDyadicNineNodalPolynomial, factorTwoDyadicNineNode,
    Fin.prod_univ_succ]
  ring

theorem factorTwoDyadicNineNodalPolynomial_eval_node (i : Fin 9) :
    factorTwoDyadicNineNodalPolynomial.eval (factorTwoDyadicNineNode i) = 0 := by
  unfold factorTwoDyadicNineNodalPolynomial
  rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem factorTwoDyadicNineNodalPolynomial_natDegree :
    factorTwoDyadicNineNodalPolynomial.natDegree = 9 := by
  unfold factorTwoDyadicNineNodalPolynomial
  rw [natDegree_prod_of_monic
    (h := fun i _hi ↦ monic_X_sub_C (factorTwoDyadicNineNode i))]
  simp

theorem factorTwoDyadicNineNodalPolynomial_monic :
    factorTwoDyadicNineNodalPolynomial.Monic := by
  unfold factorTwoDyadicNineNodalPolynomial
  exact monic_prod_of_monic _ _ fun i _hi ↦
    monic_X_sub_C (factorTwoDyadicNineNode i)

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
      rw [hderiv]
      rw [ih, Function.iterate_succ_apply]

/-- The ninth derivative of the monic nodal polynomial is exactly `9!`.
This uses only monicity and degree, not the explicit coefficient expansion. -/
theorem iterate_derivative_factorTwoDyadicNineNodalPolynomial :
    Polynomial.derivative^[9] factorTwoDyadicNineNodalPolynomial =
      Polynomial.C (362880 : ℝ) := by
  ext m
  rw [coeff_iterate_derivative]
  by_cases hm : m = 0
  · subst m
    simp only [zero_add, coeff_C_zero]
    rw [show factorTwoDyadicNineNodalPolynomial.coeff 9 = 1 by
      simpa [factorTwoDyadicNineNodalPolynomial_natDegree] using
        factorTwoDyadicNineNodalPolynomial_monic.coeff_natDegree]
    norm_num [Nat.descFactorial]
  · have hlarge : factorTwoDyadicNineNodalPolynomial.natDegree < m + 9 := by
      rw [factorTwoDyadicNineNodalPolynomial_natDegree]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hlarge]
    rw [coeff_C_ne_zero hm]
    simp only [smul_zero]

/-! ## Structural interpolation remainder -/

/-- Every function with a bounded ninth derivative on `[-1,1]` admits a
degree-eight interpolant whose error is controlled by the single fixed
dyadic nodal polynomial.  The proof is the classical structural argument:
subtract the interpolant and a suitable multiple of the nodal polynomial,
then apply repeated Rolle to its ten zeros. -/
theorem exists_dyadicNine_interpolant_remainder
    (F : ℝ → ℝ) (hF : ContDiffOn ℝ 9 F (Icc (-1 : ℝ) 1))
    (M : ℝ)
    (h9 : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) x| ≤ M) :
    ∃ Q : ℝ[X], Q.natDegree < 9 ∧
      ∀ x ∈ Icc (-1 : ℝ) 1,
        |F x - Q.eval ((x + 1) / 2)| ≤
          (M / 362880) *
            |factorTwoDyadicNineNodalPolynomial.eval x| := by
  let R : ℝ[X] := Lagrange.interpolate Finset.univ factorTwoDyadicNineNode
    (fun i ↦ F (factorTwoDyadicNineNode i))
  let A : ℝ[X] := Polynomial.C 2 * Polynomial.X - Polynomial.C 1
  let Q : ℝ[X] := R.comp A
  have hnodeInjective : Function.Injective factorTwoDyadicNineNode :=
    factorTwoDyadicNineNode_strictMono.injective
  have hnodeInjOn : Set.InjOn factorTwoDyadicNineNode
      (Finset.univ : Finset (Fin 9)) := hnodeInjective.injOn
  have hRnode (i : Fin 9) :
      R.eval (factorTwoDyadicNineNode i) =
        F (factorTwoDyadicNineNode i) := by
    dsimp only [R]
    exact Lagrange.eval_interpolate_at_node
      (fun j ↦ F (factorTwoDyadicNineNode j)) hnodeInjOn
      (Finset.mem_univ i)
  have hRnatDegree : R.natDegree ≤ 8 := by
    rw [natDegree_le_iff_degree_le]
    simpa only [R, Finset.card_univ, Fintype.card_fin, Nat.reduceSub] using
      Lagrange.degree_interpolate_le
        (fun i ↦ F (factorTwoDyadicNineNode i)) hnodeInjOn
  have hAnatDegree : A.natDegree ≤ 1 := by
    dsimp only [A]
    calc
      (Polynomial.C 2 * Polynomial.X - Polynomial.C 1 : ℝ[X]).natDegree =
          (Polynomial.C 2 * Polynomial.X : ℝ[X]).natDegree := natDegree_sub_C
      _ ≤ Polynomial.X.natDegree := natDegree_C_mul_le _ _
      _ ≤ 1 := natDegree_X_le
  have hQnatDegree : Q.natDegree < 9 := by
    dsimp only [Q]
    calc
      (R.comp A).natDegree ≤ R.natDegree * A.natDegree := natDegree_comp_le
      _ ≤ R.natDegree * 1 := Nat.mul_le_mul_left _ hAnatDegree
      _ = R.natDegree := Nat.mul_one _
      _ ≤ 8 := hRnatDegree
      _ < 9 := by omega
  have hQeval (x : ℝ) : Q.eval ((x + 1) / 2) = R.eval x := by
    simp only [Q, A, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
    congr 1
    ring
  refine ⟨Q, hQnatDegree, ?_⟩
  intro x hx
  by_cases hxnode : ∃ i : Fin 9, x = factorTwoDyadicNineNode i
  · obtain ⟨i, rfl⟩ := hxnode
    rw [hQeval, hRnode, sub_self, abs_zero,
      factorTwoDyadicNineNodalPolynomial_eval_node, abs_zero, mul_zero]
  · have hxne (i : Fin 9) : x ≠ factorTwoDyadicNineNode i := by
      intro hxi
      exact hxnode ⟨i, hxi⟩
    have hPne : factorTwoDyadicNineNodalPolynomial.eval x ≠ 0 := by
      unfold factorTwoDyadicNineNodalPolynomial
      rw [eval_prod, Finset.prod_ne_zero_iff]
      intro i _hi
      simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using hxne i
    let lam : ℝ :=
      (F x - R.eval x) / factorTwoDyadicNineNodalPolynomial.eval x
    let g : ℝ → ℝ := fun y ↦
      F y - R.eval y -
        lam * factorTwoDyadicNineNodalPolynomial.eval y
    have hRcont : ContDiff ℝ 9 (fun y : ℝ ↦ R.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        R.contDiff_aeval (𝕜 := ℝ) 9
    have hPcont : ContDiff ℝ 9
        (fun y : ℝ ↦ factorTwoDyadicNineNodalPolynomial.eval y) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        factorTwoDyadicNineNodalPolynomial.contDiff_aeval (𝕜 := ℝ) 9
    have hg : ContDiffOn ℝ 9 g (Icc (-1 : ℝ) 1) := by
      dsimp only [g]
      exact (hF.sub hRcont.contDiffOn).sub
        (contDiff_const.mul hPcont).contDiffOn
    let nodes : Finset ℝ :=
      Finset.univ.image factorTwoDyadicNineNode
    have hxnotNodes : x ∉ nodes := by
      simp only [nodes, Finset.mem_image, Finset.mem_univ, true_and]
      intro h
      obtain ⟨i, hix⟩ := h
      exact hxne i hix.symm
    have hnodesCard : nodes.card = 9 := by
      dsimp only [nodes]
      rw [Finset.card_image_of_injective _ hnodeInjective,
        Finset.card_univ, Fintype.card_fin]
    have hzerosCard : (insert x nodes).card = 9 + 1 := by
      rw [Finset.card_insert_of_notMem hxnotNodes, hnodesCard]
    have hzerosMem : ∀ z ∈ insert x nodes, z ∈ Icc (-1 : ℝ) 1 := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
        exact factorTwoDyadicNineNode_mem_Icc i
    have hzeros : ∀ z ∈ insert x nodes, g z = 0 := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · dsimp only [g, lam]
        rw [div_mul_cancel₀ _ hPne]
        ring
      · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
        dsimp only [g]
        rw [hRnode, factorTwoDyadicNineNodalPolynomial_eval_node]
        ring
    obtain ⟨c, hc, hgzero⟩ :=
      exists_iteratedDerivWithin_eq_zero_of_finset_zeros
        (by norm_num) 9 g hg (insert x nodes) hzerosCard hzerosMem hzeros
    have hUnique : UniqueDiffOn ℝ (Icc (-1 : ℝ) 1) :=
      uniqueDiffOn_Icc (by norm_num)
    have hRderiv : Polynomial.derivative^[9] R = 0 :=
      iterate_derivative_eq_zero (hRnatDegree.trans_lt (by norm_num))
    have hRwithin :
        iteratedDerivWithin 9 (fun y : ℝ ↦ R.eval y)
          (Icc (-1 : ℝ) 1) c = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv hUnique hRcont.contDiffAt hc,
        iteratedDeriv_polynomial_eval, hRderiv, eval_zero]
    have hPwithin :
        iteratedDerivWithin 9
          (fun y : ℝ ↦ factorTwoDyadicNineNodalPolynomial.eval y)
          (Icc (-1 : ℝ) 1) c = 362880 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv hUnique hPcont.contDiffAt hc,
        iteratedDeriv_polynomial_eval,
        iterate_derivative_factorTwoDyadicNineNodalPolynomial, eval_C]
    have hgderiv :
        iteratedDerivWithin 9 g (Icc (-1 : ℝ) 1) c =
          iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) c -
            lam * 362880 := by
      have hFRwithin :
          iteratedDerivWithin 9 (fun y : ℝ ↦ F y - R.eval y)
              (Icc (-1 : ℝ) 1) c =
            iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) c -
              iteratedDerivWithin 9 (fun y : ℝ ↦ R.eval y)
                (Icc (-1 : ℝ) 1) c := by
        simpa only [Pi.sub_apply] using
          iteratedDerivWithin_sub (n := 9) hc hUnique (hF c hc)
            hRcont.contDiffAt.contDiffWithinAt
      have hlamPwithin :
          iteratedDerivWithin 9
              (fun y : ℝ ↦
                lam * factorTwoDyadicNineNodalPolynomial.eval y)
              (Icc (-1 : ℝ) 1) c =
            lam * iteratedDerivWithin 9
              (fun y : ℝ ↦ factorTwoDyadicNineNodalPolynomial.eval y)
              (Icc (-1 : ℝ) 1) c := by
        exact iteratedDerivWithin_const_mul_field lam _
      have houter :
          iteratedDerivWithin 9
              (fun y : ℝ ↦ F y - R.eval y -
                lam * factorTwoDyadicNineNodalPolynomial.eval y)
              (Icc (-1 : ℝ) 1) c =
            iteratedDerivWithin 9 (fun y : ℝ ↦ F y - R.eval y)
                (Icc (-1 : ℝ) 1) c -
              iteratedDerivWithin 9
                (fun y : ℝ ↦
                  lam * factorTwoDyadicNineNodalPolynomial.eval y)
                (Icc (-1 : ℝ) 1) c := by
        simpa only [Pi.sub_apply] using
          iteratedDerivWithin_sub (n := 9) hc hUnique
            ((hF c hc).sub hRcont.contDiffAt.contDiffWithinAt)
            ((contDiff_const.mul hPcont).contDiffAt.contDiffWithinAt)
      change iteratedDerivWithin 9
        (fun y : ℝ ↦ F y - R.eval y -
          lam * factorTwoDyadicNineNodalPolynomial.eval y)
        (Icc (-1 : ℝ) 1) c = _
      rw [houter, hFRwithin, hlamPwithin, hRwithin, hPwithin]
      ring
    have hlameq : lam * 362880 =
        iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) c := by
      linarith [hgzero, hgderiv]
    have hlambound : |lam| ≤ M / 362880 := by
      have hb := h9 c hc
      rw [← hlameq] at hb
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 362880)).2
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 362880)] using hb
    rw [hQeval]
    have herror : F x - R.eval x =
        lam * factorTwoDyadicNineNodalPolynomial.eval x := by
      dsimp only [lam]
      rw [div_mul_cancel₀ _ hPne]
    rw [herror, abs_mul]
    exact mul_le_mul_of_nonneg_right hlambound (abs_nonneg _)

/-- The dyadic nodal mass is within a small rational factor of the optimal
monic Legendre mass.  The looser `3/200000` value is chosen to keep all later
Schur arithmetic transparent. -/
theorem integral_factorTwoDyadicNineNodalPolynomial_sq_le :
    (∫ x : ℝ in -1..1,
      factorTwoDyadicNineNodalPolynomial.eval x ^ 2) ≤
        (3 / 200000 : ℝ) := by
  rw [show (fun x : ℝ ↦ factorTwoDyadicNineNodalPolynomial.eval x ^ 2) =
      fun x ↦
        (x ^ 9 - (9159 / 4096 : ℝ) * x ^ 7 +
          (27961839 / 16777216 : ℝ) * x ^ 5 -
            (31683823501 / 68719476736 : ℝ) * x ^ 3 +
              (2442078171225 / 70368744177664 : ℝ) * x) ^ 2 by
    funext x
    rw [factorTwoDyadicNineNodalPolynomial_eval]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67DyadicNineInterpolationStructural
