import ArithmeticHodge.Analysis.FiniteRepeatedRolle
import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardLegendreRemainderStructural
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open ArithmeticHodge.Analysis.FiniteRepeatedRolle
open ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality
open ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
open ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
open ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicResidual
open ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

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

/-- The fixed dyadic grid converts a pointwise ninth-derivative envelope
into the universal centered `L²` constant
`(3/200000) / (9!)² = 1/8778792960000000`. -/
theorem integral_sq_sub_polynomial_le_dyadicNineRemainder
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc (-1 : ℝ) 1))
    (Q : ℝ[X]) (M : ℝ) (hM : 0 ≤ M)
    (hrem : ∀ x ∈ Icc (-1 : ℝ) 1,
      |F x - Q.eval ((x + 1) / 2)| ≤
        (M / 362880) *
          |factorTwoDyadicNineNodalPolynomial.eval x|) :
    (∫ x : ℝ in -1..1,
      (F x - Q.eval ((x + 1) / 2)) ^ 2) ≤
        (1 / 8778792960000000 : ℝ) * M ^ 2 := by
  have hQcont : Continuous
      (fun x : ℝ ↦ Q.eval ((x + 1) / 2)) := by
    fun_prop
  have hRcont : ContinuousOn
      (fun x : ℝ ↦ (F x - Q.eval ((x + 1) / 2)) ^ 2)
      (Icc (-1 : ℝ) 1) := (hF.sub hQcont.continuousOn).pow 2
  have hPcont : Continuous
      (fun x : ℝ ↦
        (M / 362880) ^ 2 *
          factorTwoDyadicNineNodalPolynomial.eval x ^ 2) := by
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1,
        (F x - Q.eval ((x + 1) / 2)) ^ 2) ≤
      ∫ x : ℝ in -1..1,
        (M / 362880) ^ 2 *
          factorTwoDyadicNineNodalPolynomial.eval x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hRcont.intervalIntegrable_of_Icc (by norm_num))
      (hPcont.intervalIntegrable (-1) 1)
    intro x hx
    have h := hrem x hx
    have hright :
        0 ≤ (M / 362880) *
          |factorTwoDyadicNineNodalPolynomial.eval x| := by
      positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hright).2 h
    rw [sq_abs] at hsquare
    calc
      (F x - Q.eval ((x + 1) / 2)) ^ 2 ≤
          ((M / 362880) *
            |factorTwoDyadicNineNodalPolynomial.eval x|) ^ 2 := hsquare
      _ = (M / 362880) ^ 2 *
          factorTwoDyadicNineNodalPolynomial.eval x ^ 2 := by
        rw [mul_pow, sq_abs]
  calc
    _ ≤ ∫ x : ℝ in -1..1,
        (M / 362880) ^ 2 *
          factorTwoDyadicNineNodalPolynomial.eval x ^ 2 := hmono
    _ = (M / 362880) ^ 2 *
        (∫ x : ℝ in -1..1,
          factorTwoDyadicNineNodalPolynomial.eval x ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (M / 362880) ^ 2 * (3 / 200000 : ℝ) :=
      mul_le_mul_of_nonneg_left
        integral_factorTwoDyadicNineNodalPolynomial_sq_le (sq_nonneg _)
    _ = (1 / 8778792960000000 : ℝ) * M ^ 2 := by
      ring

/-- Combined interpolation-and-mass form.  This is the interface consumed
by the four forward-Hankel representers: only their ninth derivative bound
remains representer-specific. -/
theorem exists_dyadicNine_interpolant_L2_remainder
    (F : ℝ → ℝ) (hF : ContDiffOn ℝ 9 F (Icc (-1 : ℝ) 1))
    (M : ℝ)
    (h9 : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) x| ≤ M) :
    ∃ Q : ℝ[X], Q.natDegree < 9 ∧
      (∀ x ∈ Icc (-1 : ℝ) 1,
        |F x - Q.eval ((x + 1) / 2)| ≤
          (M / 362880) *
            |factorTwoDyadicNineNodalPolynomial.eval x|) ∧
      (∫ x : ℝ in -1..1,
        (F x - Q.eval ((x + 1) / 2)) ^ 2) ≤
          (1 / 8778792960000000 : ℝ) * M ^ 2 := by
  have hM : 0 ≤ M :=
    (abs_nonneg (iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) 0)).trans
      (h9 0 (by norm_num))
  obtain ⟨Q, hQ, hrem⟩ := exists_dyadicNine_interpolant_remainder F hF M h9
  exact ⟨Q, hQ, hrem,
    integral_sq_sub_polynomial_le_dyadicNineRemainder
      F hF.continuousOn Q M hM hrem⟩

/-! ## Moment-gap pairing -/

private theorem sq_intervalIntegral_mul_le_dyadic
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    (∫ x : ℝ in -1..1, f x * g x) ^ 2 ≤
      (∫ x : ℝ in -1..1, f x ^ 2) *
        (∫ x : ℝ in -1..1, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ := by
    dsimp only [μ]
    exact (hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hgMeas : AEStronglyMeasurable g μ := by
    dsimp only [μ]
    exact (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

/-- A nine-moment gap and a ninth-derivative envelope bound the whole
representer pairing at once.  The polynomial interpolant disappears by the
moment gap; Cauchy--Schwarz sees only the single dyadic remainder mass. -/
theorem sq_intervalIntegral_mul_le_dyadicNineRemainder
    (w F : ℝ → ℝ) (hw : Continuous w)
    (hF : ContinuousOn F (Icc (-1 : ℝ) 1))
    (hF9 : ContDiffOn ℝ 9 F (Icc (-1 : ℝ) 1))
    (hlow : centeredLegendreMomentsVanishBelow w 9)
    (M : ℝ)
    (h9 : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 F (Icc (-1 : ℝ) 1) x| ≤ M) :
    (∫ x : ℝ in -1..1, w x * F x) ^ 2 ≤
      (1 / 8778792960000000 : ℝ) * M ^ 2 *
        factorTwoIntrinsicEnergy w := by
  obtain ⟨Q, hQ, _hrem, hmass⟩ :=
    exists_dyadicNine_interpolant_L2_remainder F hF9 M h9
  let R : ℝ → ℝ := fun x ↦ F x - Q.eval ((x + 1) / 2)
  have hR : ContinuousOn R (Icc (-1 : ℝ) 1) := by
    dsimp only [R]
    exact hF.sub (by fun_prop : Continuous
      (fun x : ℝ ↦ Q.eval ((x + 1) / 2))).continuousOn
  have hpoly :
      (∫ x : ℝ in -1..1, w x * Q.eval ((x + 1) / 2)) = 0 :=
    intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow Q hQ
  have hwR : IntervalIntegrable (fun x : ℝ ↦ w x * R x)
      volume (-1) 1 :=
    (hw.continuousOn.mul hR).intervalIntegrable_of_Icc (by norm_num)
  have hwQ : IntervalIntegrable
      (fun x : ℝ ↦ w x * Q.eval ((x + 1) / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpair :
      (∫ x : ℝ in -1..1, w x * F x) =
        ∫ x : ℝ in -1..1, R x * w x := by
    calc
      (∫ x : ℝ in -1..1, w x * F x) =
          ∫ x : ℝ in -1..1,
            w x * R x + w x * Q.eval ((x + 1) / 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [R]
        ring
      _ = (∫ x : ℝ in -1..1, w x * R x) +
          ∫ x : ℝ in -1..1,
            w x * Q.eval ((x + 1) / 2) := by
        rw [intervalIntegral.integral_add hwR hwQ]
      _ = ∫ x : ℝ in -1..1, R x * w x := by
        rw [hpoly, add_zero]
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
  have hcauchy :=
    sq_intervalIntegral_mul_le_dyadic R w hR hw.continuousOn
  have hwNonneg : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦
      sq_nonneg (w x)
  rw [hpair]
  exact hcauchy.trans <| by
    unfold factorTwoIntrinsicEnergy
    exact mul_le_mul_of_nonneg_right hmass hwNonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67DyadicNineInterpolationStructural
