import ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18RowDecompositionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51Polynomial18TailStructural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoPolynomialLagRepresenterStructural
open YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural
open YoshidaFourCellOddP51EndpointStripRepresenterStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
open YoshidaFourCellOddP51Kernel18RowDecompositionStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition

/-!
# Finite polynomial tail of the degree-eighteen P51 row

The degree-eighteen regular-kernel center and the exact inverse-solved
`q51` profile are honest polynomials of degrees at most eighteen and
fifty-one.  Their symmetric lag convolution is odd, hence the generic
degree-seventy estimate improves to degree sixty-nine.  This file realizes
the scaled regular row in `L²(0,1)`, removes every shifted-Legendre degree
below `53`, and records the exact finite `P53`--`P69` packet and its norm.
-/

private def polynomial18Coefficient : ℕ → ℝ
  | 0 => 1
  | 1 => -(1 / 6)
  | 2 => -(1 / 2)
  | 3 => 7 / 360
  | 4 => 5 / 24
  | 5 => -(31 / 15120)
  | 6 => -(61 / 720)
  | 7 => 127 / 604800
  | 8 => 277 / 8064
  | 9 => -(73 / 3421440)
  | 10 => -(50521 / 3628800)
  | 11 => 1414477 / 653837184000
  | 12 => 540553 / 95800320
  | 13 => -(8191 / 37362124800)
  | 14 => -(199360981 / 87178291200)
  | 15 => 16931177 / 762187345920000
  | 16 => 3878302429 / 4184557977600
  | 17 => -(5749691557 / 2554547108585472000)
  | 18 => -(2404879675441 / 6402373705728000)
  | _ => 0

/-- Polynomial object whose evaluation is the actual degree-eighteen lag
kernel used in the P51 row decomposition. -/
def fourCellOddP51Polynomial18RegularLagPolynomial : ℝ[X] :=
  let u : ℝ[X] := (fourCellOperatorHalfWidth / 2) • X
  (1 / 4 : ℝ) •
    ∑ n ∈ Finset.range 19, polynomial18Coefficient n • u ^ n

theorem fourCellOddP51Polynomial18RegularLagPolynomial_eval (x : ℝ) :
    fourCellOddP51Polynomial18RegularLagPolynomial.eval x =
      fourCellOddP51Polynomial18RegularLagKernel x := by
  unfold fourCellOddP51Polynomial18RegularLagPolynomial
    polynomial18Coefficient
    fourCellOddP51Polynomial18RegularLagKernel
  change _ = (1 / 4 : ℝ) *
    ((1 - (fourCellOperatorHalfWidth * x / 2) ^ 2 / 2 +
        5 * (fourCellOperatorHalfWidth * x / 2) ^ 4 / 24 -
        61 * (fourCellOperatorHalfWidth * x / 2) ^ 6 / 720 +
        277 * (fourCellOperatorHalfWidth * x / 2) ^ 8 / 8064 -
        50521 * (fourCellOperatorHalfWidth * x / 2) ^ 10 / 3628800 +
        540553 * (fourCellOperatorHalfWidth * x / 2) ^ 12 / 95800320 -
        199360981 * (fourCellOperatorHalfWidth * x / 2) ^ 14 /
          87178291200 +
        3878302429 * (fourCellOperatorHalfWidth * x / 2) ^ 16 /
          4184557977600 -
        2404879675441 * (fourCellOperatorHalfWidth * x / 2) ^ 18 /
          6402373705728000) +
      (-(fourCellOperatorHalfWidth * x / 2) / 6 +
        7 * (fourCellOperatorHalfWidth * x / 2) ^ 3 / 360 -
        31 * (fourCellOperatorHalfWidth * x / 2) ^ 5 / 15120 +
        127 * (fourCellOperatorHalfWidth * x / 2) ^ 7 / 604800 -
        73 * (fourCellOperatorHalfWidth * x / 2) ^ 9 / 3421440 +
        1414477 * (fourCellOperatorHalfWidth * x / 2) ^ 11 /
          653837184000 -
        8191 * (fourCellOperatorHalfWidth * x / 2) ^ 13 / 37362124800 +
        16931177 * (fourCellOperatorHalfWidth * x / 2) ^ 15 /
          762187345920000 -
        5749691557 * (fourCellOperatorHalfWidth * x / 2) ^ 17 /
          2554547108585472000))
  simp only [Polynomial.eval_smul, Polynomial.eval_finset_sum,
    Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

theorem natDegree_fourCellOddP51Polynomial18RegularLagPolynomial_le :
    fourCellOddP51Polynomial18RegularLagPolynomial.natDegree ≤ 18 := by
  unfold fourCellOddP51Polynomial18RegularLagPolynomial
  dsimp only
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  have hn19 : n < 19 := Finset.mem_range.mp hn
  apply (Polynomial.natDegree_smul_le _ _).trans
  calc
    (((fourCellOperatorHalfWidth / 2) • X : ℝ[X]) ^ n).natDegree ≤
        n * ((fourCellOperatorHalfWidth / 2) • X : ℝ[X]).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left n
      ((Polynomial.natDegree_smul_le _ _).trans (by simp))
    _ ≤ 18 := by
      rw [Nat.mul_one]
      omega

theorem natDegree_fourCellOddQ51Polynomial_le :
    fourCellOddQ51Polynomial.natDegree ≤ 51 := by
  unfold fourCellOddQ51Polynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · rw [Polynomial.natDegree_neg]
    exact (natDegree_centeredShiftedLegendreReal_le 1).trans (by norm_num)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply (Polynomial.natDegree_smul_le _ _).trans
    rw [Polynomial.natDegree_neg]
    apply (natDegree_centeredShiftedLegendreReal_le
      (fourCellOddFiniteRetainedDegree i)).trans
    have hi := i.isLt
    unfold fourCellOddFiniteRetainedDegree
    omega

theorem odd_fourCellOddQ51Polynomial_eval :
    Function.Odd fourCellOddQ51Polynomial.eval := by
  intro x
  change fourCellOddQ51Polynomial.eval (-x) =
    -fourCellOddQ51Polynomial.eval x
  rw [fourCellOddQ51Polynomial_eval, fourCellOddQ51Polynomial_eval]
  exact odd_fourCellOddQ51 x

/-- Polynomial representing the scaled degree-eighteen regular row
`-2 h K(q18,q51)`. -/
def fourCellOddP51Polynomial18RegularSourcePolynomial : ℝ[X] :=
  (-2 * fourCellOperatorHalfWidth) •
    factorTwoPolynomialLagK
      fourCellOddP51Polynomial18RegularLagPolynomial
      fourCellOddQ51Polynomial

theorem fourCellOddP51Polynomial18RegularSourcePolynomial_eval (x : ℝ) :
    fourCellOddP51Polynomial18RegularSourcePolynomial.eval x =
      (-2 * fourCellOperatorHalfWidth) *
        factorTwoContinuousLagK
          fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x := by
  unfold fourCellOddP51Polynomial18RegularSourcePolynomial
  rw [Polynomial.eval_smul, eval_factorTwoPolynomialLagK]
  simp only [smul_eq_mul]
  have hlag : fourCellOddP51Polynomial18RegularLagPolynomial.eval =
      fourCellOddP51Polynomial18RegularLagKernel := by
    funext t
    exact fourCellOddP51Polynomial18RegularLagPolynomial_eval t
  have hq : fourCellOddQ51Polynomial.eval = fourCellOddQ51 := by
    funext t
    exact fourCellOddQ51Polynomial_eval t
  rw [hlag, hq]

theorem odd_fourCellOddP51Polynomial18RegularSourcePolynomial_eval :
    Function.Odd fourCellOddP51Polynomial18RegularSourcePolynomial.eval := by
  intro x
  change fourCellOddP51Polynomial18RegularSourcePolynomial.eval (-x) =
    -fourCellOddP51Polynomial18RegularSourcePolynomial.eval x
  rw [fourCellOddP51Polynomial18RegularSourcePolynomial_eval,
    fourCellOddP51Polynomial18RegularSourcePolynomial_eval,
    ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural.odd_factorTwoContinuousLagK_of_odd
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
      odd_fourCellOddQ51]
  ring

theorem natDegree_fourCellOddP51Polynomial18RegularSourcePolynomial_le :
    fourCellOddP51Polynomial18RegularSourcePolynomial.natDegree ≤ 69 := by
  unfold fourCellOddP51Polynomial18RegularSourcePolynomial
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply natDegree_le_sixtyNine_of_le_seventy_of_odd
  · exact (natDegree_factorTwoPolynomialLagK_le _ _).trans (by
      have hq :=
        natDegree_fourCellOddP51Polynomial18RegularLagPolynomial_le
      have hp := natDegree_fourCellOddQ51Polynomial_le
      omega)
  · intro x
    change (factorTwoPolynomialLagK
        fourCellOddP51Polynomial18RegularLagPolynomial
        fourCellOddQ51Polynomial).eval (-x) =
      -(factorTwoPolynomialLagK
        fourCellOddP51Polynomial18RegularLagPolynomial
        fourCellOddQ51Polynomial).eval x
    rw [eval_factorTwoPolynomialLagK, eval_factorTwoPolynomialLagK]
    exact ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural.odd_factorTwoContinuousLagK_of_odd
      fourCellOddP51Polynomial18RegularLagPolynomial.eval
      fourCellOddQ51Polynomial.eval odd_fourCellOddQ51Polynomial_eval x

/-- Pullback of the centered odd regular-row polynomial along `x = 2t-1`.
This is the coordinate system in which a centered `P53+` residual is a
shifted-Legendre Hilbert tail. -/
def fourCellOddP51Polynomial18RegularSourceUnitPolynomial : ℝ[X] :=
  fourCellOddP51Polynomial18RegularSourcePolynomial.comp
    ((2 : ℝ) • X - C 1)

theorem fourCellOddP51Polynomial18RegularSourceUnitPolynomial_eval
    (t : ℝ) :
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval t =
      (-2 * fourCellOperatorHalfWidth) *
        factorTwoContinuousLagK
          fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
          (2 * t - 1) := by
  unfold fourCellOddP51Polynomial18RegularSourceUnitPolynomial
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_X, Polynomial.eval_C,
    fourCellOddP51Polynomial18RegularSourcePolynomial_eval]
  simp only [smul_eq_mul]

theorem natDegree_fourCellOddP51Polynomial18RegularSourceUnitPolynomial_le :
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial.natDegree ≤ 69 := by
  have haff : (((2 : ℝ) • X - C 1 : ℝ[X]).natDegree) ≤ 1 := by
    compute_degree
  unfold fourCellOddP51Polynomial18RegularSourceUnitPolynomial
  calc
    (fourCellOddP51Polynomial18RegularSourcePolynomial.comp
        ((2 : ℝ) • X - C 1)).natDegree ≤
        fourCellOddP51Polynomial18RegularSourcePolynomial.natDegree *
          ((2 : ℝ) • X - C 1 : ℝ[X]).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ 69 * 1 := Nat.mul_le_mul
      natDegree_fourCellOddP51Polynomial18RegularSourcePolynomial_le haff
    _ = 69 := by norm_num

theorem fourCellOddP51Polynomial18RegularSourceUnitPolynomial_eval_one_sub
    (t : ℝ) :
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval (1 - t) =
      -fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval t := by
  unfold fourCellOddP51Polynomial18RegularSourceUnitPolynomial
  simp only [Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_C,
    smul_eq_mul]
  rw [show 2 * (1 - t) - 1 = -(2 * t - 1) by ring]
  exact odd_fourCellOddP51Polynomial18RegularSourcePolynomial_eval (2 * t - 1)

/-- Full unit-interval `L²` source of the polynomial regular row, in
centered-pullback coordinates. -/
def fourCellOddP51Polynomial18RegularSourceL2 : UnitIntervalL2 :=
  polynomialToL2
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial

/-- Exact `P53+` part of the polynomial regular row. -/
def fourCellOddP51Polynomial18RegularP53PlusL2 : UnitIntervalL2 :=
  fourCellOddP51Polynomial18RegularSourceL2 -
    shiftedLegendrePartialProjection
      fourCellOddP51Polynomial18RegularSourceL2 53

private theorem repr_shiftedLegendrePartialProjection
    (F : UnitIntervalL2) (N n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        (shiftedLegendrePartialProjection F N) n =
      if n < N then shiftedLegendreHilbertBasis.repr F n else 0 := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply]
  unfold shiftedLegendrePartialProjection
  rw [inner_sum]
  by_cases hn : n < N
  · rw [if_pos hn]
    have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n n)]
      simp
    · intro b hb hbn
      rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n b),
        if_neg (Ne.symm hbn)]
      simp
    · exact fun hnnot ↦ (hnnot hnmem).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    rw [inner_smul_right,
      (orthonormal_iff_ite.mp
        shiftedLegendreHilbertBasis.orthonormal n b)]
    rw [if_neg]
    · simp
    · intro hnb
      subst b
      exact hn (Finset.mem_range.mp hb)

theorem repr_fourCellOddP51Polynomial18RegularP53PlusL2 (n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularP53PlusL2 n =
      if n < 53 then 0 else
        shiftedLegendreHilbertBasis.repr
          fourCellOddP51Polynomial18RegularSourceL2 n := by
  unfold fourCellOddP51Polynomial18RegularP53PlusL2
  rw [shiftedLegendreHilbertBasis.repr_apply_apply, inner_sub_right,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    repr_shiftedLegendrePartialProjection]
  by_cases hn : n < 53 <;> simp [hn]

private theorem repr_polynomialToL2_eq_zero_of_natDegree_lt
    (p : ℝ[X]) (n : ℕ) (hp : p.natDegree < n) :
    shiftedLegendreHilbertBasis.repr (polynomialToL2 p) n = 0 := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm]
  change ‖shiftedLegendreL2 n‖⁻¹ *
      inner ℝ (polynomialToL2 p)
        (polynomialToL2 (shiftedLegendreReal n)) = 0
  rw [← integral_polynomial_mul_eq_inner]
  change ‖shiftedLegendreL2 n‖⁻¹ *
      (∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLegendreReal n).eval (t : ℝ)) = 0
  have hbridge :
      (∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ x : ℝ in 0..1,
          p.eval x * (shiftedLegendreReal n).eval x :=
    integral_unitInterval_eq_intervalIntegral
      (fun x : ℝ ↦ p.eval x * (shiftedLegendreReal n).eval x)
  rw [hbridge,
    integral_eval_mul_shiftedLegendreReal_eq_zero n p hp, mul_zero]

/-- No shifted-Legendre coordinate above degree `69` occurs in the full
polynomial regular source. -/
theorem repr_fourCellOddP51Polynomial18RegularSourceL2_eq_zero_of_sixtyNine_lt
    (n : ℕ) (hn : 69 < n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularSourceL2 n = 0 := by
  unfold fourCellOddP51Polynomial18RegularSourceL2
  apply repr_polynomialToL2_eq_zero_of_natDegree_lt
  exact natDegree_fourCellOddP51Polynomial18RegularSourceUnitPolynomial_le.trans_lt hn

/-- Centered oddness removes every even shifted-Legendre coordinate of the
full regular source. -/
theorem repr_fourCellOddP51Polynomial18RegularSourceL2_eq_zero_of_even
    (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularSourceL2 n = 0 := by
  unfold fourCellOddP51Polynomial18RegularSourceL2
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm]
  change ‖shiftedLegendreL2 n‖⁻¹ *
      inner ℝ
        (polynomialToL2
          fourCellOddP51Polynomial18RegularSourceUnitPolynomial)
        (polynomialToL2 (shiftedLegendreReal n)) = 0
  rw [← integral_polynomial_mul_eq_inner]
  suffices (∫ t : unitInterval,
      fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = 0 by
    rw [this, mul_zero]
  apply unitIntervalIntegral_eq_zero_of_symm_neg
  intro t
  have hleg :
      (shiftedLegendreReal n).eval (1 - (t : ℝ)) =
        (-1 : ℝ) ^ n * (shiftedLegendreReal n).eval (t : ℝ) := by
    simpa only [unitInterval.coe_symm_eq] using
      shiftedLegendreReal_eval_symm n t
  change
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval
          (unitInterval.symm t : ℝ) *
        (shiftedLegendreReal n).eval (unitInterval.symm t : ℝ) =
      -(fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ))
  rw [unitInterval.coe_symm_eq,
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial_eval_one_sub,
    hleg, hn.neg_one_pow]
  ring

theorem repr_fourCellOddP51Polynomial18RegularP53PlusL2_eq_zero_of_even
    (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularP53PlusL2 n = 0 := by
  rw [repr_fourCellOddP51Polynomial18RegularP53PlusL2]
  split_ifs
  · rfl
  · exact
      repr_fourCellOddP51Polynomial18RegularSourceL2_eq_zero_of_even n hn

theorem repr_fourCellOddP51Polynomial18RegularP53PlusL2_eq_zero_of_sixtyNine_lt
    (n : ℕ) (hn : 69 < n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularP53PlusL2 n = 0 := by
  rw [repr_fourCellOddP51Polynomial18RegularP53PlusL2, if_neg (by omega)]
  exact
    repr_fourCellOddP51Polynomial18RegularSourceL2_eq_zero_of_sixtyNine_lt n hn

/-- The exact finite shifted-Legendre packet left by the polynomial source
after the `P53` cutoff. -/
def fourCellOddP51Polynomial18RegularP53P69PacketL2 : UnitIntervalL2 :=
  ∑ n ∈ Finset.Ico 53 70,
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularSourceL2 n •
      shiftedLegendreHilbertBasis n

private theorem repr_fourCellOddP51Polynomial18RegularP53P69PacketL2
    (n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51Polynomial18RegularP53P69PacketL2 n =
      if n ∈ Finset.Ico 53 70 then
        shiftedLegendreHilbertBasis.repr
          fourCellOddP51Polynomial18RegularSourceL2 n
      else 0 := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply]
  unfold fourCellOddP51Polynomial18RegularP53P69PacketL2
  rw [inner_sum]
  by_cases hn : n ∈ Finset.Ico 53 70
  · rw [if_pos hn, Finset.sum_eq_single n]
    · rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n n)]
      simp
    · intro b hb hbn
      rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n b),
        if_neg (Ne.symm hbn)]
      simp
    · exact fun hnnot ↦ (hnnot hn).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    rw [inner_smul_right,
      (orthonormal_iff_ite.mp
        shiftedLegendreHilbertBasis.orthonormal n b)]
    rw [if_neg]
    · simp
    · intro hnb
      subst b
      exact hn hb

/-- The projected polynomial tail is exactly the finite packet of degrees
`53` through `69`; there is no infinite remainder. -/
theorem fourCellOddP51Polynomial18RegularP53PlusL2_eq_packet :
    fourCellOddP51Polynomial18RegularP53PlusL2 =
      fourCellOddP51Polynomial18RegularP53P69PacketL2 := by
  apply shiftedLegendreHilbertBasis.repr.injective
  ext n
  rw [repr_fourCellOddP51Polynomial18RegularP53PlusL2,
    repr_fourCellOddP51Polynomial18RegularP53P69PacketL2]
  by_cases hnlow : n < 53
  · have hnnot : n ∉ Finset.Ico 53 70 := by
      intro hnmem
      have hbounds := Finset.mem_Ico.mp hnmem
      omega
    rw [if_pos hnlow, if_neg hnnot]
  · rw [if_neg hnlow]
    by_cases hnhigh : n < 70
    · have hnmem : n ∈ Finset.Ico 53 70 :=
        Finset.mem_Ico.mpr ⟨by omega, hnhigh⟩
      rw [if_pos hnmem]
    · have hnnot : n ∉ Finset.Ico 53 70 := by
        intro hnmem
        exact hnhigh (Finset.mem_Ico.mp hnmem).2
      rw [if_neg hnnot]
      · exact
          repr_fourCellOddP51Polynomial18RegularSourceL2_eq_zero_of_sixtyNine_lt
            n (by omega)

/-- Finite Parseval norm of the polynomial `P53`--`P69` packet. -/
theorem norm_sq_fourCellOddP51Polynomial18RegularP53PlusL2_eq_finiteSum :
    ‖fourCellOddP51Polynomial18RegularP53PlusL2‖ ^ 2 =
      ∑ n ∈ Finset.Ico 53 70,
        (shiftedLegendreHilbertBasis.repr
          fourCellOddP51Polynomial18RegularSourceL2 n) ^ 2 := by
  rw [fourCellOddP51Polynomial18RegularP53PlusL2_eq_packet]
  have hinner := shiftedLegendreHilbertBasis.orthonormal.inner_sum
    (fun n ↦ shiftedLegendreHilbertBasis.repr
      fourCellOddP51Polynomial18RegularSourceL2 n)
    (fun n ↦ shiftedLegendreHilbertBasis.repr
      fourCellOddP51Polynomial18RegularSourceL2 n)
    (Finset.Ico 53 70)
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [fourCellOddP51Polynomial18RegularP53P69PacketL2,
    RCLike.star_def, RCLike.conj_to_real, map_id, id_eq, pow_two] using hinner

private theorem inner_shiftedLegendrePartialProjection_eq_zero_of_tail
    (F R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ (shiftedLegendrePartialProjection F 53) R = 0 := by
  unfold shiftedLegendrePartialProjection
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro n hn
  rw [real_inner_smul_left,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    hR n (Finset.mem_range.mp hn), mul_zero]

/-- Removing the low projection preserves the regular-row pairing against
every genuine `P53+` Hilbert tail. -/
theorem inner_fourCellOddP51Polynomial18RegularSourceL2_eq_P53PlusL2
    (R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ fourCellOddP51Polynomial18RegularSourceL2 R =
      inner ℝ fourCellOddP51Polynomial18RegularP53PlusL2 R := by
  unfold fourCellOddP51Polynomial18RegularP53PlusL2
  rw [inner_sub_left,
    inner_shiftedLegendrePartialProjection_eq_zero_of_tail _ R hR,
    sub_zero]

/-- Exact finite-band Cauchy bound for the polynomial regular row. -/
theorem sq_inner_fourCellOddP51Polynomial18RegularSourceL2_le_finiteSum
    (R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ fourCellOddP51Polynomial18RegularSourceL2 R ^ 2 ≤
      (∑ n ∈ Finset.Ico 53 70,
        (shiftedLegendreHilbertBasis.repr
          fourCellOddP51Polynomial18RegularSourceL2 n) ^ 2) * ‖R‖ ^ 2 := by
  rw [inner_fourCellOddP51Polynomial18RegularSourceL2_eq_P53PlusL2 R hR]
  have hinner := abs_real_inner_le_norm
    fourCellOddP51Polynomial18RegularP53PlusL2 R
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  rw [sq_abs, mul_pow,
    norm_sq_fourCellOddP51Polynomial18RegularP53PlusL2_eq_finiteSum]
    at hsquare
  exact hsquare

/-- The centered-pullback Hilbert source pairs exactly as the positive-half
degree-eighteen regular density.  Oddness is what removes the factor two
introduced by the affine pullback. -/
theorem inner_fourCellOddP51Polynomial18RegularSourceL2_centeredPullbackL2
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    inner ℝ fourCellOddP51Polynomial18RegularSourceL2
        (centeredPullbackL2 r hr) =
      ∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x := by
  let S : ℝ → ℝ := fun x ↦
    (-2 * fourCellOperatorHalfWidth) *
      factorTwoContinuousLagK
        fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x
  have hScont : Continuous S := by
    dsimp only [S]
    exact (continuous_factorTwoContinuousLagK
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
      (by
        simpa only [fourCellOddP51Polynomial18RegularLagKernel] using
          continuous_fourCellOddP51Polynomial18RegularLagKernel)
      contDiff_fourCellOddQ51.continuous).const_mul _
  have hSodd : Function.Odd S := by
    intro x
    dsimp only [S]
    rw [ArithmeticHodge.Analysis.YoshidaFactorTwoPolynomialLagRepresenterStructural.odd_factorTwoContinuousLagK_of_odd
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
      odd_fourCellOddQ51 x]
    ring
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  have hf : MemLp f 2 := by
    simpa only [f] using centeredPullback_memLp_two r hr
  have hpair := integral_mul_polynomial_eq_inner f hf
    fourCellOddP51Polynomial18RegularSourceUnitPolynomial
  have hpair' :
      (∫ t : unitInterval,
        f t *
          fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval
            (t : ℝ)) =
        inner ℝ (centeredPullbackL2 r hr)
          fourCellOddP51Polynomial18RegularSourceL2 := by
    simpa only [f, centeredPullbackL2,
      fourCellOddP51Polynomial18RegularSourceL2] using hpair
  have hintegrand :
      (fun t : unitInterval ↦
        f t *
          fourCellOddP51Polynomial18RegularSourceUnitPolynomial.eval
            (t : ℝ)) =
      fun t : unitInterval ↦
        r (2 * (t : ℝ) - 1) * S (2 * (t : ℝ) - 1) := by
    funext t
    unfold f centeredPullback
    rw [fourCellOddP51Polynomial18RegularSourceUnitPolynomial_eval]
  rw [hintegrand] at hpair'
  have hbridge :
      (∫ t : unitInterval,
        r (2 * (t : ℝ) - 1) * S (2 * (t : ℝ) - 1)) =
      ∫ t : ℝ in 0..1,
        r (2 * t - 1) * S (2 * t - 1) :=
    integral_unitInterval_eq_intervalIntegral
      (fun t : ℝ ↦ r (2 * t - 1) * S (2 * t - 1))
  rw [hbridge] at hpair'
  have hchange := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ r x * S x)
  rw [hchange] at hpair'
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ r x * S x)
    ((hr.mul hScont).intervalIntegrable _ _)
    (by
      intro x
      change r (-x) * S (-x) = r x * S x
      rw [hodd x, hSodd x]
      ring)
  rw [hfold] at hpair'
  calc
    inner ℝ fourCellOddP51Polynomial18RegularSourceL2
        (centeredPullbackL2 r hr) =
        inner ℝ (centeredPullbackL2 r hr)
          fourCellOddP51Polynomial18RegularSourceL2 :=
      real_inner_comm _ _
    _ = (1 / 2 : ℝ) *
        (2 * ∫ x : ℝ in 0..1, r x * S x) := hpair'.symm
    _ = ∫ x : ℝ in 0..1, S x * r x := by
      rw [show (∫ x : ℝ in 0..1, r x * S x) =
          ∫ x : ℝ in 0..1, S x * r x by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring]
      ring

/-- Exact production pairing of the finite `P53`--`P69` packet against a
smooth odd residual satisfying all retained moment conditions. -/
theorem inner_fourCellOddP51Polynomial18RegularP53PlusL2_centeredPullbackL2
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    inner ℝ fourCellOddP51Polynomial18RegularP53PlusL2
        (centeredPullbackL2 r hr.continuous) =
      ∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x := by
  rw [← inner_fourCellOddP51Polynomial18RegularSourceL2_eq_P53PlusL2
    (centeredPullbackL2 r hr.continuous)
    (oddP53PlusHilbertTail_centeredPullbackL2 r hr hodd htail)]
  exact inner_fourCellOddP51Polynomial18RegularSourceL2_centeredPullbackL2
    r hr.continuous hodd

/-- Production-normalized Cauchy bound for the exact polynomial regular
row.  Its scalar is a finite sum over the surviving degrees only. -/
theorem sq_integral_fourCellOddP51Polynomial18RegularRow_le_finiteSum
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    (∫ x : ℝ in 0..1,
      ((-2 * fourCellOperatorHalfWidth) *
        factorTwoContinuousLagK
          fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
        r x) ^ 2 ≤
      (∑ n ∈ Finset.Ico 53 70,
        (shiftedLegendreHilbertBasis.repr
          fourCellOddP51Polynomial18RegularSourceL2 n) ^ 2) *
        ∫ x : ℝ in 0..1, r x ^ 2 := by
  have hbound :=
    sq_inner_fourCellOddP51Polynomial18RegularSourceL2_le_finiteSum
      (centeredPullbackL2 r hr.continuous)
      (oddP53PlusHilbertTail_centeredPullbackL2 r hr hodd htail)
  rw [inner_fourCellOddP51Polynomial18RegularSourceL2_centeredPullbackL2
      r hr.continuous hodd,
    norm_sq_centeredPullbackL2_eq_zero_one_of_odd
      r hr.continuous hodd] at hbound
  exact hbound

private theorem inner_shiftedLegendrePartialProjection_eq_partialNormSq
    (F : UnitIntervalL2) (N : ℕ) :
    inner ℝ F (shiftedLegendrePartialProjection F N) =
      shiftedLegendrePartialNormSq F N := by
  rw [shiftedLegendrePartialProjection, inner_sum,
    shiftedLegendrePartialNormSq]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [real_inner_smul_right]
  have hrepr : inner ℝ F (shiftedLegendreHilbertBasis n) =
      shiftedLegendreHilbertBasis.repr F n := by
    rw [real_inner_comm]
    exact (shiftedLegendreHilbertBasis.repr_apply_apply F n).symm
  rw [hrepr]
  ring

/-- Pythagorean norm after deleting all degrees below `53`. -/
theorem norm_sq_fourCellOddP51Polynomial18RegularP53PlusL2 :
    ‖fourCellOddP51Polynomial18RegularP53PlusL2‖ ^ 2 =
      ‖fourCellOddP51Polynomial18RegularSourceL2‖ ^ 2 -
        shiftedLegendrePartialNormSq
          fourCellOddP51Polynomial18RegularSourceL2 53 := by
  unfold fourCellOddP51Polynomial18RegularP53PlusL2
  rw [norm_sub_sq_real,
    inner_shiftedLegendrePartialProjection_eq_partialNormSq,
    norm_sq_shiftedLegendrePartialProjection]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51Polynomial18TailStructural
