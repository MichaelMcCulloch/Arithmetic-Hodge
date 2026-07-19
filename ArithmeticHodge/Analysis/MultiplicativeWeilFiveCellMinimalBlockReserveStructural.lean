import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilMinimalBlockEndpointEliminationStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The coupled endpoint obstruction in a minimal negative five-cell block

For a five-cell block write `a`, `m`, and `e` for its first cell, middle
three cells, and last cell.  Minimality does more than make the two adjacent
four-cell blocks nonnegative.  At the two endpoint cuts it forces the same
remote corner `X = Re cross(a,e)` to turn both endpoint--middle crosses into
strict Schur reversals.

The theorem below records this simultaneous constraint and substitutes the
exact production identity

`X = Re local(a,e) - log 2 * Re prime₂(a,e)`.

Thus the sign obstruction to a universal positive local cross does not end
the five-cell route: a genuine minimal counterexample would have to satisfy
two coupled determinant reversals with one and the same local-minus-prime
corner.
-/

/-- The exact local-minus-prime value of the remote endpoint corner. -/
def fiveCellRemoteEndpointBalance (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriLocalCriticalForm
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re -
    Real.log 2 *
      (bombieriQuadraticCrossTest
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 4)) 2).re

/-- The remote global corner is exactly its local-minus-prime balance. -/
theorem fiveCell_remoteEndpointGlobalCross_re_eq_balance
    (parent : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re =
        fiveCellRemoteEndpointBalance parent k := by
  have h :=
    two_mul_fiveCell_remoteEndpointGlobalCross_re_eq_local_sub_prime parent k
  unfold fiveCellRemoteEndpointBalance
  linarith

/-- The physical middle three cells of a five-cell block. -/
def fiveCellMiddleThree (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterCell parent (k + 1) +
    monotoneQuarterCell parent (k + 2) +
      monotoneQuarterCell parent (k + 3)

/-- The two near entries in the left endpoint row. -/
def fiveCellLeftNearCross (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 1))).re +
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 2))).re

/-- The two near entries in the right endpoint row. -/
def fiveCellRightNearCross (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent (k + 2))
      (monotoneQuarterCell parent (k + 4))).re +
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent (k + 3))
      (monotoneQuarterCell parent (k + 4))).re

/-- Exact common-parent row at the left endpoint: two near Gram entries and
the lag-three corrected-Chebyshev contribution. -/
theorem fiveCell_leftEndpointMiddleCross_re_eq_near_add_chebyshev
    (parent : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (fiveCellMiddleThree parent k)).re =
        fiveCellLeftNearCross parent k +
          monotoneQuarterFarChebyshevContribution parent k 3 := by
  rw [fiveCellMiddleThree,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    Complex.add_re, Complex.add_re,
    monotoneQuarterCell_far_globalCross_re_eq_contribution
      parent k 3 (by omega)]
  rfl

/-- Exact common-parent row at the right endpoint.  Its far entry begins one
cell later, while the remaining two entries are the reversed near row. -/
theorem fiveCell_middleRightEndpointCross_re_eq_chebyshev_add_near
    (parent : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (fiveCellMiddleThree parent k)
      (monotoneQuarterCell parent (k + 4))).re =
        monotoneQuarterFarChebyshevContribution parent (k + 1) 3 +
          fiveCellRightNearCross parent k := by
  rw [fiveCellMiddleThree,
    bombieriTwoBlockGlobalCrossSymbol_add_left,
    bombieriTwoBlockGlobalCrossSymbol_add_left,
    Complex.add_re, Complex.add_re]
  have hfar := monotoneQuarterCell_far_globalCross_re_eq_contribution
    parent (k + 1) 3 (by omega)
  rw [show k + 1 + 3 = k + 4 by ring] at hfar
  rw [hfar]
  unfold fiveCellRightNearCross
  ring

/-- The same local-minus-prime remote balance is exactly the lag-four
corrected-Chebyshev contribution. -/
theorem fiveCellRemoteEndpointBalance_eq_farChebyshevContribution
    (parent : BombieriTest) (k : ℤ) :
    fiveCellRemoteEndpointBalance parent k =
      monotoneQuarterFarChebyshevContribution parent k 4 := by
  rw [← fiveCell_remoteEndpointGlobalCross_re_eq_balance]
  exact monotoneQuarterCell_far_globalCross_re_eq_contribution
    parent k 4 (by omega)

private theorem finiteBlock_one_eq_cell
    (parent : BombieriTest) (lo : ℤ) (start offset : ℕ) :
    monotoneQuarterFiniteBlock parent lo (start + offset) 1 =
      monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start + (offset : ℤ)) := by
  rw [monotoneQuarterFiniteBlock_one]
  congr 1
  unfold monotoneQuarterFiniteBlockBase
  push_cast
  ring

private theorem finiteBlock_four_from_middle_right
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo (start + 1) 4 =
      monotoneQuarterFiniteBlock parent lo (start + 1) 3 +
        monotoneQuarterFiniteBlock parent lo (start + 4) 1 := by
  have h := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + 1) 4 3 (by omega)
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using h

private theorem finiteBlock_four_from_left_middle
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 4 =
      monotoneQuarterFiniteBlock parent lo start 1 +
        monotoneQuarterFiniteBlock parent lo (start + 1) 3 := by
  have h := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start 4 1 (by omega)
  simpa only [Nat.add_sub_cancel] using h

/-- Scalar form of the simultaneous endpoint-cut constraints forced by a
minimal negative five-cell block.  Here `A,M,E` are the three diagonal
values, `U,V` are the two endpoint--middle crosses, and `X` is the single
remote endpoint corner. -/
def FiveCellCoupledEndpointSchurConstraints
    (A M E U V X : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ E ∧
    0 ≤ A + M + 2 * U ∧
    0 ≤ M + E + 2 * V ∧
    U + X < -(A + (M + E + 2 * V)) / 2 ∧
    A * (M + E + 2 * V) < (U + X) ^ 2 ∧
    V + X < -((A + M + 2 * U) + E) / 2 ∧
    (A + M + 2 * U) * E < (V + X) ^ 2 ∧
    A + M + E + 2 * (U + V + X) < 0

/-- Determinant of the exact real three-block matrix on
`(left endpoint, middle three cells, right endpoint)`. -/
def fiveCellThreeBlockDeterminant (A M E U V X : ℝ) : ℝ :=
  A * M * E + 2 * U * V * X - A * V ^ 2 - M * X ^ 2 - E * U ^ 2

/-- The actual three-block determinant cut from one five-cell common parent. -/
def fiveCellCommonParentThreeBlockDeterminant
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  fiveCellThreeBlockDeterminant
    (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
    (bombieriRealQuadraticValue (fiveCellMiddleThree parent k))
    (bombieriRealQuadraticValue (monotoneQuarterCell parent (k + 4)))
    ((bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (fiveCellMiddleThree parent k)).re)
    ((bombieriTwoBlockGlobalCrossSymbol
      (fiveCellMiddleThree parent k)
      (monotoneQuarterCell parent (k + 4))).re)
    ((bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re)

/-- Lossless arithmetic expansion of the genuine common-parent determinant.
Only four signed ingredients remain beyond the three diagonals: two near
rows and the corrected-Chebyshev contributions at lags three, three, and
four. -/
theorem fiveCellCommonParentThreeBlockDeterminant_eq_near_chebyshev
    (parent : BombieriTest) (k : ℤ) :
    fiveCellCommonParentThreeBlockDeterminant parent k =
      fiveCellThreeBlockDeterminant
        (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
        (bombieriRealQuadraticValue (fiveCellMiddleThree parent k))
        (bombieriRealQuadraticValue (monotoneQuarterCell parent (k + 4)))
        (fiveCellLeftNearCross parent k +
          monotoneQuarterFarChebyshevContribution parent k 3)
        (monotoneQuarterFarChebyshevContribution parent (k + 1) 3 +
          fiveCellRightNearCross parent k)
        (monotoneQuarterFarChebyshevContribution parent k 4) := by
  unfold fiveCellCommonParentThreeBlockDeterminant
  rw [fiveCell_leftEndpointMiddleCross_re_eq_near_add_chebyshev,
    fiveCell_middleRightEndpointCross_re_eq_chebyshev_add_near,
    fiveCell_remoteEndpointGlobalCross_re_eq_balance,
    fiveCellRemoteEndpointBalance_eq_farChebyshevContribution]

private theorem middlePivot_determinant_identity
    (A M E U V X : ℝ) :
    (A * M - U ^ 2) * (M * E - V ^ 2) - (M * X - U * V) ^ 2 =
      M * fiveCellThreeBlockDeterminant A M E U V X := by
  unfold fiveCellThreeBlockDeterminant
  ring

private theorem middlePivot_quadratic_identity
    (A M E U V X : ℝ) :
    M * (A + M + E + 2 * (U + V + X)) =
      (M + U + V) ^ 2 +
        (A * M - U ^ 2) + (M * E - V ^ 2) +
          2 * (M * X - U * V) := by
  ring

private theorem two_by_two_quadratic_nonnegative
    {A E X : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hdet : X ^ 2 ≤ A * E) :
    0 ≤ A + E + 2 * X := by
  nlinarith [sq_nonneg (A - E), sq_nonneg (A + E + 2 * X)]

/-- All principal minors, including the full determinant, make the exact
three-block quadratic nonnegative.  This is the pivot-free semidefinite
closure needed at five cells; the proof also handles a zero middle diagonal.
-/
theorem threeBlockQuadratic_nonnegative_of_principalMinors_and_determinant
    {A M E U V X : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hAE : X ^ 2 ≤ A * E)
    (hdet : 0 ≤ fiveCellThreeBlockDeterminant A M E U V X) :
    0 ≤ A + M + E + 2 * (U + V + X) := by
  by_cases hMzero : M = 0
  · have hU : U = 0 := by
      rw [hMzero, mul_zero] at hAM
      nlinarith [sq_nonneg U]
    have hV : V = 0 := by
      rw [hMzero, zero_mul] at hME
      nlinarith [sq_nonneg V]
    rw [hMzero, hU, hV]
    simpa only [add_zero, zero_add] using
      two_by_two_quadratic_nonnegative hA hE hAE
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    let alpha : ℝ := A * M - U ^ 2
    let beta : ℝ := M * E - V ^ 2
    let delta : ℝ := M * X - U * V
    have halpha : 0 ≤ alpha := by
      dsimp only [alpha]
      linarith
    have hbeta : 0 ≤ beta := by
      dsimp only [beta]
      linarith
    have hdelta : delta ^ 2 ≤ alpha * beta := by
      have hid := middlePivot_determinant_identity A M E U V X
      dsimp only [alpha, beta, delta]
      nlinarith [mul_nonneg hM hdet]
    have hschur : 0 ≤ alpha + beta + 2 * delta := by
      nlinarith [sq_nonneg (alpha - beta),
        sq_nonneg (alpha + beta + 2 * delta)]
    have hidentity := middlePivot_quadratic_identity A M E U V X
    dsimp only [alpha, beta, delta] at hschur
    nlinarith [sq_nonneg (M + U + V)]

/-- If all three pairwise Schur bounds hold in a minimal five-cell scalar
configuration, then the genuinely three-way determinant must be strictly
negative.  This isolates the next analytic common-parent relation exactly. -/
theorem FiveCellCoupledEndpointSchurConstraints.threeBlockDeterminant_neg_of_pairwise
    {A M E U V X : ℝ}
    (h : FiveCellCoupledEndpointSchurConstraints A M E U V X)
    (hAM : U ^ 2 ≤ A * M)
    (hME : V ^ 2 ≤ M * E)
    (hAE : X ^ 2 ≤ A * E) :
    fiveCellThreeBlockDeterminant A M E U V X < 0 := by
  rcases h with
    ⟨hA, hM, hE, _hL, _hR, _hleftMean, _hleftDet,
      _hrightMean, _hrightDet, hwhole⟩
  by_contra hnot
  have hdet : 0 ≤ fiveCellThreeBlockDeterminant A M E U V X :=
    le_of_not_gt hnot
  have hnonnegative :=
    threeBlockQuadratic_nonnegative_of_principalMinors_and_determinant
      hA hM hE hAM hME hAE hdet
  exact (not_lt_of_ge hnonnegative) hwhole

/-- Geometric-mean form of the two strict Schur reversals.  This extracts the
sharp signed information from the squared determinant inequalities: the
remote-corrected endpoint rows lie strictly below the negative square roots
of their two diagonal products. -/
theorem FiveCellCoupledEndpointSchurConstraints.twoSidedGeometricDeficit
    {A M E U V X : ℝ}
    (h : FiveCellCoupledEndpointSchurConstraints A M E U V X) :
    Real.sqrt (A * (M + E + 2 * V)) < -(U + X) ∧
      Real.sqrt ((A + M + 2 * U) * E) < -(V + X) := by
  rcases h with
    ⟨hA, _hM, hE, hL, hR, hleftMean, hleftDet,
      hrightMean, hrightDet, _hwhole⟩
  have hleftNeg : U + X < 0 := by
    nlinarith
  have hrightNeg : V + X < 0 := by
    nlinarith
  have hleftProduct : 0 ≤ A * (M + E + 2 * V) :=
    mul_nonneg hA hR
  have hrightProduct : 0 ≤ (A + M + 2 * U) * E :=
    mul_nonneg hL hE
  have hleftSqrt := Real.sq_sqrt hleftProduct
  have hrightSqrt := Real.sq_sqrt hrightProduct
  have hleftSqrtNonneg :=
    Real.sqrt_nonneg (A * (M + E + 2 * V))
  have hrightSqrtNonneg :=
    Real.sqrt_nonneg ((A + M + 2 * U) * E)
  constructor <;> nlinarith

/-- In a support-minimal negative block of length five, both endpoint cuts
strictly reverse their Schur determinants after insertion of the same exact
local-minus-prime remote corner.  The adjacent four-cell diagonals are
expanded losslessly into the endpoint, middle-three, and near-cross terms.
-/
theorem supportMinimalNegativeMonotoneBlock_length_five_coupledEndpointSchur
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlock parent lo (start + 1) 3
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    FiveCellCoupledEndpointSchurConstraints A M E U V X := by
  dsimp only
  unfold FiveCellCoupledEndpointSchurConstraints
  let k := monotoneQuarterFiniteBlockBase lo start
  let a : BombieriTest := monotoneQuarterCell parent k
  let m : BombieriTest :=
    monotoneQuarterFiniteBlock parent lo (start + 1) 3
  let e : BombieriTest := monotoneQuarterCell parent (k + 4)
  let A : ℝ := bombieriRealQuadraticValue a
  let M : ℝ := bombieriRealQuadraticValue m
  let E : ℝ := bombieriRealQuadraticValue e
  let U : ℝ := (bombieriTwoBlockGlobalCrossSymbol a m).re
  let V : ℝ := (bombieriTwoBlockGlobalCrossSymbol m e).re
  let X : ℝ := fiveCellRemoteEndpointBalance parent k
  have hlen4 : 4 ≤ len :=
    four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have haBlock : monotoneQuarterFiniteBlock parent lo start 1 = a := by
    dsimp only [a, k]
    simpa only [zero_add, Int.ofNat_zero, add_zero] using
      finiteBlock_one_eq_cell parent lo start 0
  have heBlock : monotoneQuarterFiniteBlock parent lo (start + 4) 1 = e := by
    dsimp only [e, k]
    exact finiteBlock_one_eq_cell parent lo start 4
  have haCell :
      monotoneQuarterCell parent
          (monotoneQuarterFiniteBlockBase lo start) = a := by
    rfl
  have heCell :
      monotoneQuarterCell parent
          (monotoneQuarterFiniteBlockBase lo (start + 4)) = e := by
    dsimp only [e, k]
    congr 1
    unfold monotoneQuarterFiniteBlockBase
    push_cast
    ring
  have hprefixBlock :
      monotoneQuarterFiniteBlock parent lo start 4 = a + m := by
    rw [finiteBlock_four_from_left_middle, haBlock]
  have hsuffixBlock :
      monotoneQuarterFiniteBlock parent lo (start + 1) 4 = m + e := by
    rw [finiteBlock_four_from_middle_right, heBlock]
  have hX :
      (bombieriTwoBlockGlobalCrossSymbol a e).re = X := by
    dsimp only [a, e, X, k]
    exact fiveCell_remoteEndpointGlobalCross_re_eq_balance parent
      (monotoneQuarterFiniteBlockBase lo start)
  have hA : 0 ≤ A := by
    dsimp only [A]
    rw [← haBlock]
    exact supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 1 (by omega) (by omega)
  have hM : 0 ≤ M := by
    dsimp only [M, m]
    exact supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 1 3 (by omega) (by omega)
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← heBlock]
    exact supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 4 1 (by omega) (by omega)
  have hprefix : 0 ≤ A + M + 2 * U := by
    have hp := supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 4 (by omega) (by omega)
    rw [show start + 0 = start by omega, hprefixBlock,
      bombieriRealQuadraticValue_add] at hp
    simpa only [A, M, U] using hp
  have hsuffix : 0 ≤ M + E + 2 * V := by
    have hs := supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 1 4 (by omega) (by omega)
    rw [hsuffixBlock, bombieriRealQuadraticValue_add] at hs
    simpa only [M, E, V] using hs
  have hleftCut :=
    supportMinimalNegativeMonotoneBlock_leftEndpoint_constraints hmin
  have hrightCut :=
    supportMinimalNegativeMonotoneBlock_rightEndpoint_constraints hmin
  have hleftCross :
      (bombieriTwoBlockGlobalCrossSymbol a (m + e)).re = U + X := by
    rw [bombieriTwoBlockGlobalCrossSymbol_add_right, Complex.add_re, hX]
  have hrightCross :
      (bombieriTwoBlockGlobalCrossSymbol (a + m) e).re = V + X := by
    rw [bombieriTwoBlockGlobalCrossSymbol_add_left, Complex.add_re, hX]
    ring
  have hleftMean : U + X < -(A + (M + E + 2 * V)) / 2 := by
    have h := hleftCut.cross_strictly_below_arithmeticMean
    simp only [hlen] at h
    norm_num at h
    rw [haCell, hsuffixBlock,
      hleftCross, bombieriRealQuadraticValue_add] at h
    dsimp only [A, M, E, V] at ⊢
    linarith
  have hleftDet : A * (M + E + 2 * V) < (U + X) ^ 2 := by
    have h := hleftCut.determinant_strictly_reversed
    simp only [hlen] at h
    norm_num at h
    rw [haCell, hsuffixBlock,
      hleftCross, bombieriRealQuadraticValue_add] at h
    simpa only [A, M, E, V] using h
  have hrightMean : V + X < -((A + M + 2 * U) + E) / 2 := by
    have h := hrightCut.cross_strictly_below_arithmeticMean
    simp only [hlen] at h
    norm_num at h
    rw [hprefixBlock, heCell,
      hrightCross, bombieriRealQuadraticValue_add] at h
    dsimp only [A, M, E, U] at ⊢
    linarith
  have hrightDet : (A + M + 2 * U) * E < (V + X) ^ 2 := by
    have h := hrightCut.determinant_strictly_reversed
    simp only [hlen] at h
    norm_num at h
    rw [hprefixBlock, heCell,
      hrightCross, bombieriRealQuadraticValue_add] at h
    simpa only [A, M, E, U] using h
  have hwhole : A + M + E + 2 * (U + V + X) < 0 := by
    have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent lo start 5 4 (by omega)
    norm_num at hsplit
    have hblock : monotoneQuarterFiniteBlock parent lo start len =
        (a + m) + e := by
      rw [hlen, hsplit, hprefixBlock, heCell]
    have hneg := hmin.negative
    rw [hblock, bombieriRealQuadraticValue_add,
      bombieriRealQuadraticValue_add,
      bombieriTwoBlockGlobalCrossSymbol_add_left,
      Complex.add_re, hX] at hneg
    dsimp only [A, M, E, U, V] at ⊢
    linarith
  exact ⟨hA, hM, hE, hprefix, hsuffix, hleftMean, hleftDet,
    hrightMean, hrightDet, hwhole⟩

/-- Sharp signed reserve forced at both ends of an actual minimal negative
five-cell block.  The same production local-minus-prime corner must lie below
both negative geometric means. -/
theorem supportMinimalNegativeMonotoneBlock_length_five_twoSidedGeometricDeficit
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) (hlen : len = 5) :
    let k := monotoneQuarterFiniteBlockBase lo start
    let a := monotoneQuarterCell parent k
    let m := monotoneQuarterFiniteBlock parent lo (start + 1) 3
    let e := monotoneQuarterCell parent (k + 4)
    let A := bombieriRealQuadraticValue a
    let M := bombieriRealQuadraticValue m
    let E := bombieriRealQuadraticValue e
    let U := (bombieriTwoBlockGlobalCrossSymbol a m).re
    let V := (bombieriTwoBlockGlobalCrossSymbol m e).re
    let X := fiveCellRemoteEndpointBalance parent k
    Real.sqrt (A * (M + E + 2 * V)) < -(U + X) ∧
      Real.sqrt ((A + M + 2 * U) * E) < -(V + X) := by
  have h :=
    supportMinimalNegativeMonotoneBlock_length_five_coupledEndpointSchur
      hmin hlen
  exact FiveCellCoupledEndpointSchurConstraints.twoSidedGeometricDeficit h

/-!
The coupled determinant information is strictly stronger than the bare
overlap signs, but it still cannot by itself sign the remote corner.  The
following exact rational model satisfies every scalar consequence above with
`X > 0`.  Hence a length-five contradiction needs an analytic common-parent
relation between `U`, `V`, and the local-minus-prime value `X`; the two
endpoint-cut consequences alone cannot supply a sign.
-/

/-- Both endpoint arithmetic-mean and determinant reversals are compatible
with a strictly positive remote endpoint corner. -/
theorem coupledEndpointSchurConstraints_allow_positive_remote :
    ∃ A M E U V X : ℝ,
      FiveCellCoupledEndpointSchurConstraints A M E U V X ∧ 0 < X := by
  refine ⟨1, 4, 1, -(11 / 5), -(11 / 5), 1, ?_, by norm_num⟩
  unfold FiveCellCoupledEndpointSchurConstraints
  norm_num

/-- Even all three pairwise determinant bounds are compatible with the full
minimal five-cell deficit and a positive remote corner.  In this exact model
the two adjacent minors vanish, the endpoint minor is positive, and only the
genuinely three-way determinant detects negativity. -/
theorem coupledEndpointSchurConstraints_allow_all_pairwiseSchur_but_not_threeBlock :
    ∃ A M E U V X : ℝ,
      FiveCellCoupledEndpointSchurConstraints A M E U V X ∧
        U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E ∧ X ^ 2 ≤ A * E ∧
        0 < X ∧ fiveCellThreeBlockDeterminant A M E U V X < 0 := by
  refine ⟨1, 1, 1, -1, -1, (2 / 5 : ℝ), ?_⟩
  unfold FiveCellCoupledEndpointSchurConstraints
    fiveCellThreeBlockDeterminant
  norm_num

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural
