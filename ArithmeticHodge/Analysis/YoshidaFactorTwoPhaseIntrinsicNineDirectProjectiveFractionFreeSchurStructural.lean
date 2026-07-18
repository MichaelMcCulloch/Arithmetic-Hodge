import Mathlib.Algebra.Polynomial.Roots
import ArithmeticHodge.Analysis.FractionFreeSchurDeterminantStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveFractionFreeSchurStructural

noncomputable section

open FractionFreeSchurDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

/-!
# Fraction-free `6 + r` Schur determinants for the projective pencil

The first six retained coordinates are the strict production core.  Clearing
its determinant compresses each of the `7`, `8`, and `9` leading determinant
polynomials to a determinant of size at most three.
-/

/-- The affine polynomial matrix whose determinant is the public prefix
polynomial. -/
def factorTwoIntrinsicNineDirectPrefixPolynomialMatrix
    (k : ℕ) (hk : k ≤ 9) : Matrix (Fin k) (Fin k) ℝ[X] :=
  (X : ℝ[X]) •
      (factorTwoIntrinsicNineDirectDephasedLinear k hk).map C +
    (factorTwoIntrinsicNineDirectDephasedConstant k hk).map C

theorem factorTwoIntrinsicNineDirectPrefixPolynomialMatrix_det
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix k hk).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk := by
  rfl

private theorem factorTwoIntrinsicNineDirectDephasedConstant_castAdd
    (k r : ℕ) (hkr : k + r ≤ 9) :
    (factorTwoIntrinsicNineDirectDephasedConstant (k + r) hkr).submatrix
        (Fin.castAdd r) (Fin.castAdd r) =
      factorTwoIntrinsicNineDirectDephasedConstant k (by omega) := by
  classical
  ext i j
  have hcast (u : Fin k) :
      Fin.castLE hkr (Fin.castAdd r u) =
        Fin.castLE (by omega : k ≤ 9) u := by
    apply Fin.ext
    rfl
  simp [factorTwoIntrinsicNineDirectDephasedConstant,
    factorTwoIntrinsicNineDirectPrefixEven,
    factorTwoIntrinsicNineDirectPrefixPlus,
    factorTwoIntrinsicNineDirectPrefixAlternating,
    factorTwoIntrinsicNineDirectPrefix, hcast]

private theorem factorTwoIntrinsicNineDirectDephasedLinear_castAdd
    (k r : ℕ) (hkr : k + r ≤ 9) :
    (factorTwoIntrinsicNineDirectDephasedLinear (k + r) hkr).submatrix
        (Fin.castAdd r) (Fin.castAdd r) =
      factorTwoIntrinsicNineDirectDephasedLinear k (by omega) := by
  classical
  ext i j
  have hcast (u : Fin k) :
      Fin.castLE hkr (Fin.castAdd r u) =
        Fin.castLE (by omega : k ≤ 9) u := by
    apply Fin.ext
    rfl
  simp [factorTwoIntrinsicNineDirectDephasedLinear,
    factorTwoIntrinsicNineDirectPrefixEven,
    factorTwoIntrinsicNineDirectPrefixMinus,
    factorTwoIntrinsicNineDirectPrefixAlternating,
    factorTwoIntrinsicNineDirectPrefix, hcast]

private theorem factorTwoIntrinsicNineDirectPrefixPolynomialMatrix_castAdd
    (k r : ℕ) (hkr : k + r ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix (k + r) hkr).submatrix
        (Fin.castAdd r) (Fin.castAdd r) =
      factorTwoIntrinsicNineDirectPrefixPolynomialMatrix k (by omega) := by
  have hlinear := factorTwoIntrinsicNineDirectDephasedLinear_castAdd k r hkr
  have hconstant := factorTwoIntrinsicNineDirectDephasedConstant_castAdd k r hkr
  apply Matrix.ext
  intro i j
  have hlinearEntry :
      factorTwoIntrinsicNineDirectDephasedLinear (k + r) hkr
          (Fin.castAdd r i) (Fin.castAdd r j) =
        factorTwoIntrinsicNineDirectDephasedLinear k (by omega) i j := by
    simpa only [Matrix.submatrix_apply] using congrFun (congrFun hlinear i) j
  have hconstantEntry :
      factorTwoIntrinsicNineDirectDephasedConstant (k + r) hkr
          (Fin.castAdd r i) (Fin.castAdd r j) =
        factorTwoIntrinsicNineDirectDephasedConstant k (by omega) i j := by
    simpa only [Matrix.submatrix_apply] using congrFun (congrFun hconstant i) j
  simp only [factorTwoIntrinsicNineDirectPrefixPolynomialMatrix,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul]
  rw [hlinearEntry, hconstantEntry]

/-- Coordinate equivalence exposing the strict first six modes and a retained
tail of size `r`. -/
def factorTwoIntrinsicNineDirectSixTailEquiv (r : ℕ) :
    (Fin 6 ⊕ Fin r) ≃ Fin (6 + r) :=
  finSumFinEquiv

/-- Reindexed polynomial prefix in `6 + r` block form. -/
def factorTwoIntrinsicNineDirectSplitPolynomialMatrix
    (r : ℕ) (hr : 6 + r ≤ 9) :
    Matrix (Fin 6 ⊕ Fin r) (Fin 6 ⊕ Fin r) ℝ[X] :=
  (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix (6 + r) hr).submatrix
    (factorTwoIntrinsicNineDirectSixTailEquiv r)
    (factorTwoIntrinsicNineDirectSixTailEquiv r)

/-- Polynomial coupling from the strict six-mode core to the last `r`
coordinates. -/
def factorTwoIntrinsicNineDirectCoreTailPolynomialMatrix
    (r : ℕ) (hr : 6 + r ≤ 9) : Matrix (Fin 6) (Fin r) ℝ[X] :=
  (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr).submatrix
    Sum.inl Sum.inr

/-- Polynomial coupling from the last `r` coordinates back to the strict
six-mode core. -/
def factorTwoIntrinsicNineDirectTailCorePolynomialMatrix
    (r : ℕ) (hr : 6 + r ≤ 9) : Matrix (Fin r) (Fin 6) ℝ[X] :=
  (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr).submatrix
    Sum.inr Sum.inl

/-- Last `r × r` block of the polynomial prefix. -/
def factorTwoIntrinsicNineDirectTailPolynomialMatrix
    (r : ℕ) (hr : 6 + r ≤ 9) : Matrix (Fin r) (Fin r) ℝ[X] :=
  (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr).submatrix
    Sum.inr Sum.inr

/-- Exact `6 + r` polynomial block decomposition. -/
theorem factorTwoIntrinsicNineDirectSplitPolynomialMatrix_eq_fromBlocks
    (r : ℕ) (hr : 6 + r ≤ 9) :
    factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr =
      Matrix.fromBlocks
        (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix 6 (by omega))
        (factorTwoIntrinsicNineDirectCoreTailPolynomialMatrix r hr)
        (factorTwoIntrinsicNineDirectTailCorePolynomialMatrix r hr)
        (factorTwoIntrinsicNineDirectTailPolynomialMatrix r hr) := by
  have hcore :=
    factorTwoIntrinsicNineDirectPrefixPolynomialMatrix_castAdd 6 r hr
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa only [factorTwoIntrinsicNineDirectSplitPolynomialMatrix,
      factorTwoIntrinsicNineDirectSixTailEquiv,
      Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁] using
      congrFun (congrFun hcore i) j
  · rfl
  · rfl
  · rfl

theorem factorTwoIntrinsicNineDirectSplitPolynomialMatrix_det
    (r : ℕ) (hr : 6 + r ≤ 9) :
    (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
        (6 + r) hr := by
  rw [factorTwoIntrinsicNineDirectSplitPolynomialMatrix,
    Matrix.det_submatrix_equiv_self,
    factorTwoIntrinsicNineDirectPrefixPolynomialMatrix_det]

/-- Determinant of the strict six-mode affine core. -/
def factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix : ℝ[X] :=
  (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix 6 (by omega)).det

/-- The strict six-mode core determinant is positive on the complete
nonnegative projective half-line. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix_eval_pos
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix.eval x := by
  let t := Real.sqrt x
  have hxt : x = t ^ 2 := by
    dsimp only [t]
    exact (Real.sq_sqrt hx).symm
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix,
    factorTwoIntrinsicNineDirectPrefixPolynomialMatrix_det,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_eval 6
      (by omega) x,
    factorTwoIntrinsicNineDirectDephasedMatrix_det_eq_projectivePrefix
      6 (by omega) t x hxt]
  simpa only [hxt] using
    (factorTwoIntrinsicNineDirectProjectivePrefix_six_posDef t).det_pos

/-- Fraction-free Schur matrix for the final `r` retained coordinates. -/
def factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix
    (r : ℕ) (hr : 6 + r ≤ 9) : Matrix (Fin r) (Fin r) ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix •
      factorTwoIntrinsicNineDirectTailPolynomialMatrix r hr -
    factorTwoIntrinsicNineDirectTailCorePolynomialMatrix r hr *
      (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix 6
        (by omega)).adjugate *
      factorTwoIntrinsicNineDirectCoreTailPolynomialMatrix r hr

private theorem map_fractionFreeSchurMatrix
    {m n R S : Type*}
    [DecidableEq m] [Fintype m]
    [DecidableEq n] [Fintype n]
    [CommRing R] [CommRing S]
    (f : R →+* S)
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) :
    Matrix.map (A.det • D - C * A.adjugate * B) f =
      (Matrix.map A f).det • Matrix.map D f -
        Matrix.map C f * (Matrix.map A f).adjugate * Matrix.map B f := by
  have hdet : f A.det = (Matrix.map A f).det := by
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using f.map_det A
  have hadjugate :
      Matrix.map A.adjugate f = (Matrix.map A f).adjugate := by
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using
      f.map_adjugate A
  rw [Matrix.map_sub, Matrix.map_smul', Matrix.map_mul, Matrix.map_mul,
    hdet, hadjugate] <;> simp

private theorem map_fromBlocks
    {m n R S : Type*}
    [DecidableEq m] [Fintype m]
    [DecidableEq n] [Fintype n]
    [CommRing R] [CommRing S]
    (f : R →+* S)
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) :
    Matrix.map (Matrix.fromBlocks A B C D) f =
      Matrix.fromBlocks (Matrix.map A f) (Matrix.map B f)
        (Matrix.map C f) (Matrix.map D f) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

private theorem eval_det
    {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n ℝ[X]) (x : ℝ) :
    M.det.eval x = (Matrix.map M (Polynomial.evalRingHom x)).det := by
  change (Polynomial.evalRingHom x) M.det = _
  have hmap := (Polynomial.evalRingHom x).map_det M
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using hmap

/-- The determinant of the fraction-free `r × r` Schur matrix is the
`6 + r` prefix determinant, multiplied by the unavoidable power of the
strict six-mode determinant. -/
theorem factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix_det
    (r : ℕ) (hr0 : 0 < r) (hr : 6 + r ≤ 9) :
    (factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix r hr).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix ^ (r - 1) *
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
          (6 + r) hr := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr0
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro x hx
  simp only [Set.mem_setOf_eq]
  let f : ℝ[X] →+* ℝ := Polynomial.evalRingHom x
  let A0 : Matrix (Fin 6) (Fin 6) ℝ :=
    Matrix.map
      (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix 6 (by omega)) f
  let B0 : Matrix (Fin 6) (Fin r) ℝ :=
    Matrix.map (factorTwoIntrinsicNineDirectCoreTailPolynomialMatrix r hr) f
  let C0 : Matrix (Fin r) (Fin 6) ℝ :=
    Matrix.map (factorTwoIntrinsicNineDirectTailCorePolynomialMatrix r hr) f
  let D0 : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.map (factorTwoIntrinsicNineDirectTailPolynomialMatrix r hr) f
  have hAeval :
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix.eval x =
        A0.det := by
    dsimp only [A0, f]
    simpa only [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix] using
      eval_det
        (factorTwoIntrinsicNineDirectPrefixPolynomialMatrix 6 (by omega)) x
  have hApos : 0 < A0.det := by
    rw [← hAeval]
    exact factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix_eval_pos
      x hx
  have hblocksMap := congrArg
    (fun M ↦ Matrix.map M f)
    (factorTwoIntrinsicNineDirectSplitPolynomialMatrix_eq_fromBlocks r hr)
  dsimp only at hblocksMap
  rw [map_fromBlocks] at hblocksMap
  have hfullEval :
      (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
          (6 + r) hr).eval x =
        (Matrix.fromBlocks A0 B0 C0 D0).det := by
    calc
      (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
          (6 + r) hr).eval x =
          (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr).det.eval x := by
        rw [factorTwoIntrinsicNineDirectSplitPolynomialMatrix_det]
      _ = (Matrix.map
            (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr) f).det := by
        simpa only [f] using
          eval_det (factorTwoIntrinsicNineDirectSplitPolynomialMatrix r hr) x
      _ = (Matrix.fromBlocks A0 B0 C0 D0).det := by
        rw [hblocksMap]
  have hfractionFree := det_det_smul_sub_mul_adjugate_mul
    A0 B0 C0 D0 hApos.ne'
  calc
    (factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix r hr).det.eval x =
        (A0.det • D0 - C0 * A0.adjugate * B0).det := by
      rw [eval_det, factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix,
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix,
        map_fractionFreeSchurMatrix]
    _ = A0.det ^ (r - 1) *
        (Matrix.fromBlocks A0 B0 C0 D0).det := by
      simpa using hfractionFree
    _ = (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix ^ (r - 1) *
          factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
            (6 + r) hr).eval x := by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, hAeval, hfullEval]

/-- The seventh prefix determinant is one entry of the fraction-free Schur
matrix. -/
theorem factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrixOne_det :
    (factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix
      1 (by omega)).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven := by
  simpa only [Nat.reduceAdd, Nat.reduceSub, pow_zero, one_mul,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven] using
    factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix_det
      1 (by omega) (by omega)

/-- The second fraction-free Schur determinant is `p₆ p₈`. -/
theorem factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrixTwo_det
    (hr : 6 + 2 ≤ 9) :
    (factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix
      2 hr).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix *
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
          (6 + 2) hr := by
  simpa only [Nat.reduceSub, pow_one] using
    factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix_det
      2 (by omega) hr

/-- The complete fraction-free Schur determinant is `p₆² p₉`. -/
theorem factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrixThree_det
    (hr : 6 + 3 ≤ 9) :
    (factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix
      3 hr).det =
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSix ^ 2 *
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
          (6 + 3) hr := by
  simpa only [Nat.reduceSub] using
    factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix_det
      3 (by omega) hr

end


end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveFractionFreeSchurStructural
