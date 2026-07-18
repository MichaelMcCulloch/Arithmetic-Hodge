import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur

/-!
# A structural `3 x 3` rank-one Schur criterion

This file gives a division-free scalar API for a real symmetric `3 x 3`
form.  The hypotheses are its three positive leading principal minors.  The
main criterion says that subtracting a rank-one form preserves
nonnegativity exactly when the corresponding adjugate quadratic is bounded
by the determinant.

The proof uses the sequential Schur pivots and an explicit sum-of-squares
Lagrange identity.  It does not enumerate parameters or use a numerical
certificate.
-/

/-- The quadratic form of the symmetric matrix with upper-triangular entries
`q00,q01,q02,q11,q12,q22`. -/
def symmetricQuadratic
    (q00 q01 q02 q11 q12 q22 x0 x1 x2 : ℝ) : ℝ :=
  q00 * x0 ^ 2 + 2 * q01 * x0 * x1 + 2 * q02 * x0 * x2 +
    q11 * x1 ^ 2 + 2 * q12 * x1 * x2 + q22 * x2 ^ 2

/-- The leading `2 x 2` principal minor. -/
def leadingMinorTwo (q00 q01 q11 : ℝ) : ℝ :=
  q00 * q11 - q01 ^ 2

/-- The determinant of the symmetric `3 x 3` matrix. -/
def symmetricDeterminant
    (q00 q01 q02 q11 q12 q22 : ℝ) : ℝ :=
  q00 * (q11 * q22 - q12 ^ 2) -
    q01 * (q01 * q22 - q02 * q12) +
    q02 * (q01 * q12 - q02 * q11)

/-- Evaluation of the adjugate matrix on a real row `ell`. -/
def adjugateQuadratic
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) : ℝ :=
  (q11 * q22 - q12 ^ 2) * ell0 ^ 2 +
    2 * (q02 * q12 - q01 * q22) * ell0 * ell1 +
    2 * (q01 * q12 - q02 * q11) * ell0 * ell2 +
    (q00 * q22 - q02 ^ 2) * ell1 ^ 2 +
    2 * (q01 * q02 - q00 * q12) * ell1 * ell2 +
    (q00 * q11 - q01 ^ 2) * ell2 ^ 2

/-- The vector obtained by applying the explicit adjugate matrix to `ell`. -/
def adjugateVector
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) : Fin 3 → ℝ
  | 0 =>
      (q11 * q22 - q12 ^ 2) * ell0 +
        (q02 * q12 - q01 * q22) * ell1 +
        (q01 * q12 - q02 * q11) * ell2
  | 1 =>
      (q02 * q12 - q01 * q22) * ell0 +
        (q00 * q22 - q02 ^ 2) * ell1 +
        (q01 * q02 - q00 * q12) * ell2
  | 2 =>
      (q01 * q12 - q02 * q11) * ell0 +
        (q01 * q02 - q00 * q12) * ell1 +
        (q00 * q11 - q01 ^ 2) * ell2

private theorem sequential_quadratic_identity
    (q00 q01 q02 q11 q12 q22 x0 x1 x2 : ℝ) :
    q00 * leadingMinorTwo q00 q01 q11 *
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 =
      leadingMinorTwo q00 q01 q11 *
          (q00 * x0 + q01 * x1 + q02 * x2) ^ 2 +
        (leadingMinorTwo q00 q01 q11 * x1 +
            (q00 * q12 - q01 * q02) * x2) ^ 2 +
        q00 * symmetricDeterminant q00 q01 q02 q11 q12 q22 * x2 ^ 2 := by
  unfold leadingMinorTwo symmetricQuadratic symmetricDeterminant
  ring

private theorem sequential_adjugate_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    q00 * leadingMinorTwo q00 q01 q11 *
        adjugateQuadratic q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 =
      leadingMinorTwo q00 q01 q11 *
          symmetricDeterminant q00 q01 q02 q11 q12 q22 * ell0 ^ 2 +
        symmetricDeterminant q00 q01 q02 q11 q12 q22 *
          (q00 * ell1 - q01 * ell0) ^ 2 +
        q00 *
          (leadingMinorTwo q00 q01 q11 * ell2 -
              (q00 * q12 - q01 * q02) * ell1 +
              (q01 * q12 - q02 * q11) * ell0) ^ 2 := by
  unfold leadingMinorTwo symmetricDeterminant adjugateQuadratic
  ring

/-- Sylvester's three scalar pivots make the symmetric quadratic
nonnegative.  This formulation is convenient when the entries are explicit
functions of an external phase parameter. -/
theorem symmetricQuadratic_nonneg
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (x0 x1 x2 : ℝ) :
    0 ≤ symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 := by
  have hscaled :
      0 ≤ q00 * leadingMinorTwo q00 q01 q11 *
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 := by
    rw [sequential_quadratic_identity]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hminor.le (sq_nonneg _))
        (sq_nonneg _))
      (mul_nonneg (mul_nonneg h00.le hdet.le) (sq_nonneg _))
  have hscaled' :
      0 ≤ symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 *
        (q00 * leadingMinorTwo q00 q01 q11) := by
    simpa only [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' (mul_pos h00 hminor)

/-- Under the same three pivots, the adjugate quadratic is nonnegative. -/
theorem adjugateQuadratic_nonneg
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (ell0 ell1 ell2 : ℝ) :
    0 ≤ adjugateQuadratic
      q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  have hscaled :
      0 ≤ q00 * leadingMinorTwo q00 q01 q11 *
        adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
    rw [sequential_adjugate_identity]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hminor.le hdet.le) (sq_nonneg _))
        (mul_nonneg hdet.le (sq_nonneg _)))
      (mul_nonneg h00.le (sq_nonneg _))
  have hscaled' :
      0 ≤ adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 *
        (q00 * leadingMinorTwo q00 q01 q11) := by
    simpa only [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' (mul_pos h00 hminor)

private theorem adjugate_lagrange_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 x0 x1 x2 : ℝ) :
    let D := leadingMinorTwo q00 q01 q11
    let T := symmetricDeterminant q00 q01 q02 q11 q12 q22
    let Q := symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2
    let A := adjugateQuadratic
      q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
    let L := ell0 * x0 + ell1 * x1 + ell2 * x2
    let y0 := q00 * x0 + q01 * x1 + q02 * x2
    let y1 := D * x1 + (q00 * q12 - q01 * q02) * x2
    let p1 := q00 * ell1 - q01 * ell0
    let p2 := D * ell2 - (q00 * q12 - q01 * q02) * ell1 +
      (q01 * q12 - q02 * q11) * ell0
    (q00 * D) ^ 2 * (Q * A - T * L ^ 2) =
      D * T * (y0 * p1 - y1 * ell0) ^ 2 +
        q00 * D * (y0 * p2 - T * x2 * ell0) ^ 2 +
        q00 * (y1 * p2 - T * x2 * p1) ^ 2 := by
  dsimp only
  unfold leadingMinorTwo symmetricDeterminant symmetricQuadratic
    adjugateQuadratic
  ring

/-- The exact adjugate Cauchy inequality for a positive definite real
`3 x 3` form.  Its proof is a three-square Lagrange identity in the two
successive Schur coordinates. -/
theorem adjugate_cauchy
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (ell0 ell1 ell2 x0 x1 x2 : ℝ) :
    symmetricDeterminant q00 q01 q02 q11 q12 q22 *
        (ell0 * x0 + ell1 * x1 + ell2 * x2) ^ 2 ≤
      symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 *
        adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  let D := leadingMinorTwo q00 q01 q11
  let T := symmetricDeterminant q00 q01 q02 q11 q12 q22
  let Q := symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2
  let A := adjugateQuadratic
    q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  let L := ell0 * x0 + ell1 * x1 + ell2 * x2
  let y0 := q00 * x0 + q01 * x1 + q02 * x2
  let y1 := D * x1 + (q00 * q12 - q01 * q02) * x2
  let p1 := q00 * ell1 - q01 * ell0
  let p2 := D * ell2 - (q00 * q12 - q01 * q02) * ell1 +
    (q01 * q12 - q02 * q11) * ell0
  have hD : 0 < D := by simpa only [D] using hminor
  have hT : 0 < T := by simpa only [T] using hdet
  have hidentity := adjugate_lagrange_identity
    q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 x0 x1 x2
  have hrhs :
      0 ≤ D * T * (y0 * p1 - y1 * ell0) ^ 2 +
        q00 * D * (y0 * p2 - T * x2 * ell0) ^ 2 +
        q00 * (y1 * p2 - T * x2 * p1) ^ 2 := by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hD.le hT.le) (sq_nonneg _))
        (mul_nonneg (mul_nonneg h00.le hD.le) (sq_nonneg _)))
      (mul_nonneg h00.le (sq_nonneg _))
  have hscaled : 0 ≤ (q00 * D) ^ 2 * (Q * A - T * L ^ 2) := by
    rw [hidentity]
    exact hrhs
  have hfactor : 0 < (q00 * D) ^ 2 := sq_pos_of_pos (mul_pos h00 hD)
  have hscaled' : 0 ≤ (Q * A - T * L ^ 2) * (q00 * D) ^ 2 := by
    simpa only [mul_comm] using hscaled
  have hgap : 0 ≤ Q * A - T * L ^ 2 :=
    nonneg_of_mul_nonneg_left hscaled' hfactor
  apply sub_nonneg.mp
  simpa only [D, T, Q, A, L] using hgap

private theorem adjugateVector_linear
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    ell0 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0 +
        ell1 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1 +
        ell2 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2 =
      adjugateQuadratic
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring

private theorem adjugateVector_quadratic
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    symmetricQuadratic q00 q01 q02 q11 q12 q22
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0)
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1)
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2) =
      symmetricDeterminant q00 q01 q02 q11 q12 q22 *
        adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold symmetricQuadratic symmetricDeterminant adjugateQuadratic
  ring

/-- Converse strict rank-one Schur test.  If a positive `3 x 3` form
strictly dominates a fixed border functional in every nonzero direction,
then the inverse-free adjugate gap is strictly positive. -/
theorem adjugateQuadratic_lt_symmetricDeterminant_mul_of_border_lt
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 d : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (hd : 0 < d)
    (hborder : ∀ x0 x1 x2 : ℝ,
      x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 →
      (ell0 * x0 + ell1 * x1 + ell2 * x2) ^ 2 <
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 * d) :
    adjugateQuadratic q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 <
      symmetricDeterminant q00 q01 q02 q11 q12 q22 * d := by
  let T := symmetricDeterminant q00 q01 q02 q11 q12 q22
  let A := adjugateQuadratic
    q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  have hT : 0 < T := by simpa only [T] using hdet
  have hA : 0 ≤ A := by
    simpa only [A] using adjugateQuadratic_nonneg
      q00 q01 q02 q11 q12 q22 h00 hminor hdet ell0 ell1 ell2
  change A < T * d
  by_cases hAzero : A = 0
  · rw [hAzero]
    exact mul_pos hT hd
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    let v := adjugateVector
      q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
    have hlinear := adjugateVector_linear
      q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
    have hquadratic := adjugateVector_quadratic
      q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
    have hvne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra hv
      push_neg at hv
      rcases hv with ⟨h0, h1, h2⟩
      dsimp only [v] at h0 h1 h2
      rw [h0, h1, h2] at hlinear
      norm_num at hlinear
      exact hAzero hlinear.symm
    have hv := hborder (v 0) (v 1) (v 2) hvne
    dsimp only [v] at hv
    rw [hlinear, hquadratic] at hv
    change A ^ 2 < T * A * d at hv
    nlinarith

/-- Exact rank-one Schur criterion.  For a positive definite symmetric
`3 x 3` form `Q` and a row `L`, the form `Q - k L^2` is nonnegative in every
direction exactly when `k * (L adj(Q) L^T) <= det(Q)`.

No sign hypothesis on `k` is needed: for `k < 0` the rank-one update is
automatically positive, and the adjugate condition is automatic as well. -/
theorem rankOne_sub_nonneg_iff
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (k ell0 ell1 ell2 : ℝ) :
    (∀ x0 x1 x2 : ℝ,
      0 ≤ symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 -
        k * (ell0 * x0 + ell1 * x1 + ell2 * x2) ^ 2) ↔
      k * adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 ≤
        symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  let T := symmetricDeterminant q00 q01 q02 q11 q12 q22
  let A := adjugateQuadratic
    q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  have hT : 0 < T := by simpa only [T] using hdet
  have hA : 0 ≤ A := by
    simpa only [A] using adjugateQuadratic_nonneg
      q00 q01 q02 q11 q12 q22 h00 hminor hdet ell0 ell1 ell2
  constructor
  · intro h
    change k * A ≤ T
    by_cases hAzero : A = 0
    · rw [hAzero, mul_zero]
      exact hT.le
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      let v := adjugateVector
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
      have hv := h (v 0) (v 1) (v 2)
      have hlinear := adjugateVector_linear
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
      have hquadratic := adjugateVector_quadratic
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
      dsimp only [v] at hv
      rw [hlinear, hquadratic] at hv
      change 0 ≤ T * A - k * A ^ 2 at hv
      nlinarith
  · intro hAdj x0 x1 x2
    let Q := symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2
    let L := ell0 * x0 + ell1 * x1 + ell2 * x2
    have hQ : 0 ≤ Q := by
      simpa only [Q] using symmetricQuadratic_nonneg
        q00 q01 q02 q11 q12 q22 h00 hminor hdet x0 x1 x2
    by_cases hk : 0 ≤ k
    · have hCauchy : T * L ^ 2 ≤ Q * A := by
        simpa only [T, Q, A, L] using adjugate_cauchy
          q00 q01 q02 q11 q12 q22 h00 hminor hdet
          ell0 ell1 ell2 x0 x1 x2
      have hscaled : k * (T * L ^ 2) ≤ k * (Q * A) :=
        mul_le_mul_of_nonneg_left hCauchy hk
      have hupper : Q * (k * A) ≤ Q * T :=
        mul_le_mul_of_nonneg_left hAdj hQ
      have hfinal : T * (k * L ^ 2) ≤ T * Q := by
        calc
          T * (k * L ^ 2) = k * (T * L ^ 2) := by ring
          _ ≤ k * (Q * A) := hscaled
          _ = Q * (k * A) := by ring
          _ ≤ Q * T := hupper
          _ = T * Q := by ring
      have : k * L ^ 2 ≤ Q := by nlinarith
      simpa only [Q, L] using sub_nonneg.mpr this
    · have hkneg : k < 0 := lt_of_not_ge hk
      have hupdate : 0 ≤ -k * L ^ 2 :=
        mul_nonneg (neg_nonneg.mpr hkneg.le) (sq_nonneg L)
      have : 0 ≤ Q - k * L ^ 2 := by
        nlinarith
      simpa only [Q, L] using this

end ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
