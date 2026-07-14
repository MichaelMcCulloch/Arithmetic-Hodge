import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreeConvexPencil

open ThreeByThreeRankOneSchur

/-!
# Strict convexity of real symmetric `3 x 3` pencils

Positive leading Sylvester pivots give strict positivity of the associated
quadratic form.  Conversely, strict positivity recovers all three pivots.
It follows without a determinant expansion that every convex interpolation
of two positive-definite symmetric `3 x 3` forms is again positive definite.
-/

private theorem sequential_quadratic_identity
    (q00 q01 q02 q11 q12 q22 x0 x1 x2 : ℝ) :
    q00 * leadingMinorTwo q00 q01 q11 *
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 =
      leadingMinorTwo q00 q01 q11 *
          (q00 * x0 + q01 * x1 + q02 * x2) ^ 2 +
        (leadingMinorTwo q00 q01 q11 * x1 +
            (q00 * q12 - q01 * q02) * x2) ^ 2 +
        q00 * symmetricDeterminant q00 q01 q02 q11 q12 q22 *
          x2 ^ 2 := by
  unfold leadingMinorTwo symmetricQuadratic symmetricDeterminant
  ring

/-- Strict Sylvester pivots make the `3 x 3` quadratic strictly positive
away from the coefficient origin. -/
theorem symmetricQuadratic_pos
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (x0 x1 x2 : ℝ) (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0) :
    0 < symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 := by
  have hscale : 0 < q00 * leadingMinorTwo q00 q01 q11 :=
    mul_pos h00 hminor
  have hrhs : 0 <
      leadingMinorTwo q00 q01 q11 *
          (q00 * x0 + q01 * x1 + q02 * x2) ^ 2 +
        (leadingMinorTwo q00 q01 q11 * x1 +
            (q00 * q12 - q01 * q02) * x2) ^ 2 +
        q00 * symmetricDeterminant q00 q01 q02 q11 q12 q22 *
          x2 ^ 2 := by
    by_cases hx2 : x2 = 0
    · subst x2
      by_cases hx1 : x1 = 0
      · subst x1
        have hx0 : x0 ≠ 0 := by
          rcases hne with hx0 | hx1 | hx2
          · exact hx0
          · exact (hx1 rfl).elim
          · exact (hx2 rfl).elim
        have hterm := mul_pos hminor
          (sq_pos_of_ne_zero (mul_ne_zero h00.ne' hx0))
        simpa using hterm
      · have hfirst : 0 ≤ leadingMinorTwo q00 q01 q11 *
            (q00 * x0 + q01 * x1) ^ 2 :=
          mul_nonneg hminor.le (sq_nonneg _)
        have hsecond : 0 <
            (leadingMinorTwo q00 q01 q11 * x1) ^ 2 :=
          sq_pos_of_ne_zero (mul_ne_zero hminor.ne' hx1)
        have hsum := add_pos_of_nonneg_of_pos hfirst hsecond
        simpa using hsum
    · exact add_pos_of_nonneg_of_pos
        (add_nonneg
          (mul_nonneg hminor.le (sq_nonneg _))
          (sq_nonneg _))
        (mul_pos (mul_pos h00 hdet) (sq_pos_of_ne_zero hx2))
  have hscaled : 0 < q00 * leadingMinorTwo q00 q01 q11 *
      symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 := by
    rw [sequential_quadratic_identity]
    exact hrhs
  exact ((mul_pos_iff.mp hscaled).resolve_right (fun hneg ↦
    (not_lt_of_ge hscale.le) hneg.1)).2

/-- Strict positivity of a symmetric `3 x 3` quadratic recovers its three
leading Sylvester pivots. -/
theorem leadingMinors_pos_of_symmetricQuadratic_pos
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (hpos : ∀ x0 x1 x2 : ℝ,
      x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 →
        0 < symmetricQuadratic
          q00 q01 q02 q11 q12 q22 x0 x1 x2) :
    0 < q00 ∧
      0 < leadingMinorTwo q00 q01 q11 ∧
      0 < symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  have h00 : 0 < q00 := by
    have h := hpos 1 0 0 (Or.inl one_ne_zero)
    simpa [symmetricQuadratic] using h
  have hminor : 0 < leadingMinorTwo q00 q01 q11 := by
    have h := hpos q01 (-q00) 0
      (Or.inr (Or.inl (neg_ne_zero.mpr h00.ne')))
    have hid :
        symmetricQuadratic q00 q01 q02 q11 q12 q22
            q01 (-q00) 0 =
          q00 * leadingMinorTwo q00 q01 q11 := by
      unfold symmetricQuadratic leadingMinorTwo
      ring
    rw [hid] at h
    exact ((mul_pos_iff.mp h).resolve_right (fun hneg ↦
      (not_lt_of_ge h00.le) hneg.1)).2
  let D : ℝ := leadingMinorTwo q00 q01 q11
  let A : ℝ := q00 * q12 - q01 * q02
  let x0 : ℝ := q01 * A - q02 * D
  let x1 : ℝ := -q00 * A
  let x2 : ℝ := q00 * D
  have hx2 : 0 < x2 := by
    dsimp only [x2, D]
    exact mul_pos h00 hminor
  have hspecial := hpos x0 x1 x2 (Or.inr (Or.inr hx2.ne'))
  have hid :
      symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 =
        q00 ^ 2 * D *
          symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
    dsimp only [x0, x1, x2, A, D]
    unfold symmetricQuadratic leadingMinorTwo symmetricDeterminant
    ring
  rw [hid] at hspecial
  have hfactor : 0 < q00 ^ 2 * D := by
    exact mul_pos (sq_pos_of_pos h00) hminor
  have hdet :
      0 < symmetricDeterminant q00 q01 q02 q11 q12 q22 :=
    ((mul_pos_iff.mp hspecial).resolve_right (fun hneg ↦
      (not_lt_of_ge hfactor.le) hneg.1)).2
  exact ⟨h00, hminor, hdet⟩

/-- Convex interpolation preserves all three strict Sylvester pivots. -/
theorem convex_leadingMinors_pos
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 lambda mu : ℝ)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu)
    (hsum : lambda + mu = 1)
    (hp00 : 0 < p00)
    (hpminor : 0 < leadingMinorTwo p00 p01 p11)
    (hpdet : 0 < symmetricDeterminant p00 p01 p02 p11 p12 p22)
    (hm00 : 0 < m00)
    (hmminor : 0 < leadingMinorTwo m00 m01 m11)
    (hmdet : 0 < symmetricDeterminant m00 m01 m02 m11 m12 m22) :
    0 < lambda * p00 + mu * m00 ∧
      0 < leadingMinorTwo
        (lambda * p00 + mu * m00)
        (lambda * p01 + mu * m01)
        (lambda * p11 + mu * m11) ∧
      0 < symmetricDeterminant
        (lambda * p00 + mu * m00)
        (lambda * p01 + mu * m01)
        (lambda * p02 + mu * m02)
        (lambda * p11 + mu * m11)
        (lambda * p12 + mu * m12)
        (lambda * p22 + mu * m22) := by
  apply leadingMinors_pos_of_symmetricQuadratic_pos
  intro x0 x1 x2 hne
  have hp := symmetricQuadratic_pos
    p00 p01 p02 p11 p12 p22 hp00 hpminor hpdet x0 x1 x2 hne
  have hm := symmetricQuadratic_pos
    m00 m01 m02 m11 m12 m22 hm00 hmminor hmdet x0 x1 x2 hne
  have hform :
      symmetricQuadratic
          (lambda * p00 + mu * m00)
          (lambda * p01 + mu * m01)
          (lambda * p02 + mu * m02)
          (lambda * p11 + mu * m11)
          (lambda * p12 + mu * m12)
          (lambda * p22 + mu * m22) x0 x1 x2 =
        lambda * symmetricQuadratic
          p00 p01 p02 p11 p12 p22 x0 x1 x2 +
        mu * symmetricQuadratic
          m00 m01 m02 m11 m12 m22 x0 x1 x2 := by
    unfold symmetricQuadratic
    ring
  rw [hform]
  rcases hlambda.eq_or_lt with rfl | hlambdaPos
  · have hmuOne : mu = 1 := by linarith
    simpa [hmuOne] using hm
  · exact add_pos_of_pos_of_nonneg
      (mul_pos hlambdaPos hp) (mul_nonneg hmu hm.le)

end ArithmeticHodge.Analysis.ThreeByThreeConvexPencil
