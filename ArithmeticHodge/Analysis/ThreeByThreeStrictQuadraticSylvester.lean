import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreeStrictQuadraticSylvester

open ThreeByThreeRankOneSchur

/-!
# Extracting strict Sylvester gates from a quadratic form

The converse direction needed by the retuned endpoint certificates is most
transparent with explicit Schur witness vectors.  Positivity on `e₀` gives
the first pivot.  Positivity on `(-q₀₁,q₀₀,0)` gives the leading
minor.  The final vector annihilates the first two fraction-free Schur
coordinates, leaving the determinant times the leading minor.
-/

/-- The vector which annihilates the first two fraction-free Schur
coordinates evaluates the quadratic as the leading minor times the full
determinant. -/
theorem symmetricQuadratic_schurWitness
    (q00 q01 q02 q11 q12 q22 : ℝ) :
    symmetricQuadratic q00 q01 q02 q11 q12 q22
        (q01 * q12 - q11 * q02)
        (q01 * q02 - q00 * q12)
        (leadingMinorTwo q00 q01 q11) =
      leadingMinorTwo q00 q01 q11 *
        symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  unfold symmetricQuadratic leadingMinorTwo symmetricDeterminant
  ring

/-- Strict positivity of a real symmetric `3 × 3` quadratic away from the
origin forces its three leading Sylvester pivots to be strictly positive.
The proof is division-free and uses only three explicit vectors. -/
theorem sylvester_pos_of_symmetricQuadratic_pos
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (hpos : ∀ x0 x1 x2 : ℝ,
      x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 →
        0 < symmetricQuadratic
          q00 q01 q02 q11 q12 q22 x0 x1 x2) :
    0 < q00 ∧
      0 < leadingMinorTwo q00 q01 q11 ∧
        0 < symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  have h00 : 0 < q00 := by
    have h := hpos 1 0 0 (Or.inl (by norm_num))
    simpa [symmetricQuadratic] using h
  have hminor : 0 < leadingMinorTwo q00 q01 q11 := by
    have h := hpos (-q01) q00 0
      (Or.inr (Or.inl h00.ne'))
    have heval :
        symmetricQuadratic q00 q01 q02 q11 q12 q22
            (-q01) q00 0 =
          q00 * leadingMinorTwo q00 q01 q11 := by
      unfold symmetricQuadratic leadingMinorTwo
      ring
    rw [heval] at h
    have hcomm :
        0 < leadingMinorTwo q00 q01 q11 * q00 := by
      simpa only [mul_comm] using h
    exact pos_of_mul_pos_left hcomm h00.le
  have hdet :
      0 < symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
    have h := hpos
      (q01 * q12 - q11 * q02)
      (q01 * q02 - q00 * q12)
      (leadingMinorTwo q00 q01 q11)
      (Or.inr (Or.inr hminor.ne'))
    rw [symmetricQuadratic_schurWitness] at h
    have hcomm :
        0 < symmetricDeterminant q00 q01 q02 q11 q12 q22 *
          leadingMinorTwo q00 q01 q11 := by
      simpa only [mul_comm] using h
    exact pos_of_mul_pos_left hcomm hminor.le
  exact ⟨h00, hminor, hdet⟩

end ArithmeticHodge.Analysis.ThreeByThreeStrictQuadraticSylvester
