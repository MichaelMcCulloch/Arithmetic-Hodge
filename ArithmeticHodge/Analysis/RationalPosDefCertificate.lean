import ArithmeticHodge.Analysis.HermitianLowTail

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace ArithmeticHodge.Analysis

theorem rationalLDL_posDef_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hL : IsUnit L) (hd : ∀ i, 0 < d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosDef ((Rat.castHom ℂ).mapMatrix A) := by
  rw [hA, map_mul, map_mul]
  have hL' : IsUnit ((Rat.castHom ℂ).mapMatrix L) :=
    hL.map (Rat.castHom ℂ).mapMatrix
  rw [show (Rat.castHom ℂ).mapMatrix Lᴴ =
      star ((Rat.castHom ℂ).mapMatrix L) by
    ext i j
    simp [RingHom.mapMatrix_apply]]
  apply hL'.posDef_star_right_conjugate_iff.mpr
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero (Rat.castHom ℂ))]
  apply Matrix.PosDef.diagonal
  intro i
  rw [Complex.pos_iff]
  simpa using hd i

end ArithmeticHodge.Analysis
