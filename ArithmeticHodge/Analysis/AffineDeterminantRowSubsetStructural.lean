import Mathlib.LinearAlgebra.Matrix.Polynomial

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.AffineDeterminantRowSubsetStructural

noncomputable section

/-!
# Coefficients of an affine determinant by mixed rows

Multilinearity in the rows expands an affine determinant into one mixed
determinant for each row subset.  This avoids a Leibniz expansion over
permutations and exposes every polynomial coefficient invariantly.
-/

/-- The determinant of `X A + B` is the generating polynomial of the mixed
row determinants: rows in `s` come from `A`, and rows outside `s` come from
`B`. -/
theorem det_X_smul_add_C_eq_sum_mixedRows
    {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (A B : Matrix n n R) :
    Matrix.det ((X : R[X]) • A.map C + B.map C) =
      ∑ s : Finset n,
        C (Matrix.det (s.piecewise A B)) * X ^ s.card := by
  classical
  change
    (Matrix.detRowAlternating :
      (n → R[X]) [⋀^n]→ₗ[R[X]] R[X]).toMultilinearMap
        ((fun i j ↦ X * C (A i j)) +
          (fun i j ↦ C (B i j))) = _
  rw [(Matrix.detRowAlternating :
    (n → R[X]) [⋀^n]→ₗ[R[X]] R[X]).toMultilinearMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _hs
  let M : Matrix n n R[X] := s.piecewise (A.map C) (B.map C)
  have hrows :
      s.piecewise
          (fun i j ↦ X * C (A i j))
          (fun i j ↦ C (B i j)) =
        s.piecewise (fun i ↦ (X : R[X]) • M i) M := by
    ext i j
    by_cases hi : i ∈ s <;> simp [M, hi]
  rw [hrows]
  rw [(Matrix.detRowAlternating :
    (n → R[X]) [⋀^n]→ₗ[R[X]] R[X]).toMultilinearMap.map_piecewise_smul]
  simp only [Finset.prod_const, smul_eq_mul]
  rw [show M = Matrix.map (s.piecewise A B) C by
    ext i j
    by_cases hi : i ∈ s <;> simp [M, hi]]
  change X ^ s.card * Matrix.det (Matrix.map (s.piecewise A B) C) = _
  have hmap :
      Matrix.map (s.piecewise A B) C =
        (C : R →+* R[X]).mapMatrix (s.piecewise A B) := by
    rfl
  rw [hmap, ← RingHom.map_det C]
  exact mul_comm _ _

/-- The coefficient of degree `j` is the sum of exactly those mixed-row
determinants that use `j` rows of `A`. -/
theorem coeff_det_X_smul_add_C_eq_sum_mixedRows_card
    {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (A B : Matrix n n R) (j : ℕ) :
    Polynomial.coeff
        (Matrix.det ((X : R[X]) • A.map C + B.map C)) j =
      ∑ s ∈ (Finset.univ : Finset n).powersetCard j,
        Matrix.det (s.piecewise A B) := by
  classical
  rw [det_X_smul_add_C_eq_sum_mixedRows,
    Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [← Finset.univ_filter_card_eq n j, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases h : j = s.card
  · simp [h]
  · simp [h, Ne.symm h]

end

end ArithmeticHodge.Analysis.AffineDeterminantRowSubsetStructural
