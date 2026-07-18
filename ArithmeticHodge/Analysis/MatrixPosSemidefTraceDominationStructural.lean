import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

set_option autoImplicit false

open Matrix
open Unitary
open scoped BigOperators

namespace ArithmeticHodge.Analysis

noncomputable section

/-- A real positive-semidefinite matrix is bounded above, in the Loewner order,
by its trace times the identity. -/
theorem Matrix.PosSemidef.trace_smul_one_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    (G.trace • (1 : Matrix ι ι ℝ) - G).PosSemidef := by
  let d : ι → ℝ := fun i ↦ G.trace - hG.isHermitian.eigenvalues i
  have hd (i : ι) : 0 ≤ d i := by
    dsimp only [d]
    rw [hG.isHermitian.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ i)]
    simp only [add_sub_cancel_left]
    exact Finset.sum_nonneg fun j _ ↦ hG.eigenvalues_nonneg j
  have hdiag : (diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd
  have hdiagonal :
      diagonal d =
        G.trace • (1 : Matrix ι ι ℝ) -
          diagonal hG.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [d, hij]
  rw [show
      G.trace • (1 : Matrix ι ι ℝ) - G =
        conjStarAlgAut ℝ _ hG.isHermitian.eigenvectorUnitary (diagonal d) by
      calc
        G.trace • (1 : Matrix ι ι ℝ) - G =
            G.trace • (1 : Matrix ι ι ℝ) -
              conjStarAlgAut ℝ _ hG.isHermitian.eigenvectorUnitary
                (diagonal hG.isHermitian.eigenvalues) := by
                  simpa [RCLike.ofReal_real_eq_id] using
                    congrArg
                      (fun A : Matrix ι ι ℝ ↦
                        G.trace • (1 : Matrix ι ι ℝ) - A)
                      hG.isHermitian.spectral_theorem
        _ = conjStarAlgAut ℝ _ hG.isHermitian.eigenvectorUnitary
              (G.trace • (1 : Matrix ι ι ℝ) -
                diagonal hG.isHermitian.eigenvalues) := by
                  rw [map_sub, map_smul, map_one]
        _ = conjStarAlgAut ℝ _ hG.isHermitian.eigenvectorUnitary
              (diagonal d) := by rw [hdiagonal]]
  simpa [conjStarAlgAut_apply] using
    hdiag.mul_mul_conjTranspose_same
      (hG.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)

/-- Any scalar upper bound on the trace of a real positive-semidefinite matrix
is automatically a Loewner upper bound for the whole matrix. -/
theorem Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {gamma : ℝ}
    (htrace : G.trace ≤ gamma) :
    (gamma • (1 : Matrix ι ι ℝ) - G).PosSemidef := by
  have hscalar :
      ((gamma - G.trace) • (1 : Matrix ι ι ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sub_nonneg.mpr htrace)
  have hsum := hscalar.add (Matrix.PosSemidef.trace_smul_one_sub hG)
  have heq :
      gamma • (1 : Matrix ι ι ℝ) - G =
        (gamma - G.trace) • (1 : Matrix ι ι ℝ) +
          (G.trace • (1 : Matrix ι ι ℝ) - G) := by
    module
  rw [heq]
  exact hsum

end

end ArithmeticHodge.Analysis
