import Mathlib.Analysis.Matrix.PosDef

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis

theorem sesquilinear_orthogonal_sum_self
    {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (w : ι → E) (c : ι → ℂ) (v : E)
    (hleft : ∀ i, B (w i) v = 0)
    (hright : ∀ i, B v (w i) = 0) :
    B (∑ i, c i • w i + v) (∑ i, c i • w i + v) =
      star c ⬝ᵥ ((fun i j ↦ B (w i) (w j)) *ᵥ c) + B v v := by
  classical
  simp [dotProduct, Matrix.mulVec, hleft, hright, mul_comm]

theorem posDef_add_tail_strictPos
    {ι T : Type*} [Fintype ι] [Zero T]
    {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (qTail : T → ℝ)
    (hqTail_nonneg : ∀ v, 0 ≤ qTail v)
    (hqTail_pos : ∀ v, v ≠ 0 → 0 < qTail v)
    {c : ι → ℂ} {v : T} (hne : c ≠ 0 ∨ v ≠ 0) :
    0 < (star c ⬝ᵥ (A *ᵥ c)).re + qTail v := by
  rcases hne with hc | hv
  · exact add_pos_of_pos_of_nonneg (hA.re_dotProduct_pos hc) (hqTail_nonneg v)
  · exact add_pos_of_nonneg_of_pos (hA.posSemidef.re_dotProduct_nonneg c) (hqTail_pos v hv)

theorem sesquilinear_orthogonal_sum_re_pos
    {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (K : Submodule ℂ E) (w : ι → E) (c : ι → ℂ) (v : K)
    (hleft : ∀ i, B (w i) (v : E) = 0)
    (hright : ∀ i, B (v : E) (w i) = 0)
    (hgram : Matrix.PosDef (fun i j ↦ B (w i) (w j)))
    (htail_nonneg : ∀ x : K, 0 ≤ (B (x : E) (x : E)).re)
    (htail_pos : ∀ x : K, x ≠ 0 → 0 < (B (x : E) (x : E)).re)
    (hne : c ≠ 0 ∨ v ≠ 0) :
    0 < (B (∑ i, c i • w i + (v : E))
      (∑ i, c i • w i + (v : E))).re := by
  rw [sesquilinear_orthogonal_sum_self B w c (v : E) hleft hright, Complex.add_re]
  exact posDef_add_tail_strictPos hgram
    (fun x : K ↦ (B (x : E) (x : E)).re) htail_nonneg htail_pos hne

end ArithmeticHodge.Analysis
