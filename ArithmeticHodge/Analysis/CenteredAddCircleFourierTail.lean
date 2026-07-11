import ArithmeticHodge.Analysis.CenteredAddCircleFourierSymmetry
import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace ArithmeticHodge.Analysis

local notation "⟪" x ", " y "⟫" => inner ℂ x y

theorem orthonormal_remainder_norm_sq
    {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : ι → E} (hv : Orthonormal ℂ v) (x : E) (s : Finset ι) :
    ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 := by
  have h₂ :
      (∑ i ∈ s, ∑ j ∈ s,
        ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) =
      (∑ k ∈ s, ⟪v k, x⟫ * ⟪x, v k⟫ : ℂ) := by
    classical
    exact hv.inner_left_right_finset
  have h₃ : ∀ z : ℂ, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj, Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  rw [@norm_sub_sq ℂ, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner ℂ E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm,
    ← mul_assoc, h₂, add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]
  rfl

theorem fourier_partial_remainder_norm_sq
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (s : Finset ℤ) :
    ‖f - ∑ i ∈ s, fourierCoeff f i • fourierLp 2 i‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i ∈ s, ‖fourierCoeff f i‖ ^ 2 := by
  have h := orthonormal_remainder_norm_sq
    ((fourierBasis (T := T)).orthonormal) f s
  simp_rw [← (fourierBasis (T := T)).repr_apply_apply] at h
  simp_rw [fourierBasis_repr] at h
  rw [coe_fourierBasis] at h
  exact h

theorem hasSum_fourier_plancherel
    {T : ℝ} [hT : Fact (0 < T)]
    (f g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    HasSum (fun i : ℤ =>
      conj (fourierCoeff f i) * fourierCoeff g i) (inner ℂ f g) := by
  have h := (fourierBasis (T := T)).hasSum_inner_mul_inner f g
  apply h.congr_fun
  intro i
  rw [← inner_conj_symm]
  rw [← (fourierBasis (T := T)).repr_apply_apply]
  rw [← (fourierBasis (T := T)).repr_apply_apply]
  rw [fourierBasis_repr, fourierBasis_repr]

private theorem hasSum_symmetricIcc_of_hasSum
    {E : Type*} [NormedAddCommGroup E] {u : ℤ → E} {x : E}
    (h : HasSum u x) :
    HasSum u x (SummationFilter.symmetricIcc ℤ) := by
  exact h.mono_left (SummationFilter.symmetricIcc ℤ).le_atTop

theorem fourier_series_symmetric_tendsto
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n • fourierLp 2 n)
      atTop (𝓝 f) := by
  rw [← SummationFilter.hasSum_symmetricIcc_iff]
  exact hasSum_symmetricIcc_of_hasSum (hasSum_fourier_series_L2 f)

theorem fourier_series_symmetric_remainder_norm_tendsto_zero
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ => ‖f - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n • fourierLp 2 n‖)
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
  have hsub : Tendsto
      (fun N : ℕ => f - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n • fourierLp 2 n)
      atTop (𝓝 0) := by
    simpa using hconst.sub (fourier_series_symmetric_tendsto f)
  simpa using tendsto_norm.comp hsub

theorem centered_parseval_symmetric_tendsto
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖centeredFourierCoeff ha f n‖ ^ 2)
      atTop (𝓝 ((2 * a)⁻¹ • ∫ x in -a..a, ‖f x‖ ^ 2)) := by
  unfold centeredFourierCoeff
  rw [← SummationFilter.hasSum_symmetricIcc_iff]
  convert hasSum_symmetricIcc_of_hasSum
    (hasSum_sq_fourierCoeffOn (neg_lt_self ha) hL2) using 1
  ring_nf

theorem fourier_parseval_tail_tsum_tendsto_zero
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ =>
        ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)},
          ‖fourierCoeff f n‖ ^ 2)
      atTop (𝓝 0) := by
  exact (tendsto_tsum_compl_atTop_zero
    (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)).comp
      (Finset.tendsto_Icc_neg (R := ℤ))

end ArithmeticHodge.Analysis
