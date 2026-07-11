import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace ArithmeticHodge.Analysis

noncomputable def coerciveRieszCorrection
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) : V :=
  hB.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ V).symm ell)

theorem coerciveRieszCorrection_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) (w : V) :
    B (coerciveRieszCorrection hB ell) w = ell w := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp only [coerciveRieszCorrection, ContinuousLinearEquiv.apply_symm_apply,
    InnerProductSpace.toDual_symm_apply]

theorem norm_coerciveRieszCorrection_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ v, mu * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖coerciveRieszCorrection hB ell‖ ≤ ‖ell‖ / mu := by
  by_cases hu : coerciveRieszCorrection hB ell = 0
  · rw [hu, norm_zero]
    positivity
  · have hnorm : 0 < ‖coerciveRieszCorrection hB ell‖ := norm_pos_iff.mpr hu
    have hbound :
        mu * ‖coerciveRieszCorrection hB ell‖ * ‖coerciveRieszCorrection hB ell‖ ≤
          ‖ell‖ * ‖coerciveRieszCorrection hB ell‖ := by
      calc
        mu * ‖coerciveRieszCorrection hB ell‖ * ‖coerciveRieszCorrection hB ell‖ ≤
            B (coerciveRieszCorrection hB ell) (coerciveRieszCorrection hB ell) :=
          hcoercive (coerciveRieszCorrection hB ell)
        _ = ell (coerciveRieszCorrection hB ell) :=
          coerciveRieszCorrection_apply hB ell (coerciveRieszCorrection hB ell)
        _ ≤ ‖ell (coerciveRieszCorrection hB ell)‖ := Real.le_norm_self _
        _ ≤ ‖ell‖ * ‖coerciveRieszCorrection hB ell‖ :=
          ContinuousLinearMap.le_opNorm _ _
    have hcancel : mu * ‖coerciveRieszCorrection hB ell‖ ≤ ‖ell‖ :=
      le_of_mul_le_mul_right hbound hnorm
    exact (le_div_iff₀ hmu).2 (by simpa [mul_comm] using hcancel)

theorem coerciveRieszCorrection_energy_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ v, mu * ‖v‖ * ‖v‖ ≤ B v v) :
    B (coerciveRieszCorrection hB ell)
      (coerciveRieszCorrection hB ell) ≤ ‖ell‖ ^ 2 / mu := by
  calc
    B (coerciveRieszCorrection hB ell) (coerciveRieszCorrection hB ell) =
        ell (coerciveRieszCorrection hB ell) :=
      coerciveRieszCorrection_apply hB ell (coerciveRieszCorrection hB ell)
    _ ≤ ‖ell (coerciveRieszCorrection hB ell)‖ := Real.le_norm_self _
    _ ≤ ‖ell‖ * ‖coerciveRieszCorrection hB ell‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ell‖ * (‖ell‖ / mu) :=
      mul_le_mul_of_nonneg_left
        (norm_coerciveRieszCorrection_le hB ell hmu hcoercive) (norm_nonneg ell)
    _ = ‖ell‖ ^ 2 / mu := by ring

end ArithmeticHodge.Analysis
