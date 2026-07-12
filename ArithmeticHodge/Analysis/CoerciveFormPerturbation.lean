import ArithmeticHodge.Analysis.ComplexCoerciveRieszCorrection

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bilinear form remains coercive after subtracting a perturbation whose
operator norm is bounded strictly below the original coercivity constant. -/
theorem isCoercive_sub_of_opNorm_le
    (B K : E →L[ℝ] E →L[ℝ] ℝ) {mu delta : ℝ}
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ B x x)
    (hK : ‖K‖ ≤ delta) (hdelta : delta < mu) :
    IsCoercive (B - K) := by
  refine ⟨mu - delta, sub_pos.mpr hdelta, ?_⟩
  intro x
  have hKxx : K x x ≤ delta * ‖x‖ * ‖x‖ := by
    calc
      K x x ≤ ‖K x x‖ := Real.le_norm_self _
      _ ≤ ‖K‖ * ‖x‖ * ‖x‖ := K.le_opNorm₂ x x
      _ ≤ delta * ‖x‖ * ‖x‖ := by
        gcongr
  change (mu - delta) * ‖x‖ * ‖x‖ ≤ B x x - K x x
  nlinarith [hcoercive x, hKxx]

/-- Subtracting a bilinear form whose operator norm is below a coercivity
constant preserves coercivity. -/
theorem isCoercive_sub_of_opNorm_lt
    (B K : E →L[ℝ] E →L[ℝ] ℝ) {mu : ℝ}
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ B x x)
    (hK : ‖K‖ < mu) :
    IsCoercive (B - K) := by
  exact isCoercive_sub_of_opNorm_le B K hcoercive le_rfl hK

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
local instance : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H

/-- The real part of a complex sesquilinear form remains coercive after a
perturbation whose complex operator norm is bounded below the original
coercivity constant. -/
theorem complexToRealForm_sub_isCoercive_of_opNorm_le
    (B K : H →L⋆[ℂ] H →L[ℂ] ℂ) {mu delta : ℝ}
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re)
    (hK : ‖K‖ ≤ delta) (hdelta : delta < mu) :
    IsCoercive (complexToRealForm (B - K)) := by
  refine ⟨mu - delta, sub_pos.mpr hdelta, ?_⟩
  intro x
  have hKxx : (K x x).re ≤ delta * ‖x‖ * ‖x‖ := by
    calc
      (K x x).re ≤ ‖K x x‖ := Complex.re_le_norm (K x x)
      _ ≤ ‖K‖ * ‖x‖ * ‖x‖ := K.le_opNorm₂ x x
      _ ≤ delta * ‖x‖ * ‖x‖ := by
        gcongr
  change (mu - delta) * ‖x‖ * ‖x‖ ≤ (B x x - K x x).re
  rw [Complex.sub_re]
  nlinarith [hcoercive x, hKxx]

/-- Complex sesquilinear specialization with the perturbation controlled by
its operator norm. -/
theorem complexToRealForm_sub_isCoercive_of_opNorm_lt
    (B K : H →L⋆[ℂ] H →L[ℂ] ℂ) {mu : ℝ}
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re)
    (hK : ‖K‖ < mu) :
    IsCoercive (complexToRealForm (B - K)) := by
  exact complexToRealForm_sub_isCoercive_of_opNorm_le
    B K hcoercive le_rfl hK

end Complex

end

end ArithmeticHodge.Analysis
