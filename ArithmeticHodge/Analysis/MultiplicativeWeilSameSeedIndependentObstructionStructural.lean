import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

open Complex Real
open scoped InnerProductSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Same-seed numerical radius versus independent contraction

For a lag-one sesquilinear cross `B(x,y)`, same-seed estimates control only
the diagonal values `B(x,x)`.  Complex polarization recovers `B(x,y)`, but
the sharp universal estimate loses a factor two.  Thus a same-seed
factor-two theorem cannot, by polarization alone, supply the constant-one
independent contraction needed by an adjacent two-seed determinant.

The abstract result below proves the factor-two bound.  The explicit
two-dimensional nilpotent realizes the obstruction: every diagonal value is
bounded by the energy, while one independent unit-vector cross has norm two.
This finite model is also compatible with viewing the cross as one off-diagonal
block of a Hermitian Toeplitz form, so common-shift covariance adds no missing
constant-one estimate.
-/

/-- A diagonal (numerical-radius) bound for a complex-linear operator. -/
def HasNumericalRadiusBound {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (w : ℝ) : Prop :=
  ∀ x : E, ‖inner ℂ (T x) x‖ ≤ w * ‖x‖ ^ 2

/-- Polarization of a numerical-radius bound gives the sum-of-squares bound. -/
theorem norm_inner_map_le_numericalRadius_mul_add_sq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) {w : ℝ}
    (hT : HasNumericalRadiusBound T w) (x y : E) :
    ‖inner ℂ (T x) y‖ ≤ w * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [inner_map_polarization']
  let q : E → ℂ := fun z ↦ inner ℂ (T z) z
  have hnorm :
      ‖q (x + y) - q (x - y) - Complex.I * q (x + Complex.I • y) +
          Complex.I * q (x - Complex.I • y)‖ ≤
        ‖q (x + y)‖ + ‖q (x - y)‖ +
          ‖q (x + Complex.I • y)‖ + ‖q (x - Complex.I • y)‖ := by
    calc
      ‖q (x + y) - q (x - y) - Complex.I * q (x + Complex.I • y) +
          Complex.I * q (x - Complex.I • y)‖
          ≤ ‖q (x + y) - q (x - y) - Complex.I * q (x + Complex.I • y)‖ +
              ‖Complex.I * q (x - Complex.I • y)‖ := norm_add_le _ _
      _ ≤ (‖q (x + y) - q (x - y)‖ +
              ‖Complex.I * q (x + Complex.I • y)‖) +
              ‖Complex.I * q (x - Complex.I • y)‖ := by
            gcongr
            exact norm_sub_le _ _
      _ ≤ ((‖q (x + y)‖ + ‖q (x - y)‖) +
              ‖Complex.I * q (x + Complex.I • y)‖) +
              ‖Complex.I * q (x - Complex.I • y)‖ := by
            gcongr
            exact norm_sub_le _ _
      _ = ‖q (x + y)‖ + ‖q (x - y)‖ +
          ‖q (x + Complex.I • y)‖ + ‖q (x - Complex.I • y)‖ := by
            simp only [norm_mul, norm_I, one_mul]
  have hplus := hT (x + y)
  have hminus := hT (x - y)
  have hIplus := hT (x + Complex.I • y)
  have hIminus := hT (x - Complex.I • y)
  change ‖q (x + y)‖ ≤ w * ‖x + y‖ ^ 2 at hplus
  change ‖q (x - y)‖ ≤ w * ‖x - y‖ ^ 2 at hminus
  change ‖q (x + Complex.I • y)‖ ≤
    w * ‖x + Complex.I • y‖ ^ 2 at hIplus
  change ‖q (x - Complex.I • y)‖ ≤
    w * ‖x - Complex.I • y‖ ^ 2 at hIminus
  have hpar := parallelogram_law_with_norm ℂ x y
  have hparI := parallelogram_law_with_norm ℂ x (Complex.I • y)
  simp only [norm_smul, norm_I, one_mul] at hparI
  have hsum :
      ‖q (x + y)‖ + ‖q (x - y)‖ +
          ‖q (x + Complex.I • y)‖ + ‖q (x - Complex.I • y)‖ ≤
        4 * w * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    calc
      ‖q (x + y)‖ + ‖q (x - y)‖ +
          ‖q (x + Complex.I • y)‖ + ‖q (x - Complex.I • y)‖ ≤
          w * ‖x + y‖ ^ 2 + w * ‖x - y‖ ^ 2 +
            w * ‖x + Complex.I • y‖ ^ 2 +
              w * ‖x - Complex.I • y‖ ^ 2 := by gcongr
      _ = w * ((‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) +
          (‖x + Complex.I • y‖ ^ 2 +
            ‖x - Complex.I • y‖ ^ 2)) := by ring
      _ = w * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) +
          2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by rw [hpar, hparI]
      _ = 4 * w * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring
  have hnorm' :
      ‖inner ℂ (T x + T y) (x + y) -
          inner ℂ (T x - T y) (x - y) -
          Complex.I * inner ℂ (T x + Complex.I • T y)
            (x + Complex.I • y) +
          Complex.I * inner ℂ (T x - Complex.I • T y)
            (x - Complex.I • y)‖ ≤
        ‖q (x + y)‖ + ‖q (x - y)‖ +
          ‖q (x + Complex.I • y)‖ + ‖q (x - Complex.I • y)‖ := by
    simpa only [q, map_add, map_sub, map_smul] using hnorm
  rw [norm_div]
  norm_num
  have hbound := hnorm'.trans hsum
  linarith

/-- The numerical-radius estimate controls every independent matrix
coefficient with the sharp universal loss `2`. -/
theorem norm_inner_map_le_two_mul_numericalRadius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) {w : ℝ}
    (hT : HasNumericalRadiusBound T w) (x y : E) :
    ‖inner ℂ (T x) y‖ ≤ 2 * w * ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let ux : E := (((‖x‖⁻¹ : ℝ) : ℂ)) • x
  let uy : E := (((‖y‖⁻¹ : ℝ) : ℂ)) • y
  have hux : ‖ux‖ = 1 := by
    dsimp only [ux]
    rw [norm_smul]
    simp [hxpos.ne']
  have huy : ‖uy‖ = 1 := by
    dsimp only [uy]
    rw [norm_smul]
    simp [hypos.ne']
  have hscaled :=
    norm_inner_map_le_numericalRadius_mul_add_sq T hT ux uy
  rw [hux, huy] at hscaled
  norm_num at hscaled
  have hscale :
      inner ℂ (T ux) uy =
        (((‖x‖⁻¹ * ‖y‖⁻¹ : ℝ) : ℂ)) * inner ℂ (T x) y := by
    dsimp only [ux, uy]
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp
    ring
  rw [hscale, norm_mul] at hscaled
  have hcoeff :
      ‖((↑(‖x‖⁻¹ * ‖y‖⁻¹) : ℂ))‖ = ‖x‖⁻¹ * ‖y‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hxpos) (inv_pos.mpr hypos))]
  rw [hcoeff] at hscaled
  calc
    ‖inner ℂ (T x) y‖ =
        (‖x‖ * ‖y‖) * ((‖x‖⁻¹ * ‖y‖⁻¹) *
          ‖inner ℂ (T x) y‖) := by
            field_simp [hxpos.ne', hypos.ne']
    _ ≤ (‖x‖ * ‖y‖) * (w * 2) := by
      exact mul_le_mul_of_nonneg_left hscaled (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 2 * w * ‖x‖ * ‖y‖ := by ring

/-! ## Sharp two-dimensional obstruction -/

/-- The two-dimensional nilpotent with matrix `[[0, 2], [0, 0]]`. -/
def sameSeedNilpotent :
    EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := EuclideanSpace.single 0 (2 * z 1)
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' c x := by
    ext i
    fin_cases i
    · simp
      ring
    · simp

/-- The nilpotent has numerical radius at most one.  This is the exact
abstract analogue of every same-seed factor-two pencil being nonnegative. -/
theorem sameSeedNilpotent_hasNumericalRadiusBound :
    HasNumericalRadiusBound sameSeedNilpotent 1 := by
  intro z
  change ‖inner ℂ (EuclideanSpace.single 0 (2 * z 1)) z‖ ≤ 1 * ‖z‖ ^ 2
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.norm_sq_eq]
  simp only [norm_mul, Fin.sum_univ_two, one_mul]
  have hleft :
      ‖(starRingEnd ℂ) (2 * z 1)‖ * ‖z 0‖ = 2 * ‖z 1‖ * ‖z 0‖ := by
    rw [starRingEnd_apply, norm_star, norm_mul]
    norm_num
  rw [hleft]
  nlinarith [sq_nonneg (‖z 0‖ - ‖z 1‖)]

/-- Coordinate vectors exposing the independent cross of the nilpotent. -/
def sameSeedNilpotentSource : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 1 1

def sameSeedNilpotentTarget : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1

/-- The independent source-target coefficient has norm exactly two. -/
theorem sameSeedNilpotent_independent_cross_norm :
    ‖inner ℂ (sameSeedNilpotent sameSeedNilpotentSource)
      sameSeedNilpotentTarget‖ = 2 := by
  norm_num [sameSeedNilpotent, sameSeedNilpotentSource,
    sameSeedNilpotentTarget, EuclideanSpace.inner_single_left]

/-- Both source and target vectors have unit energy. -/
theorem sameSeedNilpotent_source_target_norm :
    ‖sameSeedNilpotentSource‖ = 1 ∧ ‖sameSeedNilpotentTarget‖ = 1 := by
  constructor <;>
    simp [sameSeedNilpotentSource, sameSeedNilpotentTarget,
      PiLp.norm_single]

/-- Constant one cannot replace the universal polarization loss two: the
same-seed diagonal bound holds, while the independent determinant bound
fails by the exact factor four after squaring. -/
theorem sameSeedNilpotent_not_independent_contraction :
    ‖inner ℂ (sameSeedNilpotent sameSeedNilpotentSource)
        sameSeedNilpotentTarget‖ ^ 2 >
      ‖sameSeedNilpotentSource‖ ^ 2 * ‖sameSeedNilpotentTarget‖ ^ 2 := by
  rw [sameSeedNilpotent_independent_cross_norm]
  obtain ⟨hsource, htarget⟩ := sameSeedNilpotent_source_target_norm
  rw [hsource, htarget]
  norm_num

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
