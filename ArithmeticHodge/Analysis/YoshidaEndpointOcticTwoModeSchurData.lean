import ArithmeticHodge.Analysis.FixedTwoModeQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointOcticTwoModeSchurData

open YoshidaEndpointOcticPotential
open FixedTwoModeQuadratic

noncomputable section

/-- The component of `q P₁` orthogonal to the fixed `P₁,P₃` block. -/
def octicResidualP1 (x : ℝ) : ℝ :=
  yoshidaEndpointOctic x * centeredP1 x -
    (13771 / 27720 : ℝ) * centeredP1 x -
    (28 / 65 : ℝ) * centeredP3 x

/-- The component of `q P₃` orthogonal to the fixed `P₁,P₃` block. -/
def octicResidualP3 (x : ℝ) : ℝ :=
  yoshidaEndpointOctic x * centeredP3 x -
    (12 / 65 : ℝ) * centeredP1 x -
    (23161 / 51480 : ℝ) * centeredP3 x

/-- Exact squared mass of the unnormalized centered `P₁`. -/
theorem integral_centeredP1_sq :
    (∫ x : ℝ in -1..1, centeredP1 x ^ 2) = 2 / 3 := by
  simp only [centeredP1]
  rw [integral_pow_nat]
  norm_num

/-- Exact orthogonality of the two unnormalized centered modes. -/
theorem integral_centeredP1_mul_p3 :
    (∫ x : ℝ in -1..1, centeredP1 x * centeredP3 x) = 0 := by
  rw [show (fun x : ℝ ↦ centeredP1 x * centeredP3 x) =
    fun x ↦ x ^ 4 * (5 / 2) + x ^ 2 * (-3 / 2) by
    funext x
    simp only [centeredP1, centeredP3]
    ring]
  rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const,
    integral_pow_nat, integral_pow_nat]
  norm_num

/-- Exact squared mass of the unnormalized centered `P₃`. -/
theorem integral_centeredP3_sq :
    (∫ x : ℝ in -1..1, centeredP3 x ^ 2) = 2 / 7 := by
  rw [show (fun x : ℝ ↦ centeredP3 x ^ 2) =
    fun x ↦ x ^ 6 * (25 / 4) + x ^ 4 * (-15 / 2) + x ^ 2 * (9 / 4) by
    funext x
    simp only [centeredP3]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octicResidualP1_mul_p1 :
    (∫ x : ℝ in -1..1, octicResidualP1 x * centeredP1 x) = 0 := by
  rw [show (fun x : ℝ ↦ octicResidualP1 x * centeredP1 x) =
    fun x ↦ yoshidaEndpointOctic x * centeredP1 x ^ 2 +
      (-13771 / 27720 : ℝ) * centeredP1 x ^ 2 +
      (-28 / 65 : ℝ) * (centeredP1 x * centeredP3 x) by
    funext x
    simp only [octicResidualP1]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_mul_p1_sq, integral_centeredP1_sq,
    integral_centeredP1_mul_p3]
  norm_num

theorem integral_octicResidualP1_mul_p3 :
    (∫ x : ℝ in -1..1, octicResidualP1 x * centeredP3 x) = 0 := by
  rw [show (fun x : ℝ ↦ octicResidualP1 x * centeredP3 x) =
    fun x ↦ yoshidaEndpointOctic x * centeredP1 x * centeredP3 x +
      (-13771 / 27720 : ℝ) * (centeredP1 x * centeredP3 x) +
      (-28 / 65 : ℝ) * centeredP3 x ^ 2 by
    funext x
    simp only [octicResidualP1]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_mul_p1_mul_p3, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  norm_num

theorem integral_octicResidualP3_mul_p1 :
    (∫ x : ℝ in -1..1, octicResidualP3 x * centeredP1 x) = 0 := by
  rw [show (fun x : ℝ ↦ octicResidualP3 x * centeredP1 x) =
    fun x ↦ yoshidaEndpointOctic x * centeredP1 x * centeredP3 x +
      (-12 / 65 : ℝ) * centeredP1 x ^ 2 +
      (-23161 / 51480 : ℝ) * (centeredP1 x * centeredP3 x) by
    funext x
    simp only [octicResidualP3]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_mul_p1_mul_p3, integral_centeredP1_sq,
    integral_centeredP1_mul_p3]
  norm_num

theorem integral_octicResidualP3_mul_p3 :
    (∫ x : ℝ in -1..1, octicResidualP3 x * centeredP3 x) = 0 := by
  rw [show (fun x : ℝ ↦ octicResidualP3 x * centeredP3 x) =
    fun x ↦ yoshidaEndpointOctic x * centeredP3 x ^ 2 +
      (-12 / 65 : ℝ) * (centeredP1 x * centeredP3 x) +
      (-23161 / 51480 : ℝ) * centeredP3 x ^ 2 by
    funext x
    simp only [octicResidualP3]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_mul_p3_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  norm_num

/-- Exact `(1,1)` entry of the residual Gram matrix. -/
def residualGramC11 : ℝ := 682243552 / 393230282445

/-- Exact off-diagonal entry of the residual Gram matrix. -/
def residualGramC13 : ℝ := 1116608 / 189143955

/-- Exact `(3,3)` entry of the residual Gram matrix. -/
def residualGramC33 : ℝ := 8663255456 / 430680785535

theorem integral_octicResidualP1_sq :
    (∫ x : ℝ in -1..1, octicResidualP1 x ^ 2) = residualGramC11 := by
  rw [show (fun x : ℝ ↦ octicResidualP1 x ^ 2) = fun x ↦
    yoshidaEndpointOctic x ^ 2 * centeredP1 x ^ 2 +
      (-(2 * (13771 / 27720 : ℝ))) *
        (yoshidaEndpointOctic x * centeredP1 x ^ 2) +
      (-(2 * (28 / 65 : ℝ))) *
        (yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) +
      (13771 / 27720 : ℝ) ^ 2 * centeredP1 x ^ 2 +
      (2 * (13771 / 27720 : ℝ) * (28 / 65 : ℝ)) *
        (centeredP1 x * centeredP3 x) +
      (28 / 65 : ℝ) ^ 2 * centeredP3 x ^ 2 by
    funext x
    simp only [octicResidualP1]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_sq_mul_p1_sq, integral_octic_mul_p1_sq,
    integral_octic_mul_p1_mul_p3, integral_centeredP1_sq,
    integral_centeredP1_mul_p3, integral_centeredP3_sq]
  norm_num [residualGramC11]

theorem integral_octicResidualP1_mul_residualP3 :
    (∫ x : ℝ in -1..1, octicResidualP1 x * octicResidualP3 x) =
      residualGramC13 := by
  rw [show (fun x : ℝ ↦ octicResidualP1 x * octicResidualP3 x) = fun x ↦
    yoshidaEndpointOctic x ^ 2 * centeredP1 x * centeredP3 x +
      (-(12 / 65 : ℝ)) *
        (yoshidaEndpointOctic x * centeredP1 x ^ 2) +
      (-((23161 / 51480 : ℝ) + (13771 / 27720 : ℝ))) *
        (yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) +
      (-(28 / 65 : ℝ)) *
        (yoshidaEndpointOctic x * centeredP3 x ^ 2) +
      ((13771 / 27720 : ℝ) * (12 / 65 : ℝ)) * centeredP1 x ^ 2 +
      ((13771 / 27720 : ℝ) * (23161 / 51480 : ℝ) +
        (28 / 65 : ℝ) * (12 / 65 : ℝ)) *
          (centeredP1 x * centeredP3 x) +
      ((28 / 65 : ℝ) * (23161 / 51480 : ℝ)) * centeredP3 x ^ 2 by
    funext x
    simp only [octicResidualP1, octicResidualP3]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_sq_mul_p1_mul_p3, integral_octic_mul_p1_sq,
    integral_octic_mul_p1_mul_p3, integral_octic_mul_p3_sq,
    integral_centeredP1_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  norm_num [residualGramC13]

theorem integral_octicResidualP3_sq :
    (∫ x : ℝ in -1..1, octicResidualP3 x ^ 2) = residualGramC33 := by
  rw [show (fun x : ℝ ↦ octicResidualP3 x ^ 2) = fun x ↦
    yoshidaEndpointOctic x ^ 2 * centeredP3 x ^ 2 +
      (-(2 * (12 / 65 : ℝ))) *
        (yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) +
      (-(2 * (23161 / 51480 : ℝ))) *
        (yoshidaEndpointOctic x * centeredP3 x ^ 2) +
      (12 / 65 : ℝ) ^ 2 * centeredP1 x ^ 2 +
      (2 * (12 / 65 : ℝ) * (23161 / 51480 : ℝ)) *
        (centeredP1 x * centeredP3 x) +
      (23161 / 51480 : ℝ) ^ 2 * centeredP3 x ^ 2 by
    funext x
    simp only [octicResidualP3]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octic_sq_mul_p3_sq, integral_octic_mul_p1_mul_p3,
    integral_octic_mul_p3_sq, integral_centeredP1_sq,
    integral_centeredP1_mul_p3, integral_centeredP3_sq]
  norm_num [residualGramC33]

/-- Raw `(1,1)` low-block entry after subtracting the target `7/5`. -/
def rawLowQ11 : ℝ := 2683 / 41580

/-- Raw off-diagonal low-block entry after subtracting the target `7/5`. -/
def rawLowQ13 : ℝ := 8 / 65

/-- Raw `(3,3)` low-block entry after subtracting the target `7/5`. -/
def rawLowQ33 : ℝ := 45469 / 180180

/-- Uniform reserve left in the odd tail after the target `7/5`. -/
def tailReserve : ℝ := 53 / 60

/-- `(1,1)` entry after the exact residual Schur loss. -/
def schurS11 : ℝ := rawLowQ11 - residualGramC11 / tailReserve

/-- Off-diagonal entry after the exact residual Schur loss. -/
def schurS13 : ℝ := rawLowQ13 - residualGramC13 / tailReserve

/-- `(3,3)` entry after the exact residual Schur loss. -/
def schurS33 : ℝ := rawLowQ33 - residualGramC33 / tailReserve

theorem one_sixteenth_lt_schurS11 : (1 / 16 : ℝ) < schurS11 := by
  norm_num [schurS11, rawLowQ11, residualGramC11, tailReserve]

theorem abs_schurS13_lt_seven_sixtieth : |schurS13| < (7 / 60 : ℝ) := by
  norm_num [schurS13, rawLowQ13, residualGramC13, tailReserve,
    abs_of_nonneg]

theorem eleven_forty_eighths_lt_schurS33 : (11 / 48 : ℝ) < schurS33 := by
  norm_num [schurS33, rawLowQ33, residualGramC33, tailReserve]

/-- The three exact scalar comparisons imply positivity of the fixed Schur block. -/
theorem schurQuadratic_nonneg (a b : ℝ) :
    0 ≤ schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 := by
  exact nonneg_of_fixed_comparison
    (le_of_lt one_sixteenth_lt_schurS11)
    (le_of_lt abs_schurS13_lt_seven_sixtieth)
    (le_of_lt eleven_forty_eighths_lt_schurS33)

end


end ArithmeticHodge.Analysis.YoshidaEndpointOcticTwoModeSchurData
