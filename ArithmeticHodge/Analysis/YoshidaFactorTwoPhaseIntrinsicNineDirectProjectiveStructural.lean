import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectDiskBoundaryStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction

/-!
# Projective circle reduction for the direct cutoff-nine matrix

The direct retained quadratic is affine in the two phase coordinates.  On the
rational chart of the phase circle, its positive homogenization is therefore
a quadratic pencil in the tangent parameter.  This keeps the phase-native
matrix intact and introduces no static transfer.
-/

/-- Positive homogenization of the direct cutoff-nine quadratic on the
rational circle chart.  The two endpoint quadratics are its constant and
quadratic coefficients; the alternating coefficient remains linear in `t`. -/
def factorTwoIntrinsicNineDirectProjectiveQuadratic
    (t x : ℝ) (c : Fin 9 → ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectCoordinateQuadratic 1 0 c +
    x * factorTwoIntrinsicNineDirectCoordinateQuadratic (-1) 0 c +
    2 * t *
      (factorTwoIntrinsicNineDirectCoordinateQuadratic 0 1 c -
        factorTwoIntrinsicNineDirectCoordinateQuadratic 0 0 c)

/-- Matrix form of the same projective pencil. -/
def factorTwoIntrinsicNineDirectProjectiveMatrix
    (t x : ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  factorTwoIntrinsicNineDirectLowMatrix 1 0 +
    x • factorTwoIntrinsicNineDirectLowMatrix (-1) 0 +
    (2 * t) •
      (factorTwoIntrinsicNineDirectLowMatrix 0 1 -
        factorTwoIntrinsicNineDirectLowMatrix 0 0)

private theorem factorTwoIntrinsicNineDirectCoordinateBilinear_affine_phase
    (a b : ℝ) (c d : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateBilinear a b c d =
      factorTwoIntrinsicNineDirectCoordinateBilinear 0 0 c d +
        a * (factorTwoIntrinsicNineDirectCoordinateBilinear 1 0 c d -
          factorTwoIntrinsicNineDirectCoordinateBilinear 0 0 c d) +
        b * (factorTwoIntrinsicNineDirectCoordinateBilinear 0 1 c d -
          factorTwoIntrinsicNineDirectCoordinateBilinear 0 0 c d) := by
  have hsum := factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase
    a b (c + d)
  have hc := factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase
    a b c
  have hd := factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase
    a b d
  unfold factorTwoIntrinsicNineDirectCoordinateBilinear
  rw [hsum, hc, hd]
  ring

/-- The direct matrix itself is affine in the phase coordinates. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_affine_phase
    (a b : ℝ) :
    factorTwoIntrinsicNineDirectLowMatrix a b =
      factorTwoIntrinsicNineDirectLowMatrix 0 0 +
        a • (factorTwoIntrinsicNineDirectLowMatrix 1 0 -
          factorTwoIntrinsicNineDirectLowMatrix 0 0) +
        b • (factorTwoIntrinsicNineDirectLowMatrix 0 1 -
          factorTwoIntrinsicNineDirectLowMatrix 0 0) := by
  ext i j
  change factorTwoIntrinsicNineDirectCoordinateBilinear a b
      (factorTwoIntrinsicNineDirectUnit i)
      (factorTwoIntrinsicNineDirectUnit j) = _
  simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul] using
      factorTwoIntrinsicNineDirectCoordinateBilinear_affine_phase
        a b (factorTwoIntrinsicNineDirectUnit i)
          (factorTwoIntrinsicNineDirectUnit j)

/-- Exact matrix homogenization on the rational circle chart. -/
theorem factorTwoIntrinsicNineDirectProjectiveMatrix_eq_phase
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectProjectiveMatrix t x =
      (1 + x) • factorTwoIntrinsicNineDirectLowMatrix
        ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  subst x
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hphase := factorTwoIntrinsicNineDirectLowMatrix_affine_phase
    ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
  have hminus := factorTwoIntrinsicNineDirectLowMatrix_affine_phase (-1) 0
  unfold factorTwoIntrinsicNineDirectProjectiveMatrix
  rw [hphase, hminus]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

/-- Reflection of the four odd coordinates in the direct coordinate order. -/
def factorTwoIntrinsicNineDirectParityFlip
    (c : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![c 0, c 1, c 2, -c 3, -c 4, -c 5, c 6, c 7, -c 8]

@[simp]
theorem factorTwoIntrinsicNineDirectParityFlip_apply_apply
    (c : Fin 9 → ℝ) (i : Fin 9) :
    factorTwoIntrinsicNineDirectParityFlip
        (factorTwoIntrinsicNineDirectParityFlip c) i = c i := by
  fin_cases i <;> simp [factorTwoIntrinsicNineDirectParityFlip]

@[simp]
theorem factorTwoIntrinsicNineDirectParityFlip_involutive
    (c : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectParityFlip
        (factorTwoIntrinsicNineDirectParityFlip c) = c := by
  funext i
  exact factorTwoIntrinsicNineDirectParityFlip_apply_apply c i

/-- Changing the sign of the alternating phase is congruent to reflecting
all retained odd coordinates. -/
theorem factorTwoIntrinsicNineDirectCoordinateQuadratic_parityFlip
    (a b : ℝ) (c : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateQuadratic a b
        (factorTwoIntrinsicNineDirectParityFlip c) =
      factorTwoIntrinsicNineDirectCoordinateQuadratic a (-b) c := by
  unfold factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicNineDirectParityFlip
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicNineP678LowReserve
  simp
  ring

/-- Projective reflection: changing the sign of the tangent parameter is
absorbed by the odd-coordinate congruence. -/
theorem factorTwoIntrinsicNineDirectProjectiveQuadratic_neg_t
    (t x : ℝ) (c : Fin 9 → ℝ) :
    factorTwoIntrinsicNineDirectProjectiveQuadratic (-t) x c =
      factorTwoIntrinsicNineDirectProjectiveQuadratic t x
        (factorTwoIntrinsicNineDirectParityFlip c) := by
  unfold factorTwoIntrinsicNineDirectProjectiveQuadratic
  rw [factorTwoIntrinsicNineDirectCoordinateQuadratic_parityFlip,
    factorTwoIntrinsicNineDirectCoordinateQuadratic_parityFlip,
    factorTwoIntrinsicNineDirectCoordinateQuadratic_parityFlip,
    factorTwoIntrinsicNineDirectCoordinateQuadratic_parityFlip]
  simp only [neg_zero]
  rw [factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase 0 (-1) c]
  ring

/-- Consequently only the nonnegative projective half-line needs a proof. -/
theorem factorTwoIntrinsicNineDirectProjectiveQuadratic_nonneg_of_nonnegative
    (h : ∀ t : ℝ, 0 ≤ t → ∀ c : Fin 9 → ℝ,
      0 ≤ factorTwoIntrinsicNineDirectProjectiveQuadratic t (t ^ 2) c) :
    ∀ t : ℝ, ∀ c : Fin 9 → ℝ,
      0 ≤ factorTwoIntrinsicNineDirectProjectiveQuadratic t (t ^ 2) c := by
  intro t c
  by_cases ht : 0 ≤ t
  · exact h t ht c
  · have hneg : 0 ≤ -t := by linarith
    have hvalue := h (-t) hneg (factorTwoIntrinsicNineDirectParityFlip c)
    rw [factorTwoIntrinsicNineDirectProjectiveQuadratic_neg_t,
      neg_sq] at hvalue
    simpa only [factorTwoIntrinsicNineDirectParityFlip_involutive] using hvalue

/-- Exact rational-circle homogenization. -/
theorem factorTwoIntrinsicNineDirectProjectiveQuadratic_eq_phase
    (t x : ℝ) (c : Fin 9 → ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectProjectiveQuadratic t x c =
      (1 + x) *
        factorTwoIntrinsicNineDirectCoordinateQuadratic
          ((1 - x) / (1 + x)) (2 * t / (1 + x)) c := by
  subst x
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hphase :=
    factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase
      ((1 - t ^ 2) / (1 + t ^ 2))
      (2 * t / (1 + t ^ 2)) c
  have hminus :=
    factorTwoIntrinsicNineDirectCoordinateQuadratic_affine_phase (-1) 0 c
  rw [hphase]
  unfold factorTwoIntrinsicNineDirectProjectiveQuadratic
  rw [hminus]
  field_simp [hden]
  ring

/-- Every point of the unit circle except `(-1,0)` lies in the rational
projective chart with tangent parameter `b / (1 + a)`. -/
theorem unitCircle_eq_projectiveChart
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (ha : a ≠ -1) :
    let t := b / (1 + a)
    a = (1 - t ^ 2) / (1 + t ^ 2) ∧
      b = 2 * t / (1 + t ^ 2) := by
  dsimp only
  have hden : 1 + a ≠ 0 := by
    intro h
    apply ha
    linarith
  have hnorm : (1 + a) ^ 2 + b ^ 2 = 2 * (1 + a) := by
    nlinarith
  constructor
  · field_simp [hden]
    nlinarith
  · field_simp [hden]
    rw [hnorm]
    ring

/-- The phase-native projective pencil, together with the chart endpoint,
is sufficient for positive semidefiniteness of the direct matrix on the
entire unit circle. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_projective
    (hminus :
      (factorTwoIntrinsicNineDirectLowMatrix (-1) 0).PosSemidef)
    (hprojective : ∀ t : ℝ, ∀ c : Fin 9 → ℝ,
      0 ≤ factorTwoIntrinsicNineDirectProjectiveQuadratic t (t ^ 2) c)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  by_cases ha : a = -1
  · have hb : b = 0 := by
      rw [ha] at hab
      nlinarith [sq_nonneg b]
    simpa only [ha, hb] using hminus
  · let t := b / (1 + a)
    obtain ⟨haChart, hbChart⟩ := unitCircle_eq_projectiveChart a b hab ha
    apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_nonneg
    intro c
    have hproj := hprojective t c
    rw [factorTwoIntrinsicNineDirectProjectiveQuadratic_eq_phase
      t (t ^ 2) c rfl, ← haChart, ← hbChart] at hproj
    exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hproj)
      (by positivity : 0 < 1 + t ^ 2)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural
