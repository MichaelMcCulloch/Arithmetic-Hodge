import ArithmeticHodge.Analysis.ShiftedLegendreJacobiRecurrenceStructural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreDiagonalStructural

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreJacobiRecurrenceStructural
open YoshidaEndpointPotentialBound
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialLegendreOffDiagonalStructural

noncomputable section

/-!
# All-degree diagonal endpoint-potential Legendre recurrence

The Jacobi recurrence and the closed distance-two off-diagonal entries
determine every diagonal entry from the zero mode.  This is a uniform
structural argument: no Legendre mode is expanded.
-/

/-- The endpoint-potential bilinear form on real polynomials. -/
def endpointPotentialPolynomialPair (p q : ℝ[X]) : ℝ :=
  ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * p.eval x * q.eval x

/-- The diagonal endpoint-potential entry in centered Legendre degree `n`. -/
def endpointPotentialLegendreDiagonal (n : ℕ) : ℝ :=
  endpointPotentialPolynomialPair
    (centeredShiftedLegendreReal n)
    (centeredShiftedLegendreReal n)

/-- The diagonal recurrence starts from the exact total endpoint-potential
mass. -/
theorem endpointPotentialLegendreDiagonal_zero :
    endpointPotentialLegendreDiagonal 0 = 2 - 2 * Real.log 2 := by
  simp [endpointPotentialLegendreDiagonal, endpointPotentialPolynomialPair,
    integral_endpointPotential_one]

private theorem continuous_polynomialEval (p : ℝ[X]) :
    Continuous (fun x : ℝ ↦ p.eval x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (p.hasDerivAt x).continuousAt

private theorem intervalIntegrable_endpointPotentialPolynomialPair
    (p q : ℝ[X]) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x * q.eval x)
      volume (-1) 1 := by
  simpa only [mul_assoc] using
    intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ p.eval x * q.eval x)
      ((continuous_polynomialEval p).mul (continuous_polynomialEval q))

private theorem endpointPotentialPolynomialPair_smul_left
    (c : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (c • p) q =
      c * endpointPotentialPolynomialPair p q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (c • p).eval x * q.eval x) =
    fun x : ℝ ↦
      c * (yoshidaEndpointPotential x * p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem endpointPotentialPolynomialPair_sub_left
    (p r q : ℝ[X]) :
    endpointPotentialPolynomialPair (p - r) q =
      endpointPotentialPolynomialPair p q -
        endpointPotentialPolynomialPair r q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (p - r).eval x * q.eval x) =
    fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * q.eval x -
        yoshidaEndpointPotential x * r.eval x * q.eval x by
    funext x
    simp only [Polynomial.eval_sub]
    ring,
    intervalIntegral.integral_sub
      (intervalIntegrable_endpointPotentialPolynomialPair p q)
      (intervalIntegrable_endpointPotentialPolynomialPair r q)]

private theorem endpointPotentialPolynomialPair_neg_left
    (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (-p) q =
      -endpointPotentialPolynomialPair p q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (-p).eval x * q.eval x) =
    fun x : ℝ ↦
      -(yoshidaEndpointPotential x * p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_neg]
    ring,
    intervalIntegral.integral_neg]

private theorem endpointPotentialPolynomialPair_comm (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p q =
      endpointPotentialPolynomialPair q p := by
  unfold endpointPotentialPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem endpointPotentialPolynomialPair_smul_right
    (c : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p (c • q) =
      c * endpointPotentialPolynomialPair p q := by
  calc
    _ = endpointPotentialPolynomialPair (c • q) p :=
      endpointPotentialPolynomialPair_comm _ _
    _ = c * endpointPotentialPolynomialPair q p :=
      endpointPotentialPolynomialPair_smul_left _ _ _
    _ = _ := by rw [endpointPotentialPolynomialPair_comm q p]

private theorem endpointPotentialPolynomialPair_sub_right
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair p (q - r) =
      endpointPotentialPolynomialPair p q -
        endpointPotentialPolynomialPair p r := by
  calc
    _ = endpointPotentialPolynomialPair (q - r) p :=
      endpointPotentialPolynomialPair_comm _ _
    _ = endpointPotentialPolynomialPair q p -
          endpointPotentialPolynomialPair r p :=
      endpointPotentialPolynomialPair_sub_left _ _ _
    _ = _ := by
      rw [endpointPotentialPolynomialPair_comm q p,
        endpointPotentialPolynomialPair_comm r p]

private theorem endpointPotentialPolynomialPair_neg_right
    (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p (-q) =
      -endpointPotentialPolynomialPair p q := by
  calc
    _ = endpointPotentialPolynomialPair (-q) p :=
      endpointPotentialPolynomialPair_comm _ _
    _ = -endpointPotentialPolynomialPair q p :=
      endpointPotentialPolynomialPair_neg_left _ _
    _ = _ := by rw [endpointPotentialPolynomialPair_comm q p]

/-- Multiplication by the centered coordinate is self-adjoint for the
endpoint-potential bilinear form. -/
theorem endpointPotentialPolynomialPair_X (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (X * p) q =
      endpointPotentialPolynomialPair p (X * q) := by
  unfold endpointPotentialPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- Every distance-two off-diagonal entry has the simple value
`1 / (2n + 3)`. -/
theorem endpointPotentialPolynomialPair_distance_two (n : ℕ) :
    endpointPotentialPolynomialPair
        (centeredShiftedLegendreReal n)
        (centeredShiftedLegendreReal (n + 2)) =
      1 / (2 * (n : ℝ) + 3) := by
  have h :=
    integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := n) (n := n + 2) (by omega)
      (show Even (n + (n + 2)) from ⟨n + 1, by omega⟩)
  change endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal n)
      (centeredShiftedLegendreReal (n + 2)) =
    2 / ((((n + 2 : ℕ) : ℝ) - n) *
      (((n + 2 : ℕ) : ℝ) + n + 1)) at h
  rw [h]
  have hden :
      ((((n + 2 : ℕ) : ℝ) - n) *
          (((n + 2 : ℕ) : ℝ) + n + 1)) =
        2 * (2 * (n : ℝ) + 3) := by
    push_cast
    ring
  rw [hden]
  have hn : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn]

private theorem endpointPotentialPolynomialPair_lower_distance_two_weighted
    (n : ℕ) :
    (n : ℝ) * endpointPotentialPolynomialPair
        (centeredShiftedLegendreReal (n - 1))
        (centeredShiftedLegendreReal (n + 1)) =
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
  cases n with
  | zero => norm_num
  | succ k =>
      rw [show k + 1 - 1 = k by omega,
        show k + 1 + 1 = k + 2 by omega,
        endpointPotentialPolynomialPair_distance_two k]
      push_cast
      ring

/-- Uniform diagonal recurrence.  Its correction term comes entirely from
the two distance-two entries adjacent to degree `n`. -/
theorem endpointPotentialLegendreDiagonal_succ (n : ℕ) :
    (2 * (n : ℝ) + 3) * endpointPotentialLegendreDiagonal (n + 1) =
      (2 * (n : ℝ) + 1) * endpointPotentialLegendreDiagonal n +
        2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
          (2 * (n : ℝ) + 3)) := by
  let Q : ℕ → ℝ[X] := centeredShiftedLegendreReal
  let P : ℝ[X] → ℝ[X] → ℝ := endpointPotentialPolynomialPair
  let D : ℕ → ℝ := fun k ↦ P (Q k) (Q k)
  let M : ℕ → ℕ → ℝ := fun i j ↦ P (Q i) (Q j)
  let K : ℝ := P (X * Q n) (Q (n + 1))
  have hN :
      (((n + 1 : ℕ) : ℝ) * D (n + 1)) =
        -(((2 * n + 1 : ℕ) : ℝ) * K) -
          (n : ℝ) * M (n - 1) (n + 1) := by
    have h := congrArg
      (fun p : ℝ[X] ↦ endpointPotentialPolynomialPair p
        (centeredShiftedLegendreReal (n + 1)))
      (centeredShiftedLegendreReal_recurrence n)
    simp only [endpointPotentialPolynomialPair_smul_left,
      endpointPotentialPolynomialPair_sub_left,
      endpointPotentialPolynomialPair_neg_left] at h
    simpa only [Q, P, D, M, K] using h
  have hNext :
      (((n + 2 : ℕ) : ℝ) * M n (n + 2)) =
        -(((2 * n + 3 : ℕ) : ℝ) * K) -
          (((n + 1 : ℕ) : ℝ) * D n) := by
    have h := congrArg
      (fun p : ℝ[X] ↦ endpointPotentialPolynomialPair
        (centeredShiftedLegendreReal n) p)
      (centeredShiftedLegendreReal_recurrence (n + 1))
    simp only [endpointPotentialPolynomialPair_smul_right,
      endpointPotentialPolynomialPair_sub_right,
      endpointPotentialPolynomialPair_neg_right] at h
    rw [← endpointPotentialPolynomialPair_X
      (centeredShiftedLegendreReal n)
      (centeredShiftedLegendreReal (n + 1))] at h
    simpa only [Q, P, D, M, K, Nat.add_sub_cancel,
      show n + 1 + 1 = n + 2 by omega,
      show 2 * (n + 1) + 1 = 2 * n + 3 by omega] using h
  have hminusWeighted :
      (n : ℝ) * M (n - 1) (n + 1) =
        (n : ℝ) / (2 * (n : ℝ) + 1) := by
    simpa only [M, P, Q] using
      endpointPotentialPolynomialPair_lower_distance_two_weighted n
  have hoffTwo :
      M n (n + 2) = 1 / (2 * (n : ℝ) + 3) := by
    simpa only [M, P, Q] using
      endpointPotentialPolynomialPair_distance_two n
  rw [hminusWeighted] at hN
  rw [hoffTwo] at hNext
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN hNext
  have helim :
      (2 * (n : ℝ) + 3) * (n + 1 : ℝ) * D (n + 1) =
        (2 * (n : ℝ) + 1) * (n + 1 : ℝ) * D n +
          ((2 * (n : ℝ) + 1) * (n + 2 : ℝ) /
              (2 * (n : ℝ) + 3) -
            (2 * (n : ℝ) + 3) * (n : ℝ) /
              (2 * (n : ℝ) + 1)) := by
    linear_combination
      (2 * (n : ℝ) + 3) * hN -
        (2 * (n : ℝ) + 1) * hNext
  have hcorr :
      (2 * (n : ℝ) + 1) * (n + 2 : ℝ) /
          (2 * (n : ℝ) + 3) -
        (2 * (n : ℝ) + 3) * (n : ℝ) /
          (2 * (n : ℝ) + 1) =
      2 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
    have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [h1, h3]
    ring
  rw [hcorr] at helim
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hscaled :
      (n + 1 : ℝ) *
          ((2 * (n : ℝ) + 3) * D (n + 1) -
            (2 * (n : ℝ) + 1) * D n) =
        2 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
    calc
      _ = (2 * (n : ℝ) + 3) * (n + 1 : ℝ) * D (n + 1) -
          (2 * (n : ℝ) + 1) * (n + 1 : ℝ) * D n := by ring
      _ = _ := by linarith
  have hdiff :
      (2 * (n : ℝ) + 3) * D (n + 1) -
          (2 * (n : ℝ) + 1) * D n =
        2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
          (2 * (n : ℝ) + 3)) := by
    have hfraction :
        2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
            (2 * (n : ℝ) + 3)) =
          (2 / ((2 * (n : ℝ) + 1) *
            (2 * (n : ℝ) + 3))) / (n + 1 : ℝ) := by
      field_simp [hn1, h1, h3]
    rw [hfraction]
    apply (eq_div_iff hn1).2
    calc
      ((2 * (n : ℝ) + 3) * D (n + 1) -
          (2 * (n : ℝ) + 1) * D n) * (n + 1 : ℝ) =
          (n + 1 : ℝ) *
          ((2 * (n : ℝ) + 3) * D (n + 1) -
            (2 * (n : ℝ) + 1) * D n) := by ring
      _ = 2 / ((2 * (n : ℝ) + 1) *
          (2 * (n : ℝ) + 3)) := hscaled
  change (2 * (n : ℝ) + 3) * D (n + 1) =
    (2 * (n : ℝ) + 1) * D n +
      2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
        (2 * (n : ℝ) + 3))
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreDiagonalStructural
