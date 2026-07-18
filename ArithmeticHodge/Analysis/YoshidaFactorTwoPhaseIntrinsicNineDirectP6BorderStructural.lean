import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural

noncomputable section

open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# The structural `P6` border over the strict six-mode core

The first unresolved cutoff-nine extension is the leading `Fin 7` prefix in
the direct order

`(P0,P2,P4,P1,P3,P5 | P6)`.

This file packages that extension as one scalar border functional.  Its only
analytic input is the strict Cauchy--Schwarz inequality comparing that row to
the already positive-definite six-mode core.  No determinant coefficient is
expanded.
-/

/-- The direct phase-native prefix through `P6`. -/
def factorTwoIntrinsicNineDirectP6PrefixMatrix
    (a b : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  factorTwoIntrinsicNineDirectPrefix 7 (by omega)
    (factorTwoIntrinsicNineDirectLowMatrix a b)

/-- The `P6` row restricted to the first six direct coordinates. -/
def factorTwoIntrinsicNineDirectP6BorderVector
    (a b : ℝ) : Fin 6 → ℝ :=
  fun i ↦ factorTwoIntrinsicNineDirectP6PrefixMatrix a b
    (Fin.castSucc i) (Fin.last 6)

/-- The linear functional carried by the complete `P6` border. -/
def factorTwoIntrinsicNineDirectP6BorderFunctional
    (a b : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x ⬝ᵥ factorTwoIntrinsicNineDirectP6BorderVector a b

/-- The retained `P6` diagonal after the `15 / 16` reserve charge. -/
def factorTwoIntrinsicNineDirectP6RetainedDiagonal
    (a b : ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectP6PrefixMatrix a b
    (Fin.last 6) (Fin.last 6)

theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian
    (a b : ℝ) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).IsHermitian := by
  have hFull :
      (factorTwoIntrinsicNineDirectLowMatrix a b).IsHermitian := by
    simpa only [Matrix.IsHermitian, conjTranspose, star_trivial] using
      factorTwoIntrinsicNineDirectLowMatrix_transpose a b
  exact hFull.submatrix (Fin.castLE (by omega : 7 ≤ 9))

theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_leading
    (a b : ℝ) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).submatrix
        Fin.castSucc Fin.castSucc =
      factorTwoIntrinsicNineDirectCoreMatrix a b := by
  rw [factorTwoIntrinsicNineDirectP6PrefixMatrix,
    factorTwoIntrinsicNineDirectPrefix_succ_leading,
    factorTwoIntrinsicNineDirectPrefix_six_eq_core]

private theorem matrix_quadratic_snoc
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : M.IsHermitian) (x : Fin n → ℝ) (r : ℝ) :
    Fin.snoc x r ⬝ᵥ (M *ᵥ Fin.snoc x r) =
      x ⬝ᵥ ((M.submatrix Fin.castSucc Fin.castSucc) *ᵥ x) +
        2 * r * (x ⬝ᵥ fun i ↦ M (Fin.castSucc i) (Fin.last n)) +
        M (Fin.last n) (Fin.last n) * r ^ 2 := by
  have hcross (i : Fin n) :
      M (Fin.last n) (Fin.castSucc i) =
        M (Fin.castSucc i) (Fin.last n) := by
    have h := hM.apply (Fin.last n) (Fin.castSucc i)
    simpa only [star_trivial] using h.symm
  have hcomm :
      (∑ i : Fin n, M (Fin.castSucc i) (Fin.last n) * x i) =
        ∑ i : Fin n, x i * M (Fin.castSucc i) (Fin.last n) := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hfactor :
      (∑ i : Fin n, x i * (M (Fin.castSucc i) (Fin.last n) * r)) =
        r * ∑ i : Fin n, x i * M (Fin.castSucc i) (Fin.last n) := by
    calc
      _ = ∑ i : Fin n,
          (x i * M (Fin.castSucc i) (Fin.last n)) * r := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i : Fin n,
          x i * M (Fin.castSucc i) (Fin.last n)) * r := by
            rw [Finset.sum_mul]
      _ = _ := by ring
  unfold dotProduct mulVec
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.submatrix_apply]
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last]
  simp_rw [hcross]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [hcomm, hfactor]
  ring

/-- Exact completion-of-the-square coordinates for the `P6` extension. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_quadratic_snoc
    (a b : ℝ) (x : Fin 6 → ℝ) (r : ℝ) :
    Fin.snoc x r ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6PrefixMatrix a b *ᵥ Fin.snoc x r) =
      x ⬝ᵥ (factorTwoIntrinsicNineDirectCoreMatrix a b *ᵥ x) +
        2 * r * factorTwoIntrinsicNineDirectP6BorderFunctional a b x +
        factorTwoIntrinsicNineDirectP6RetainedDiagonal a b * r ^ 2 := by
  let M := factorTwoIntrinsicNineDirectP6PrefixMatrix a b
  have h := matrix_quadratic_snoc M
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian a b) x r
  rw [factorTwoIntrinsicNineDirectP6PrefixMatrix_leading] at h
  simpa only [M, factorTwoIntrinsicNineDirectP6BorderFunctional,
    factorTwoIntrinsicNineDirectP6BorderVector,
    factorTwoIntrinsicNineDirectP6RetainedDiagonal] using h

/-- The retained scalar diagonal is the honest `P6` phase diagonal minus its
exact share of the balanced low reserve. -/
theorem factorTwoIntrinsicNineDirectP6RetainedDiagonal_eq
    (a b : ℝ) :
    factorTwoIntrinsicNineDirectP6RetainedDiagonal a b =
      factorTwoP6PhaseDiagonal a -
        (3 / 320 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP6 := by
  unfold factorTwoIntrinsicNineDirectP6RetainedDiagonal
    factorTwoIntrinsicNineDirectP6PrefixMatrix
    factorTwoIntrinsicNineDirectPrefix
    factorTwoIntrinsicNineDirectLowMatrix
    factorTwoIntrinsicNineDirectCoordinateBilinear
    factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicNineP678LowReserve
    factorTwoIntrinsicNineDirectUnit
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
  simp [Pi.single_apply, factorTwoEndpointPhaseDiagonal,
    factorTwoP6PhaseDiagonal]
  ring

/-- The charged `P6` diagonal keeps a uniform positive margin on the disk. -/
theorem one_div_one_hundred_sixty_le_P6RetainedDiagonal
    (a b : ℝ) (ha : a ^ 2 ≤ 1) :
    (1 / 160 : ℝ) ≤
      factorTwoIntrinsicNineDirectP6RetainedDiagonal a b := by
  rw [factorTwoIntrinsicNineDirectP6RetainedDiagonal_eq,
    factorTwoCenteredP6_energy]
  have h := one_twentieth_energy_le_P6_phase_diagonal a ha
  rw [factorTwoCenteredP6_energy] at h
  norm_num at h ⊢
  linarith

/-- The exact strict Cauchy inequality for the `P6` row closes the first
bordered extension.  This is a quadratic completion, not a determinant
expansion. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_border_cauchy
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hborder : ∀ (x : Fin 6 → ℝ), x ≠ 0 →
      factorTwoIntrinsicNineDirectP6BorderFunctional a b x ^ 2 <
        (x ⬝ᵥ (factorTwoIntrinsicNineDirectCoreMatrix a b *ᵥ x)) *
          factorTwoIntrinsicNineDirectP6RetainedDiagonal a b) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).PosDef := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hd : 0 < factorTwoIntrinsicNineDirectP6RetainedDiagonal a b :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 160)
      (one_div_one_hundred_sixty_le_P6RetainedDiagonal a b ha)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian a b)
  intro y hy
  cases y using Fin.snocCases with
  | snoc x r =>
      simp only [star_trivial]
      rw [factorTwoIntrinsicNineDirectP6PrefixMatrix_quadratic_snoc]
      by_cases hx : x = 0
      · subst x
        have hr : r ≠ 0 := by
          intro hr
          subst r
          apply hy
          funext i
          exact Fin.lastCases
            (by rw [Fin.snoc_last]; rfl)
            (fun j ↦ by rw [Fin.snoc_castSucc]; rfl) i
        simp only [mulVec_zero, dotProduct_zero,
          factorTwoIntrinsicNineDirectP6BorderFunctional,
          zero_dotProduct, zero_add, mul_zero]
        exact mul_pos hd (sq_pos_of_ne_zero hr)
      · let Q := x ⬝ᵥ
            (factorTwoIntrinsicNineDirectCoreMatrix a b *ᵥ x)
        let L := factorTwoIntrinsicNineDirectP6BorderFunctional a b x
        let d := factorTwoIntrinsicNineDirectP6RetainedDiagonal a b
        have hgap : L ^ 2 < Q * d := by
          simpa only [Q, L, d] using hborder x hx
        have hscaled : 0 < d * (Q + 2 * r * L + d * r ^ 2) := by
          rw [show d * (Q + 2 * r * L + d * r ^ 2) =
              (d * r + L) ^ 2 + (Q * d - L ^ 2) by ring]
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hgap)
        have hd' : 0 < d := by simpa only [d] using hd
        change 0 < Q + 2 * r * L + d * r ^ 2
        nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
