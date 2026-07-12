import ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaDiagonalUniformQBounds

open ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity
open ArithmeticHodge.Analysis.YoshidaOddGramPrefix

private def diagonalQWeight (j : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ * (1 / 4 : ℝ) ^ (j + 1)

private def diagonalQAbscissa (j : ℕ) : ℝ :=
  2 * (j + 1 : ℕ) + 1 / 2

def diagonalQMain (n : ℕ) : ℝ :=
  -2 / (3 * Real.sqrt 2 * yoshidaLength * yoshidaKappa n ^ 2)

private def diagonalQLowerTerm (n j : ℕ) : ℝ :=
  -2 * diagonalQWeight j / (yoshidaLength * yoshidaKappa n ^ 2)

private def diagonalQUpperTerm (n j : ℕ) : ℝ :=
  diagonalQLowerTerm n j +
    6 * diagonalQWeight j * diagonalQAbscissa j ^ 2 /
      (yoshidaLength * (yoshidaKappa n ^ 2) ^ 2)

private theorem yoshidaKappa_pos_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    0 < yoshidaKappa n := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold yoshidaKappa
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnR)
    yoshidaLength_pos

private theorem hasSum_quarter_pow :
    HasSum (fun j : ℕ ↦ (1 / 4 : ℝ) ^ j) (4 / 3) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one
    (k := 0) (r := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h ⊢
  simpa using h

private theorem hasSum_succ_mul_quarter_pow :
    HasSum (fun j : ℕ ↦
      ((j + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ j) (16 / 9) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one
    (k := 1) (r := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h ⊢
  simpa using h

private theorem hasSum_choose_two_mul_quarter_pow :
    HasSum (fun j : ℕ ↦
      (((j + 2).choose 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ j)
      (64 / 27) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one
    (k := 2) (r := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h ⊢
  simpa using h

private theorem hasSum_succ_sq_mul_quarter_pow :
    HasSum (fun j : ℕ ↦
      (((j + 1 : ℕ) : ℝ) ^ 2) * (1 / 4 : ℝ) ^ j)
      (80 / 27) := by
  have h :=
    (hasSum_choose_two_mul_quarter_pow.mul_left (2 : ℝ)).sub
      hasSum_succ_mul_quarter_pow
  convert h using 1
  · funext j
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · norm_num

private theorem hasSum_diagonalQWeight :
    HasSum diagonalQWeight (1 / (3 * Real.sqrt 2)) := by
  have h := hasSum_quarter_pow.mul_left
    ((Real.sqrt 2)⁻¹ * (1 / 4 : ℝ))
  convert h using 1
  · funext j
    unfold diagonalQWeight
    rw [pow_succ]
    ring
  · ring

private theorem hasSum_diagonalQWeight_mul_abscissa_sq :
    HasSum (fun j : ℕ ↦
      diagonalQWeight j * diagonalQAbscissa j ^ 2)
      (425 / (108 * Real.sqrt 2)) := by
  have hpoly := (((hasSum_succ_sq_mul_quarter_pow.mul_left (4 : ℝ)).add
    (hasSum_succ_mul_quarter_pow.mul_left (2 : ℝ))).add
      (hasSum_quarter_pow.mul_left (1 / 4 : ℝ)))
  have h := hpoly.mul_left ((Real.sqrt 2)⁻¹ * (1 / 4 : ℝ))
  convert h using 1
  · funext j
    unfold diagonalQWeight diagonalQAbscissa
    push_cast
    rw [pow_succ]
    ring
  · ring

private theorem diagonalQWeight_eq (j : ℕ) :
    diagonalQWeight j =
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ (j + 1) := by
  unfold diagonalQWeight
  rw [one_div_pow]
  ring

private theorem diagonal_q_ratio_lower
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    -1 / p ≤ (x - p) / (x + p) ^ 2 := by
  have hxp : 0 < x + p := by linarith
  have hid :
      (x - p) / (x + p) ^ 2 - (-1 / p) =
        x * (3 * p + x) / (p * (p + x) ^ 2) := by
    field_simp [hp.ne', hxp.ne']
    ring
  have hnonneg :
      0 ≤ (x - p) / (x + p) ^ 2 - (-1 / p) := by
    rw [hid]
    positivity
  linarith

private theorem diagonal_q_ratio_upper
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (x - p) / (x + p) ^ 2 ≤ -1 / p + 3 * x / p ^ 2 := by
  have hxp : 0 < x + p := by linarith
  have hid :
      (-1 / p + 3 * x / p ^ 2) - (x - p) / (x + p) ^ 2 =
        x ^ 2 * (5 * p + 3 * x) / (p ^ 2 * (p + x) ^ 2) := by
    field_simp [hp.ne', hxp.ne']
    ring
  have hnonneg :
      0 ≤ (-1 / p + 3 * x / p ^ 2) -
        (x - p) / (x + p) ^ 2 := by
    rw [hid]
    positivity
  linarith

private theorem diagonal_q_ratio_abs_le
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    |(x - p) / (x + p) ^ 2| ≤ 1 / p := by
  have hxp : 0 < x + p := by linarith
  have hnum : |x - p| ≤ x + p := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_div, abs_pow, abs_of_pos hxp]
  calc
    |x - p| / (x + p) ^ 2 ≤
        (x + p) / (x + p) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 1 / (x + p) := by
      field_simp [hxp.ne']
    _ ≤ 1 / p := by
      exact one_div_le_one_div_of_le hp (by linarith)

private theorem diagonalHighQTerm_eq_ratio
    (n j : ℕ) :
    diagonalHighQTerm n j =
      (2 * diagonalQWeight j / yoshidaLength) *
        ((diagonalQAbscissa j ^ 2 - yoshidaKappa n ^ 2) /
          (diagonalQAbscissa j ^ 2 + yoshidaKappa n ^ 2) ^ 2) := by
  have hden :
      (2 * (((j + 1 : ℕ) : ℝ)) + 1 / 2) ^ 2 +
          yoshidaKappa n ^ 2 ≠ 0 := by
    positivity
  unfold diagonalHighQTerm diagonalQAbscissa
  dsimp only
  rw [← diagonalQWeight_eq]
  push_cast at hden ⊢
  field_simp [yoshidaLength_pos.ne', hden]

private theorem diagonalHighQTerm_bounds
    {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    diagonalQLowerTerm n j ≤ diagonalHighQTerm n j ∧
      diagonalHighQTerm n j ≤ diagonalQUpperTerm n j := by
  let p : ℝ := yoshidaKappa n ^ 2
  let x : ℝ := diagonalQAbscissa j ^ 2
  have hkappa := yoshidaKappa_pos_of_one_le hn
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hw : 0 ≤ diagonalQWeight j := by
    unfold diagonalQWeight
    positivity
  have hfactor : 0 ≤ 2 * diagonalQWeight j / yoshidaLength := by
    exact div_nonneg (mul_nonneg (by norm_num) hw) yoshidaLength_pos.le
  rw [diagonalHighQTerm_eq_ratio]
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (diagonal_q_ratio_lower hp hx) hfactor
    dsimp only [diagonalQLowerTerm, p, x] at h ⊢
    convert h using 1
    all_goals ring
  · have h := mul_le_mul_of_nonneg_left
      (diagonal_q_ratio_upper hp hx) hfactor
    dsimp only [diagonalQUpperTerm, diagonalQLowerTerm, p, x] at h ⊢
    convert h using 1
    all_goals ring

private theorem diagonalHighQTerm_abs_le
    {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    |diagonalHighQTerm n j| ≤
      2 * diagonalQWeight j /
        (yoshidaLength * yoshidaKappa n ^ 2) := by
  let p : ℝ := yoshidaKappa n ^ 2
  let x : ℝ := diagonalQAbscissa j ^ 2
  have hkappa := yoshidaKappa_pos_of_one_le hn
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hw : 0 ≤ diagonalQWeight j := by
    unfold diagonalQWeight
    positivity
  have hfactor : 0 ≤ 2 * diagonalQWeight j / yoshidaLength := by
    exact div_nonneg (mul_nonneg (by norm_num) hw) yoshidaLength_pos.le
  rw [diagonalHighQTerm_eq_ratio, abs_mul,
    abs_of_nonneg hfactor]
  calc
    (2 * diagonalQWeight j / yoshidaLength) *
        |(x - p) / (x + p) ^ 2| ≤
      (2 * diagonalQWeight j / yoshidaLength) * (1 / p) :=
        mul_le_mul_of_nonneg_left (diagonal_q_ratio_abs_le hp hx) hfactor
    _ = 2 * diagonalQWeight j /
        (yoshidaLength * yoshidaKappa n ^ 2) := by
      dsimp only [p]
      ring

private theorem summable_diagonalHighQTerm
    {n : ℕ} (hn : 1 ≤ n) :
    Summable (diagonalHighQTerm n) := by
  have hmajor := hasSum_diagonalQWeight.mul_left
    (2 / (yoshidaLength * yoshidaKappa n ^ 2))
  apply hmajor.summable.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  have h := diagonalHighQTerm_abs_le hn j
  convert h using 1
  all_goals ring

private theorem hasSum_diagonalQLowerTerm
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (diagonalQLowerTerm n) (diagonalQMain n) := by
  have _hkappa := yoshidaKappa_pos_of_one_le hn
  have h := hasSum_diagonalQWeight.mul_left
    (-2 / (yoshidaLength * yoshidaKappa n ^ 2))
  convert h using 1
  · funext j
    unfold diagonalQLowerTerm
    ring
  · unfold diagonalQMain
    ring

private theorem hasSum_diagonalQUpperTerm
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (diagonalQUpperTerm n)
      (diagonalQMain n +
        425 / (18 * Real.sqrt 2 * yoshidaLength *
          (yoshidaKappa n ^ 2) ^ 2)) := by
  have hlower := hasSum_diagonalQLowerTerm hn
  have hcorrection :=
    hasSum_diagonalQWeight_mul_abscissa_sq.mul_left
      (6 / (yoshidaLength * (yoshidaKappa n ^ 2) ^ 2))
  convert hlower.add hcorrection using 1
  · funext j
    unfold diagonalQUpperTerm
    ring
  · ring

/--
The dyadic Q-series lies above its leading negative geometric term, and its
positive displacement is bounded by the exact weighted geometric second
moment.  The estimate is valid for every positive Yoshida mode.
-/
theorem diagonalHighQ_bounds
    {n : ℕ} (hn : 1 ≤ n) :
    diagonalQMain n ≤ diagonalHighQ n ∧
      diagonalHighQ n ≤ diagonalQMain n +
        425 / (18 * Real.sqrt 2 * yoshidaLength *
          (yoshidaKappa n ^ 2) ^ 2) := by
  have hq := summable_diagonalHighQTerm hn
  have hlower := hasSum_diagonalQLowerTerm hn
  have hupper := hasSum_diagonalQUpperTerm hn
  constructor
  · calc
      diagonalQMain n = ∑' j : ℕ, diagonalQLowerTerm n j :=
        hlower.tsum_eq.symm
      _ ≤ ∑' j : ℕ, diagonalHighQTerm n j :=
        hlower.summable.tsum_le_tsum
          (fun j ↦ (diagonalHighQTerm_bounds hn j).1) hq
      _ = diagonalHighQ n := by rfl
  · calc
      diagonalHighQ n = ∑' j : ℕ, diagonalHighQTerm n j := by rfl
      _ ≤ ∑' j : ℕ, diagonalQUpperTerm n j :=
        hq.tsum_le_tsum
          (fun j ↦ (diagonalHighQTerm_bounds hn j).2) hupper.summable
      _ = diagonalQMain n +
          425 / (18 * Real.sqrt 2 * yoshidaLength *
            (yoshidaKappa n ^ 2) ^ 2) := hupper.tsum_eq

/-- The same enclosure with the sign used by the uniform moment identity. -/
theorem neg_diagonalHighQ_sub_neg_main_bounds
    {n : ℕ} (hn : 1 ≤ n) :
    -(425 / (18 * Real.sqrt 2 * yoshidaLength *
        (yoshidaKappa n ^ 2) ^ 2)) ≤
        (-diagonalHighQ n) - (-diagonalQMain n) ∧
      (-diagonalHighQ n) - (-diagonalQMain n) ≤ 0 := by
  rcases diagonalHighQ_bounds hn with ⟨hlower, hupper⟩
  constructor <;> linarith

end ArithmeticHodge.Analysis.YoshidaDiagonalUniformQBounds
