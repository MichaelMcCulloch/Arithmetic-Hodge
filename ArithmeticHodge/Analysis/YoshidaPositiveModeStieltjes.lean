import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import ArithmeticHodge.Analysis.YoshidaSineSeriesTail

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaPositiveModeStieltjes

noncomputable section

open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel
open YoshidaSineSeriesTail

/-- The divided difference of one complete-Bernstein atom
`t ↦ 2 a t / (t + λ)` is a rank-one Cauchy kernel. -/
theorem stieltjesAtom_dividedDifference
    {L a lam x y : ℝ}
    (hL : L ≠ 0) (hx : x + lam ≠ 0) (hy : y + lam ≠ 0)
    (hxy : x ≠ y) :
    (2 / L) *
        ((2 * a * x / (x + lam) - 2 * a * y / (y + lam)) / (x - y)) =
      (4 * a * lam / L) / ((x + lam) * (y + lam)) := by
  field_simp [hL, hx, hy, sub_ne_zero.mpr hxy]
  ring

/-- A finite positive Stieltjes profile, written in complete-Bernstein form.
The intended Yoshida specialization has `t = κ²`. -/
def stieltjesFiniteG
    {α : Type*} (s : Finset α) (a lam : α → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ s, 2 * a k * t / (t + lam k)

/-- Every off-diagonal divided difference of a finite positive Stieltjes
profile is the corresponding weighted Cauchy Gram kernel. -/
theorem stieltjesFinite_dividedDifference
    {α : Type*} (s : Finset α) (a lam : α → ℝ)
    {L x y : ℝ} (hL : L ≠ 0) (hxy : x ≠ y)
    (hx : ∀ k ∈ s, x + lam k ≠ 0)
    (hy : ∀ k ∈ s, y + lam k ≠ 0) :
    (2 / L) *
        ((stieltjesFiniteG s a lam x - stieltjesFiniteG s a lam y) /
          (x - y)) =
      ∑ k ∈ s,
        (4 * a k * lam k / L) /
          ((x + lam k) * (y + lam k)) := by
  classical
  simp only [stieltjesFiniteG, ← Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact stieltjesAtom_dividedDifference hL (hx k hk) (hy k hk) hxy

/-- The Cauchy feature vector belonging to a Stieltjes atom. -/
def stieltjesCauchyVector
    {α ι : Type*} (lam : α → ℝ) (t : ι → ℝ) (k : α) : ι → ℝ :=
  fun i ↦ (t i + lam k)⁻¹

/-- The finite Loewner kernel as an explicit sum of weighted rank-one
Cauchy Gram matrices. -/
def stieltjesLoewnerGram
    {α ι : Type*} (s : Finset α) (L : ℝ) (a lam : α → ℝ)
    (t : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ k ∈ s, (4 * a k * lam k / L) •
    Matrix.vecMulVec (stieltjesCauchyVector lam t k)
      (star (stieltjesCauchyVector lam t k))

@[simp] theorem stieltjesLoewnerGram_apply
    {α ι : Type*} (s : Finset α) (L : ℝ) (a lam : α → ℝ)
    (t : ι → ℝ) (i j : ι) :
    stieltjesLoewnerGram s L a lam t i j =
      ∑ k ∈ s, (4 * a k * lam k / L) /
        ((t i + lam k) * (t j + lam k)) := by
  classical
  simp only [stieltjesLoewnerGram, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, star_trivial, smul_eq_mul,
    stieltjesCauchyVector]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [div_eq_mul_inv, mul_inv]

/-- Positive Stieltjes weights and poles make every finite Loewner block
positive semidefinite, independently of the number or placement of nodes. -/
theorem stieltjesLoewnerGram_posSemidef
    {α ι : Type*} [Finite ι]
    (s : Finset α) {L : ℝ} (a lam : α → ℝ) (t : ι → ℝ)
    (hL : 0 < L) (ha : ∀ k ∈ s, 0 ≤ a k)
    (hlam : ∀ k ∈ s, 0 ≤ lam k) :
    (stieltjesLoewnerGram s L a lam t).PosSemidef := by
  classical
  apply Matrix.posSemidef_sum s
  intro k hk
  apply (Matrix.posSemidef_vecMulVec_self_star
    (stieltjesCauchyVector lam t k)).smul
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (ha k hk)) (hlam k hk)) hL.le

/-- Positive atom weights in the exact Yoshida Stieltjes expansion.  `none`
is the combined polar atom and `some k` is the `k`-th dyadic Cauchy atom. -/
def yoshidaStieltjesWeight : Option ℕ → ℝ
  | none => Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2
  | some k => 1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k

/-- Squared pole locations in the Yoshida Stieltjes expansion. -/
def yoshidaStieltjesPole : Option ℕ → ℝ
  | none => (1 / 2 : ℝ) ^ 2
  | some k => oddRate k ^ 2

theorem yoshidaStieltjesWeight_pos (k : Option ℕ) :
    0 < yoshidaStieltjesWeight k := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  cases k with
  | none =>
      rw [yoshidaStieltjesWeight]
      have hsne : Real.sqrt 2 ≠ 1 := by
        intro hs
        rw [hs] at hssq
        norm_num at hssq
      rw [show Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2 =
          (Real.sqrt 2 - 1) ^ 2 / Real.sqrt 2 by
        field_simp [hspos.ne']
        ring]
      exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hsne)) hspos
  | some k =>
      rw [yoshidaStieltjesWeight]
      have hsone : 1 < Real.sqrt 2 := by nlinarith
      have hinv : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsone
      have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hdiv : (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤
          (Real.sqrt 2)⁻¹ :=
        div_le_self (inv_nonneg.mpr hspos.le) hpow
      linarith

theorem yoshidaStieltjesPole_pos (k : Option ℕ) :
    0 < yoshidaStieltjesPole k := by
  cases k with
  | none => norm_num [yoshidaStieltjesPole]
  | some k =>
      exact sq_pos_of_pos (oddRate_pos k)

/-- Every finite truncation of the exact Yoshida Stieltjes atom family gives
a positive-semidefinite Loewner kernel on an arbitrary finite node family. -/
theorem yoshidaFiniteStieltjesLoewnerGram_posSemidef
    {ι : Type*} [Finite ι] (s : Finset (Option ℕ)) (t : ι → ℝ) :
    (stieltjesLoewnerGram s yoshidaLength yoshidaStieltjesWeight
      yoshidaStieltjesPole t).PosSemidef := by
  apply stieltjesLoewnerGram_posSemidef s
  · exact yoshidaLength_pos
  · intro k _
    exact (yoshidaStieltjesWeight_pos k).le
  · intro k _
    exact (yoshidaStieltjesPole_pos k).le

/-- The positive Stieltjes profile behind Yoshida's sine moments.  The first
term collects the two polar exponentials; the series is the already-proved
dyadic Cauchy expansion. -/
def yoshidaStieltjesProfile (t : ℝ) : ℝ :=
  2 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2) /
      ((1 / 2 : ℝ) ^ 2 + t) +
    ∑' k : ℕ,
      2 * (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
        (oddRate k ^ 2 + t)

/-- Exact source-level identification of the Yoshida sine moment with a
positive Stieltjes profile evaluated at `κₙ²`.  No moment enclosure or
finite-dimensional certificate enters this identity. -/
theorem yoshidaSineMoment_eq_neg_kappa_mul_stieltjesProfile
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n =
      -yoshidaKappa n *
        yoshidaStieltjesProfile (yoshidaKappa n ^ 2) := by
  rw [yoshidaSineMoment_eq_explicitCauchySeries hn]
  have hpolar : sinePolarValue n =
      -yoshidaKappa n *
        (2 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2) /
          ((1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2)) := by
    rw [sinePolarValue]
    ring
  have hterm (k : ℕ) : sineCauchyTerm n k =
      yoshidaKappa n *
        (2 * (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
          (oddRate k ^ 2 + yoshidaKappa n ^ 2)) := by
    rw [sineCauchyTerm]
    ring
  rw [hpolar]
  simp_rw [hterm]
  rw [tsum_mul_left]
  unfold yoshidaStieltjesProfile
  ring

/-- Complete-Bernstein normalization of the Yoshida Stieltjes profile. -/
def yoshidaStieltjesG (t : ℝ) : ℝ :=
  t * yoshidaStieltjesProfile t

theorem yoshidaKappa_mul_sineMoment_eq_neg_stieltjesG
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaKappa n * yoshidaSineMoment n =
      -yoshidaStieltjesG (yoshidaKappa n ^ 2) := by
  rw [yoshidaSineMoment_eq_neg_kappa_mul_stieltjesProfile hn,
    yoshidaStieltjesG]
  ring

/-- The exact numerator occurring in every positive-mode off-diagonal entry
of `evenMomentGram` is a divided difference of `yoshidaStieltjesG`. -/
theorem yoshidaSine_dividedDifference_eq_stieltjes
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (2 / yoshidaLength) *
        (yoshidaKappa m * yoshidaSineMoment m -
          yoshidaKappa n * yoshidaSineMoment n) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) =
      (2 / yoshidaLength) *
        (yoshidaStieltjesG (yoshidaKappa n ^ 2) -
          yoshidaStieltjesG (yoshidaKappa m ^ 2)) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  rw [yoshidaKappa_mul_sineMoment_eq_neg_stieltjesG hn,
    yoshidaKappa_mul_sineMoment_eq_neg_stieltjesG hm]
  ring

end

end ArithmeticHodge.Analysis.YoshidaPositiveModeStieltjes
