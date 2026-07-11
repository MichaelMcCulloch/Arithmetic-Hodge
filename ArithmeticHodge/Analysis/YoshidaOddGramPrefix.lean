import ArithmeticHodge.Analysis.MatrixAbsEntryComparison
import ArithmeticHodge.Analysis.TrapezoidalErrorBounds
import ArithmeticHodge.Analysis.YoshidaClippedLowModes
import ArithmeticHodge.Analysis.YoshidaOddComparisonCertificate
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

open Matrix Set MeasureTheory intervalIntegral Interval
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaOddGramPrefix

noncomputable section

/-!
# Yoshida's leading odd Gram prefix

This module fixes the desingularized sine and diagonal moments used in the
real-space calculation of Yoshida's odd Gram matrix.  It proves the exact
algebraic reduction of the leading `3 × 3` block and shows that deliberately
coarse rational moment boxes suffice for the corresponding entries of the
production odd comparison certificate.

The proposition `ClippedOddMomentBridge` records, but does not assume or prove,
the remaining analytic identity between the production clipped critical form
and this real moment model.  In particular, this module does not prove the
moment enclosures, positivity of the clipped Gram, Yoshida positivity, or RH.
-/

/-- Yoshida's full clipped interval length `L = log 2`. -/
def yoshidaLength : ℝ := Real.log 2

/-- The angular frequency `2πn/L`. -/
def yoshidaKappa (n : ℕ) : ℝ :=
  2 * Real.pi * n / yoshidaLength

/-- The singular real-space weight before adding its principal-part
counterterm. -/
def yoshidaWeight (u : ℝ) : ℝ :=
  2 * (Real.exp (u / 2) + Real.exp (-u / 2) -
    Real.exp (u / 2) / (Real.exp u - Real.exp (-u)))

/-- The intended removable extension of `yoshidaWeight u + 1/u` at zero.
Continuity and differentiability of this extension remain analytic
obligations for the numerical enclosure layer. -/
def yoshidaWeightPlus (u : ℝ) : ℝ :=
  if u = 0 then 7 / 2 else yoshidaWeight u + 1 / u

/-- The stable integrand defining the sine moment `S_n`. -/
def yoshidaSineMomentIntegrand (n : ℕ) (u : ℝ) : ℝ :=
  yoshidaWeightPlus u * Real.sin (yoshidaKappa n * u) -
    yoshidaKappa n * Real.sinc (yoshidaKappa n * u)

/-- Yoshida's desingularized sine moment `S_n`. -/
def yoshidaSineMoment (n : ℕ) : ℝ :=
  ∫ u in 0..yoshidaLength, yoshidaSineMomentIntegrand n u

/-- The stable integrand in the diagonal moment `D_n`. -/
def yoshidaDiagonalMomentIntegrand (n : ℕ) (u : ℝ) : ℝ :=
  yoshidaWeightPlus u *
      ((yoshidaLength - u) / yoshidaLength) *
      Real.cos (yoshidaKappa n * u) +
    2 * Real.sin (yoshidaKappa n * u / 2) ^ 2 / u +
    Real.cos (yoshidaKappa n * u) / yoshidaLength

/-- Yoshida's desingularized diagonal moment `D_n`. -/
def yoshidaDiagonalMoment (n : ℕ) : ℝ :=
  (∫ u in 0..yoshidaLength, yoshidaDiagonalMomentIntegrand n u) -
    (Real.log yoshidaLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi)

/-- The real odd Gram model expressed through arbitrary sine and diagonal
moment families.  Later analytic work must instantiate these with
`yoshidaSineMoment` and `yoshidaDiagonalMoment`. -/
def oddMomentGram (S D : ℕ → ℝ) (n m : ℕ) : ℝ :=
  if n = m then
    D n + S n / (yoshidaLength * yoshidaKappa n)
  else
    (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
      (yoshidaKappa n * S m - yoshidaKappa m * S n) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)

theorem oddMomentGram_comm (S D : ℕ → ℝ) (n m : ℕ) :
    oddMomentGram S D n m = oddMomentGram S D m n := by
  by_cases hnm : n = m
  · subst m
    rfl
  rw [oddMomentGram, if_neg hnm, oddMomentGram, if_neg (Ne.symm hnm)]
  rw [add_comm n m]
  have hnum : yoshidaKappa m * S n - yoshidaKappa n * S m =
      -(yoshidaKappa n * S m - yoshidaKappa m * S n) := by ring
  have hden : yoshidaKappa m ^ 2 - yoshidaKappa n ^ 2 =
      -(yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by ring
  rw [hnum, hden]
  rw [show 2 * (-1 : ℝ) ^ (m + n) / yoshidaLength *
      -(yoshidaKappa n * S m - yoshidaKappa m * S n) =
      -(2 * (-1 : ℝ) ^ (m + n) / yoshidaLength *
        (yoshidaKappa n * S m - yoshidaKappa m * S n)) by ring]
  rw [neg_div_neg_eq]

theorem yoshidaLength_pos : 0 < yoshidaLength := by
  exact Real.log_pos (by norm_num)

theorem oddMomentGram_one_one (S D : ℕ → ℝ) :
    oddMomentGram S D 1 1 = D 1 + S 1 / (2 * Real.pi) := by
  rw [oddMomentGram, if_pos rfl]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

theorem oddMomentGram_two_two (S D : ℕ → ℝ) :
    oddMomentGram S D 2 2 = D 2 + S 2 / (4 * Real.pi) := by
  rw [oddMomentGram, if_pos rfl]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

theorem oddMomentGram_three_three (S D : ℕ → ℝ) :
    oddMomentGram S D 3 3 = D 3 + S 3 / (6 * Real.pi) := by
  rw [oddMomentGram, if_pos rfl]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

theorem oddMomentGram_one_two (S D : ℕ → ℝ) :
    oddMomentGram S D 1 2 = (S 2 - 2 * S 1) / (3 * Real.pi) := by
  rw [oddMomentGram, if_neg (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

theorem oddMomentGram_one_three (S D : ℕ → ℝ) :
    oddMomentGram S D 1 3 = (3 * S 1 - S 3) / (8 * Real.pi) := by
  rw [oddMomentGram, if_neg (by norm_num : (1 : ℕ) ≠ 3)]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

theorem oddMomentGram_two_three (S D : ℕ → ℝ) :
    oddMomentGram S D 2 3 = (2 * S 3 - 3 * S 2) / (5 * Real.pi) := by
  rw [oddMomentGram, if_neg (by norm_num : (2 : ℕ) ≠ 3)]
  simp only [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]
  ring

set_option maxHeartbeats 800000 in
/-- Certified quadrature through a smooth surrogate.  The target integrand
need only be integrable and uniformly close to a `C²` surrogate.  The total
radius is the uniform approximation budget plus the composite-trapezoid
remainder.  This form avoids assuming that a piecewise removable definition
such as `yoshidaWeightPlus` is already globally `C²`. -/
theorem intervalIntegral_mem_surrogateTrapezoidalInterval
    {f q : ℝ → ℝ} {a b ζ δ : ℝ} {N : ℕ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable q volume a b)
    (happrox : ∀ x ∈ Icc a b, |f x - q x| ≤ δ)
    (hqC2 : ContDiffOn ℝ 2 q [[a, b]])
    (hsecond : ∀ x,
      |iteratedDerivWithin 2 q [[a, b]] x| ≤ ζ)
    (hN : 0 < N) :
    let radius :=
      δ * (b - a) + |b - a| ^ 3 * ζ / (12 * N ^ 2)
    trapezoidal_integral q N a b - radius ≤
        ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤
        trapezoidal_integral q N a b + radius := by
  dsimp only
  have hdiff : |(∫ x in a..b, f x) - ∫ x in a..b, q x| ≤
      δ * (b - a) := by
    rw [← intervalIntegral.integral_sub hf hq, ← Real.norm_eq_abs]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := δ) (f := fun x ↦ f x - q x)
      (fun x hx ↦ by
        rw [Real.norm_eq_abs]
        apply happrox x
        rw [uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩)
    simpa [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using hnorm
  have hquad := trapezoidal_error_le_of_c2 hqC2 hsecond hN
  rw [trapezoidal_error, abs_le] at hquad
  rw [abs_le] at hdiff
  constructor <;> linarith [hdiff.1, hdiff.2, hquad.1, hquad.2]

private theorem pi_lower : (31415 / 10000 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  norm_num at h ⊢
  linarith

/-- Coarse, millesimal moment boxes already imply all six independent
comparison inequalities for the leading odd block.  The constants are the
leading entries of `yoshidaOddComparison10`, with correction radius `1/40`.
No floating-point value occurs in this proof. -/
theorem oddMomentGram_prefix_comparison_of_coarse_enclosures
    (S D : ℕ → ℝ)
    (hS1l : (-1452 / 1000 : ℝ) ≤ S 1)
    (hS1u : S 1 ≤ (-1450 / 1000 : ℝ))
    (hS2l : (-1510 / 1000 : ℝ) ≤ S 2)
    (hS2u : S 2 ≤ (-1507 / 1000 : ℝ))
    (hS3l : (-1531 / 1000 : ℝ) ≤ S 3)
    (hS3u : S 3 ≤ (-1528 / 1000 : ℝ))
    (hD1l : (382 / 1000 : ℝ) ≤ D 1)
    (hD2l : (1063 / 1000 : ℝ) ≤ D 2)
    (hD3l : (1466 / 1000 : ℝ) ≤ D 3) :
    (63 / 512 : ℝ) ≤ oddMomentGram S D 1 1 - 1 / 40 ∧
    (117 / 128 : ℝ) ≤ oddMomentGram S D 2 2 - 1 / 40 ∧
    (347 / 256 : ℝ) ≤ oddMomentGram S D 3 3 - 1 / 40 ∧
    |oddMomentGram S D 1 2| + 1 / 40 ≤ (91 / 512 : ℝ) ∧
    |oddMomentGram S D 1 3| + 1 / 40 ≤ (73 / 512 : ℝ) ∧
    |oddMomentGram S D 2 3| + 1 / 40 ≤ (63 / 512 : ℝ) := by
  rw [oddMomentGram_one_one, oddMomentGram_two_two,
    oddMomentGram_three_three, oddMomentGram_one_two,
    oddMomentGram_one_three, oddMomentGram_two_three]
  have hp : (31415 / 10000 : ℝ) < Real.pi := pi_lower
  have hp0 : 0 < Real.pi := Real.pi_pos
  constructor
  · have hden : 0 < 2 * Real.pi := by positivity
    have hdiv : (63 / 512 : ℝ) + 1 / 40 - D 1 ≤
        S 1 / (2 * Real.pi) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  constructor
  · have hden : 0 < 4 * Real.pi := by positivity
    have hdiv : (117 / 128 : ℝ) + 1 / 40 - D 2 ≤
        S 2 / (4 * Real.pi) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  constructor
  · have hden : 0 < 6 * Real.pi := by positivity
    have hdiv : (347 / 256 : ℝ) + 1 / 40 - D 3 ≤
        S 3 / (6 * Real.pi) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  constructor
  · have hnum0 : 0 ≤ S 2 - 2 * S 1 := by nlinarith
    rw [abs_of_nonneg (div_nonneg hnum0 (by positivity))]
    have hden : 0 < 3 * Real.pi := by positivity
    have hfrac : (S 2 - 2 * S 1) / (3 * Real.pi) ≤
        (91 / 512 : ℝ) - 1 / 40 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  constructor
  · have hnum : 3 * S 1 - S 3 ≤ 0 := by nlinarith
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum (by positivity))]
    have hrewrite : -((3 * S 1 - S 3) / (8 * Real.pi)) =
        (S 3 - 3 * S 1) / (8 * Real.pi) := by ring
    rw [hrewrite]
    have hden : 0 < 8 * Real.pi := by positivity
    have hfrac : (S 3 - 3 * S 1) / (8 * Real.pi) ≤
        (73 / 512 : ℝ) - 1 / 40 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  · have hnum0 : 0 ≤ 2 * S 3 - 3 * S 2 := by nlinarith
    rw [abs_of_nonneg (div_nonneg hnum0 (by positivity))]
    have hden : 0 < 5 * Real.pi := by positivity
    have hfrac : (2 * S 3 - 3 * S 2) / (5 * Real.pi) ≤
        (63 / 512 : ℝ) - 1 / 40 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith

/-- Exact worst-case margins supplied by the coarse rational boxes, in the
same order as the six comparison inequalities above. -/
theorem oddPrefix_coarse_corner_margin_identities :
    (382 / 1000 : ℚ) + (-1452 / 1000 : ℚ) /
        (2 * (31415 / 10000 : ℚ)) - ((63 / 512 : ℚ) + 1 / 40) =
      1147359 / 402112000 ∧
    (1063 / 1000 : ℚ) + (-1510 / 1000 : ℚ) /
        (4 * (31415 / 10000 : ℚ)) - ((117 / 128 : ℚ) + 1 / 40) =
      379189 / 100528000 ∧
    (1466 / 1000 : ℚ) + (-1531 / 1000 : ℚ) /
        (6 * (31415 / 10000 : ℚ)) - ((347 / 256 : ℚ) + 1 / 40) =
      2597713 / 603168000 ∧
    ((91 / 512 : ℚ) - 1 / 40) -
        ((-1507 / 1000 : ℚ) - 2 * (-1452 / 1000 : ℚ)) /
          (3 * (31415 / 10000 : ℚ)) =
      217319 / 48253440 ∧
    ((73 / 512 : ℚ) - 1 / 40) -
        ((-1528 / 1000 : ℚ) - 3 * (-1452 / 1000 : ℚ)) /
          (8 * (31415 / 10000 : ℚ)) =
      81263 / 16084480 ∧
    ((63 / 512 : ℚ) - 1 / 40) -
        (2 * (-1528 / 1000 : ℚ) - 3 * (-1510 / 1000 : ℚ)) /
          (5 * (31415 / 10000 : ℚ)) =
      67657 / 16084480 := by
  norm_num

/-- Embed the leading three frequencies into the production odd `Fin 10`
index. -/
def oddPrefixIndex (i : Fin 3) : YoshidaOddIndex :=
  ⟨i.1, by omega⟩

/-- The leading principal `3 × 3` submatrix of the production real odd
comparison certificate. -/
def yoshidaOddComparisonPrefix : Matrix (Fin 3) (Fin 3) ℝ :=
  (((Rat.castHom ℝ).mapMatrix yoshidaOddComparison10).submatrix
    oddPrefixIndex oddPrefixIndex)

theorem yoshidaOddComparisonPrefix_eq :
    yoshidaOddComparisonPrefix =
      !![(63 : ℝ) / 512, -91 / 512, -73 / 512;
         -91 / 512, 117 / 128, -63 / 512;
         -73 / 512, -63 / 512, 347 / 256] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [yoshidaOddComparisonPrefix, oddPrefixIndex,
      yoshidaOddComparison10]

private theorem posDef_submatrix_of_injective
    {m n R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (M : Matrix n n R) (hM : M.PosDef) (e : m → n)
    (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  refine ⟨hM.1.submatrix _, fun x hx ↦ ?_⟩
  have hxmap : x.mapDomain e ≠ 0 := by
    intro hzero
    apply hx
    apply Finsupp.mapDomain_injective he
    simpa using hzero
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 hxmap

theorem yoshidaOddComparisonPrefix_posDef :
    yoshidaOddComparisonPrefix.PosDef := by
  apply posDef_submatrix_of_injective
    ((Rat.castHom ℝ).mapMatrix yoshidaOddComparison10)
    yoshidaOddComparison10_posDef_real oddPrefixIndex
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : YoshidaOddIndex ↦ x.1) hij

/-- The leading real moment-model matrix, with indices `0,1,2` representing
frequencies `1,2,3`. -/
def oddMomentPrefixGram (S D : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ oddMomentGram S D (i.1 + 1) (j.1 + 1)

/-- Matrix-shaped form of the coarse comparison theorem.  This is the direct
interface needed by absolute-entry positive-definiteness arguments. -/
theorem oddMomentPrefixGram_comparison_of_coarse_enclosures
    (S D : ℕ → ℝ)
    (hS1l : (-1452 / 1000 : ℝ) ≤ S 1)
    (hS1u : S 1 ≤ (-1450 / 1000 : ℝ))
    (hS2l : (-1510 / 1000 : ℝ) ≤ S 2)
    (hS2u : S 2 ≤ (-1507 / 1000 : ℝ))
    (hS3l : (-1531 / 1000 : ℝ) ≤ S 3)
    (hS3u : S 3 ≤ (-1528 / 1000 : ℝ))
    (hD1l : (382 / 1000 : ℝ) ≤ D 1)
    (hD2l : (1063 / 1000 : ℝ) ≤ D 2)
    (hD3l : (1466 / 1000 : ℝ) ≤ D 3) :
    (∀ i, yoshidaOddComparisonPrefix i i ≤
      oddMomentPrefixGram S D i i - 1 / 40) ∧
    ∀ i j, i ≠ j →
      |oddMomentPrefixGram S D i j| + 1 / 40 ≤
        -yoshidaOddComparisonPrefix i j := by
  have hcomp := oddMomentGram_prefix_comparison_of_coarse_enclosures S D
    hS1l hS1u hS2l hS2u hS3l hS3u hD1l hD2l hD3l
  rcases hcomp with ⟨h00, h11, h22, h01, h02, h12⟩
  have h10 : |oddMomentGram S D 2 1| + 1 / 40 ≤ (91 / 512 : ℝ) := by
    rw [oddMomentGram_comm]
    exact h01
  have h20 : |oddMomentGram S D 3 1| + 1 / 40 ≤ (73 / 512 : ℝ) := by
    rw [oddMomentGram_comm]
    exact h02
  have h21 : |oddMomentGram S D 3 2| + 1 / 40 ≤ (63 / 512 : ℝ) := by
    rw [oddMomentGram_comm]
    exact h12
  rw [yoshidaOddComparisonPrefix_eq]
  constructor
  · intro i
    fin_cases i
    · simpa [oddMomentPrefixGram] using h00
    · simpa [oddMomentPrefixGram] using h11
    · simpa [oddMomentPrefixGram] using h22
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · convert h01 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · convert h02 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · convert h10 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · exact (hij rfl).elim
    · convert h12 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · convert h20 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · convert h21 using 1
      all_goals norm_num [oddMomentPrefixGram]
    · exact (hij rfl).elim

/-- Yoshida's half interval length `a = log(2)/2`. -/
def yoshidaHalfLength : ℝ := yoshidaLength / 2

theorem yoshidaHalfLength_pos : 0 < yoshidaHalfLength := by
  exact div_pos yoshidaLength_pos (by norm_num)

/-- The production clipped odd Gram restricted to frequencies `1,2,3`. -/
def clippedOddPrefixGram : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ yoshidaClippedOddGram
    yoshidaHalfLength yoshidaHalfLength_pos (oddPrefixIndex i) (oddPrefixIndex j)

/-- The exact remaining analytic boundary: the production clipped critical
Gram equals the real `S_n,D_n` moment model.  This is a proposition to be
proved downstream, not an axiom or theorem of this module. -/
def ClippedOddMomentBridge : Prop :=
  ∀ i j : Fin 3,
    clippedOddPrefixGram i j =
      (oddMomentPrefixGram yoshidaSineMoment yoshidaDiagonalMoment i j : ℂ)

/-- Once the analytic bridge and the coarse moment boxes are proved, all six
independent leading-prefix comparisons hold for the actual clipped Gram. -/
theorem clippedOddPrefix_comparison_of_bridge_and_coarse_enclosures
    (hbridge : ClippedOddMomentBridge)
    (hS1l : (-1452 / 1000 : ℝ) ≤ yoshidaSineMoment 1)
    (hS1u : yoshidaSineMoment 1 ≤ (-1450 / 1000 : ℝ))
    (hS2l : (-1510 / 1000 : ℝ) ≤ yoshidaSineMoment 2)
    (hS2u : yoshidaSineMoment 2 ≤ (-1507 / 1000 : ℝ))
    (hS3l : (-1531 / 1000 : ℝ) ≤ yoshidaSineMoment 3)
    (hS3u : yoshidaSineMoment 3 ≤ (-1528 / 1000 : ℝ))
    (hD1l : (382 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 1)
    (hD2l : (1063 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 2)
    (hD3l : (1466 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 3) :
    (63 / 512 : ℝ) ≤ (clippedOddPrefixGram 0 0).re - 1 / 40 ∧
    (117 / 128 : ℝ) ≤ (clippedOddPrefixGram 1 1).re - 1 / 40 ∧
    (347 / 256 : ℝ) ≤ (clippedOddPrefixGram 2 2).re - 1 / 40 ∧
    ‖clippedOddPrefixGram 0 1‖ + 1 / 40 ≤ (91 / 512 : ℝ) ∧
    ‖clippedOddPrefixGram 0 2‖ + 1 / 40 ≤ (73 / 512 : ℝ) ∧
    ‖clippedOddPrefixGram 1 2‖ + 1 / 40 ≤ (63 / 512 : ℝ) := by
  have hmodel := oddMomentGram_prefix_comparison_of_coarse_enclosures
    yoshidaSineMoment yoshidaDiagonalMoment
    hS1l hS1u hS2l hS2u hS3l hS3u hD1l hD2l hD3l
  have h00 := hbridge 0 0
  have h11 := hbridge 1 1
  have h22 := hbridge 2 2
  have h01 := hbridge 0 1
  have h02 := hbridge 0 2
  have h12 := hbridge 1 2
  norm_num [oddMomentPrefixGram] at h00 h11 h22 h01 h02 h12
  rw [h00, h11, h22, h01, h02, h12]
  simpa only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs] using hmodel

/-- The analytic moment bridge makes the actual leading clipped Gram
Hermitian. -/
theorem clippedOddPrefixGram_isHermitian_of_bridge
    (hbridge : ClippedOddMomentBridge) :
    clippedOddPrefixGram.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [hbridge j i, hbridge i j]
  rw [Complex.star_def, Complex.conj_ofReal]
  norm_cast
  unfold oddMomentPrefixGram
  exact oddMomentGram_comm _ _ _ _

/-- Matrix-shaped comparison between the actual clipped Gram and the exact
leading rational certificate. -/
theorem clippedOddPrefixGram_matrix_comparison_of_bridge_and_coarse_enclosures
    (hbridge : ClippedOddMomentBridge)
    (hS1l : (-1452 / 1000 : ℝ) ≤ yoshidaSineMoment 1)
    (hS1u : yoshidaSineMoment 1 ≤ (-1450 / 1000 : ℝ))
    (hS2l : (-1510 / 1000 : ℝ) ≤ yoshidaSineMoment 2)
    (hS2u : yoshidaSineMoment 2 ≤ (-1507 / 1000 : ℝ))
    (hS3l : (-1531 / 1000 : ℝ) ≤ yoshidaSineMoment 3)
    (hS3u : yoshidaSineMoment 3 ≤ (-1528 / 1000 : ℝ))
    (hD1l : (382 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 1)
    (hD2l : (1063 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 2)
    (hD3l : (1466 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 3) :
    (∀ i, yoshidaOddComparisonPrefix i i ≤
      (clippedOddPrefixGram i i).re - 1 / 40) ∧
    ∀ i j, i ≠ j →
      ‖clippedOddPrefixGram i j‖ + 1 / 40 ≤
        -yoshidaOddComparisonPrefix i j := by
  have hmodel := oddMomentPrefixGram_comparison_of_coarse_enclosures
    yoshidaSineMoment yoshidaDiagonalMoment
    hS1l hS1u hS2l hS2u hS3l hS3u hD1l hD2l hD3l
  constructor
  · intro i
    rw [hbridge i i]
    simpa using hmodel.1 i
  · intro i j hij
    rw [hbridge i j]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hmodel.2 i j hij

/-- The bridge plus the matrix comparison already imply positive
definiteness of the actual leading clipped Gram. -/
theorem clippedOddPrefixGram_posDef_of_bridge_and_comparison
    (hbridge : ClippedOddMomentBridge)
    (hdiag : ∀ i, yoshidaOddComparisonPrefix i i ≤
      (clippedOddPrefixGram i i).re - 1 / 40)
    (hoff : ∀ i j, i ≠ j →
      ‖clippedOddPrefixGram i j‖ + 1 / 40 ≤
        -yoshidaOddComparisonPrefix i j) :
    clippedOddPrefixGram.PosDef := by
  apply Matrix.posDef_of_abs_entry_comparison
    clippedOddPrefixGram yoshidaOddComparisonPrefix
    (clippedOddPrefixGram_isHermitian_of_bridge hbridge)
    yoshidaOddComparisonPrefix_posDef
  · intro i
    linarith [hdiag i]
  · intro i j hij
    linarith [hoff i j hij]

/-- The honest analytic bridge and nine coarse scalar moment enclosures imply
positive definiteness of the actual leading `3 × 3` clipped odd Gram. -/
theorem clippedOddPrefixGram_posDef_of_bridge_and_coarse_enclosures
    (hbridge : ClippedOddMomentBridge)
    (hS1l : (-1452 / 1000 : ℝ) ≤ yoshidaSineMoment 1)
    (hS1u : yoshidaSineMoment 1 ≤ (-1450 / 1000 : ℝ))
    (hS2l : (-1510 / 1000 : ℝ) ≤ yoshidaSineMoment 2)
    (hS2u : yoshidaSineMoment 2 ≤ (-1507 / 1000 : ℝ))
    (hS3l : (-1531 / 1000 : ℝ) ≤ yoshidaSineMoment 3)
    (hS3u : yoshidaSineMoment 3 ≤ (-1528 / 1000 : ℝ))
    (hD1l : (382 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 1)
    (hD2l : (1063 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 2)
    (hD3l : (1466 / 1000 : ℝ) ≤ yoshidaDiagonalMoment 3) :
    clippedOddPrefixGram.PosDef := by
  have hcomp :=
    clippedOddPrefixGram_matrix_comparison_of_bridge_and_coarse_enclosures
      hbridge hS1l hS1u hS2l hS2u hS3l hS3u hD1l hD2l hD3l
  exact clippedOddPrefixGram_posDef_of_bridge_and_comparison
    hbridge hcomp.1 hcomp.2

end

end ArithmeticHodge.Analysis.YoshidaOddGramPrefix
