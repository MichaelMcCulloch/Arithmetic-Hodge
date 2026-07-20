import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound
import ArithmeticHodge.Analysis.YoshidaEulerGammaUltraFine
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries
import ArithmeticHodge.Analysis.YoshidaPositiveLogEnclosures
import ArithmeticHodge.Analysis.YoshidaQuarterVerticalDigammaHighEnclosures
import ArithmeticHodge.Analysis.YoshidaZeroModeStieltjesIdentity

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open DigammaTrapezoid
open RatInterval
open YoshidaDiagonalDigammaHighBound
open YoshidaEulerGammaUltraFine
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPhasePerturbationOneSubCosSeries
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaPositiveLogEnclosures
open YoshidaQuarterVerticalDigammaHighEnclosures
open YoshidaSineMomentEnclosures
open YoshidaZeroModeStieltjesIdentity

/-!
# Accelerated enclosures for the factor-two `1 - cos` perturbation

The bare rational summand only has a polynomial tail.  We split

`(1 - q)^2 R = R - 2 q R + q^2 R`.

The complete `R` sum is a difference of real digamma values, while the two
remaining corrections have geometric tails.  This file establishes that
exact reduction before introducing mode-by-mode rational intervals.
-/

/-- The unweighted quarter-line rational summand. -/
def factorTwoOneSubCosMainTerm (n k : ℕ) : ℝ :=
  factorTwoMomentY n ^ 2 /
    (factorTwoCauchyX k *
      (factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2))

/-- The first dyadic correction `q R`. -/
def factorTwoOneSubCosDyadicCorrection (n k : ℕ) : ℝ :=
  factorTwoOneSubCosMainTerm n k * factorTwoDyadicQ k

/-- The second dyadic correction `q^2 R`. -/
def factorTwoOneSubCosSecondDyadicCorrection (n k : ℕ) : ℝ :=
  factorTwoOneSubCosDyadicCorrection n k * factorTwoDyadicQ k

theorem factorTwoCauchyX_pos (k : ℕ) :
    0 < factorTwoCauchyX k := by
  unfold factorTwoCauchyX
  positivity

theorem factorTwoOneSubCosMainTerm_nonneg (n k : ℕ) :
    0 ≤ factorTwoOneSubCosMainTerm n k := by
  unfold factorTwoOneSubCosMainTerm
  have hx := factorTwoCauchyX_pos k
  have hden : 0 < factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2 := by
    nlinarith [sq_nonneg (factorTwoMomentY n)]
  exact div_nonneg (sq_nonneg _) (mul_pos hx hden).le

theorem factorTwoDyadicQ_nonneg (k : ℕ) :
    0 ≤ factorTwoDyadicQ k := by
  unfold factorTwoDyadicQ
  positivity

theorem factorTwoDyadicQ_le_invFourPow (k : ℕ) :
    factorTwoDyadicQ k ≤ (1 / 4 : ℝ) ^ k := by
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  unfold factorTwoDyadicQ
  rw [show (1 / 4 : ℝ) ^ k = 1 / (4 : ℝ) ^ k by
    rw [div_pow]
    simp]
  exact div_le_div_of_nonneg_right hsqrt (by positivity)

/-- Exact algebraic acceleration of a single dyadic Cauchy rank. -/
theorem factorTwoAntisymmetricOneSubCosDyadicTerm_eq_corrections
    (n k : ℕ) :
    factorTwoAntisymmetricOneSubCosDyadicTerm n k =
      factorTwoOneSubCosMainTerm n k -
        2 * factorTwoOneSubCosDyadicCorrection n k +
        factorTwoOneSubCosSecondDyadicCorrection n k := by
  simp only [factorTwoAntisymmetricOneSubCosDyadicTerm, factorTwoDyadicD,
    factorTwoOneSubCosMainTerm, factorTwoOneSubCosDyadicCorrection,
    factorTwoOneSubCosSecondDyadicCorrection]
  ring

/-- The slow rational term is the loss in the real reciprocal kernel between
height zero and the sampled height. -/
theorem factorTwoOneSubCosMainTerm_eq_reciprocal_sub (n k : ℕ) :
    factorTwoOneSubCosMainTerm n k =
      shiftedReciprocalRealPart (1 / 4) 0 k -
        shiftedReciprocalRealPart (1 / 4) (factorTwoMomentY n) k := by
  unfold factorTwoOneSubCosMainTerm factorTwoCauchyX
    shiftedReciprocalRealPart reciprocalRealPart
  have hx : (0 : ℝ) < 1 / 4 + k := by positivity
  have hxy : (1 / 4 + (k : ℝ)) ^ 2 + factorTwoMomentY n ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (factorTwoMomentY n)]
  field_simp [hx.ne', hxy]
  ring

/-- The unweighted quarter-line rational series is summable. -/
theorem summable_factorTwoOneSubCosMainTerm (n : ℕ) :
    Summable (factorTwoOneSubCosMainTerm n) := by
  have hdiff :=
    (summable_quarterDigammaSeriesTerm (2 * factorTwoMomentY n)).sub
      (summable_quarterDigammaSeriesTerm 0)
  have hshift : Summable
      (fun m : ℕ ↦ factorTwoOneSubCosMainTerm n (m + 1)) := by
    apply hdiff.congr
    intro m
    rw [factorTwoOneSubCosMainTerm_eq_reciprocal_sub]
    unfold quarterDigammaSeriesTerm
    rw [show 2 * factorTwoMomentY n / 2 = factorTwoMomentY n by ring]
    push_cast
    ring
  exact (summable_nat_add_iff 1).mp hshift

/-- Exact evaluation of the shifted slow series as a real-digamma
difference. -/
theorem factorTwoOneSubCosMain_tsum_eq_digammaDifference (n : ℕ) :
    (∑' m : ℕ, factorTwoOneSubCosMainTerm n (m + 1)) =
      (Complex.digamma
          ((1 / 4 : ℝ) + factorTwoMomentY n * Complex.I)).re -
        (Complex.digamma (1 / 4 : ℂ)).re -
        factorTwoOneSubCosMainTerm n 0 := by
  have htwo := digamma_quarter_vertical_re_eq_trapezoid_series
    (2 * factorTwoMomentY n)
  have hzero := digamma_quarter_vertical_re_eq_trapezoid_series 0
  rw [show 2 * factorTwoMomentY n / 2 = factorTwoMomentY n by ring] at htwo
  norm_num at hzero
  have hqdiff :
      (∑' m : ℕ, quarterDigammaSeriesTerm
          (2 * factorTwoMomentY n) m) -
          ∑' m : ℕ, quarterDigammaSeriesTerm 0 m =
        ∑' m : ℕ, factorTwoOneSubCosMainTerm n (m + 1) := by
    rw [← (summable_quarterDigammaSeriesTerm
      (2 * factorTwoMomentY n)).tsum_sub
        (summable_quarterDigammaSeriesTerm 0)]
    apply tsum_congr
    intro m
    rw [factorTwoOneSubCosMainTerm_eq_reciprocal_sub]
    unfold quarterDigammaSeriesTerm
    rw [show 2 * factorTwoMomentY n / 2 = factorTwoMomentY n by ring]
    push_cast
    ring
  have hhead := factorTwoOneSubCosMainTerm_eq_reciprocal_sub n 0
  norm_num at hhead
  have harg :
      ((1 / 4 : ℝ) : ℂ) +
          ((2 * factorTwoMomentY n : ℝ) : ℂ) / 2 * Complex.I =
        ((1 / 4 : ℝ) : ℂ) +
          (factorTwoMomentY n : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg] at htwo
  linarith [htwo, hzero, hqdiff, hhead]

/-- Fine interval for the negative quarter-line digamma baseline. -/
def factorTwoQuarterDigammaNegInterval : RatInterval :=
  eulerGammaUltraFineInterval + piFineInterval / pure 2 +
    pure 3 * factorTwoPrimeLogTwoInterval

theorem factorTwoQuarterDigammaNegInterval_contains :
    factorTwoQuarterDigammaNegInterval.Contains
      (-(Complex.digamma (1 / 4 : ℂ)).re) := by
  have hpi := contains_div_of_pos
    (by norm_num [RatInterval.pure]) piFineInterval_contains
    (contains_pure 2)
  have hlog : factorTwoPrimeLogTwoInterval.Contains (Real.log 2) := by
    have h := factorTwoPrimeLogTwoInterval_contains
    unfold factorTwoMomentLength YoshidaEndpointHyperbolicBound.yoshidaEndpointA
      at h
    convert h using 1
    ring
  have hsum := contains_add
    (contains_add eulerGammaUltraFineInterval_contains hpi)
    (contains_mul (contains_pure 3) hlog)
  have hclosed := digamma_one_fourth_re_eq
  unfold YoshidaZeroModeStructuralCore.structuralYoshidaLength at hclosed
  unfold factorTwoQuarterDigammaNegInterval
  rw [hclosed]
  convert hsum using 1
  ring

theorem factorTwoQuarterDigammaNegInterval_width_le :
    width factorTwoQuarterDigammaNegInterval ≤
      (1 / 1000000000000 : ℚ) := by
  decide +kernel

/-- Closed-baseline version of the slow shifted sum. -/
theorem factorTwoOneSubCosMain_tsum_eq_closedDigamma (n : ℕ) :
    (∑' m : ℕ, factorTwoOneSubCosMainTerm n (m + 1)) =
      (Complex.digamma
          ((1 / 4 : ℝ) + factorTwoMomentY n * Complex.I)).re +
        Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 -
        factorTwoOneSubCosMainTerm n 0 := by
  rw [factorTwoOneSubCosMain_tsum_eq_digammaDifference,
    digamma_one_fourth_re_eq]
  unfold YoshidaZeroModeStructuralCore.structuralYoshidaLength
  ring

theorem factorTwoOneSubCosMainTerm_le_four (n k : ℕ) :
    factorTwoOneSubCosMainTerm n k ≤ 4 := by
  have hx := factorTwoCauchyX_pos k
  have hxQuarter : (1 / 4 : ℝ) ≤ factorTwoCauchyX k := by
    unfold factorTwoCauchyX
    norm_num
  have hsum : 0 ≤ factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2 := by
    positivity
  rw [factorTwoOneSubCosMainTerm, div_le_iff₀ (mul_pos hx (by
    have : 0 < factorTwoCauchyX k ^ 2 := sq_pos_of_pos hx
    nlinarith [sq_nonneg (factorTwoMomentY n)]))]
  calc
    factorTwoMomentY n ^ 2 ≤
        factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2 := by
      nlinarith [sq_nonneg (factorTwoCauchyX k)]
    _ ≤ 4 * (factorTwoCauchyX k *
        (factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2)) := by
      have hscale : 1 ≤ 4 * factorTwoCauchyX k := by linarith
      calc
        factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2 =
            1 * (factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2) := by
          ring
        _ ≤ (4 * factorTwoCauchyX k) *
            (factorTwoCauchyX k ^ 2 + factorTwoMomentY n ^ 2) :=
          mul_le_mul_of_nonneg_right hscale hsum
        _ = _ := by ring

theorem factorTwoDyadicQ_le_one (k : ℕ) :
    factorTwoDyadicQ k ≤ 1 := by
  calc
    factorTwoDyadicQ k ≤ (1 / 4 : ℝ) ^ k :=
      factorTwoDyadicQ_le_invFourPow k
    _ ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)

theorem factorTwoOneSubCosDyadicCorrection_nonneg (n k : ℕ) :
    0 ≤ factorTwoOneSubCosDyadicCorrection n k := by
  unfold factorTwoOneSubCosDyadicCorrection
  exact mul_nonneg (factorTwoOneSubCosMainTerm_nonneg n k)
    (factorTwoDyadicQ_nonneg k)

theorem factorTwoOneSubCosSecondDyadicCorrection_nonneg (n k : ℕ) :
    0 ≤ factorTwoOneSubCosSecondDyadicCorrection n k := by
  unfold factorTwoOneSubCosSecondDyadicCorrection
  exact mul_nonneg (factorTwoOneSubCosDyadicCorrection_nonneg n k)
    (factorTwoDyadicQ_nonneg k)

theorem summable_factorTwoOneSubCosDyadicCorrection (n : ℕ) :
    Summable (factorTwoOneSubCosDyadicCorrection n) := by
  apply (summable_factorTwoOneSubCosMainTerm n).of_nonneg_of_le
    (factorTwoOneSubCosDyadicCorrection_nonneg n)
  intro k
  unfold factorTwoOneSubCosDyadicCorrection
  exact mul_le_of_le_one_right (factorTwoOneSubCosMainTerm_nonneg n k)
    (factorTwoDyadicQ_le_one k)

theorem summable_factorTwoOneSubCosSecondDyadicCorrection (n : ℕ) :
    Summable (factorTwoOneSubCosSecondDyadicCorrection n) := by
  apply (summable_factorTwoOneSubCosDyadicCorrection n).of_nonneg_of_le
    (factorTwoOneSubCosSecondDyadicCorrection_nonneg n)
  intro k
  unfold factorTwoOneSubCosSecondDyadicCorrection
  exact mul_le_of_le_one_right
    (factorTwoOneSubCosDyadicCorrection_nonneg n k)
    (factorTwoDyadicQ_le_one k)

theorem factorTwoOneSubCosDyadicCorrection_le_geometric (n k : ℕ) :
    factorTwoOneSubCosDyadicCorrection n k ≤
      4 * (1 / 4 : ℝ) ^ k := by
  unfold factorTwoOneSubCosDyadicCorrection
  exact mul_le_mul (factorTwoOneSubCosMainTerm_le_four n k)
    (factorTwoDyadicQ_le_invFourPow k)
    (factorTwoDyadicQ_nonneg k) (by norm_num)

theorem factorTwoOneSubCosSecondDyadicCorrection_le_geometric (n k : ℕ) :
    factorTwoOneSubCosSecondDyadicCorrection n k ≤
      4 * (1 / 16 : ℝ) ^ k := by
  unfold factorTwoOneSubCosSecondDyadicCorrection
    factorTwoOneSubCosDyadicCorrection
  calc
    factorTwoOneSubCosMainTerm n k * factorTwoDyadicQ k *
          factorTwoDyadicQ k ≤
        4 * (1 / 4 : ℝ) ^ k * factorTwoDyadicQ k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (factorTwoOneSubCosMainTerm_le_four n k)
          (factorTwoDyadicQ_le_invFourPow k)
          (factorTwoDyadicQ_nonneg k) (by norm_num))
        (factorTwoDyadicQ_nonneg k)
    _ ≤ 4 * (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k := by
      exact mul_le_mul_of_nonneg_left
        (factorTwoDyadicQ_le_invFourPow k) (by positivity)
    _ = 4 * (1 / 16 : ℝ) ^ k := by
      rw [show 4 * (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k =
        4 * ((1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) by ring]
      rw [← mul_pow]
      norm_num

/-- Uniform `4^{-K}` tail bound for the first correction. -/
theorem factorTwoOneSubCosDyadicCorrection_tail_le (n K : ℕ) :
    (∑' j : ℕ, factorTwoOneSubCosDyadicCorrection n (K + j)) ≤
      6 / (4 : ℝ) ^ K := by
  let C : ℝ := 4 / (4 : ℝ) ^ K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ factorTwoOneSubCosDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2
        (summable_factorTwoOneSubCosDyadicCorrection n)
  have hpoint (j : ℕ) :
      factorTwoOneSubCosDyadicCorrection n (K + j) ≤
        C * (1 / 4 : ℝ) ^ j := by
    have h := factorTwoOneSubCosDyadicCorrection_le_geometric n (K + j)
    rw [pow_add] at h
    calc
      factorTwoOneSubCosDyadicCorrection n (K + j) ≤
          4 * ((1 / 4 : ℝ) ^ K * (1 / 4 : ℝ) ^ j) := h
      _ = C * (1 / 4 : ℝ) ^ j := by
        dsimp only [C]
        norm_num [div_pow]
        ring
  have hsum := hcorr.tsum_le_tsum hpoint hgeom
  calc
    (∑' j : ℕ, factorTwoOneSubCosDyadicCorrection n (K + j)) ≤
        ∑' j : ℕ, C * (1 / 4 : ℝ) ^ j := hsum
    _ = C * ((1 - (1 / 4 : ℝ))⁻¹) := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    _ ≤ C * (3 / 2 : ℝ) := by
      gcongr
      norm_num
    _ = 6 / (4 : ℝ) ^ K := by
      dsimp only [C]
      ring

/-- Uniform `16^{-K}` tail bound for the squared correction. -/
theorem factorTwoOneSubCosSecondDyadicCorrection_tail_le (n K : ℕ) :
    (∑' j : ℕ, factorTwoOneSubCosSecondDyadicCorrection n (K + j)) ≤
      5 / (16 : ℝ) ^ K := by
  let C : ℝ := 4 / (16 : ℝ) ^ K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 16 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ factorTwoOneSubCosSecondDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2
        (summable_factorTwoOneSubCosSecondDyadicCorrection n)
  have hpoint (j : ℕ) :
      factorTwoOneSubCosSecondDyadicCorrection n (K + j) ≤
        C * (1 / 16 : ℝ) ^ j := by
    have h :=
      factorTwoOneSubCosSecondDyadicCorrection_le_geometric n (K + j)
    rw [pow_add] at h
    calc
      factorTwoOneSubCosSecondDyadicCorrection n (K + j) ≤
          4 * ((1 / 16 : ℝ) ^ K * (1 / 16 : ℝ) ^ j) := h
      _ = C * (1 / 16 : ℝ) ^ j := by
        dsimp only [C]
        norm_num [div_pow]
        ring
  have hsum := hcorr.tsum_le_tsum hpoint hgeom
  calc
    (∑' j : ℕ,
        factorTwoOneSubCosSecondDyadicCorrection n (K + j)) ≤
        ∑' j : ℕ, C * (1 / 16 : ℝ) ^ j := hsum
    _ = C * ((1 - (1 / 16 : ℝ))⁻¹) := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)]
    _ ≤ C * (5 / 4 : ℝ) := by
      gcongr
      norm_num
    _ = 5 / (16 : ℝ) ^ K := by
      dsimp only [C]
      ring

/-! ## Rational intervals for the two geometric corrections -/

theorem factorTwoMomentY_eq_yoshidaY (n : ℕ) :
    factorTwoMomentY n = yoshidaY n := by
  unfold factorTwoMomentY yoshidaY factorTwoNaturalFrequency
  rw [factorTwoMomentLength_eq_yoshidaLength]

/-! ## A fine logarithm enclosure for the vertical quarter point -/

/-- The prime-scale `log 2` interval gives a substantially sharper height
box than the legacy sine-moment interval. -/
def factorTwoOneSubCosFineYInterval (n : ℕ) : RatInterval :=
  ⟨piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper,
    piFineInterval.upper * n / factorTwoPrimeLogTwoInterval.lower⟩

theorem factorTwoOneSubCosFineYInterval_contains (n : ℕ) :
    (factorTwoOneSubCosFineYInterval n).Contains (factorTwoMomentY n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (piFineInterval.lower : ℝ) * (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (piFineInterval.upper : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.2 hn0
  have hLlo : (0 : ℝ) < (factorTwoPrimeLogTwoInterval.lower : ℚ) := by
    norm_num [factorTwoPrimeLogTwoInterval]
  have hy : factorTwoMomentY n =
      Real.pi * (n : ℝ) / factorTwoMomentLength := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    ring
  rw [hy]
  unfold factorTwoOneSubCosFineYInterval Contains
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  exact ⟨
    div_le_div₀ hnum0 hnumLo factorTwoMomentLength_pos
      factorTwoPrimeLogTwoInterval_contains.2,
    div_le_div₀
      (mul_nonneg (by
        exact_mod_cast (show (0 : ℚ) ≤ piFineInterval.upper by
          norm_num [piFineInterval])) hn0)
      hnumHi hLlo factorTwoPrimeLogTwoInterval_contains.1⟩

private theorem factorTwoOneSubCosFineYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (factorTwoOneSubCosFineYInterval n).lower := by
  unfold factorTwoOneSubCosFineYInterval piFineInterval
    factorTwoPrimeLogTwoInterval
  positivity

/-- Exact rational box for `1/16 + y_n^2`. -/
def factorTwoOneSubCosLogArgumentInterval (n : ℕ) : RatInterval :=
  pure (1 / 16) + nonnegSquare (factorTwoOneSubCosFineYInterval n)

theorem factorTwoOneSubCosLogArgumentInterval_contains (n : ℕ) :
    (factorTwoOneSubCosLogArgumentInterval n).Contains
      ((1 / 16 : ℝ) + factorTwoMomentY n ^ 2) := by
  have hconst : (pure (1 / 16 : ℚ)).Contains (1 / 16 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  exact contains_add hconst
    (contains_nonnegSquare
      (factorTwoOneSubCosFineYInterval_lower_nonneg n)
      (factorTwoOneSubCosFineYInterval_contains n))

/-- A nearby exact power of two used to reduce the logarithm to a uniformly
small positive atanh argument. -/
def factorTwoOneSubCosLogScaleExponent (n : ℕ) : ℕ :=
  Nat.log2 (20 * n ^ 2)

def factorTwoOneSubCosLogScale (n : ℕ) : ℚ :=
  (2 : ℚ) ^ factorTwoOneSubCosLogScaleExponent n

/-- Interval image of `(z-s)/(z+s)`, where `s` is the nearby power of two. -/
def factorTwoOneSubCosLogRatioInputInterval (n : ℕ) : RatInterval :=
  (factorTwoOneSubCosLogArgumentInterval n -
      pure (factorTwoOneSubCosLogScale n)) /
    (factorTwoOneSubCosLogArgumentInterval n +
      pure (factorTwoOneSubCosLogScale n))

/-- On the finite production band the chosen power is below the entire
argument box and the resulting atanh input stays uniformly in `[0,1)`. -/
theorem factorTwoOneSubCosLogRatioInputInterval_bounds :
    ∀ n : FactorTwoCanonicalEvenIndex, n.1 ≠ 0 →
      0 ≤ (factorTwoOneSubCosLogRatioInputInterval n.1).lower ∧
      (factorTwoOneSubCosLogRatioInputInterval n.1).upper < 1 ∧
      0 < (factorTwoOneSubCosLogArgumentInterval n.1 +
        pure (factorTwoOneSubCosLogScale n.1)).lower := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem factorTwoOneSubCosLogRatioInputInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoOneSubCosLogRatioInputInterval n.1).Contains
      (((1 / 16 : ℝ) + factorTwoMomentY n.1 ^ 2 -
          factorTwoOneSubCosLogScale n.1) /
        ((1 / 16 : ℝ) + factorTwoMomentY n.1 ^ 2 +
          factorTwoOneSubCosLogScale n.1)) := by
  have hz := factorTwoOneSubCosLogArgumentInterval_contains n.1
  have hs := contains_pure (factorTwoOneSubCosLogScale n.1)
  exact contains_div_of_pos
    (factorTwoOneSubCosLogRatioInputInterval_bounds n hn).2.2
    (contains_sub hz hs) (contains_add hz hs)

/-- Fine enclosure of the logarithm in the vertical digamma main term. -/
def factorTwoOneSubCosLogArgumentLogInterval (n : ℕ) : RatInterval :=
  pure (factorTwoOneSubCosLogScaleExponent n) *
      factorTwoPrimeLogTwoInterval +
    positiveLogRatioInterval
      (factorTwoOneSubCosLogRatioInputInterval n) 24

theorem factorTwoOneSubCosLogArgumentLogInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoOneSubCosLogArgumentLogInterval n.1).Contains
      (Real.log ((1 / 16 : ℝ) + factorTwoMomentY n.1 ^ 2)) := by
  let z : ℝ := (1 / 16 : ℝ) + factorTwoMomentY n.1 ^ 2
  let s : ℚ := factorTwoOneSubCosLogScale n.1
  let x : ℝ := (z - s) / (z + s)
  have hz : 0 < z := by
    dsimp only [z]
    positivity
  have hsQ : 0 < s := by
    dsimp only [s, factorTwoOneSubCosLogScale]
    positivity
  have hs : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsQ
  have hzs : z + (s : ℝ) ≠ 0 := (add_pos hz hs).ne'
  have hxs : x =
      ((z - (s : ℝ)) / (z + (s : ℝ))) := rfl
  have hratio : (1 + x) / (1 - x) = z / (s : ℝ) := by
    rw [hxs]
    field_simp [hz.ne', hs.ne', hzs]
    ring
  have hscaleCast : (s : ℝ) =
      (2 : ℝ) ^ factorTwoOneSubCosLogScaleExponent n.1 := by
    dsimp only [s, factorTwoOneSubCosLogScale]
    norm_num
  have hlogScale : Real.log (s : ℝ) =
      factorTwoOneSubCosLogScaleExponent n.1 *
        factorTwoMomentLength := by
    rw [hscaleCast, Real.log_pow]
    rw [factorTwoMomentLength_eq_yoshidaLength]
    rfl
  have hxI := factorTwoOneSubCosLogRatioInputInterval_contains n hn
  have hxI' : (factorTwoOneSubCosLogRatioInputInterval n.1).Contains x := by
    simpa only [x, z, s] using hxI
  have hbounds := factorTwoOneSubCosLogRatioInputInterval_bounds n hn
  have hlogRatio := positiveLogRatioInterval_contains
    hbounds.1 hbounds.2.1 hxI' 24
  have hscaleI := contains_mul
    (contains_pure (factorTwoOneSubCosLogScaleExponent n.1))
    factorTwoPrimeLogTwoInterval_contains
  have hsum := contains_add hscaleI hlogRatio
  unfold factorTwoOneSubCosLogArgumentLogInterval
  convert hsum using 1
  rw [hratio, Real.log_div hz.ne' hs.ne', hlogScale]
  dsimp only [z]
  norm_num only [Rat.cast_natCast]
  ring

private def factorTwoOneSubCosMainDenomInterval (n k : ℕ) : RatInterval :=
  pure (quarterShiftQ k ^ 2) +
    nonnegSquare (factorTwoOneSubCosFineYInterval n)

private theorem factorTwoOneSubCosMainDenomInterval_lower_pos (n k : ℕ) :
    0 < (factorTwoOneSubCosMainDenomInterval n k).lower := by
  change 0 < quarterShiftQ k ^ 2 +
    (factorTwoOneSubCosFineYInterval n).lower ^ 2
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (quarterShiftQ_pos k))
    (sq_nonneg _)

/-- Exact interval for the unweighted rational term `R_k`. -/
def factorTwoOneSubCosMainInterval (n k : ℕ) : RatInterval :=
  nonnegSquare (factorTwoOneSubCosFineYInterval n) /
      factorTwoOneSubCosMainDenomInterval n k /
    pure (quarterShiftQ k)

theorem factorTwoOneSubCosMainInterval_contains (n k : ℕ) :
    (factorTwoOneSubCosMainInterval n k).Contains
      (factorTwoOneSubCosMainTerm n k) := by
  have hy := factorTwoOneSubCosFineYInterval_contains n
  have hySq := contains_nonnegSquare
    (factorTwoOneSubCosFineYInterval_lower_nonneg n) hy
  have hxSq : (pure (quarterShiftQ k ^ 2)).Contains
      (((k : ℝ) + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hden : (factorTwoOneSubCosMainDenomInterval n k).Contains
      (((k : ℝ) + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) := by
    exact contains_add hxSq hySq
  have hratio := contains_div_of_pos
    (factorTwoOneSubCosMainDenomInterval_lower_pos n k) hySq hden
  have hfull := contains_div_of_pos
    (by simpa only [RatInterval.pure] using quarterShiftQ_pos k)
    hratio (contains_pure (quarterShiftQ k))
  unfold factorTwoOneSubCosMainInterval factorTwoOneSubCosMainTerm
    factorTwoCauchyX
  convert hfull using 1
  · norm_num [quarterShiftQ]
    field_simp

def factorTwoOneSubCosDyadicQInterval (k : ℕ) : RatInterval :=
  sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)

theorem factorTwoOneSubCosDyadicQInterval_contains (k : ℕ) :
    (factorTwoOneSubCosDyadicQInterval k).Contains
      (factorTwoDyadicQ k) := by
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval])
      sqrtTwoInterval_contains
  have hpow : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
    simpa using contains_pure ((4 : ℚ) ^ k)
  unfold factorTwoOneSubCosDyadicQInterval factorTwoDyadicQ
  exact contains_div_of_pos (by
    change 0 < (4 : ℚ) ^ k
    positivity) hsInv hpow

def factorTwoOneSubCosDyadicCorrectionInterval (n k : ℕ) : RatInterval :=
  factorTwoOneSubCosMainInterval n k *
    factorTwoOneSubCosDyadicQInterval k

theorem factorTwoOneSubCosDyadicCorrectionInterval_contains (n k : ℕ) :
    (factorTwoOneSubCosDyadicCorrectionInterval n k).Contains
      (factorTwoOneSubCosDyadicCorrection n k) := by
  exact contains_mul (factorTwoOneSubCosMainInterval_contains n k)
    (factorTwoOneSubCosDyadicQInterval_contains k)

def factorTwoOneSubCosSecondDyadicCorrectionInterval
    (n k : ℕ) : RatInterval :=
  factorTwoOneSubCosDyadicCorrectionInterval n k *
    factorTwoOneSubCosDyadicQInterval k

theorem factorTwoOneSubCosSecondDyadicCorrectionInterval_contains
    (n k : ℕ) :
    (factorTwoOneSubCosSecondDyadicCorrectionInterval n k).Contains
      (factorTwoOneSubCosSecondDyadicCorrection n k) := by
  exact contains_mul
    (factorTwoOneSubCosDyadicCorrectionInterval_contains n k)
    (factorTwoOneSubCosDyadicQInterval_contains k)

def factorTwoOneSubCosDyadicCorrectionHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoOneSubCosDyadicCorrectionHeadInterval n K +
      factorTwoOneSubCosDyadicCorrectionInterval n K

theorem factorTwoOneSubCosDyadicCorrectionHeadInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosDyadicCorrectionHeadInterval n K).Contains
      (∑ k ∈ Finset.range K, factorTwoOneSubCosDyadicCorrection n k) := by
  induction K with
  | zero =>
      norm_num [factorTwoOneSubCosDyadicCorrectionHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoOneSubCosDyadicCorrectionInterval_contains n K)

def factorTwoOneSubCosDyadicCorrectionTailInterval (K : ℕ) : RatInterval :=
  ⟨0, 6 / (4 : ℚ) ^ K⟩

theorem factorTwoOneSubCosDyadicCorrectionTailInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosDyadicCorrectionTailInterval K).Contains
      (∑' j : ℕ, factorTwoOneSubCosDyadicCorrection n (K + j)) := by
  have hlo : 0 ≤
      ∑' j : ℕ, factorTwoOneSubCosDyadicCorrection n (K + j) :=
    tsum_nonneg fun j ↦ factorTwoOneSubCosDyadicCorrection_nonneg n (K + j)
  have hup := factorTwoOneSubCosDyadicCorrection_tail_le n K
  exact ⟨by
    simpa [factorTwoOneSubCosDyadicCorrectionTailInterval, Contains] using hlo,
    by
      simpa only [factorTwoOneSubCosDyadicCorrectionTailInterval, Contains,
        Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hup⟩

def factorTwoOneSubCosDyadicCorrectionFullInterval
    (n K : ℕ) : RatInterval :=
  factorTwoOneSubCosDyadicCorrectionHeadInterval n K +
    factorTwoOneSubCosDyadicCorrectionTailInterval K

theorem factorTwoOneSubCosDyadicCorrectionFullInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosDyadicCorrectionFullInterval n K).Contains
      (∑' k : ℕ, factorTwoOneSubCosDyadicCorrection n k) := by
  have hsplit :=
    (summable_factorTwoOneSubCosDyadicCorrection n).sum_add_tsum_nat_add K
  rw [← hsplit]
  exact contains_add
    (factorTwoOneSubCosDyadicCorrectionHeadInterval_contains n K)
    (by simpa [Nat.add_comm] using
      factorTwoOneSubCosDyadicCorrectionTailInterval_contains n K)

def factorTwoOneSubCosSecondDyadicCorrectionHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoOneSubCosSecondDyadicCorrectionHeadInterval n K +
      factorTwoOneSubCosSecondDyadicCorrectionInterval n K

theorem factorTwoOneSubCosSecondDyadicCorrectionHeadInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosSecondDyadicCorrectionHeadInterval n K).Contains
      (∑ k ∈ Finset.range K,
        factorTwoOneSubCosSecondDyadicCorrection n k) := by
  induction K with
  | zero =>
      norm_num [factorTwoOneSubCosSecondDyadicCorrectionHeadInterval,
        Contains, RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoOneSubCosSecondDyadicCorrectionInterval_contains n K)

def factorTwoOneSubCosSecondDyadicCorrectionTailInterval
    (K : ℕ) : RatInterval :=
  ⟨0, 5 / (16 : ℚ) ^ K⟩

theorem factorTwoOneSubCosSecondDyadicCorrectionTailInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosSecondDyadicCorrectionTailInterval K).Contains
      (∑' j : ℕ,
        factorTwoOneSubCosSecondDyadicCorrection n (K + j)) := by
  have hlo : 0 ≤
      ∑' j : ℕ, factorTwoOneSubCosSecondDyadicCorrection n (K + j) :=
    tsum_nonneg fun j ↦
      factorTwoOneSubCosSecondDyadicCorrection_nonneg n (K + j)
  have hup := factorTwoOneSubCosSecondDyadicCorrection_tail_le n K
  exact ⟨by
    simpa [factorTwoOneSubCosSecondDyadicCorrectionTailInterval, Contains]
      using hlo,
    by
      simpa only [factorTwoOneSubCosSecondDyadicCorrectionTailInterval,
        Contains, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hup⟩

def factorTwoOneSubCosSecondDyadicCorrectionFullInterval
    (n K : ℕ) : RatInterval :=
  factorTwoOneSubCosSecondDyadicCorrectionHeadInterval n K +
    factorTwoOneSubCosSecondDyadicCorrectionTailInterval K

theorem factorTwoOneSubCosSecondDyadicCorrectionFullInterval_contains
    (n K : ℕ) :
    (factorTwoOneSubCosSecondDyadicCorrectionFullInterval n K).Contains
      (∑' k : ℕ, factorTwoOneSubCosSecondDyadicCorrection n k) := by
  have hsplit :=
    (summable_factorTwoOneSubCosSecondDyadicCorrection n).sum_add_tsum_nat_add K
  rw [← hsplit]
  exact contains_add
    (factorTwoOneSubCosSecondDyadicCorrectionHeadInterval_contains n K)
    (by simpa [Nat.add_comm] using
      factorTwoOneSubCosSecondDyadicCorrectionTailInterval_contains n K)

/-- Exact accelerated form of the shifted dyadic Cauchy series. -/
theorem factorTwoAntisymmetricOneSubCosDyadic_tsum_eq_digammaCorrections
    (n : ℕ) :
    (∑' m : ℕ,
        factorTwoAntisymmetricOneSubCosDyadicTerm n (m + 1)) =
      ((Complex.digamma
          ((1 / 4 : ℝ) + factorTwoMomentY n * Complex.I)).re -
        (Complex.digamma (1 / 4 : ℂ)).re -
        factorTwoOneSubCosMainTerm n 0) -
      2 * ((∑' k : ℕ, factorTwoOneSubCosDyadicCorrection n k) -
        factorTwoOneSubCosDyadicCorrection n 0) +
      ((∑' k : ℕ, factorTwoOneSubCosSecondDyadicCorrection n k) -
        factorTwoOneSubCosSecondDyadicCorrection n 0) := by
  have hM := summable_factorTwoOneSubCosMainTerm n
  have hC := summable_factorTwoOneSubCosDyadicCorrection n
  have hE := summable_factorTwoOneSubCosSecondDyadicCorrection n
  have hMshift : HasSum
      (fun m : ℕ ↦ factorTwoOneSubCosMainTerm n (m + 1))
      ((∑' k : ℕ, factorTwoOneSubCosMainTerm n k) -
        factorTwoOneSubCosMainTerm n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hM.hasSum
  have hCshift : HasSum
      (fun m : ℕ ↦ factorTwoOneSubCosDyadicCorrection n (m + 1))
      ((∑' k : ℕ, factorTwoOneSubCosDyadicCorrection n k) -
        factorTwoOneSubCosDyadicCorrection n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hC.hasSum
  have hEshift : HasSum
      (fun m : ℕ ↦ factorTwoOneSubCosSecondDyadicCorrection n (m + 1))
      ((∑' k : ℕ, factorTwoOneSubCosSecondDyadicCorrection n k) -
        factorTwoOneSubCosSecondDyadicCorrection n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hE.hasSum
  have hcombined := (hMshift.sub (hCshift.mul_left 2)).add hEshift
  have hfactor : HasSum
      (fun m : ℕ ↦
        factorTwoAntisymmetricOneSubCosDyadicTerm n (m + 1))
      (((∑' k : ℕ, factorTwoOneSubCosMainTerm n k) -
          factorTwoOneSubCosMainTerm n 0) -
        2 * ((∑' k : ℕ, factorTwoOneSubCosDyadicCorrection n k) -
          factorTwoOneSubCosDyadicCorrection n 0) +
        ((∑' k : ℕ, factorTwoOneSubCosSecondDyadicCorrection n k) -
          factorTwoOneSubCosSecondDyadicCorrection n 0)) := by
    convert hcombined using 1
    funext m
    rw [factorTwoAntisymmetricOneSubCosDyadicTerm_eq_corrections]
  rw [hfactor.tsum_eq]
  rw [show (∑' k : ℕ, factorTwoOneSubCosMainTerm n k) -
      factorTwoOneSubCosMainTerm n 0 =
        ∑' m : ℕ, factorTwoOneSubCosMainTerm n (m + 1) by
    simpa only [Finset.sum_range_one] using
      ((hasSum_nat_add_iff' 1).2 hM.hasSum).tsum_eq.symm]
  rw [factorTwoOneSubCosMain_tsum_eq_digammaDifference]

/-- Full positive-mode perturbation moment in accelerated digamma form. -/
theorem factorTwoAntisymmetricOneSubCosMoment_eq_digammaCorrections
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoAntisymmetricOneSubCosMoment n.1 =
      -factorTwoHeadDefect * factorTwoOneSubCosMainTerm n.1 0 -
        (((Complex.digamma
            ((1 / 4 : ℝ) + factorTwoMomentY n.1 * Complex.I)).re -
          (Complex.digamma (1 / 4 : ℂ)).re -
          factorTwoOneSubCosMainTerm n.1 0) -
        2 * ((∑' k : ℕ, factorTwoOneSubCosDyadicCorrection n.1 k) -
          factorTwoOneSubCosDyadicCorrection n.1 0) +
        ((∑' k : ℕ,
            factorTwoOneSubCosSecondDyadicCorrection n.1 k) -
          factorTwoOneSubCosSecondDyadicCorrection n.1 0)) +
      2 * (Real.log 3 / Real.sqrt 3) *
        (1 - Real.cos
          (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  rw [factorTwoAntisymmetricOneSubCosMoment_eq_dyadicCauchySeries n hn]
  have htail :
      (∑' m : ℕ,
          factorTwoDyadicD (m + 1) * factorTwoMomentY n.1 ^ 2 /
            (factorTwoCauchyX (m + 1) *
              (factorTwoCauchyX (m + 1) ^ 2 +
                factorTwoMomentY n.1 ^ 2))) =
        ∑' m : ℕ,
          factorTwoAntisymmetricOneSubCosDyadicTerm n.1 (m + 1) := by
    rfl
  rw [htail,
    factorTwoAntisymmetricOneSubCosDyadic_tsum_eq_digammaCorrections]
  unfold factorTwoOneSubCosMainTerm
  ring

/-! ## Composed high-band perturbation enclosure -/

/-- High-frequency interval for the full real vertical digamma value. -/
def factorTwoOneSubCosVerticalDigammaInterval (n : ℕ) : RatInterval :=
  quarterVerticalDigammaLogResidualTarget n +
    factorTwoOneSubCosLogArgumentLogInterval n / pure 2

theorem factorTwoOneSubCosVerticalDigammaInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoOneSubCosVerticalDigammaInterval n.1).Contains
      ((Complex.digamma
        ((1 / 4 : ℝ) + factorTwoMomentY n.1 * Complex.I)).re) := by
  have hres := quarterVerticalDigammaLogResidualTarget_contains
    (n := n.1) hn
  have hy : YoshidaDiagonalUniformIdentity.yoshidaY n.1 =
      factorTwoMomentY n.1 := by
    unfold YoshidaDiagonalUniformIdentity.yoshidaY
      YoshidaOddGramPrefix.yoshidaKappa
      factorTwoMomentY factorTwoNaturalFrequency
    rw [factorTwoMomentLength_eq_yoshidaLength]
    ring
  rw [hy] at hres
  have hlog := factorTwoOneSubCosLogArgumentLogInterval_contains n hn
  have hhalf := contains_div_of_pos
    (by norm_num [RatInterval.pure]) hlog (contains_pure 2)
  have hsum := contains_add hres hhalf
  unfold factorTwoOneSubCosVerticalDigammaInterval
  convert hsum using 1
  ring

/-- Direct positive-mode target obtained by substituting the exact accelerated
digamma identity.  The first and second geometric corrections use cutoffs
`20` and `10`, respectively. -/
def factorTwoAntisymmetricOneSubCosPositiveInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  -(factorTwoHeadDefectInterval *
      factorTwoOneSubCosMainInterval n.1 0) -
    (((factorTwoOneSubCosVerticalDigammaInterval n.1 +
          factorTwoQuarterDigammaNegInterval -
          factorTwoOneSubCosMainInterval n.1 0) -
        pure 2 *
          (factorTwoOneSubCosDyadicCorrectionFullInterval n.1 20 -
            factorTwoOneSubCosDyadicCorrectionInterval n.1 0)) +
      (factorTwoOneSubCosSecondDyadicCorrectionFullInterval n.1 10 -
        factorTwoOneSubCosSecondDyadicCorrectionInterval n.1 0)) +
    pure 2 * factorTwoPrimeBetaInterval *
      (pure 1 - factorTwoPrimeCosInterval n)

theorem factorTwoAntisymmetricOneSubCosPositiveInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoAntisymmetricOneSubCosPositiveInterval n).Contains
      (factorTwoAntisymmetricOneSubCosMoment n.1) := by
  rw [factorTwoAntisymmetricOneSubCosMoment_eq_digammaCorrections n hn]
  have hmain0 := factorTwoOneSubCosMainInterval_contains n.1 0
  have hhead := contains_neg
    (contains_mul factorTwoHeadDefectInterval_contains hmain0)
  have hhead' :
      (-(factorTwoHeadDefectInterval *
        factorTwoOneSubCosMainInterval n.1 0)).Contains
        (-factorTwoHeadDefect * factorTwoOneSubCosMainTerm n.1 0) := by
    convert hhead using 1
    ring
  have hvertical := factorTwoOneSubCosVerticalDigammaInterval_contains n hn
  have hslow := contains_sub
    (contains_add hvertical factorTwoQuarterDigammaNegInterval_contains)
    hmain0
  have hfirst := contains_sub
    (factorTwoOneSubCosDyadicCorrectionFullInterval_contains n.1 20)
    (factorTwoOneSubCosDyadicCorrectionInterval_contains n.1 0)
  have hsecond := contains_sub
    (factorTwoOneSubCosSecondDyadicCorrectionFullInterval_contains n.1 10)
    (factorTwoOneSubCosSecondDyadicCorrectionInterval_contains n.1 0)
  have hcore := contains_add
    (contains_sub hslow (contains_mul (contains_pure 2) hfirst)) hsecond
  have hprime := contains_mul
    (contains_mul (contains_pure 2) factorTwoPrimeBetaInterval_contains)
    (contains_sub (contains_pure 1) (factorTwoPrimeCosInterval_contains n))
  have hprime' :
      (pure 2 * factorTwoPrimeBetaInterval *
        (pure 1 - factorTwoPrimeCosInterval n)).Contains
          (2 * (Real.log 3 / Real.sqrt 3) *
            (1 - Real.cos
              (2 * factorTwoMomentY n.1 * factorTwoPrimeShift))) := by
    convert hprime using 1
    norm_num
  exact contains_add (contains_sub hhead' hcore) hprime'

/-- Unified target, with the exact zero mode handled without inflation. -/
def factorTwoAntisymmetricOneSubCosMomentInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then pure 0
  else factorTwoAntisymmetricOneSubCosPositiveInterval n

theorem factorTwoAntisymmetricOneSubCosMomentInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAntisymmetricOneSubCosMomentInterval n).Contains
      (factorTwoAntisymmetricOneSubCosMoment n.1) := by
  by_cases hn : n.1 = 0
  · simp only [factorTwoAntisymmetricOneSubCosMomentInterval, hn, if_pos]
    have hzero : factorTwoAntisymmetricOneSubCosMoment 0 = 0 := by
      unfold factorTwoAntisymmetricOneSubCosMoment
        factorTwoAntisymmetricPerturbationFunctional factorTwoNaturalFrequency
      simp
    rw [hzero]
    norm_num [Contains, RatInterval.pure]
  · simp only [factorTwoAntisymmetricOneSubCosMomentInterval, hn]
    exact factorTwoAntisymmetricOneSubCosPositiveInterval_contains n hn

/-! ## Width certificate -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_018_022 :
    ∀ n : FactorTwoCanonicalEvenIndex, 18 ≤ n.1 → n.1 ≤ 22 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_023_027 :
    ∀ n : FactorTwoCanonicalEvenIndex, 23 ≤ n.1 → n.1 ≤ 27 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_028_032 :
    ∀ n : FactorTwoCanonicalEvenIndex, 28 ≤ n.1 → n.1 ≤ 32 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_033_037 :
    ∀ n : FactorTwoCanonicalEvenIndex, 33 ≤ n.1 → n.1 ≤ 37 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_038_042 :
    ∀ n : FactorTwoCanonicalEvenIndex, 38 ≤ n.1 → n.1 ≤ 42 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_043_047 :
    ∀ n : FactorTwoCanonicalEvenIndex, 43 ≤ n.1 → n.1 ≤ 47 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_048_052 :
    ∀ n : FactorTwoCanonicalEvenIndex, 48 ≤ n.1 → n.1 ≤ 52 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_053_057 :
    ∀ n : FactorTwoCanonicalEvenIndex, 53 ≤ n.1 → n.1 ≤ 57 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_058_062 :
    ∀ n : FactorTwoCanonicalEvenIndex, 58 ≤ n.1 → n.1 ≤ 62 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_063_067 :
    ∀ n : FactorTwoCanonicalEvenIndex, 63 ≤ n.1 → n.1 ≤ 67 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_068_072 :
    ∀ n : FactorTwoCanonicalEvenIndex, 68 ≤ n.1 → n.1 ≤ 72 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_073_077 :
    ∀ n : FactorTwoCanonicalEvenIndex, 73 ≤ n.1 → n.1 ≤ 77 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_078_082 :
    ∀ n : FactorTwoCanonicalEvenIndex, 78 ≤ n.1 → n.1 ≤ 82 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_083_087 :
    ∀ n : FactorTwoCanonicalEvenIndex, 83 ≤ n.1 → n.1 ≤ 87 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_088_092 :
    ∀ n : FactorTwoCanonicalEvenIndex, 88 ≤ n.1 → n.1 ≤ 92 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_093_097 :
    ∀ n : FactorTwoCanonicalEvenIndex, 93 ≤ n.1 → n.1 ≤ 97 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_098_102 :
    ∀ n : FactorTwoCanonicalEvenIndex, 98 ≤ n.1 → n.1 ≤ 102 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_103_107 :
    ∀ n : FactorTwoCanonicalEvenIndex, 103 ≤ n.1 → n.1 ≤ 107 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_108_112 :
    ∀ n : FactorTwoCanonicalEvenIndex, 108 ≤ n.1 → n.1 ≤ 112 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_113_117 :
    ∀ n : FactorTwoCanonicalEvenIndex, 113 ≤ n.1 → n.1 ≤ 117 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_118_122 :
    ∀ n : FactorTwoCanonicalEvenIndex, 118 ≤ n.1 → n.1 ≤ 122 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_123_127 :
    ∀ n : FactorTwoCanonicalEvenIndex, 123 ≤ n.1 → n.1 ≤ 127 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_128_132 :
    ∀ n : FactorTwoCanonicalEvenIndex, 128 ≤ n.1 → n.1 ≤ 132 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_133_137 :
    ∀ n : FactorTwoCanonicalEvenIndex, 133 ≤ n.1 → n.1 ≤ 137 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_138_142 :
    ∀ n : FactorTwoCanonicalEvenIndex, 138 ≤ n.1 → n.1 ≤ 142 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_143_147 :
    ∀ n : FactorTwoCanonicalEvenIndex, 143 ≤ n.1 → n.1 ≤ 147 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_148_152 :
    ∀ n : FactorTwoCanonicalEvenIndex, 148 ≤ n.1 → n.1 ≤ 152 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_153_157 :
    ∀ n : FactorTwoCanonicalEvenIndex, 153 ≤ n.1 → n.1 ≤ 157 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_158_162 :
    ∀ n : FactorTwoCanonicalEvenIndex, 158 ≤ n.1 → n.1 ≤ 162 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_163_167 :
    ∀ n : FactorTwoCanonicalEvenIndex, 163 ≤ n.1 → n.1 ≤ 167 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_168_172 :
    ∀ n : FactorTwoCanonicalEvenIndex, 168 ≤ n.1 → n.1 ≤ 172 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_173_177 :
    ∀ n : FactorTwoCanonicalEvenIndex, 173 ≤ n.1 → n.1 ≤ 177 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_178_182 :
    ∀ n : FactorTwoCanonicalEvenIndex, 178 ≤ n.1 → n.1 ≤ 182 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_183_187 :
    ∀ n : FactorTwoCanonicalEvenIndex, 183 ≤ n.1 → n.1 ≤ 187 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_188_192 :
    ∀ n : FactorTwoCanonicalEvenIndex, 188 ≤ n.1 → n.1 ≤ 192 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_193_197 :
    ∀ n : FactorTwoCanonicalEvenIndex, 193 ≤ n.1 → n.1 ≤ 197 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_198_200 :
    ∀ n : FactorTwoCanonicalEvenIndex, 198 ≤ n.1 → n.1 ≤ 200 →
      width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  decide +kernel

/-- Every mode from `18` through `200` has total composed width at most
`10⁻⁹`. -/
theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_high
    (n : FactorTwoCanonicalEvenIndex) (hn018 : 18 ≤ n.1) :
    width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
      (1 / 1000000000 : ℚ) := by
  by_cases hn022 : n.1 ≤ 22
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_018_022 n (by omega) hn022
  by_cases hn027 : n.1 ≤ 27
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_023_027 n (by omega) hn027
  by_cases hn032 : n.1 ≤ 32
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_028_032 n (by omega) hn032
  by_cases hn037 : n.1 ≤ 37
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_033_037 n (by omega) hn037
  by_cases hn042 : n.1 ≤ 42
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_038_042 n (by omega) hn042
  by_cases hn047 : n.1 ≤ 47
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_043_047 n (by omega) hn047
  by_cases hn052 : n.1 ≤ 52
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_048_052 n (by omega) hn052
  by_cases hn057 : n.1 ≤ 57
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_053_057 n (by omega) hn057
  by_cases hn062 : n.1 ≤ 62
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_058_062 n (by omega) hn062
  by_cases hn067 : n.1 ≤ 67
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_063_067 n (by omega) hn067
  by_cases hn072 : n.1 ≤ 72
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_068_072 n (by omega) hn072
  by_cases hn077 : n.1 ≤ 77
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_073_077 n (by omega) hn077
  by_cases hn082 : n.1 ≤ 82
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_078_082 n (by omega) hn082
  by_cases hn087 : n.1 ≤ 87
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_083_087 n (by omega) hn087
  by_cases hn092 : n.1 ≤ 92
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_088_092 n (by omega) hn092
  by_cases hn097 : n.1 ≤ 97
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_093_097 n (by omega) hn097
  by_cases hn102 : n.1 ≤ 102
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_098_102 n (by omega) hn102
  by_cases hn107 : n.1 ≤ 107
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_103_107 n (by omega) hn107
  by_cases hn112 : n.1 ≤ 112
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_108_112 n (by omega) hn112
  by_cases hn117 : n.1 ≤ 117
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_113_117 n (by omega) hn117
  by_cases hn122 : n.1 ≤ 122
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_118_122 n (by omega) hn122
  by_cases hn127 : n.1 ≤ 127
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_123_127 n (by omega) hn127
  by_cases hn132 : n.1 ≤ 132
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_128_132 n (by omega) hn132
  by_cases hn137 : n.1 ≤ 137
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_133_137 n (by omega) hn137
  by_cases hn142 : n.1 ≤ 142
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_138_142 n (by omega) hn142
  by_cases hn147 : n.1 ≤ 147
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_143_147 n (by omega) hn147
  by_cases hn152 : n.1 ≤ 152
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_148_152 n (by omega) hn152
  by_cases hn157 : n.1 ≤ 157
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_153_157 n (by omega) hn157
  by_cases hn162 : n.1 ≤ 162
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_158_162 n (by omega) hn162
  by_cases hn167 : n.1 ≤ 167
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_163_167 n (by omega) hn167
  by_cases hn172 : n.1 ≤ 172
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_168_172 n (by omega) hn172
  by_cases hn177 : n.1 ≤ 177
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_173_177 n (by omega) hn177
  by_cases hn182 : n.1 ≤ 182
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_178_182 n (by omega) hn182
  by_cases hn187 : n.1 ≤ 187
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_183_187 n (by omega) hn187
  by_cases hn192 : n.1 ≤ 192
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_188_192 n (by omega) hn192
  by_cases hn197 : n.1 ≤ 197
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_193_197 n (by omega) hn197
  exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_198_200 n (by omega) (by omega)

theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_zero :
    width (factorTwoAntisymmetricOneSubCosMomentInterval
      ⟨0, by omega⟩) = 0 := by
  decide +kernel

/-- Unified certificate on `{0} ∪ [18, 200]`. -/
theorem factorTwoAntisymmetricOneSubCosMomentInterval_width_le_certified
    (n : FactorTwoCanonicalEvenIndex)
    (hn : n.1 = 0 ∨ 18 ≤ n.1) :
    width (factorTwoAntisymmetricOneSubCosMomentInterval n) ≤
      (1 / 1000000000 : ℚ) := by
  rcases hn with hn | hn
  · have hzero : n = ⟨0, by omega⟩ := Fin.ext hn
    rw [hzero,
      factorTwoAntisymmetricOneSubCosMomentInterval_width_zero]
    norm_num
  · exact factorTwoAntisymmetricOneSubCosMomentInterval_width_le_high n hn

/-- Mode `17` is the sharp failure immediately below the direct high band. -/
theorem factorTwoAntisymmetricOneSubCosMomentInterval_high_cutoff_sharp :
    (1 / 1000000000 : ℚ) <
      width (factorTwoAntisymmetricOneSubCosMomentInterval
        ⟨17, by omega⟩) := by
  decide +kernel

theorem factorTwoAntisymmetricOneSubCosMoment_zero :
    factorTwoAntisymmetricOneSubCosMoment 0 = 0 := by
  unfold factorTwoAntisymmetricOneSubCosMoment
    factorTwoAntisymmetricPerturbationFunctional factorTwoNaturalFrequency
  simp

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosEnclosures
