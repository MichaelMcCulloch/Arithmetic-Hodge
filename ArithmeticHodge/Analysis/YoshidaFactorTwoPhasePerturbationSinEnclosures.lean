import ArithmeticHodge.Analysis.YoshidaEvenSineHighEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open RatInterval
open YoshidaCauchyTailBounds
open YoshidaEvenCouplingReduction
open YoshidaEvenDigammaImagRemainder
open YoshidaEvenSineHighEnclosures
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures
open YoshidaSineSeriesTail
open YoshidaWeightedTailBounds

/-!
# Exact enclosures for the factor-two symmetric sine perturbation

The dyadic coefficient is accelerated before interval evaluation:

`(1 / 2) M_k (1 - q_k)^2 = (1 / 2) (M_k - 2 M_k q_k + M_k q_k^2)`.

The slow `M_k` sum is the existing imaginary-digamma sample.  The first
correction is Yoshida's established dyadic correction, and the new squared
correction has a `16^{-k}` tail.  This gives a compact high-mode enclosure
without truncating the unweighted Cauchy series.
-/

/-- The doubly dyadic correction `M_k q_k^2`. -/
def factorTwoSecondDyadicCorrection (n k : ℕ) : ℝ :=
  sineDyadicCorrection n k * factorTwoDyadicQ k

theorem factorTwoMomentY_eq_yoshidaY (n : ℕ) :
    factorTwoMomentY n = yoshidaY n := by
  unfold factorTwoMomentY yoshidaY factorTwoNaturalFrequency
  rw [factorTwoMomentLength_eq_yoshidaLength]

theorem factorTwoDyadicQ_mem_unitInterval (k : ℕ) :
    0 ≤ factorTwoDyadicQ k ∧ factorTwoDyadicQ k ≤ 1 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtOne : 1 ≤ Real.sqrt 2 := by nlinarith
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtPos).2 hsqrtOne
  have hpow : 1 ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hpowPos : 0 < (4 : ℝ) ^ k := by positivity
  constructor
  · unfold factorTwoDyadicQ
    positivity
  · unfold factorTwoDyadicQ
    calc
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k :=
        div_le_div_of_nonneg_right hinv hpowPos.le
      _ ≤ 1 := (div_le_one hpowPos).2 hpow

theorem factorTwoSecondDyadicCorrection_nonneg
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    0 ≤ factorTwoSecondDyadicCorrection n k := by
  unfold factorTwoSecondDyadicCorrection
  exact mul_nonneg (sineDyadicCorrection_nonneg hn k)
    (factorTwoDyadicQ_mem_unitInterval k).1

theorem summable_factorTwoSecondDyadicCorrection
    {n : ℕ} (hn : n ≠ 0) :
    Summable (factorTwoSecondDyadicCorrection n) := by
  apply (summable_sineDyadicCorrection hn).of_nonneg_of_le
    (factorTwoSecondDyadicCorrection_nonneg hn)
  intro k
  unfold factorTwoSecondDyadicCorrection
  exact mul_le_of_le_one_right (sineDyadicCorrection_nonneg hn k)
    (factorTwoDyadicQ_mem_unitInterval k).2

/-- Exact algebraic acceleration of one factor-two dyadic rank. -/
theorem factorTwoSymmetricSinDyadicTerm_eq_corrections (n k : ℕ) :
    factorTwoSymmetricSinDyadicTerm n k =
      (1 / 2 : ℝ) *
        (sineMainTerm n k - 2 * sineDyadicCorrection n k +
          factorTwoSecondDyadicCorrection n k) := by
  unfold factorTwoSymmetricSinDyadicTerm factorTwoDyadicD
    factorTwoCauchyX factorTwoSecondDyadicCorrection factorTwoDyadicQ
    sineDyadicCorrection sineMainTerm cauchyTailTerm
    yoshidaScaledFrequency
  rw [factorTwoMomentY_eq_yoshidaY, yoshidaKappa_eq_two_mul_y]
  ring

/-- The complete shifted factor-two dyadic sum in terms of one digamma sample
and two exponentially convergent corrections. -/
theorem factorTwoSymmetricSinDyadic_tsum_eq_digammaCorrections
    {n : ℕ} (hn : n ≠ 0) :
    (∑' m : ℕ, factorTwoSymmetricSinDyadicTerm n (m + 1)) =
      (1 / 2 : ℝ) *
        ((yoshidaEvenDigammaImag n - sineMainTerm n 0) -
          2 * ((∑' k : ℕ, sineDyadicCorrection n k) -
            sineDyadicCorrection n 0) +
          ((∑' k : ℕ, factorTwoSecondDyadicCorrection n k) -
            factorTwoSecondDyadicCorrection n 0)) := by
  have hM := summable_sineMainTerm hn
  have hC := summable_sineDyadicCorrection hn
  have hE := summable_factorTwoSecondDyadicCorrection hn
  have hMshift : HasSum (fun m : ℕ ↦ sineMainTerm n (m + 1))
      ((∑' k : ℕ, sineMainTerm n k) - sineMainTerm n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hM.hasSum
  have hCshift : HasSum (fun m : ℕ ↦ sineDyadicCorrection n (m + 1))
      ((∑' k : ℕ, sineDyadicCorrection n k) -
        sineDyadicCorrection n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hC.hasSum
  have hEshift : HasSum
      (fun m : ℕ ↦ factorTwoSecondDyadicCorrection n (m + 1))
      ((∑' k : ℕ, factorTwoSecondDyadicCorrection n k) -
        factorTwoSecondDyadicCorrection n 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hE.hasSum
  have hcombined :=
    ((hMshift.sub (hCshift.mul_left 2)).add hEshift).mul_left (1 / 2 : ℝ)
  have hfactor : HasSum
      (fun m : ℕ ↦ factorTwoSymmetricSinDyadicTerm n (m + 1))
      ((1 / 2 : ℝ) *
        (((∑' k : ℕ, sineMainTerm n k) - sineMainTerm n 0) -
          2 * ((∑' k : ℕ, sineDyadicCorrection n k) -
            sineDyadicCorrection n 0) +
          ((∑' k : ℕ, factorTwoSecondDyadicCorrection n k) -
            factorTwoSecondDyadicCorrection n 0))) := by
    convert hcombined using 1
    funext m
    rw [factorTwoSymmetricSinDyadicTerm_eq_corrections]
  rw [hfactor.tsum_eq, yoshidaEvenDigammaImag_eq_tsum]
  congr 4
  apply tsum_congr
  intro k
  unfold evenDigammaCauchyTerm sineMainTerm cauchyTailTerm
    yoshidaScaledFrequency
  rw [evenDigammaY, yoshidaKappa, yoshidaA, yoshidaLength]
  ring

/-- Exact full perturbation identity in accelerated digamma form. -/
theorem factorTwoSymmetricSinMoment_eq_digammaCorrections
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricSinMoment n.1 =
      -(factorTwoHeadDefect / 2) * sineMainTerm n.1 0 +
        (1 / 2 : ℝ) *
          ((yoshidaEvenDigammaImag n.1 - sineMainTerm n.1 0) -
            2 * ((∑' k : ℕ, sineDyadicCorrection n.1 k) -
              sineDyadicCorrection n.1 0) +
            ((∑' k : ℕ, factorTwoSecondDyadicCorrection n.1 k) -
              factorTwoSecondDyadicCorrection n.1 0)) -
        (Real.log 3 / Real.sqrt 3) *
          Real.sin
            (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  rw [factorTwoSymmetricSinMoment_eq_dyadicCauchySeries n hn,
    factorTwoSymmetricSinDyadic_tsum_eq_digammaCorrections hn]
  have hhead :
      -(factorTwoHeadDefect / 2) * factorTwoMomentY n.1 /
          (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n.1 ^ 2) =
        -(factorTwoHeadDefect / 2) * sineMainTerm n.1 0 := by
    rw [factorTwoMomentY_eq_yoshidaY]
    unfold factorTwoCauchyX sineMainTerm cauchyTailTerm
      yoshidaScaledFrequency
    rw [yoshidaKappa_eq_two_mul_y]
    norm_num
    ring
  rw [hhead]

theorem factorTwoSymmetricSinMoment_zero :
    factorTwoSymmetricSinMoment 0 = 0 := by
  unfold factorTwoSymmetricSinMoment factorTwoSymmetricPerturbationFunctional
    factorTwoNaturalFrequency
  simp

private theorem sineMainTerm_le_inv_frequency
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineMainTerm n k ≤ 1 / yoshidaScaledFrequency n := by
  have hy := yoshidaScaledFrequency_pos hn
  rw [sineMainTerm, cauchyTailTerm]
  rw [div_le_div_iff₀ (by positivity :
    0 < ((1 / 4 : ℝ) + k) ^ 2 + yoshidaScaledFrequency n ^ 2) hy]
  nlinarith [sq_nonneg ((1 / 4 : ℝ) + k)]

private theorem factorTwoDyadicQ_le_invFourPow (k : ℕ) :
    factorTwoDyadicQ k ≤ (1 / 4 : ℝ) ^ k := by
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  unfold factorTwoDyadicQ
  calc
    (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k :=
      div_le_div_of_nonneg_right hsqrt (by positivity)
    _ = (1 / 4 : ℝ) ^ k := by
      simpa only [one_div] using (one_div_pow (4 : ℝ) k).symm

private theorem factorTwoSecondDyadicCorrection_le_inv_geometric
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    factorTwoSecondDyadicCorrection n k ≤
      (1 / yoshidaScaledFrequency n) * (1 / 16 : ℝ) ^ k := by
  have hy := yoshidaScaledFrequency_pos hn
  have hmain0 := sineMainTerm_nonneg hn k
  have hmain := sineMainTerm_le_inv_frequency hn k
  have hq0 := (factorTwoDyadicQ_mem_unitInterval k).1
  have hq := factorTwoDyadicQ_le_invFourPow k
  have hfour0 : 0 ≤ (1 / 4 : ℝ) ^ k := by positivity
  unfold factorTwoSecondDyadicCorrection sineDyadicCorrection
  calc
    sineMainTerm n k * (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k *
          factorTwoDyadicQ k =
        sineMainTerm n k * factorTwoDyadicQ k ^ 2 := by
      unfold factorTwoDyadicQ
      ring
    _ ≤ (1 / yoshidaScaledFrequency n) * ((1 / 4 : ℝ) ^ k) ^ 2 := by
      gcongr
    _ = (1 / yoshidaScaledFrequency n) * (1 / 16 : ℝ) ^ k := by
      congr 1
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num

/-- The squared-dyadic tail has a uniform `16^{-K}` bound. -/
theorem factorTwoSecondDyadicCorrection_tail_le
    {n K : ℕ} (hn : n ≠ 0) :
    (∑' j : ℕ, factorTwoSecondDyadicCorrection n (K + j)) ≤
      2 / (yoshidaScaledFrequency n * (16 : ℝ) ^ K) := by
  let C : ℝ := 1 / (yoshidaScaledFrequency n * (16 : ℝ) ^ K)
  have hy := yoshidaScaledFrequency_pos hn
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 16 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ factorTwoSecondDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2
        (summable_factorTwoSecondDyadicCorrection hn)
  have hpoint (j : ℕ) :
      factorTwoSecondDyadicCorrection n (K + j) ≤
        C * (1 / 16 : ℝ) ^ j := by
    have h := factorTwoSecondDyadicCorrection_le_inv_geometric hn (K + j)
    rw [pow_add] at h
    calc
      factorTwoSecondDyadicCorrection n (K + j) ≤
          (1 / yoshidaScaledFrequency n) *
            ((1 / 16 : ℝ) ^ K * (1 / 16 : ℝ) ^ j) := h
      _ = C * (1 / 16 : ℝ) ^ j := by
        dsimp only [C]
        field_simp [hy.ne']
        norm_num [div_pow]
  have hsum := hcorr.tsum_le_tsum hpoint hgeom
  calc
    (∑' j : ℕ, factorTwoSecondDyadicCorrection n (K + j)) ≤
        ∑' j : ℕ, C * (1 / 16 : ℝ) ^ j := hsum
    _ = C * ((1 - (1 / 16 : ℝ))⁻¹) := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)]
    _ ≤ C * 2 := by
      gcongr
      norm_num
    _ = 2 / (yoshidaScaledFrequency n * (16 : ℝ) ^ K) := by
      dsimp only [C]
      ring

private theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

private theorem yoshidaYInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (yoshidaYInterval n).lower := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  change 0 < piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

/-- Exact rational interval for the unweighted Cauchy term `M_k`. -/
def factorTwoSineMainInterval (n k : ℕ) : RatInterval :=
  yoshidaYInterval n / cauchyDenomInterval n k

theorem factorTwoSineMainInterval_contains (n k : ℕ) :
    (factorTwoSineMainInterval n k).Contains (sineMainTerm n k) := by
  have hy := yoshidaYInterval_contains n
  have hx : (pure (quarterShiftQ k ^ 2)).Contains
      (((k : ℝ) + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hden : (cauchyDenomInterval n k).Contains
      (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2) := by
    exact contains_add hx
      (contains_nonnegSquare (yoshidaYInterval_lower_nonneg n) hy)
  have hmain := contains_div_of_pos
    (cauchyDenomInterval_lower_pos n k) hy hden
  unfold factorTwoSineMainInterval sineMainTerm cauchyTailTerm
    yoshidaScaledFrequency
  rw [yoshidaKappa_eq_two_mul_y]
  convert hmain using 1
  ring

/-- Exact rational interval for the factor `q_k`. -/
def factorTwoDyadicQInterval (k : ℕ) : RatInterval :=
  sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)

theorem factorTwoDyadicQInterval_contains (k : ℕ) :
    (factorTwoDyadicQInterval k).Contains (factorTwoDyadicQ k) := by
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval])
      sqrtTwoInterval_contains
  have hpow : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
    simpa using contains_pure ((4 : ℚ) ^ k)
  exact contains_div_of_pos (by
    change 0 < (4 : ℚ) ^ k
    positivity) hsInv hpow

/-- Exact rational interval for `M_k q_k^2`. -/
def factorTwoSecondDyadicCorrectionInterval (n k : ℕ) : RatInterval :=
  sineDyadicCorrectionInterval n k * factorTwoDyadicQInterval k

theorem factorTwoSecondDyadicCorrectionInterval_contains
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (factorTwoSecondDyadicCorrectionInterval n k).Contains
      (factorTwoSecondDyadicCorrection n k) := by
  exact contains_mul (sineDyadicCorrectionInterval_contains hn k)
    (factorTwoDyadicQInterval_contains k)

def factorTwoSecondDyadicCorrectionHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoSecondDyadicCorrectionHeadInterval n K +
      factorTwoSecondDyadicCorrectionInterval n K

theorem factorTwoSecondDyadicCorrectionHeadInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (factorTwoSecondDyadicCorrectionHeadInterval n K).Contains
      (∑ k ∈ Finset.range K, factorTwoSecondDyadicCorrection n k) := by
  induction K with
  | zero =>
      norm_num [factorTwoSecondDyadicCorrectionHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoSecondDyadicCorrectionInterval_contains hn K)

def factorTwoSecondDyadicCorrectionTailInterval
    (n K : ℕ) : RatInterval :=
  ⟨0, 2 / ((yoshidaYInterval n).lower * (16 : ℚ) ^ K)⟩

theorem factorTwoSecondDyadicCorrectionTailInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (factorTwoSecondDyadicCorrectionTailInterval n K).Contains
      (∑' j : ℕ, factorTwoSecondDyadicCorrection n (K + j)) := by
  have hlow : 0 ≤
      ∑' j : ℕ, factorTwoSecondDyadicCorrection n (K + j) :=
    tsum_nonneg fun j ↦ factorTwoSecondDyadicCorrection_nonneg hn (K + j)
  have hsource := factorTwoSecondDyadicCorrection_tail_le (n := n) (K := K) hn
  have hyI := yoshidaYInterval_contains n
  have hylQ := yoshidaYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((yoshidaYInterval n).lower : ℝ) := by
    exact_mod_cast hylQ
  have hden :
      (((yoshidaYInterval n).lower : ℚ) : ℝ) * (16 : ℝ) ^ K ≤
        yoshidaScaledFrequency n * (16 : ℝ) ^ K := by
    rw [yoshidaScaledFrequency_eq_y]
    exact mul_le_mul_of_nonneg_right hyI.1 (by positivity)
  have hupper :
      (∑' j : ℕ, factorTwoSecondDyadicCorrection n (K + j)) ≤
        2 / ((((yoshidaYInterval n).lower : ℚ) : ℝ) *
          (16 : ℝ) ^ K) :=
    hsource.trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden)
  constructor
  · simpa [factorTwoSecondDyadicCorrectionTailInterval, Contains] using hlow
  · simpa only [factorTwoSecondDyadicCorrectionTailInterval, Contains,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow] using hupper

def factorTwoSecondDyadicCorrectionFullInterval
    (n K : ℕ) : RatInterval :=
  factorTwoSecondDyadicCorrectionHeadInterval n K +
    factorTwoSecondDyadicCorrectionTailInterval n K

theorem factorTwoSecondDyadicCorrectionFullInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (factorTwoSecondDyadicCorrectionFullInterval n K).Contains
      (∑' k : ℕ, factorTwoSecondDyadicCorrection n k) := by
  have hsplit :=
    (summable_factorTwoSecondDyadicCorrection hn).sum_add_tsum_nat_add K
  rw [← hsplit]
  exact contains_add
    (factorTwoSecondDyadicCorrectionHeadInterval_contains hn K)
    (by simpa [Nat.add_comm] using
      factorTwoSecondDyadicCorrectionTailInterval_contains hn K)

/-! ## Accelerated perturbation enclosure -/

/-- The exceptional growing-head contribution. -/
def factorTwoSymmetricSinHeadInterval (n : ℕ) : RatInterval :=
  -(factorTwoHeadDefectInterval / pure 2) *
    factorTwoSineMainInterval n 0

theorem factorTwoSymmetricSinHeadInterval_contains
    (n : ℕ) :
    (factorTwoSymmetricSinHeadInterval n).Contains
      (-(factorTwoHeadDefect / 2) * sineMainTerm n 0) := by
  have hhalf : (factorTwoHeadDefectInterval / pure 2).Contains
      (factorTwoHeadDefect / 2) :=
    contains_div_of_pos
      (by norm_num [RatInterval.pure])
      factorTwoHeadDefectInterval_contains (contains_pure 2)
  exact contains_mul (contains_neg hhalf)
    (factorTwoSineMainInterval_contains n 0)

/-- The complete accelerated dyadic contribution.  Twenty first-correction
terms and twelve squared-correction terms leave geometric tails far below the
analytic cubic remainder. -/
def factorTwoSymmetricSinAcceleratedSeriesInterval (n : ℕ) : RatInterval :=
  pure (1 / 2) *
    ((evenDigammaCubicInterval n - factorTwoSineMainInterval n 0) -
      pure 2 *
        (sineDyadicCorrectionFullInterval n 20 -
          sineDyadicCorrectionInterval n 0) +
      (factorTwoSecondDyadicCorrectionFullInterval n 12 -
        factorTwoSecondDyadicCorrectionInterval n 0))

theorem factorTwoSymmetricSinAcceleratedSeriesInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (factorTwoSymmetricSinAcceleratedSeriesInterval n).Contains
      ((1 / 2 : ℝ) *
        ((yoshidaEvenDigammaImag n - sineMainTerm n 0) -
          2 * ((∑' k : ℕ, sineDyadicCorrection n k) -
            sineDyadicCorrection n 0) +
          ((∑' k : ℕ, factorTwoSecondDyadicCorrection n k) -
            factorTwoSecondDyadicCorrection n 0))) := by
  have hdigamma := evenDigammaCubicInterval_contains hn
  have hmain := factorTwoSineMainInterval_contains n 0
  have hfirstFull := sineDyadicCorrectionFullInterval_contains hn 20
  have hfirstZero := sineDyadicCorrectionInterval_contains hn 0
  have hsecondFull :=
    factorTwoSecondDyadicCorrectionFullInterval_contains hn 12
  have hsecondZero :=
    factorTwoSecondDyadicCorrectionInterval_contains hn 0
  have hhalf : (pure (1 / 2 : ℚ)).Contains (1 / 2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  exact contains_mul hhalf
    (contains_add
      (contains_sub (contains_sub hdigamma hmain)
        (contains_mul (contains_pure 2)
          (contains_sub hfirstFull hfirstZero)))
      (contains_sub hsecondFull hsecondZero))

/-- The retained-prime atom. -/
def factorTwoSymmetricSinPrimeInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoPrimeBetaInterval * factorTwoPrimeSinInterval n

theorem factorTwoSymmetricSinPrimeInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoSymmetricSinPrimeInterval n).Contains
      ((Real.log 3 / Real.sqrt 3) *
        Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  exact contains_mul factorTwoPrimeBetaInterval_contains
    (factorTwoPrimeSinInterval_contains n)

/-- Positive-mode enclosure assembled from the growing head, the accelerated
dyadic series, and the retained-prime atom. -/
def factorTwoSymmetricSinPositiveInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoSymmetricSinHeadInterval n.1 +
    factorTwoSymmetricSinAcceleratedSeriesInterval n.1 -
    factorTwoSymmetricSinPrimeInterval n

theorem factorTwoSymmetricSinPositiveInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoSymmetricSinPositiveInterval n).Contains
      (factorTwoSymmetricSinMoment n.1) := by
  rw [factorTwoSymmetricSinMoment_eq_digammaCorrections n hn]
  exact contains_sub
    (contains_add (factorTwoSymmetricSinHeadInterval_contains n.1)
      (factorTwoSymmetricSinAcceleratedSeriesInterval_contains hn))
    (factorTwoSymmetricSinPrimeInterval_contains n)

/-- Uniform exact-rational enclosure on the canonical `Fin 201` mode set.
The zero mode is evaluated exactly; positive modes use the accelerated
digamma decomposition. -/
def factorTwoSymmetricSinMomentInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then pure 0 else factorTwoSymmetricSinPositiveInterval n

theorem factorTwoSymmetricSinMomentInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoSymmetricSinMomentInterval n).Contains
      (factorTwoSymmetricSinMoment n.1) := by
  by_cases hn : n.1 = 0
  · simpa [factorTwoSymmetricSinMomentInterval, hn,
      factorTwoSymmetricSinMoment_zero] using contains_pure (0 : ℚ)
  · simpa [factorTwoSymmetricSinMomentInterval, hn] using
      factorTwoSymmetricSinPositiveInterval_contains n hn

/-! ## Width certificate -/

/-- Every high mode from `153` through the canonical top mode `200` has
width at most `10⁻⁹`. -/
theorem factorTwoSymmetricSinMomentInterval_width_le_high :
    ∀ n : FactorTwoCanonicalEvenIndex, 153 ≤ n.1 →
      width (factorTwoSymmetricSinMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  set_option maxRecDepth 1000000 in
    decide +kernel

/-- The zero mode is represented by the exact singleton interval. -/
theorem factorTwoSymmetricSinMomentInterval_width_zero :
    width (factorTwoSymmetricSinMomentInterval ⟨0, by omega⟩) = 0 := by
  decide +kernel

/-- Unified statement of the certified mode set `{0} ∪ [153, 200]`. -/
theorem factorTwoSymmetricSinMomentInterval_width_le_certified
    (n : FactorTwoCanonicalEvenIndex)
    (hn : n.1 = 0 ∨ 153 ≤ n.1) :
    width (factorTwoSymmetricSinMomentInterval n) ≤
      (1 / 1000000000 : ℚ) := by
  rcases hn with hn | hn
  · have hzero : n = ⟨0, by omega⟩ := Fin.ext hn
    rw [hzero, factorTwoSymmetricSinMomentInterval_width_zero]
    norm_num
  · exact factorTwoSymmetricSinMomentInterval_width_le_high n hn

/-- The high-mode threshold is sharp for this uniform interval construction:
mode `152` still has width strictly greater than `10⁻⁹`. -/
theorem factorTwoSymmetricSinMomentInterval_high_cutoff_sharp :
    (1 / 1000000000 : ℚ) <
      width (factorTwoSymmetricSinMomentInterval ⟨152, by omega⟩) := by
  decide +kernel

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinEnclosures
