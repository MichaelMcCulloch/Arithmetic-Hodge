import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaOddMomentTargets

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalSeriesTail
open YoshidaOddGramPrefix
open YoshidaOddMomentTargets
open YoshidaSineMomentEnclosures

noncomputable section

/-!
# Certified enclosures for Yoshida's diagonal moments

Rational interval arithmetic encloses the exact accelerated diagonal series.
The finite heads are checked in small kernel-reducible blocks, while the
remaining infinite tails use the sharp analytic estimate from
`YoshidaDiagonalSeriesTail`.
-/

def gammaInterval : RatInterval :=
  ⟨5771 / 10000, 5773 / 10000⟩

def logPiInterval : RatInterval :=
  ⟨11447 / 10000, 11448 / 10000⟩

def logFourThirdsInterval : RatInterval :=
  ⟨28768207244 / 100000000000, 28768207246 / 100000000000⟩

def kappaSqInterval (n : ℕ) : RatInterval :=
  pure 4 * nonnegSquare (yoshidaYInterval n)

def positiveSquare (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 2, I.upper ^ 2⟩

def tinyDyadic : ℚ := 1 / (4 : ℚ) ^ 32

def sqrtDyadicInterval (k : ℕ) : RatInterval :=
  if k ≤ 32 then
    sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)
  else
    ⟨0, tinyDyadic⟩

def dyadicInterval (k : ℕ) : RatInterval :=
  if k ≤ 32 then
    pure (1 / (4 : ℚ) ^ k)
  else
    ⟨0, tinyDyadic⟩

def diagonalRampInterval (n : ℕ) (a : ℚ) (q : RatInterval) : RatInterval :=
  let L := logTwoFineInterval
  let p := kappaSqInterval n
  let aI := pure a
  let aSq := pure (a ^ 2)
  ((q - pure 1 + aI * L) * (aSq - p) +
      pure 2 * aI * p * L) /
    (L * positiveSquare (aSq + p))

def diagonalAInterval : RatInterval :=
  pure 1 / (pure 2 * logTwoFineInterval) + pure (1 / 4)

def diagonalBaseInterval (n : ℕ) : RatInterval :=
  pure 2 * diagonalRampInterval n (-1 / 2) sqrtTwoInterval -
      gammaInterval - logPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

def diagonalCorrectionInterval (n k : ℕ) : RatInterval :=
  let kQ : ℚ := k
  pure 2 * diagonalRampInterval n (2 * kQ + 1 / 2)
      (sqrtDyadicInterval k) -
    (pure 1 - dyadicInterval k) / pure kQ +
      diagonalAInterval / pure (kQ ^ 2)

def diagonalHeadIntervalAux (n : ℕ) : ℕ → ℕ → RatInterval → RatInterval
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
      diagonalHeadIntervalAux n fuel (k + 1)
        (acc + diagonalCorrectionInterval n k)

def diagonalHeadInterval (n K : ℕ) : RatInterval :=
  diagonalHeadIntervalAux n K 1 (pure 0)

/-- Rational upper bound for the sharp absolute tail at series index `N`. -/
def diagonalTailRadius (n N : ℕ) : ℚ :=
  11 * ((kappaSqInterval n).upper + 1) / (10 * (N : ℚ) ^ 2)

def diagonalTailInterval (n N : ℕ) : RatInterval :=
  let r := diagonalTailRadius n N
  ⟨-r, r⟩

def diagonalSeriesInterval (n N : ℕ) : RatInterval :=
  diagonalBaseInterval n - diagonalHeadInterval n (N - 1) +
    diagonalTailInterval n N

def diagonalCutoff : ℕ → ℕ
  | 1 | 2 | 3 => 1024
  | 4 | 5 | 6 | 7 => 2048
  | _ => 4096

def diagonalCertifiedInterval (n : ℕ) : RatInterval :=
  diagonalSeriesInterval n (diagonalCutoff n)

/-! ## Soundness of the rational interval operations -/

theorem gammaInterval_contains :
    gammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := yoshida_euler_gamma_bounds
  constructor
  · norm_num [gammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [gammaInterval, Contains] at h ⊢
    exact h.2.le

theorem logPiInterval_contains :
    logPiInterval.Contains (Real.log Real.pi) := by
  have h := yoshida_log_pi_bounds
  constructor
  · norm_num [logPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [logPiInterval, Contains] at h ⊢
    exact h.2.le

theorem logFourThirdsInterval_contains :
    logFourThirdsInterval.Contains (Real.log (4 / 3)) := by
  have hlo := Real.sum_range_le_log_div (x := (1 / 7 : ℝ))
    (by norm_num) (by norm_num) 7
  have hup := Real.log_div_le_sum_range_add (x := (1 / 7 : ℝ))
    (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ, logFourThirdsInterval, Contains] at hlo hup ⊢
  constructor <;> linarith

private theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

theorem kappaSqInterval_contains (n : ℕ) :
    (kappaSqInterval n).Contains (yoshidaKappa n ^ 2) := by
  have hy := yoshidaYInterval_contains n
  have hySq := contains_nonnegSquare (yoshidaYInterval_lower_nonneg n) hy
  have hfour : (pure (4 : ℚ)).Contains (4 : ℝ) := contains_pure 4
  have h := contains_mul hfour hySq
  rw [yoshidaKappa_eq_two_mul_y]
  convert h using 1
  ring

theorem positiveSquare_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (positiveSquare I).Contains (x ^ 2) := by
  simpa only [positiveSquare, nonnegSquare] using contains_nonnegSquare hI0 hx

private theorem inv_sqrt_two_le_one : (Real.sqrt 2)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (by positivity)]
  exact Real.one_le_sqrt.mpr (by norm_num)

private theorem dyadic_tail_le_tiny
    {k : ℕ} (hk : 32 < k) :
    1 / (4 : ℝ) ^ k ≤ (tinyDyadic : ℝ) := by
  have hpow : (4 : ℝ) ^ 32 ≤ (4 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hk.le
  have hinv := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < (4 : ℝ) ^ 32) hpow
  norm_num [tinyDyadic] at hinv ⊢
  exact hinv

theorem sqrtDyadicInterval_contains (k : ℕ) :
    (sqrtDyadicInterval k).Contains
      ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) := by
  rw [sqrtDyadicInterval]
  split_ifs with hk
  · have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
      (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval])
      sqrtTwoInterval_contains
    have hfour : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
      simpa using contains_pure ((4 : ℚ) ^ k)
    exact contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ k
      positivity) hsInv hfour
  · have hk' : 32 < k := by omega
    constructor
    · norm_num [Contains]
      positivity
    · norm_num [Contains]
      calc
        (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k := by
          exact div_le_div_of_nonneg_right inv_sqrt_two_le_one (by positivity)
        _ ≤ (tinyDyadic : ℝ) := dyadic_tail_le_tiny hk'

theorem dyadicInterval_contains (k : ℕ) :
    (dyadicInterval k).Contains (1 / (4 : ℝ) ^ k) := by
  rw [dyadicInterval]
  split_ifs with hk
  · simpa using contains_pure (1 / (4 : ℚ) ^ k)
  · have hk' : 32 < k := by omega
    constructor
    · norm_num [Contains]
    · norm_num [Contains]
      simpa only [one_div] using dyadic_tail_le_tiny hk'

private theorem kappaSqInterval_lower_nonneg (n : ℕ) :
    0 ≤ (kappaSqInterval n).lower := by
  change 0 ≤ min
    (min (4 * (yoshidaYInterval n).lower ^ 2)
      (4 * (yoshidaYInterval n).upper ^ 2))
    (min (4 * (yoshidaYInterval n).lower ^ 2)
      (4 * (yoshidaYInterval n).upper ^ 2))
  simp only [min_self, le_min_iff]
  exact ⟨by positivity, by positivity⟩

private theorem mul_lower_pos_of_pos
    {I J : RatInterval}
    (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hIv : I.Valid) (hJv : J.Valid) :
    0 < (I * J).lower := by
  have hIu : 0 < I.upper := hI.trans_le hIv
  have hJu : 0 < J.upper := hJ.trans_le hJv
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hI hJ, mul_pos hI hJu⟩,
    ⟨mul_pos hIu hJ, mul_pos hIu hJu⟩⟩

theorem diagonalRampInterval_contains
    (n : ℕ) (a : ℚ) (q : RatInterval) {z : ℝ}
    (ha : a ≠ 0) (hq : q.Contains z) :
    (diagonalRampInterval n a q).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) (a : ℝ) z) := by
  let L := logTwoFineInterval
  let p := kappaSqInterval n
  let aI := pure a
  let aSq := pure (a ^ 2)
  have hL : L.Contains yoshidaLength := logTwoFineInterval_contains
  have hp : p.Contains (yoshidaKappa n ^ 2) := kappaSqInterval_contains n
  have haI : aI.Contains (a : ℝ) := contains_pure a
  have haSq : aSq.Contains ((a : ℝ) ^ 2) := by
    constructor <;> norm_num [aSq, Contains, RatInterval.pure]
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsum : (aSq + p).Contains ((a : ℝ) ^ 2 + yoshidaKappa n ^ 2) :=
    contains_add haSq hp
  have hsumLower : 0 < (aSq + p).lower := by
    change 0 < a ^ 2 + (kappaSqInterval n).lower
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha)
      (kappaSqInterval_lower_nonneg n)
  have hsq : (positiveSquare (aSq + p)).Contains
      (((a : ℝ) ^ 2 + yoshidaKappa n ^ 2) ^ 2) :=
    positiveSquare_contains hsumLower.le hsum
  have hden : (L * positiveSquare (aSq + p)).Contains
      (yoshidaLength * (((a : ℝ) ^ 2 + yoshidaKappa n ^ 2) ^ 2)) :=
    contains_mul hL hsq
  have hdenLower : 0 < (L * positiveSquare (aSq + p)).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [L, logTwoFineInterval]
    · change 0 < (aSq + p).lower ^ 2
      positivity
    · exact valid_of_contains hL
    · exact valid_of_contains hsq
  have hnum :
      ((q - RatInterval.pure 1 + aI * L) * (aSq - p) +
        RatInterval.pure 2 * aI * p * L).Contains
        ((z - 1 + (a : ℝ) * yoshidaLength) *
            ((a : ℝ) ^ 2 - yoshidaKappa n ^ 2) +
          2 * (a : ℝ) * yoshidaKappa n ^ 2 * yoshidaLength) := by
    exact contains_add
      (contains_mul
        (contains_add (contains_sub hq hone) (contains_mul haI hL))
        (contains_sub haSq hp))
      (contains_mul (contains_mul (contains_mul htwo haI) hp) hL)
  unfold diagonalRampInterval
  dsimp only
  apply contains_div_of_pos hdenLower hnum hden

noncomputable def diagonalAValue : ℝ :=
  1 / (2 * yoshidaLength) + 1 / 4

theorem diagonalAInterval_contains :
    diagonalAInterval.Contains diagonalAValue := by
  have hL := logTwoFineInterval_contains
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hquarter : (RatInterval.pure (1 / 4 : ℚ)).Contains (1 / 4 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hden : (RatInterval.pure 2 * logTwoFineInterval).Contains
      (2 * yoshidaLength) := contains_mul htwo hL
  have hdenLower : 0 < (RatInterval.pure 2 * logTwoFineInterval).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [RatInterval.pure]
    · norm_num [logTwoFineInterval]
    · exact valid_of_contains htwo
    · exact valid_of_contains hL
  unfold diagonalAInterval diagonalAValue
  exact contains_add (contains_div_of_pos hdenLower hone hden) hquarter

theorem diagonalAValue_eq_accelerationCoefficient :
    diagonalAValue = diagonalAccelerationCoefficient := by
  rfl

noncomputable def diagonalBaseValue (n : ℕ) : ℝ :=
  2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) (-1 / 2)
      (Real.sqrt 2) -
    Real.eulerMascheroniConstant - Real.log Real.pi + Real.log (4 / 3) +
      diagonalAValue * Real.pi ^ 2 / 6

/-- The interval base expression is exactly the production accelerated base. -/
theorem diagonalBaseValue_eq_acceleratedBase (n : ℕ) :
    diagonalBaseValue n = diagonalAcceleratedBase n := by
  rw [diagonalBaseValue, diagonalAcceleratedBase,
    diagonalAValue_eq_accelerationCoefficient]
  ring

theorem diagonalBaseInterval_contains_acceleratedBase (n : ℕ) :
    (diagonalBaseInterval n).Contains (diagonalAcceleratedBase n) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains n (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval n (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) (-1 / 2 : ℝ)
        (Real.sqrt 2)) := by
    convert hramp using 1
    norm_num
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsix : (RatInterval.pure (6 : ℚ)).Contains (6 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hpiSq : (positiveSquare piFineInterval).Contains (Real.pi ^ 2) :=
    positiveSquare_contains (by norm_num [piFineInterval]) piFineInterval_contains
  have htail :
      (diagonalAInterval * positiveSquare piFineInterval / RatInterval.pure 6).Contains
        (diagonalAValue * Real.pi ^ 2 / 6) :=
    contains_div_of_pos (by norm_num [RatInterval.pure])
      (contains_mul diagonalAInterval_contains hpiSq) hsix
  unfold diagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') gammaInterval_contains)
        logPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

theorem diagonalCorrectionInterval_contains
    (n k : ℕ) (hk : 0 < k) :
    (diagonalCorrectionInterval n k).Contains
      (yoshidaDiagonalDyadicPairedCorrection n k) := by
  let kQ : ℚ := k
  let aQ : ℚ := 2 * kQ + 1 / 2
  have haQ : aQ ≠ 0 := by
    dsimp [aQ, kQ]
    positivity
  have hramp := diagonalRampInterval_contains n aQ (sqrtDyadicInterval k)
    haQ (sqrtDyadicInterval_contains k)
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hkI : (RatInterval.pure kQ).Contains (k : ℝ) := by
    simpa only [kQ] using contains_pure kQ
  have hkSqI : (RatInterval.pure (kQ ^ 2)).Contains ((k : ℝ) ^ 2) := by
    constructor <;> norm_num [Contains, RatInterval.pure, kQ]
  have hquot :
      ((RatInterval.pure 1 - dyadicInterval k) / RatInterval.pure kQ).Contains
        ((1 - 1 / (4 : ℝ) ^ k) / (k : ℝ)) :=
    contains_div_of_pos (by
      change 0 < kQ
      dsimp [kQ]
      exact_mod_cast hk)
      (contains_sub hone (dyadicInterval_contains k)) hkI
  have hAquot :
      (diagonalAInterval / RatInterval.pure (kQ ^ 2)).Contains
        (diagonalAValue / (k : ℝ) ^ 2) :=
    contains_div_of_pos (by
      change 0 < kQ ^ 2
      dsimp [kQ]
      positivity)
      diagonalAInterval_contains hkSqI
  have h :
      (RatInterval.pure 2 * diagonalRampInterval n aQ (sqrtDyadicInterval k) -
          (RatInterval.pure 1 - dyadicInterval k) / RatInterval.pure kQ +
        diagonalAInterval / RatInterval.pure (kQ ^ 2)).Contains
        (2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
            (2 * (k : ℝ) + 1 / 2) ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) -
          (1 - 1 / (4 : ℝ) ^ k) / (k : ℝ) +
            diagonalAValue / (k : ℝ) ^ 2) := by
    have hramp' :
        (diagonalRampInterval n aQ (sqrtDyadicInterval k)).Contains
          (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
            (2 * (k : ℝ) + 1 / 2) ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k)) := by
      convert hramp using 1
      norm_num [aQ, kQ]
    exact contains_add (contains_sub (contains_mul htwo hramp') hquot) hAquot
  unfold diagonalCorrectionInterval yoshidaDiagonalDyadicPairedCorrection
    diagonalDyadicPairedCorrection diagonalPairedCorrection
  dsimp only
  simpa only [kQ, aQ, diagonalAValue] using h

noncomputable def diagonalHeadValueAux (n : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | fuel + 1, k =>
      yoshidaDiagonalDyadicPairedCorrection n k +
        diagonalHeadValueAux n fuel (k + 1)

theorem diagonalHeadIntervalAux_contains
    (n fuel k : ℕ) (hk : 0 < k) (acc : RatInterval) (x : ℝ)
    (hx : acc.Contains x) :
    (diagonalHeadIntervalAux n fuel k acc).Contains
      (x + diagonalHeadValueAux n fuel k) := by
  induction fuel generalizing k acc x with
  | zero => simpa [diagonalHeadIntervalAux, diagonalHeadValueAux] using hx
  | succ fuel ih =>
      rw [diagonalHeadIntervalAux, diagonalHeadValueAux]
      have hacc := contains_add hx (diagonalCorrectionInterval_contains n k hk)
      have hrec := ih (k + 1) (by omega)
        (acc + diagonalCorrectionInterval n k)
        (x + yoshidaDiagonalDyadicPairedCorrection n k) hacc
      convert hrec using 1
      ring

theorem diagonalHeadValueAux_eq_sum (n fuel k : ℕ) :
    diagonalHeadValueAux n fuel k =
      ∑ j ∈ Finset.range fuel,
        yoshidaDiagonalDyadicPairedCorrection n (k + j) := by
  induction fuel generalizing k with
  | zero => simp [diagonalHeadValueAux]
  | succ fuel ih =>
      rw [diagonalHeadValueAux, Finset.sum_range_succ']
      rw [ih]
      have hshift :
          (∑ j ∈ Finset.range fuel,
              yoshidaDiagonalDyadicPairedCorrection n ((k + 1) + j)) =
            ∑ j ∈ Finset.range fuel,
              yoshidaDiagonalDyadicPairedCorrection n (k + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (yoshidaDiagonalDyadicPairedCorrection n) (by omega)
      rw [hshift]
      simp only [Nat.add_zero]
      ring

theorem diagonalHeadInterval_contains (n K : ℕ) :
    (diagonalHeadInterval n K).Contains
      (∑ j ∈ Finset.range K,
        yoshidaDiagonalDyadicPairedCorrection n (1 + j)) := by
  have hzero : (RatInterval.pure (0 : ℚ)).Contains (0 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have h := diagonalHeadIntervalAux_contains n K 1 (by norm_num)
    (RatInterval.pure 0) 0 hzero
  rw [diagonalHeadValueAux_eq_sum] at h
  simpa only [diagonalHeadInterval, zero_add] using h

/-! ## Sharp analytic tail and exact finite-head split -/

/-- The accelerated correction series is absolutely summable.  The hypotheses
identify any certified tail; the finitely many preceding terms do not affect
absolute summability. -/
theorem summable_abs_diagonalAcceleratedCorrection_of_tail
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    Summable (fun j : ℕ ↦
      |yoshidaDiagonalDyadicPairedCorrection n (j + 1)|) := by
  refine (summable_nat_add_iff (N - 1)).1 ?_
  have htail := summable_abs_yoshidaDiagonalDyadicPairedCorrection_tail
    (n := n) (N := N) hN hmode
  convert htail using 1
  funext j
  congr 2
  omega

set_option maxHeartbeats 1000000 in
/-- The sharp analytic estimate, enlarged only by the certified rational upper
endpoint for `κₙ²`, bounds the absolute value of the actual tail. -/
theorem abs_diagonalCorrectionTail_le_radius
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    |∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)| ≤
      (diagonalTailRadius n N : ℝ) := by
  have habs := summable_abs_yoshidaDiagonalDyadicPairedCorrection_tail
    (n := n) (N := N) hN hmode
  have hnorm :
      |∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)| ≤
        ∑' j : ℕ, |yoshidaDiagonalDyadicPairedCorrection n (N + j)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun j : ℕ ↦
        yoshidaDiagonalDyadicPairedCorrection n (N + j)) habs)
  have hsharp := yoshidaDiagonalDyadicPairedCorrection_abs_tail_le_sharp
    (n := n) (N := N) hN hmode
  have hkappa : yoshidaKappa n ^ 2 ≤ ((kappaSqInterval n).upper : ℝ) :=
    (kappaSqInterval_contains n).2
  have hradius :
      11 * (yoshidaKappa n ^ 2 + 1) / (10 * (N : ℝ) ^ 2) ≤
        (diagonalTailRadius n N : ℝ) := by
    change 11 * (yoshidaKappa n ^ 2 + 1) / (10 * (N : ℝ) ^ 2) ≤
      ((11 * ((kappaSqInterval n).upper + 1) /
        (10 * (N : ℚ) ^ 2) : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  exact hnorm.trans (hsharp.trans hradius)

theorem diagonalTailInterval_contains_tsum
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (diagonalTailInterval n N).Contains
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) := by
  have h := abs_diagonalCorrectionTail_le_radius hN hmode
  rw [abs_le] at h
  unfold diagonalTailInterval
  dsimp only
  norm_num only [Contains, Rat.cast_neg]
  exact h

theorem diagonalTailInterval_contains_neg_tsum
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (diagonalTailInterval n N).Contains
      (-∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) := by
  have h := abs_diagonalCorrectionTail_le_radius hN hmode
  rw [abs_le] at h
  unfold diagonalTailInterval
  dsimp only
  norm_num only [Contains, Rat.cast_neg]
  constructor <;> linarith

/-- Exact split of the accelerated correction `tsum` into the interval head
and the tail beginning at positive series index `N`. -/
theorem diagonalCorrection_head_add_tail_eq_tsum
    {n N : ℕ} (hn : n ≠ 0) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range (N - 1),
        yoshidaDiagonalDyadicPairedCorrection n (1 + j)) +
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) =
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
  have hsplit :=
    (summable_diagonalAcceleratedCorrection hn).sum_add_tsum_nat_add (N - 1)
  simp only [diagonalAcceleratedCorrection] at hsplit
  have hhead :
      (∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection n (1 + j)) =
        ∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  have htail :
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) =
        ∑' j : ℕ,
          yoshidaDiagonalDyadicPairedCorrection n (j + (N - 1) + 1) := by
    apply tsum_congr
    intro j
    congr 1
    omega
  rw [hhead, htail]
  exact hsplit

/-- The rational series interval contains the exact production diagonal
moment whenever the analytic sharp-tail hypotheses hold. -/
theorem diagonalSeriesInterval_contains
    {n N : ℕ} (hn : n ≠ 0) (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (diagonalSeriesInterval n N).Contains (yoshidaDiagonalMoment n) := by
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries hn]
  rw [← diagonalCorrection_head_add_tail_eq_tsum (N := N) hn (by omega)]
  have hbase := diagonalBaseInterval_contains_acceleratedBase n
  have hhead := diagonalHeadInterval_contains n (N - 1)
  have htail := diagonalTailInterval_contains_neg_tsum hN hmode
  unfold diagonalSeriesInterval
  have hcombine := contains_add (contains_sub hbase hhead) htail
  convert hcombine using 1
  all_goals ring

/-! ## Kernel-checkable finite-head checkpoints -/

def diagonalChunkInterval (n start len : ℕ) : RatInterval :=
  diagonalHeadIntervalAux n len start (pure 0)

theorem pure_zero_add (I : RatInterval) : pure 0 + I = I := by
  cases I with
  | mk lower upper =>
      change (⟨0 + lower, 0 + upper⟩ : RatInterval) = ⟨lower, upper⟩
      rw [zero_add, zero_add]

theorem add_pure_zero (I : RatInterval) : I + pure 0 = I := by
  cases I with
  | mk lower upper =>
      change (⟨lower + 0, upper + 0⟩ : RatInterval) = ⟨lower, upper⟩
      rw [add_zero, add_zero]

theorem interval_add_assoc (I J K : RatInterval) :
    (I + J) + K = I + (J + K) := by
  cases I with
  | mk Il Iu =>
    cases J with
    | mk Jl Ju =>
      cases K with
      | mk Kl Ku =>
        change (⟨(Il + Jl) + Kl, (Iu + Ju) + Ku⟩ : RatInterval) =
          ⟨Il + (Jl + Kl), Iu + (Ju + Ku)⟩
        rw [add_assoc, add_assoc]

theorem diagonalHeadIntervalAux_acc
    (n fuel k : ℕ) (acc : RatInterval) :
    diagonalHeadIntervalAux n fuel k acc =
      acc + diagonalHeadIntervalAux n fuel k (pure 0) := by
  induction fuel generalizing k acc with
  | zero => simp [diagonalHeadIntervalAux, add_pure_zero]
  | succ fuel ih =>
      simp only [diagonalHeadIntervalAux]
      rw [ih (k := k + 1) (acc := acc + diagonalCorrectionInterval n k)]
      rw [ih (k := k + 1)
        (acc := pure 0 + diagonalCorrectionInterval n k)]
      rw [pure_zero_add, interval_add_assoc]

theorem diagonalHeadIntervalAux_add
    (n a b k : ℕ) (acc : RatInterval) :
    diagonalHeadIntervalAux n (a + b) k acc =
      diagonalHeadIntervalAux n b (k + a)
        (diagonalHeadIntervalAux n a k acc) := by
  induction a generalizing k acc with
  | zero => simp [diagonalHeadIntervalAux]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [diagonalHeadIntervalAux]
      rw [ih]
      congr 1
      omega

def fullChunkedHead (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | chunks + 1 =>
      fullChunkedHead n chunks +
        diagonalChunkInterval n (1 + 256 * chunks) 256

theorem fullChunkedHead_eq (n chunks : ℕ) :
    fullChunkedHead n chunks =
      diagonalHeadIntervalAux n (256 * chunks) 1 (pure 0) := by
  induction chunks with
  | zero => rfl
  | succ chunks ih =>
      rw [fullChunkedHead, ih]
      rw [show 256 * (chunks + 1) = 256 * chunks + 256 by omega]
      rw [diagonalHeadIntervalAux_add]
      rw [diagonalHeadIntervalAux_acc n 256 (1 + 256 * chunks)
        (diagonalHeadIntervalAux n (256 * chunks) 1 (pure 0))]
      simp only [diagonalChunkInterval]

def scheduledChunkLength (total i : ℕ) : ℕ :=
  if i + 1 = total then 255 else 256

def scheduledChunkInterval (n total i : ℕ) : RatInterval :=
  diagonalChunkInterval n (1 + 256 * i) (scheduledChunkLength total i)

def exactCheckpointHead (n total : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | used + 1 =>
      exactCheckpointHead n total used + scheduledChunkInterval n total used

def coarseCheckpointHead (box : ℕ → RatInterval) : ℕ → RatInterval
  | 0 => pure 0
  | used + 1 => coarseCheckpointHead box used + box used

theorem exactCheckpointHead_eq_full_of_lt
    (n total used : ℕ) (hused : used < total) :
    exactCheckpointHead n total used = fullChunkedHead n used := by
  induction used with
  | zero => rfl
  | succ used ih =>
      rw [exactCheckpointHead, fullChunkedHead]
      rw [ih (by omega)]
      unfold scheduledChunkInterval scheduledChunkLength
      rw [if_neg (by omega)]

theorem exactCheckpointHead_eq_diagonalHead
    (n chunks : ℕ) (hchunks : 0 < chunks) :
    exactCheckpointHead n chunks chunks =
      diagonalHeadInterval n (256 * chunks - 1) := by
  cases chunks with
  | zero => omega
  | succ chunks =>
    rw [exactCheckpointHead]
    rw [exactCheckpointHead_eq_full_of_lt n (chunks + 1) chunks (by omega)]
    rw [fullChunkedHead_eq]
    rw [diagonalHeadInterval,
      show 256 * (chunks + 1) - 1 = 256 * chunks + 255 by omega]
    rw [diagonalHeadIntervalAux_add]
    rw [diagonalHeadIntervalAux_acc n 255 (1 + 256 * chunks)
      (diagonalHeadIntervalAux n (256 * chunks) 1 (pure 0))]
    simp only [scheduledChunkInterval, scheduledChunkLength,
      diagonalChunkInterval, if_true]

theorem isSubinterval_refl (I : RatInterval) : IsSubinterval I I :=
  ⟨le_rfl, le_rfl⟩

theorem isSubinterval_trans
    {I J K : RatInterval} (hIJ : IsSubinterval I J)
    (hJK : IsSubinterval J K) : IsSubinterval I K :=
  ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩

theorem isSubinterval_add
    {I I' J J' : RatInterval}
    (hI : IsSubinterval I I') (hJ : IsSubinterval J J') :
    IsSubinterval (I + J) (I' + J') := by
  change I'.lower + J'.lower ≤ I.lower + J.lower ∧
    I.upper + J.upper ≤ I'.upper + J'.upper
  exact ⟨add_le_add hI.1 hJ.1, add_le_add hI.2 hJ.2⟩

theorem isSubinterval_sub_right
    (I : RatInterval) {J J' : RatInterval}
    (hJ : IsSubinterval J J') :
    IsSubinterval (I - J) (I - J') := by
  change I.lower - J'.upper ≤ I.lower - J.upper ∧
    I.upper - J.lower ≤ I.upper - J'.lower
  exact ⟨sub_le_sub_left hJ.2 _, sub_le_sub_left hJ.1 _⟩

theorem checkpointHead_subinterval
    (n chunks : ℕ) (box : ℕ → RatInterval)
    (hcert : ∀ i, i < chunks →
      IsSubinterval (scheduledChunkInterval n chunks i) (box i)) :
    IsSubinterval (exactCheckpointHead n chunks chunks)
      (coarseCheckpointHead box chunks) := by
  have hprefix : ∀ used, used ≤ chunks →
      IsSubinterval (exactCheckpointHead n chunks used)
        (coarseCheckpointHead box used) := by
    intro used hused
    induction used with
    | zero => exact isSubinterval_refl _
    | succ used ih =>
        rw [exactCheckpointHead, coarseCheckpointHead]
        exact isSubinterval_add (ih (by omega)) (hcert used (by omega))
  exact hprefix chunks le_rfl

def coarseSeriesInterval
    (n N : ℕ) (coarseHead : RatInterval) : RatInterval :=
  diagonalBaseInterval n - coarseHead + diagonalTailInterval n N

theorem diagonalSeriesInterval_sub_coarse
    {n N : ℕ} {coarseHead : RatInterval}
    (hhead : IsSubinterval (diagonalHeadInterval n (N - 1)) coarseHead) :
    IsSubinterval (diagonalSeriesInterval n N)
      (coarseSeriesInterval n N coarseHead) := by
  exact isSubinterval_add
    (isSubinterval_sub_right (diagonalBaseInterval n) hhead)
    (isSubinterval_refl _)

/-! The following one-millionth-wide boxes are proof-producing checkpoints for
the exact 256-term interval blocks (the final block has 255 terms). -/

def mode1ChunkBox : ℕ → RatInterval
  | 0 => ⟨-246172 / 1000000, -246171 / 1000000⟩
  | 1 => ⟨-114 / 1000000, -113 / 1000000⟩
  | 2 => ⟨-22 / 1000000, -21 / 1000000⟩
  | 3 => ⟨-8 / 1000000, -7 / 1000000⟩
  | _ => pure 0

def mode2ChunkBox : ℕ → RatInterval
  | 0 => ⟨-906849 / 1000000, -906848 / 1000000⟩
  | 1 => ⟨-462 / 1000000, -461 / 1000000⟩
  | 2 => ⟨-86 / 1000000, -85 / 1000000⟩
  | 3 => ⟨-31 / 1000000, -30 / 1000000⟩
  | _ => pure 0

def mode3ChunkBox : ℕ → RatInterval
  | 0 => ⟨-1305292 / 1000000, -1305291 / 1000000⟩
  | 1 => ⟨-1040 / 1000000, -1039 / 1000000⟩
  | 2 => ⟨-194 / 1000000, -193 / 1000000⟩
  | 3 => ⟨-68 / 1000000, -67 / 1000000⟩
  | _ => pure 0

def mode4ChunkBox : ℕ → RatInterval
  | 0 => ⟨-1589676 / 1000000, -1589675 / 1000000⟩
  | 1 => ⟨-1848 / 1000000, -1847 / 1000000⟩
  | 2 => ⟨-345 / 1000000, -344 / 1000000⟩
  | 3 => ⟨-122 / 1000000, -121 / 1000000⟩
  | 4 => ⟨-57 / 1000000, -56 / 1000000⟩
  | 5 => ⟨-31 / 1000000, -30 / 1000000⟩
  | 6 => ⟨-19 / 1000000, -18 / 1000000⟩
  | 7 => ⟨-12 / 1000000, -11 / 1000000⟩
  | _ => pure 0

def mode5ChunkBox : ℕ → RatInterval
  | 0 => ⟨-1810402 / 1000000, -1810401 / 1000000⟩
  | 1 => ⟨-2884 / 1000000, -2883 / 1000000⟩
  | 2 => ⟨-540 / 1000000, -539 / 1000000⟩
  | 3 => ⟨-190 / 1000000, -189 / 1000000⟩
  | 4 => ⟨-88 / 1000000, -87 / 1000000⟩
  | 5 => ⟨-48 / 1000000, -47 / 1000000⟩
  | 6 => ⟨-29 / 1000000, -28 / 1000000⟩
  | 7 => ⟨-19 / 1000000, -18 / 1000000⟩
  | _ => pure 0

def mode6ChunkBox : ℕ → RatInterval
  | 0 => ⟨-1990473 / 1000000, -1990472 / 1000000⟩
  | 1 => ⟨-4144 / 1000000, -4143 / 1000000⟩
  | 2 => ⟨-776 / 1000000, -775 / 1000000⟩
  | 3 => ⟨-273 / 1000000, -272 / 1000000⟩
  | 4 => ⟨-127 / 1000000, -126 / 1000000⟩
  | 5 => ⟨-69 / 1000000, -68 / 1000000⟩
  | 6 => ⟨-42 / 1000000, -41 / 1000000⟩
  | 7 => ⟨-27 / 1000000, -26 / 1000000⟩
  | _ => pure 0

def mode7ChunkBox : ℕ → RatInterval
  | 0 => ⟨-2142296 / 1000000, -2142295 / 1000000⟩
  | 1 => ⟨-5628 / 1000000, -5627 / 1000000⟩
  | 2 => ⟨-1056 / 1000000, -1055 / 1000000⟩
  | 3 => ⟨-371 / 1000000, -370 / 1000000⟩
  | 4 => ⟨-172 / 1000000, -171 / 1000000⟩
  | 5 => ⟨-94 / 1000000, -93 / 1000000⟩
  | 6 => ⟨-57 / 1000000, -56 / 1000000⟩
  | 7 => ⟨-37 / 1000000, -36 / 1000000⟩
  | _ => pure 0

def mode8ChunkBox : ℕ → RatInterval
  | 0 => ⟨-2273322 / 1000000, -2273321 / 1000000⟩
  | 1 => ⟨-7330 / 1000000, -7329 / 1000000⟩
  | 2 => ⟨-1378 / 1000000, -1377 / 1000000⟩
  | 3 => ⟨-485 / 1000000, -484 / 1000000⟩
  | 4 => ⟨-225 / 1000000, -224 / 1000000⟩
  | 5 => ⟨-123 / 1000000, -122 / 1000000⟩
  | 6 => ⟨-74 / 1000000, -73 / 1000000⟩
  | 7 => ⟨-48 / 1000000, -47 / 1000000⟩
  | 8 => ⟨-33 / 1000000, -32 / 1000000⟩
  | 9 => ⟨-24 / 1000000, -23 / 1000000⟩
  | 10 => ⟨-18 / 1000000, -17 / 1000000⟩
  | 11 => ⟨-14 / 1000000, -13 / 1000000⟩
  | 12 => ⟨-11 / 1000000, -10 / 1000000⟩
  | 13 => ⟨-9 / 1000000, -8 / 1000000⟩
  | 14 => ⟨-7 / 1000000, -6 / 1000000⟩
  | 15 => ⟨-6 / 1000000, -5 / 1000000⟩
  | _ => pure 0

def mode9ChunkBox : ℕ → RatInterval
  | 0 => ⟨-2388378 / 1000000, -2388377 / 1000000⟩
  | 1 => ⟨-9247 / 1000000, -9246 / 1000000⟩
  | 2 => ⟨-1742 / 1000000, -1741 / 1000000⟩
  | 3 => ⟨-613 / 1000000, -612 / 1000000⟩
  | 4 => ⟨-285 / 1000000, -284 / 1000000⟩
  | 5 => ⟨-155 / 1000000, -154 / 1000000⟩
  | 6 => ⟨-94 / 1000000, -93 / 1000000⟩
  | 7 => ⟨-61 / 1000000, -60 / 1000000⟩
  | 8 => ⟨-42 / 1000000, -41 / 1000000⟩
  | 9 => ⟨-30 / 1000000, -29 / 1000000⟩
  | 10 => ⟨-22 / 1000000, -21 / 1000000⟩
  | 11 => ⟨-17 / 1000000, -16 / 1000000⟩
  | 12 => ⟨-14 / 1000000, -13 / 1000000⟩
  | 13 => ⟨-11 / 1000000, -10 / 1000000⟩
  | 14 => ⟨-9 / 1000000, -8 / 1000000⟩
  | 15 => ⟨-7 / 1000000, -6 / 1000000⟩
  | _ => pure 0

def mode10ChunkBox : ℕ → RatInterval
  | 0 => ⟨-2490767 / 1000000, -2490766 / 1000000⟩
  | 1 => ⟨-11376 / 1000000, -11375 / 1000000⟩
  | 2 => ⟨-2149 / 1000000, -2148 / 1000000⟩
  | 3 => ⟨-756 / 1000000, -755 / 1000000⟩
  | 4 => ⟨-351 / 1000000, -350 / 1000000⟩
  | 5 => ⟨-191 / 1000000, -190 / 1000000⟩
  | 6 => ⟨-116 / 1000000, -115 / 1000000⟩
  | 7 => ⟨-75 / 1000000, -74 / 1000000⟩
  | 8 => ⟨-52 / 1000000, -51 / 1000000⟩
  | 9 => ⟨-37 / 1000000, -36 / 1000000⟩
  | 10 => ⟨-28 / 1000000, -27 / 1000000⟩
  | 11 => ⟨-21 / 1000000, -20 / 1000000⟩
  | 12 => ⟨-17 / 1000000, -16 / 1000000⟩
  | 13 => ⟨-13 / 1000000, -12 / 1000000⟩
  | 14 => ⟨-11 / 1000000, -10 / 1000000⟩
  | 15 => ⟨-9 / 1000000, -8 / 1000000⟩
  | _ => pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode1Chunk_kernel_certificate
    {i : ℕ} (hi : i < 4) :
    IsSubinterval (scheduledChunkInterval 1 4 i) (mode1ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode2Chunk_kernel_certificate
    {i : ℕ} (hi : i < 4) :
    IsSubinterval (scheduledChunkInterval 2 4 i) (mode2ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode3Chunk_kernel_certificate
    {i : ℕ} (hi : i < 4) :
    IsSubinterval (scheduledChunkInterval 3 4 i) (mode3ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode4Chunk_kernel_certificate
    {i : ℕ} (hi : i < 8) :
    IsSubinterval (scheduledChunkInterval 4 8 i) (mode4ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode5Chunk_kernel_certificate
    {i : ℕ} (hi : i < 8) :
    IsSubinterval (scheduledChunkInterval 5 8 i) (mode5ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode6Chunk_kernel_certificate
    {i : ℕ} (hi : i < 8) :
    IsSubinterval (scheduledChunkInterval 6 8 i) (mode6ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode7Chunk_kernel_certificate
    {i : ℕ} (hi : i < 8) :
    IsSubinterval (scheduledChunkInterval 7 8 i) (mode7ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode8Chunk_kernel_certificate
    {i : ℕ} (hi : i < 16) :
    IsSubinterval (scheduledChunkInterval 8 16 i) (mode8ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode9Chunk_kernel_certificate
    {i : ℕ} (hi : i < 16) :
    IsSubinterval (scheduledChunkInterval 9 16 i) (mode9ChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mode10Chunk_kernel_certificate
    {i : ℕ} (hi : i < 16) :
    IsSubinterval (scheduledChunkInterval 10 16 i) (mode10ChunkBox i) := by
  interval_cases i <;> decide +kernel

theorem diagonalHeadInterval_sub_coarseCheckpoint
    (n chunks : ℕ) (hchunks : 0 < chunks) (box : ℕ → RatInterval)
    (hcert : ∀ i, i < chunks →
      IsSubinterval (scheduledChunkInterval n chunks i) (box i)) :
    IsSubinterval (diagonalHeadInterval n (256 * chunks - 1))
      (coarseCheckpointHead box chunks) := by
  have h := checkpointHead_subinterval n chunks box hcert
  rw [exactCheckpointHead_eq_diagonalHead n chunks hchunks] at h
  exact h

theorem diagonalSeriesInterval_sub_target_of_checkpoints
    (n chunks : ℕ) (hchunks : 0 < chunks)
    (box : ℕ → RatInterval) (target : RatInterval)
    (hcert : ∀ i, i < chunks →
      IsSubinterval (scheduledChunkInterval n chunks i) (box i))
    (hcoarse : IsSubinterval
      (coarseSeriesInterval n (256 * chunks)
        (coarseCheckpointHead box chunks)) target) :
    IsSubinterval (diagonalSeriesInterval n (256 * chunks)) target := by
  apply isSubinterval_trans
    (diagonalSeriesInterval_sub_coarse
      (diagonalHeadInterval_sub_coarseCheckpoint n chunks hchunks box hcert))
  exact hcoarse

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode1CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 1 1024 (coarseCheckpointHead mode1ChunkBox 4))
      (yoshidaOddDiagonalIntervals 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode2CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 2 1024 (coarseCheckpointHead mode2ChunkBox 4))
      (yoshidaOddDiagonalIntervals 2) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode3CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 3 1024 (coarseCheckpointHead mode3ChunkBox 4))
      (yoshidaOddDiagonalIntervals 3) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode4CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 4 2048 (coarseCheckpointHead mode4ChunkBox 8))
      (yoshidaOddDiagonalIntervals 4) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode5CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 5 2048 (coarseCheckpointHead mode5ChunkBox 8))
      (yoshidaOddDiagonalIntervals 5) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode6CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 6 2048 (coarseCheckpointHead mode6ChunkBox 8))
      (yoshidaOddDiagonalIntervals 6) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode7CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 7 2048 (coarseCheckpointHead mode7ChunkBox 8))
      (yoshidaOddDiagonalIntervals 7) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode8CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 8 4096 (coarseCheckpointHead mode8ChunkBox 16))
      (yoshidaOddDiagonalIntervals 8) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode9CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 9 4096 (coarseCheckpointHead mode9ChunkBox 16))
      (yoshidaOddDiagonalIntervals 9) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem mode10CoarseSeries_kernel_certificate :
    IsSubinterval
      (coarseSeriesInterval 10 4096 (coarseCheckpointHead mode10ChunkBox 16))
      (yoshidaOddDiagonalIntervals 10) := by
  decide +kernel

theorem mode1_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 1 1024)
      (yoshidaOddDiagonalIntervals 1) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    1 4 (by norm_num) mode1ChunkBox (yoshidaOddDiagonalIntervals 1)
    (fun _ hi ↦ mode1Chunk_kernel_certificate hi)
    mode1CoarseSeries_kernel_certificate

theorem mode2_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 2 1024)
      (yoshidaOddDiagonalIntervals 2) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    2 4 (by norm_num) mode2ChunkBox (yoshidaOddDiagonalIntervals 2)
    (fun _ hi ↦ mode2Chunk_kernel_certificate hi)
    mode2CoarseSeries_kernel_certificate

theorem mode3_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 3 1024)
      (yoshidaOddDiagonalIntervals 3) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    3 4 (by norm_num) mode3ChunkBox (yoshidaOddDiagonalIntervals 3)
    (fun _ hi ↦ mode3Chunk_kernel_certificate hi)
    mode3CoarseSeries_kernel_certificate

theorem mode4_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 4 2048)
      (yoshidaOddDiagonalIntervals 4) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    4 8 (by norm_num) mode4ChunkBox (yoshidaOddDiagonalIntervals 4)
    (fun _ hi ↦ mode4Chunk_kernel_certificate hi)
    mode4CoarseSeries_kernel_certificate

theorem mode5_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 5 2048)
      (yoshidaOddDiagonalIntervals 5) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    5 8 (by norm_num) mode5ChunkBox (yoshidaOddDiagonalIntervals 5)
    (fun _ hi ↦ mode5Chunk_kernel_certificate hi)
    mode5CoarseSeries_kernel_certificate

theorem mode6_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 6 2048)
      (yoshidaOddDiagonalIntervals 6) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    6 8 (by norm_num) mode6ChunkBox (yoshidaOddDiagonalIntervals 6)
    (fun _ hi ↦ mode6Chunk_kernel_certificate hi)
    mode6CoarseSeries_kernel_certificate

theorem mode7_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 7 2048)
      (yoshidaOddDiagonalIntervals 7) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    7 8 (by norm_num) mode7ChunkBox (yoshidaOddDiagonalIntervals 7)
    (fun _ hi ↦ mode7Chunk_kernel_certificate hi)
    mode7CoarseSeries_kernel_certificate

theorem mode8_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 8 4096)
      (yoshidaOddDiagonalIntervals 8) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    8 16 (by norm_num) mode8ChunkBox (yoshidaOddDiagonalIntervals 8)
    (fun _ hi ↦ mode8Chunk_kernel_certificate hi)
    mode8CoarseSeries_kernel_certificate

theorem mode9_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 9 4096)
      (yoshidaOddDiagonalIntervals 9) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    9 16 (by norm_num) mode9ChunkBox (yoshidaOddDiagonalIntervals 9)
    (fun _ hi ↦ mode9Chunk_kernel_certificate hi)
    mode9CoarseSeries_kernel_certificate

theorem mode10_diagonal_certificate :
    IsSubinterval (diagonalSeriesInterval 10 4096)
      (yoshidaOddDiagonalIntervals 10) := by
  simpa using diagonalSeriesInterval_sub_target_of_checkpoints
    10 16 (by norm_num) mode10ChunkBox (yoshidaOddDiagonalIntervals 10)
    (fun _ hi ↦ mode10Chunk_kernel_certificate hi)
    mode10CoarseSeries_kernel_certificate

theorem diagonalCertifiedInterval_sub_target
    {n : ℕ} (hn : 1 ≤ n) (hn10 : n ≤ 10) :
    IsSubinterval (diagonalCertifiedInterval n)
      (yoshidaOddDiagonalIntervals n) := by
  interval_cases n
  · exact mode1_diagonal_certificate
  · exact mode2_diagonal_certificate
  · exact mode3_diagonal_certificate
  · exact mode4_diagonal_certificate
  · exact mode5_diagonal_certificate
  · exact mode6_diagonal_certificate
  · exact mode7_diagonal_certificate
  · exact mode8_diagonal_certificate
  · exact mode9_diagonal_certificate
  · exact mode10_diagonal_certificate

theorem diagonalCutoff_ge_sixteen
    {n : ℕ} (hn : 1 ≤ n) (hn10 : n ≤ 10) :
    16 ≤ diagonalCutoff n := by
  interval_cases n <;> norm_num [diagonalCutoff]

theorem ten_mul_mode_le_diagonalCutoff
    {n : ℕ} (hn : 1 ≤ n) (hn10 : n ≤ 10) :
    10 * n ≤ diagonalCutoff n := by
  interval_cases n <;> norm_num [diagonalCutoff]

/-- Zero-hypothesis production package: each of the ten target boxes follows
from the exact accelerated identity, analytic sharp tail, and kernel-checked
finite checkpoint certificates above. -/
theorem diagonalTargetEnclosures_from_certificate :
    YoshidaOddDiagonalTargetEnclosures := by
  intro n hn hn10
  exact contains_of_subinterval (diagonalCertifiedInterval_sub_target hn hn10)
    (diagonalSeriesInterval_contains (by omega)
      (diagonalCutoff_ge_sixteen hn hn10)
      (ten_mul_mode_le_diagonalCutoff hn hn10))

end

end ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
