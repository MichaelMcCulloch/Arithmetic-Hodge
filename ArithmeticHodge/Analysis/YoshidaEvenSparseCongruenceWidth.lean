import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceCheckDefs

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

noncomputable section

open RatInterval
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets
open YoshidaEvenSparseCongruenceData

private structure IntervalMetrics (I : RatInterval) (B W : ℚ) : Prop where
  valid : I.Valid
  absBound : I.AbsBound B
  width_le : width I ≤ W
  bound_nonneg : 0 ≤ B
  width_nonneg : 0 ≤ W

private theorem metrics_pure {q B : ℚ} (hq : |q| ≤ B) (hB : 0 ≤ B) :
    IntervalMetrics (pure q) B 0 := by
  exact ⟨valid_pure q, absBound_pure hq, by rw [width_pure], hB, le_rfl⟩

private theorem metrics_mul
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : IntervalMetrics I BI WI) (hJ : IntervalMetrics J BJ WJ) :
    IntervalMetrics (I * J) (BI * BJ) (BJ * WI + BI * WJ) := by
  refine ⟨valid_mul hI.valid hJ.valid,
    absBound_mul hI.valid hJ.valid hI.absBound hJ.absBound
      hI.bound_nonneg hJ.bound_nonneg, ?_,
    mul_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg (mul_nonneg hJ.bound_nonneg hI.width_nonneg)
      (mul_nonneg hI.bound_nonneg hJ.width_nonneg)⟩
  calc
    width (I * J) ≤ BJ * width I + BI * width J :=
      width_mul_le hI.valid hJ.valid hI.absBound hJ.absBound
        hI.bound_nonneg hJ.bound_nonneg
    _ ≤ BJ * WI + BI * WJ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hI.width_le hJ.bound_nonneg)
        (mul_le_mul_of_nonneg_left hJ.width_le hI.bound_nonneg)

private theorem metrics_sub
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : IntervalMetrics I BI WI) (hJ : IntervalMetrics J BJ WJ) :
    IntervalMetrics (I - J) (BI + BJ) (WI + WJ) := by
  refine ⟨valid_sub hI.valid hJ.valid,
    absBound_sub hI.absBound hJ.absBound, ?_,
    add_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg hI.width_nonneg hJ.width_nonneg⟩
  rw [width_sub]
  exact add_le_add hI.width_le hJ.width_le

private abbrev SineTargetMetricProp (n : ℕ) : Prop :=
  (yoshidaEvenSineTargets n).lower ≤ (yoshidaEvenSineTargets n).upper ∧
    -(8 / 5 : ℚ) ≤ (yoshidaEvenSineTargets n).lower ∧
    (yoshidaEvenSineTargets n).upper ≤ (8 / 5 : ℚ) ∧
    (yoshidaEvenSineTargets n).upper -
      (yoshidaEvenSineTargets n).lower ≤ (1 / 100000 : ℚ)

private abbrev DiagonalTargetMetricProp (n : ℕ) : Prop :=
  (yoshidaEvenDiagonalTargets n).lower ≤
      (yoshidaEvenDiagonalTargets n).upper ∧
    -(6 : ℚ) ≤ (yoshidaEvenDiagonalTargets n).lower ∧
    (yoshidaEvenDiagonalTargets n).upper ≤ (6 : ℚ) ∧
    (yoshidaEvenDiagonalTargets n).upper -
      (yoshidaEvenDiagonalTargets n).lower ≤ (1 / 100000 : ℚ)

private def evenTargetIndices : List YoshidaEvenIndex := List.ofFn id

set_option maxHeartbeats 2000000 in
private theorem sineTarget_metric_fin
    (i : YoshidaEvenIndex) (hi : i.1 ≠ 0) :
    SineTargetMetricProp i.1 := by
  have hcheck : evenTargetIndices.all
      (fun k ↦ decide (k.1 ≠ 0 → SineTargetMetricProp k.1)) = true := by
    decide +kernel
  have hiMem : i ∈ evenTargetIndices := by
    rw [evenTargetIndices, List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact (of_decide_eq_true ((List.all_eq_true.mp hcheck) i hiMem)) hi

set_option maxHeartbeats 2000000 in
private theorem diagonalTarget_metric_fin
    (i : YoshidaEvenIndex) : DiagonalTargetMetricProp i.1 := by
  have hcheck : evenTargetIndices.all
      (fun k ↦ decide (DiagonalTargetMetricProp k.1)) = true := by
    decide +kernel
  have hiMem : i ∈ evenTargetIndices := by
    rw [evenTargetIndices, List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) i hiMem)

private theorem sineTarget_metrics
    {n : ℕ} (hn : 1 ≤ n) (hn199 : n ≤ 199) :
    IntervalMetrics (yoshidaEvenSineTargets n) (8 / 5) (1 / 100000) := by
  let i : YoshidaEvenIndex := ⟨n, by omega⟩
  have hi : i.1 ≠ 0 := by
    dsimp only [i]
    omega
  have h := sineTarget_metric_fin i hi
  change SineTargetMetricProp n at h
  rcases h with ⟨hvalid, hlower, hupper, hwidth⟩
  exact ⟨hvalid, ⟨hlower, hupper⟩, hwidth, by norm_num, by norm_num⟩

private theorem diagonalTarget_metrics
    {n : ℕ} (hn199 : n ≤ 199) :
    IntervalMetrics (yoshidaEvenDiagonalTargets n) 6 (1 / 100000) := by
  let i : YoshidaEvenIndex := ⟨n, by omega⟩
  have h := diagonalTarget_metric_fin i
  change DiagonalTargetMetricProp n at h
  rcases h with ⟨hvalid, hlower, hupper, hwidth⟩
  exact ⟨hvalid, ⟨hlower, hupper⟩, hwidth, by norm_num, by norm_num⟩

private theorem invPi_metrics :
    IntervalMetrics evenInvPiInterval (1 / 3) (1 / 98000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
  norm_num [evenInvPiInterval, RatInterval.Valid,
    RatInterval.AbsBound, RatInterval.width]

private theorem invSqrtTwo_metrics :
    IntervalMetrics evenInvSqrtTwoInterval (3 / 4) (1 / 200000) := by
  change IntervalMetrics (RatInterval.inv evenSqrtTwoInterval)
    (3 / 4) (1 / 200000)
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
  norm_num [evenSqrtTwoInterval,
    RatInterval.inv, RatInterval.Valid, RatInterval.AbsBound, RatInterval.width]

private theorem abs_evenZeroCoeffQ_le_one
    {m : ℕ} (hm : 1 ≤ m) :
    |evenZeroCoeffQ m| ≤ 1 := by
  unfold evenZeroCoeffQ
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ m)]
  apply (div_le_one (by positivity : (0 : ℚ) < m)).2
  exact_mod_cast hm

private theorem abs_evenDiagonalCoeffQ_le_half
    {n : ℕ} (hn : 1 ≤ n) :
    |evenDiagonalCoeffQ n| ≤ 1 / 2 := by
  unfold evenDiagonalCoeffQ
  rw [abs_div, abs_one, abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2 * n)]
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 2 * n)
    (by norm_num : (0 : ℚ) < 2)).2
  norm_num
  exact_mod_cast hn

private theorem abs_natCast_sub_natCast_ge_one
    {n m : ℕ} (hnm : n ≠ m) :
    (1 : ℚ) ≤ |(n : ℚ) - (m : ℚ)| := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hcast : (n : ℚ) ≤ m := by exact_mod_cast Nat.le_of_lt hlt
    rw [abs_of_nonpos (sub_nonpos.mpr hcast)]
    have hsucc : n + 1 ≤ m := by omega
    have hsuccQ : (n : ℚ) + 1 ≤ m := by exact_mod_cast hsucc
    linarith
  · have hcast : (m : ℚ) ≤ n := by exact_mod_cast Nat.le_of_lt hgt
    rw [abs_of_nonneg (sub_nonneg.mpr hcast)]
    have hsucc : m + 1 ≤ n := by omega
    have hsuccQ : (m : ℚ) + 1 ≤ n := by exact_mod_cast hsucc
    linarith

private theorem abs_evenOffDiagonalCoeffQ_le
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    |evenOffDiagonalCoeffQ n m| ≤ 1 / ((n : ℚ) + m) := by
  have hsum : (0 : ℚ) < (n : ℚ) + m := by positivity
  have hdiff := abs_natCast_sub_natCast_ge_one hnm
  have hfactor :
      |(n : ℚ) ^ 2 - (m : ℚ) ^ 2| =
        |(n : ℚ) - m| * ((n : ℚ) + m) := by
    rw [show (n : ℚ) ^ 2 - (m : ℚ) ^ 2 =
      ((n : ℚ) - m) * ((n : ℚ) + m) by ring, abs_mul,
      abs_of_nonneg hsum.le]
  unfold evenOffDiagonalCoeffQ
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, hfactor]
  apply one_div_le_one_div_of_le hsum
  simpa using (mul_le_mul_of_nonneg_right hdiff hsum.le)

private theorem natCast_metrics (n : ℕ) :
    IntervalMetrics (pure (n : ℚ)) (n : ℚ) 0 := by
  apply metrics_pure
  · rw [abs_of_nonneg (by positivity)]
  · positivity

private theorem evenMomentIntervalGram_width_le
    (i j : YoshidaEvenIndex) :
    width (evenMomentIntervalGram yoshidaEvenSineTargets
      yoshidaEvenDiagonalTargets i j) ≤ 1 / 50000 := by
  have hi199 : i.1 ≤ 199 := by omega
  have hj199 : j.1 ≤ 199 := by omega
  by_cases hi : i.1 = 0
  · by_cases hj : j.1 = 0
    · have hD := diagonalTarget_metrics hi199
      simpa [evenMomentIntervalGram, hi, hj] using
        hD.width_le.trans (by norm_num : (1 / 100000 : ℚ) ≤ 1 / 50000)
    · have hj1 : 1 ≤ j.1 := Nat.one_le_iff_ne_zero.mpr hj
      have hq := metrics_pure (abs_evenZeroCoeffQ_le_one hj1) (by norm_num)
      have hS := sineTarget_metrics hj1 hj199
      have h := metrics_mul (metrics_mul (metrics_mul hq invPi_metrics)
        invSqrtTwo_metrics) hS
      simpa [evenMomentIntervalGram, hi, hj] using
        h.width_le.trans (by norm_num :
          (8 / 5 : ℚ) * ((3 / 4) * ((1 / 3) * 0 + 1 * (1 / 98000)) +
              (1 * (1 / 3)) * (1 / 200000)) +
            ((1 * (1 / 3)) * (3 / 4)) * (1 / 100000) ≤ 1 / 50000)
  · by_cases hj : j.1 = 0
    · have hi1 : 1 ≤ i.1 := Nat.one_le_iff_ne_zero.mpr hi
      have hq := metrics_pure (abs_evenZeroCoeffQ_le_one hi1) (by norm_num)
      have hS := sineTarget_metrics hi1 hi199
      have h := metrics_mul (metrics_mul (metrics_mul hq invPi_metrics)
        invSqrtTwo_metrics) hS
      simpa [evenMomentIntervalGram, hi, hj] using
        h.width_le.trans (by norm_num :
          (8 / 5 : ℚ) * ((3 / 4) * ((1 / 3) * 0 + 1 * (1 / 98000)) +
              (1 * (1 / 3)) * (1 / 200000)) +
            ((1 * (1 / 3)) * (3 / 4)) * (1 / 100000) ≤ 1 / 50000)
    · have hi1 : 1 ≤ i.1 := Nat.one_le_iff_ne_zero.mpr hi
      have hj1 : 1 ≤ j.1 := Nat.one_le_iff_ne_zero.mpr hj
      by_cases hij : i = j
      · have hD := diagonalTarget_metrics hi199
        have hq := metrics_pure (abs_evenDiagonalCoeffQ_le_half hi1)
          (by norm_num)
        have hS := sineTarget_metrics hi1 hi199
        have hprod := metrics_mul (metrics_mul hq invPi_metrics) hS
        have h := metrics_sub hD hprod
        simpa [evenMomentIntervalGram, hi, hj, hij] using
          h.width_le.trans (by norm_num :
            (1 / 100000 : ℚ) +
              ((8 / 5) * ((1 / 3) * 0 + (1 / 2) * (1 / 98000)) +
                ((1 / 2) * (1 / 3)) * (1 / 100000)) ≤ 1 / 50000)
      · have hval : i.1 ≠ j.1 := by
          intro hval
          exact hij (Fin.ext hval)
        let s : ℚ := (i.1 : ℚ) + j.1
        have hs : 0 < s := by dsimp only [s]; positivity
        have hqabs : |evenOffDiagonalCoeffQ i.1 j.1| ≤ 1 / s := by
          simpa only [s] using abs_evenOffDiagonalCoeffQ_le hi1 hj1 hval
        have hq := metrics_pure hqabs (by positivity : (0 : ℚ) ≤ 1 / s)
        have hSi := sineTarget_metrics hi1 hi199
        have hSj := sineTarget_metrics hj1 hj199
        have hscaledJ := metrics_mul (natCast_metrics j.1) hSj
        have hscaledI := metrics_mul (natCast_metrics i.1) hSi
        have hdiff := metrics_sub hscaledJ hscaledI
        have h := metrics_mul (metrics_mul hq invPi_metrics) hdiff
        have hnumeric :
            (((j.1 : ℚ) * (8 / 5) + (i.1 : ℚ) * (8 / 5)) *
                ((1 / 3) * 0 + (1 / s) * (1 / 98000)) +
              ((1 / s) * (1 / 3)) *
                ((8 / 5) * 0 + (j.1 : ℚ) * (1 / 100000) +
                  ((8 / 5) * 0 + (i.1 : ℚ) * (1 / 100000)))) ≤
              1 / 50000 := by
          dsimp only [s] at hs ⊢
          field_simp [hs.ne']
          ring_nf
          nlinarith [hs]
        simpa [evenMomentIntervalGram, hi, hj, hij, s, add_comm] using
          h.width_le.trans hnumeric

/-- Every inflated target entry has half-width at most the sparse robust
certificate budget, without enumerating the 40,000 matrix cells. -/
theorem evenTargetRadiusBoundAt (i j : YoshidaEvenIndex) :
    EvenTargetRadiusBoundAt i j := by
  have hbase := evenMomentIntervalGram_width_le i j
  unfold EvenTargetRadiusBoundAt evenTargetHalfWidth evenTargetInterval
    inflatedEvenMomentIntervalGram inflateInterval evenSparseEpsilon
    evenCorrectionRadius
  unfold RatInterval.width at hbase
  dsimp only
  linarith

theorem evenTargetRadiusBound :
    ∀ i j : YoshidaEvenIndex, EvenTargetRadiusBoundAt i j :=
  evenTargetRadiusBoundAt

end

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
