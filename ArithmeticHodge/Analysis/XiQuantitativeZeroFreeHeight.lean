import ArithmeticHodge.Analysis.ZetaZeroCount
import ArithmeticHodge.Analysis.XiLogDerivGrowth
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Quantitatively separated xi contour heights

A finite-set packing lemma and the polynomial xi zero-count bound produce
paired heights separated from every zero ordinate by an inverse polynomial.
Combined with the separated `xi'/xi` estimate, the quadratic specialization
gives a uniform quartic logarithmic-derivative bound on fixed strips.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Metric Set Topology

namespace ArithmeticHodge.Analysis

/-- A finite set cannot cover a real interval by balls whose total diameter is
less than the interval length.  This gives a quantitative point separated from
every member of the finite set. -/
theorem exists_Ioo_dist_finset_ge
    (S : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b,
      ∀ y ∈ S,
        (b - a) / (4 * ((S.card : ℝ) + 1)) ≤ dist x y := by
  classical
  let delta : ℝ := (b - a) / (4 * ((S.card : ℝ) + 1))
  let U : Set ℝ := ⋃ y ∈ S, Metric.ball y delta
  have hden : 0 < 4 * ((S.card : ℝ) + 1) := by positivity
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hab) hden
  have hU_le : volume.real U ≤ (S.card : ℝ) * (2 * delta) := by
    calc
      volume.real U ≤ ∑ y ∈ S, volume.real (Metric.ball y delta) := by
        exact measureReal_biUnion_finset_le S (fun y => Metric.ball y delta)
      _ = (S.card : ℝ) * (2 * delta) := by
        simp [Real.volume_real_ball hdelta.le, Finset.sum_const, nsmul_eq_mul]
  have hsmall : (S.card : ℝ) * (2 * delta) < b - a := by
    have hdelta_eq : 4 * ((S.card : ℝ) + 1) * delta = b - a := by
      dsimp only [delta]
      field_simp
    have hpositive :
        0 < (2 * (S.card : ℝ) + 4) * delta := by positivity
    nlinarith
  have hnot : ¬ Set.Ioo a b ⊆ U := by
    intro hsub
    have hmono : volume.real (Set.Ioo a b) ≤ volume.real U :=
      measureReal_mono hsub (by
        apply ne_of_lt
        exact (measure_biUnion_finset_le S (fun y => Metric.ball y delta)).trans_lt
          (ENNReal.sum_lt_top.mpr fun y _hy => by
            rw [Real.volume_ball]
            exact ENNReal.ofReal_lt_top))
    rw [Real.volume_real_Ioo_of_le hab.le] at hmono
    linarith
  obtain ⟨x, hxIoo, hxU⟩ : ∃ x ∈ Set.Ioo a b, x ∉ U := by
    simpa only [Set.not_subset] using hnot
  refine ⟨x, hxIoo, ?_⟩
  intro y hy
  have hnotball : x ∉ Metric.ball y delta := by
    intro hxball
    apply hxU
    exact Set.mem_iUnion_of_mem y (Set.mem_iUnion_of_mem hy hxball)
  simpa only [Metric.mem_ball, not_lt, dist_comm] using hnotball

/-- The number of distinct absolute ordinates in a critical-strip rectangle
is bounded by the multiplicity-weighted xi zero count. -/
theorem card_xiZero_absIm_image_le_xiZeroCount (T : ℝ) :
    ((xiZerosInRectangle 0 1 (-T) T).image (fun rho => |rho.im|)).card ≤
      xiZeroCount 0 1 (-T) T := by
  classical
  calc
    ((xiZerosInRectangle 0 1 (-T) T).image
        (fun rho => |rho.im|)).card ≤
        (xiZerosInRectangle 0 1 (-T) T).card := Finset.card_image_le
    _ = ∑ rho ∈ xiZerosInRectangle 0 1 (-T) T, 1 := by simp
    _ ≤ ∑ rho ∈ xiZerosInRectangle 0 1 (-T) T,
        xiZeroMultiplicity rho := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact (xiZeroMultiplicity_pos_iff rho).mpr
        ((mem_xiZerosInRectangle_iff 0 1 (-T) T rho).mp hrho).2
    _ = xiZeroCount 0 1 (-T) T :=
      (xiZeroCount_eq_sum 0 1 (-T) T).symm

/-- For every exponent larger than one, there are paired contour heights in
successive unit intervals whose distance from every xi-zero ordinate has an
eventual uniform lower bound of order `(n+2)^(-alpha)`. -/
theorem exists_quantitatively_separated_xi_height_sequence
    (alpha : ℝ) (halpha : 1 < alpha) :
    ∃ (c : ℝ) (N : ℕ) (T : ℕ → ℝ),
      0 < c ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ, (n : ℝ) < T n ∧ T n < (n : ℝ) + 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ rho : ℂ, xiFunction rho = 0 →
        c * ((n : ℝ) + 2) ^ (-alpha) ≤ abs (T n - |rho.im|) ∧
        c * ((n : ℝ) + 2) ^ (-alpha) ≤ |T n - rho.im| ∧
        c * ((n : ℝ) + 2) ^ (-alpha) ≤ |-T n - rho.im| := by
  classical
  obtain ⟨C, Rzero, hC, hRzero, hcount⟩ :=
    xiCriticalStripZeroCount_eventually_le_rpow alpha halpha
  obtain ⟨N, hN⟩ := exists_nat_ge Rzero
  let Z : ℕ → Finset ℂ := fun n =>
    xiZerosInRectangle 0 1 (-((n : ℝ) + 2)) ((n : ℝ) + 2)
  let S : ℕ → Finset ℝ := fun n => (Z n).image (fun rho => |rho.im|)
  let delta : ℕ → ℝ := fun n =>
    1 / (4 * (((S n).card : ℝ) + 1))
  have hchoice (n : ℕ) :
      ∃ t ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
        ∀ y ∈ S n, delta n ≤ dist t y := by
    simpa [delta] using
      (exists_Ioo_dist_finset_ge (S n)
        (a := (n : ℝ)) (b := (n : ℝ) + 1) (by linarith))
  let T : ℕ → ℝ := fun n => Classical.choose (hchoice n)
  have hT (n : ℕ) :
      T n ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1) ∧
        ∀ y ∈ S n, delta n ≤ dist (T n) y :=
    Classical.choose_spec (hchoice n)
  let c : ℝ := 1 / (4 * (C + 1))
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hT_tendsto : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun n => (hT n).1.1.le)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨c, N, T, hc, hT_tendsto,
    (fun n => ⟨(hT n).1.1, (hT n).1.2⟩), ?_⟩
  intro n hn rho hrho
  have hheight_pos : 0 < (n : ℝ) + 2 := by positivity
  have hheight_one : 1 ≤ (n : ℝ) + 2 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have hR : Rzero ≤ (n : ℝ) + 2 := by
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hN.trans (hNn.trans (by linarith))
  have hZcard : (Z n).card ≤
      xiZeroCount 0 1 (-((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    rw [xiZeroCount_eq_sum]
    calc
      (Z n).card = ∑ z ∈ Z n, 1 := by simp
      _ ≤ ∑ z ∈ Z n, xiZeroMultiplicity z := by
        apply Finset.sum_le_sum
        intro z hz
        exact (xiZeroMultiplicity_pos_iff z).mpr
          ((mem_xiZerosInRectangle_iff
            0 1 (-((n : ℝ) + 2)) ((n : ℝ) + 2) z).mp hz).2
  have hScard : ((S n).card : ℝ) ≤
      C * ((n : ℝ) + 2) ^ alpha := by
    calc
      ((S n).card : ℝ) ≤ ((Z n).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      _ ≤ (xiZeroCount 0 1 (-((n : ℝ) + 2))
          ((n : ℝ) + 2) : ℝ) := by exact_mod_cast hZcard
      _ ≤ C * ((n : ℝ) + 2) ^ alpha := hcount _ hR
  have hpow_pos : 0 < ((n : ℝ) + 2) ^ alpha :=
    Real.rpow_pos_of_pos hheight_pos alpha
  have hpow_one : 1 ≤ ((n : ℝ) + 2) ^ alpha :=
    Real.one_le_rpow hheight_one halpha_pos.le
  have hden_le :
      4 * (((S n).card : ℝ) + 1) ≤
        4 * (C + 1) * ((n : ℝ) + 2) ^ alpha := by
    nlinarith [mul_nonneg hC.le hpow_pos.le]
  have hden_small_pos : 0 < 4 * (((S n).card : ℝ) + 1) := by positivity
  have hgap_poly :
      c * ((n : ℝ) + 2) ^ (-alpha) ≤ delta n := by
    have hinv := one_div_le_one_div_of_le hden_small_pos hden_le
    rw [Real.rpow_neg hheight_pos.le]
    dsimp only [c, delta]
    calc
      1 / (4 * (C + 1)) * (((n : ℝ) + 2) ^ alpha)⁻¹ =
          1 / (4 * (C + 1) * ((n : ℝ) + 2) ^ alpha) := by field_simp
      _ ≤ 1 / (4 * (((S n).card : ℝ) + 1)) := hinv
  have hdelta_le_one : delta n ≤ 1 := by
    dsimp only [delta]
    apply (div_le_one (by positivity : 0 < 4 * (((S n).card : ℝ) + 1))).2
    have hcard0 : (0 : ℝ) ≤ ((S n).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hsep_abs : delta n ≤ abs (T n - |rho.im|) := by
    by_cases him : |rho.im| ≤ (n : ℝ) + 2
    · have hre := xiFunction_zero_re hrho
      have hrhoZ : rho ∈ Z n := by
        change rho ∈ xiZerosInRectangle 0 1
          (-((n : ℝ) + 2)) ((n : ℝ) + 2)
        rw [mem_xiZerosInRectangle_iff]
        refine ⟨?_, hrho⟩
        rw [xiZeroRectangle, mem_reProdIm]
        exact ⟨⟨hre.1.le, hre.2.le⟩, abs_le.mp him⟩
      have himS : |rho.im| ∈ S n := by
        exact Finset.mem_image.mpr ⟨rho, hrhoZ, rfl⟩
      simpa only [Real.dist_eq] using (hT n).2 |rho.im| himS
    · push_neg at him
      have hTupper := (hT n).1.2
      rw [abs_of_nonpos (by linarith : T n - |rho.im| ≤ 0)]
      linarith
  have hT_nonneg : 0 ≤ T n :=
    (Nat.cast_nonneg n).trans (hT n).1.1.le
  have hsep_upper_compare : abs (T n - |rho.im|) ≤ |T n - rho.im| := by
    simpa only [abs_of_nonneg hT_nonneg] using
      (abs_abs_sub_abs_le_abs_sub (T n) rho.im)
  have hsep_lower_compare : abs (T n - |rho.im|) ≤ |-T n - rho.im| := by
    have h := abs_abs_sub_abs_le_abs_sub (T n) (-rho.im)
    rw [abs_of_nonneg hT_nonneg, abs_neg] at h
    calc
      abs (T n - |rho.im|) ≤ |T n - -rho.im| := h
      _ = |-T n - rho.im| := by
        rw [show T n - -rho.im = -(-T n - rho.im) by ring, abs_neg]
  exact ⟨hgap_poly.trans hsep_abs,
    hgap_poly.trans (hsep_abs.trans hsep_upper_compare),
    hgap_poly.trans (hsep_abs.trans hsep_lower_compare)⟩

/-- Quadratic specialization in the form needed by the separated logarithmic
derivative estimate: the gap is bounded below by `c / (1 + T n ^ 2)`. -/
theorem exists_inverse_quadratic_separated_xi_height_sequence :
    ∃ (c : ℝ) (N : ℕ) (T : ℕ → ℝ),
      0 < c ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ, (n : ℝ) < T n ∧ T n < (n : ℝ) + 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ rho : ℂ, xiFunction rho = 0 →
        c / (1 + (T n) ^ 2) ≤ abs (T n - |rho.im|) ∧
        c / (1 + (T n) ^ 2) ≤ |T n - rho.im| ∧
        c / (1 + (T n) ^ 2) ≤ |-T n - rho.im| := by
  obtain ⟨c, N, T, hc, hTlim, hTbounds, hsep⟩ :=
    exists_quantitatively_separated_xi_height_sequence 2 (by norm_num)
  let d : ℝ := c / 5
  have hd : 0 < d := div_pos hc (by norm_num)
  refine ⟨d, N, T, hd, hTlim, hTbounds, ?_⟩
  intro n hn rho hrho
  have hbase := hsep n hn rho hrho
  have hn2pos : 0 < (n : ℝ) + 2 := by positivity
  have hTnonneg : 0 ≤ T n :=
    (Nat.cast_nonneg n).trans (hTbounds n).1.le
  have hn2_le : (n : ℝ) + 2 ≤ T n + 2 := by
    linarith [(hTbounds n).1]
  have hsquare : ((n : ℝ) + 2) ^ 2 ≤ (T n + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hn2_le
  have hscale : ((n : ℝ) + 2) ^ 2 ≤ 5 * (1 + (T n) ^ 2) := by
    nlinarith [sq_nonneg (2 * T n - 1)]
  have hsmall_den : 0 < ((n : ℝ) + 2) ^ 2 := sq_pos_of_pos hn2pos
  have hinv : 1 / (5 * (1 + (T n) ^ 2)) ≤
      1 / (((n : ℝ) + 2) ^ 2) :=
    one_div_le_one_div_of_le hsmall_den hscale
  have hconvert : d / (1 + (T n) ^ 2) ≤
      c * ((n : ℝ) + 2) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hn2pos.le, Real.rpow_two]
    dsimp only [d]
    calc
      c / 5 / (1 + (T n) ^ 2) =
          c * (1 / (5 * (1 + (T n) ^ 2))) := by field_simp
      _ ≤ c * (1 / (((n : ℝ) + 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinv hc.le
      _ = c * (((n : ℝ) + 2) ^ 2)⁻¹ := by rw [one_div]
  exact ⟨hconvert.trans hbase.1,
    hconvert.trans hbase.2.1,
    hconvert.trans hbase.2.2⟩

/-- Along a quantitatively separated height sequence, both horizontal edges
are zero-free and the xi logarithmic derivative has a uniform quartic bound
on any fixed real-part strip. -/
theorem exists_xi_logDeriv_quartic_height_sequence
    (sigmaLower sigmaUpper : ℝ) (hsigma : sigmaLower < sigmaUpper) :
    ∃ (K : ℝ) (N : ℕ) (T : ℕ → ℝ),
      0 < K ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ, (n : ℝ) < T n ∧ T n < (n : ℝ) + 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ sigma ∈ Set.Icc sigmaLower sigmaUpper,
        (xiFunction ((sigma : ℂ) + T n * I) ≠ 0 ∧
          ‖logDeriv xiFunction ((sigma : ℂ) + T n * I)‖ ≤
            K * (1 + |T n|) ^ 4) ∧
        (xiFunction ((sigma : ℂ) - T n * I) ≠ 0 ∧
          ‖logDeriv xiFunction ((sigma : ℂ) - T n * I)‖ ≤
            K * (1 + |T n|) ^ 4) := by
  classical
  obtain ⟨d, Nzero, T, hd, hTlim, hTbounds, hsep⟩ :=
    exists_inverse_quadratic_separated_xi_height_sequence
  let e : ℝ := min d 1
  have he : 0 < e := lt_min hd zero_lt_one
  have he_d : e ≤ d := min_le_left _ _
  have he_one : e ≤ 1 := min_le_right _ _
  obtain ⟨C, hC, hgrowth⟩ :=
    xi_logDeriv_growth_of_ne_zero sigmaLower sigmaUpper hsigma
  let K : ℝ := C * (1 + e⁻¹)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  let N : ℕ := max Nzero 4
  refine ⟨K, N, T, hK, hTlim, hTbounds, ?_⟩
  intro n hn sigma hsigma_mem
  have hnzero : Nzero ≤ n := (le_max_left Nzero 4).trans hn
  have hnfour : 4 ≤ n := (le_max_right Nzero 4).trans hn
  have hTpos : 0 < T n :=
    (Nat.cast_nonneg n).trans_lt (hTbounds n).1
  have hTfour : 4 < T n := by
    have hnfour_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnfour
    linarith [(hTbounds n).1]
  have hsep_n := hsep n hnzero
  let delta : ℝ := e / (1 + (T n) ^ 2)
  have hden_pos : 0 < 1 + (T n) ^ 2 := by positivity
  have hdelta : 0 < delta := div_pos he hden_pos
  have hdelta_one : delta ≤ 1 := by
    dsimp only [delta]
    calc
      e / (1 + (T n) ^ 2) ≤ 1 / (1 + (T n) ^ 2) :=
        div_le_div_of_nonneg_right he_one hden_pos.le
      _ ≤ 1 := (div_le_one hden_pos).2 (by
        nlinarith [sq_nonneg (T n)])
  have hbound_at (t : ℝ) (htabs : |t| = T n)
      (hordinate : ∀ rho : ℂ, xiFunction rho = 0 →
        delta ≤ |t - rho.im|) :
      xiFunction ((sigma : ℂ) + t * I) ≠ 0 ∧
        ‖logDeriv xiFunction ((sigma : ℂ) + t * I)‖ ≤
          K * (1 + |T n|) ^ 4 := by
    let s : ℂ := (sigma : ℂ) + t * I
    have hsre : s.re = sigma := by simp [s]
    have hsim : s.im = t := by simp [s]
    have habsim : |s.im| = T n := by rw [hsim, htabs]
    have him : 4 ≤ |s.im| := by rw [habsim]; linarith
    have hxi : xiFunction s ≠ 0 := by
      intro hzero
      have hcontra := hordinate s hzero
      rw [hsim, sub_self, abs_zero] at hcontra
      linarith
    have hsep_hadamard : ∀ m, ‖s - hadamardZeros m‖ ≤ 1 →
        delta ≤ ‖s - hadamardZeros m‖ := by
      intro m _hm
      calc
        delta ≤ |t - (hadamardZeros m).im| :=
          hordinate (hadamardZeros m) (hadamardZeros_spec m)
        _ = |(s - hadamardZeros m).im| := by rw [sub_im, hsim]
        _ ≤ ‖s - hadamardZeros m‖ := Complex.abs_im_le_norm _
    have hraw := hgrowth s delta
      (by rw [hsre]; exact hsigma_mem.1)
      (by rw [hsre]; exact hsigma_mem.2)
      him hxi hdelta hdelta_one hsep_hadamard
    have hdelta_inv : delta⁻¹ = e⁻¹ * (1 + (T n) ^ 2) := by
      dsimp only [delta]
      field_simp
    have hfactor : 1 + delta⁻¹ ≤
        (1 + e⁻¹) * (1 + T n) ^ 2 := by
      rw [hdelta_inv]
      have hein : 0 ≤ e⁻¹ := (inv_pos.mpr he).le
      nlinarith [sq_nonneg (T n)]
    refine ⟨hxi, ?_⟩
    calc
      ‖logDeriv xiFunction ((sigma : ℂ) + t * I)‖ =
          ‖logDeriv xiFunction s‖ := rfl
      _ ≤ C * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := hraw
      _ = C * (1 + T n) ^ 2 * (1 + delta⁻¹) := by rw [habsim]
      _ ≤ C * (1 + T n) ^ 2 *
          ((1 + e⁻¹) * (1 + T n) ^ 2) := by gcongr
      _ = K * (1 + |T n|) ^ 4 := by
        dsimp only [K]
        rw [abs_of_pos hTpos]
        ring
  constructor
  · apply hbound_at (T n) (abs_of_pos hTpos)
    intro rho hrho
    exact (div_le_div_of_nonneg_right he_d hden_pos.le).trans
      (hsep_n rho hrho).2.1
  · have htneg : |-T n| = T n := by rw [abs_neg, abs_of_pos hTpos]
    have hb := hbound_at (-T n) htneg (fun rho hrho =>
      (div_le_div_of_nonneg_right he_d hden_pos.le).trans
        (hsep_n rho hrho).2.2)
    simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hb

end ArithmeticHodge.Analysis

