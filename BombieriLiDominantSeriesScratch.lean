import ArithmeticHodge.Analysis.MultiplicativeWeilLiSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilLiPhaseRecurrence

/-!
# Scratch: dominant moduli in the full paired Bombieri--Li series

The paired Li base attached to `rho` is reciprocal under `rho ↦ 1 - rho`.
This file isolates the resulting reciprocal-product algebra, its summable
coefficient, finite modulus superlevel sets, and the dominant-family step.
-/

set_option autoImplicit false

open Complex Filter Function Metric Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The exponential base in Li's rational function. -/
def liBaseScratch (rho : ℂ) : ℂ :=
  1 - 1 / rho

/-- The direct-plus-reflected Li term. -/
def pairedLiTermScratch (n : ℕ) (rho : ℂ) : ℂ :=
  liFunction n rho + liFunction n (1 - rho)

/-- The reciprocal-symmetric modulus controlling a paired Li term. -/
def reciprocalRadiusScratch (w : ℂ) : ℝ :=
  max ‖w‖ ‖w⁻¹‖

theorem liBase_one_sub_eq_invScratch
    (rho : ℂ) (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    liBaseScratch (1 - rho) = (liBaseScratch rho)⁻¹ := by
  unfold liBaseScratch
  have hOneSub : 1 - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho1)
  have hSubOne : rho - 1 ≠ 0 := sub_ne_zero.mpr hrho1
  rw [show 1 - 1 / rho = (rho - 1) / rho by
    field_simp [hrho0]]
  rw [inv_div]
  field_simp [hOneSub, hSubOne]
  ring

theorem liBase_ne_zeroScratch
    (rho : ℂ) (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    liBaseScratch rho ≠ 0 := by
  rw [liBaseScratch, show 1 - 1 / rho = (rho - 1) / rho by
    field_simp [hrho0]]
  exact div_ne_zero (sub_ne_zero.mpr hrho1) hrho0

theorem pairedLiTerm_eq_reciprocalProductScratch
    (n : ℕ) (rho : ℂ) (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    pairedLiTermScratch n rho =
      ((liBaseScratch rho) ^ n - 1) *
        (((liBaseScratch rho)⁻¹) ^ n - 1) := by
  change (1 - (liBaseScratch rho) ^ n) +
      (1 - (liBaseScratch (1 - rho)) ^ n) = _
  rw [liBase_one_sub_eq_invScratch rho hrho0 hrho1]
  have hw := liBase_ne_zeroScratch rho hrho0 hrho1
  have hprod : (liBaseScratch rho) ^ n *
      ((liBaseScratch rho)⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  calc
    (1 - (liBaseScratch rho) ^ n) +
        (1 - ((liBaseScratch rho)⁻¹) ^ n) =
        (liBaseScratch rho) ^ n * ((liBaseScratch rho)⁻¹) ^ n -
          (liBaseScratch rho) ^ n - ((liBaseScratch rho)⁻¹) ^ n + 1 := by
      rw [hprod]
      ring
    _ = ((liBaseScratch rho) ^ n - 1) *
        (((liBaseScratch rho)⁻¹) ^ n - 1) := by ring

theorem norm_pow_mul_inv_pow_leScratch
    (w : ℂ) (hw0 : w ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hw : ‖w‖ ≤ r) (hwinv : ‖w⁻¹‖ ≤ r)
    (n i j : ℕ) (hi : i < n) (hj : j < n) :
    ‖w ^ i * (w⁻¹) ^ j‖ ≤ r ^ (n - 1) := by
  rcases le_total i j with hij | hji
  · have heq : w ^ i * (w⁻¹) ^ j = (w⁻¹) ^ (j - i) := by
      calc
        w ^ i * (w⁻¹) ^ j =
            w ^ i * ((w⁻¹) ^ i * (w⁻¹) ^ (j - i)) := by
          rw [pow_mul_pow_sub (w⁻¹) hij]
        _ = (w ^ i * (w⁻¹) ^ i) * (w⁻¹) ^ (j - i) := by ring
        _ = (w⁻¹) ^ (j - i) := by
          rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow, one_mul]
    rw [heq, norm_pow]
    calc
      ‖w⁻¹‖ ^ (j - i) ≤ r ^ (j - i) :=
        pow_le_pow_left₀ (norm_nonneg _) hwinv _
      _ ≤ r ^ (n - 1) := pow_le_pow_right₀ hr (by omega)
  · have heq : w ^ i * (w⁻¹) ^ j = w ^ (i - j) := by
      calc
        w ^ i * (w⁻¹) ^ j =
            (w ^ (i - j) * w ^ j) * (w⁻¹) ^ j := by
          rw [pow_sub_mul_pow w hji]
        _ = w ^ (i - j) * (w ^ j * (w⁻¹) ^ j) := by ring
        _ = w ^ (i - j) := by
          rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow, mul_one]
    rw [heq, norm_pow]
    calc
      ‖w‖ ^ (i - j) ≤ r ^ (i - j) :=
        pow_le_pow_left₀ (norm_nonneg _) hw _
      _ ≤ r ^ (n - 1) := pow_le_pow_right₀ hr (by omega)

theorem norm_reciprocalPowerProduct_leScratch
    (w : ℂ) (hw0 : w ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hw : ‖w‖ ≤ r) (hwinv : ‖w⁻¹‖ ≤ r) (n : ℕ) :
    ‖(w ^ n - 1) * ((w⁻¹) ^ n - 1)‖ ≤
      (n : ℝ) ^ 2 * r ^ (n - 1) * ‖w - 1‖ * ‖w⁻¹ - 1‖ := by
  let A : ℂ := ∑ i ∈ Finset.range n, w ^ i
  let B : ℂ := ∑ j ∈ Finset.range n, (w⁻¹) ^ j
  have hAB : ‖A * B‖ ≤ (n : ℝ) ^ 2 * r ^ (n - 1) := by
    calc
      ‖A * B‖ =
          ‖∑ i ∈ Finset.range n,
            ∑ j ∈ Finset.range n, w ^ i * (w⁻¹) ^ j‖ := by
        simp only [A, B, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range n, ‖w ^ i * (w⁻¹) ^ j‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun i _hi ↦ norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n,
          ∑ _j ∈ Finset.range n, r ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_pow_mul_inv_pow_leScratch w hw0 r hr hw hwinv
          n i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      _ = (n : ℝ) ^ 2 * r ^ (n - 1) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [← mul_geom_sum w n, ← mul_geom_sum (w⁻¹) n]
  change ‖((w - 1) * A) * ((w⁻¹ - 1) * B)‖ ≤ _
  have hfactor : ((w - 1) * A) * ((w⁻¹ - 1) * B) =
      (w - 1) * (w⁻¹ - 1) * (A * B) := by ring
  rw [hfactor, norm_mul, norm_mul]
  calc
    ‖w - 1‖ * ‖w⁻¹ - 1‖ * ‖A * B‖ ≤
        ‖w - 1‖ * ‖w⁻¹ - 1‖ *
          ((n : ℝ) ^ 2 * r ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left hAB
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (n : ℝ) ^ 2 * r ^ (n - 1) *
        ‖w - 1‖ * ‖w⁻¹ - 1‖ := by ring

/-- The summable coefficient left after reciprocal power growth is removed. -/
def reciprocalCoefficientScratch (w : ℂ) : ℝ :=
  ‖w - 1‖ * ‖w⁻¹ - 1‖

def zeroLiBaseScratch (zeros : ZetaZeroEnumeration) (k : ℕ) : ℂ :=
  liBaseScratch (zeros.zero k).val

def zeroReciprocalRadiusScratch
    (zeros : ZetaZeroEnumeration) (k : ℕ) : ℝ :=
  reciprocalRadiusScratch (zeroLiBaseScratch zeros k)

def zeroReciprocalCoefficientScratch
    (zeros : ZetaZeroEnumeration) (k : ℕ) : ℝ :=
  reciprocalCoefficientScratch (zeroLiBaseScratch zeros k)

theorem nontrivialZetaZero_val_ne_zeroScratch
    (rho : NontrivialZetaZero) : rho.val ≠ 0 := by
  intro h
  have hpos := rho.re_pos
  rw [h] at hpos
  norm_num at hpos

theorem nontrivialZetaZero_val_ne_oneScratch
    (rho : NontrivialZetaZero) : rho.val ≠ 1 := by
  intro h
  have hlt := rho.re_lt_one
  rw [h] at hlt
  norm_num at hlt

theorem reciprocalCoefficient_liBase_eqScratch
    (rho : ℂ) (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    reciprocalCoefficientScratch (liBaseScratch rho) =
      ‖rho‖⁻¹ * ‖1 - rho‖⁻¹ := by
  have hdirect : ‖liBaseScratch rho - 1‖ = ‖rho‖⁻¹ := by
    rw [show liBaseScratch rho - 1 = -(1 / rho) by
      unfold liBaseScratch
      ring]
    simp
  have hreflected : ‖(liBaseScratch rho)⁻¹ - 1‖ = ‖1 - rho‖⁻¹ := by
    rw [← liBase_one_sub_eq_invScratch rho hrho0 hrho1]
    rw [show liBaseScratch (1 - rho) - 1 = -(1 / (1 - rho)) by
      unfold liBaseScratch
      ring]
    simp
  simp only [reciprocalCoefficientScratch, hdirect, hreflected]

theorem summable_zeroReciprocalCoefficientScratch
    (zeros : ZetaZeroEnumeration) :
    Summable (zeroReciprocalCoefficientScratch zeros) := by
  have hdirect : Summable (fun k : ℕ ↦
      ‖(zeros.zero k).val‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using zeros.summable_inv_norm_sq
  have hreflected : Summable (fun k : ℕ ↦
      ‖1 - (zeros.zero k).val‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [ZetaZeroEnumeration.oneSub,
      oneSubNontrivialZetaZero_val, Real.rpow_two] using
      zeros.oneSub.summable_inv_norm_sq
  have hproduct : Summable (fun k : ℕ ↦
      ‖(zeros.zero k).val‖⁻¹ *
        ‖1 - (zeros.zero k).val‖⁻¹) := by
    apply (hdirect.add hreflected).of_nonneg_of_le
    · intro k
      positivity
    · intro k
      have hab0 : 0 ≤ ‖(zeros.zero k).val‖⁻¹ *
          ‖1 - (zeros.zero k).val‖⁻¹ := by
        positivity
      nlinarith [two_mul_le_add_sq
        ‖(zeros.zero k).val‖⁻¹ ‖1 - (zeros.zero k).val‖⁻¹]
  apply hproduct.congr
  intro k
  exact (reciprocalCoefficient_liBase_eqScratch
    (zeros.zero k).val
    (nontrivialZetaZero_val_ne_zeroScratch (zeros.zero k))
    (nontrivialZetaZero_val_ne_oneScratch (zeros.zero k))).symm

theorem finite_superlevel_of_summable_sqScratch
    (a : ℕ → ℝ) (ha : Summable (fun k ↦ (a k) ^ 2))
    {delta : ℝ} (hdelta : 0 < delta) :
    {k : ℕ | delta ≤ a k}.Finite := by
  have hevent : ∀ᶠ k : ℕ in cofinite, (a k) ^ 2 < delta ^ 2 :=
    ha.tendsto_cofinite_zero.eventually
      (Iio_mem_nhds (sq_pos_of_pos hdelta))
  have hmem : {k : ℕ | (a k) ^ 2 < delta ^ 2} ∈ cofinite := hevent
  have hfiniteSq : {k : ℕ | delta ^ 2 ≤ (a k) ^ 2}.Finite := by
    simpa only [compl_setOf, not_lt] using (mem_cofinite.mp hmem)
  apply hfiniteSq.subset
  intro k hk
  change delta ^ 2 ≤ (a k) ^ 2
  exact (sq_le_sq₀ hdelta.le (hdelta.le.trans hk)).2 hk

theorem norm_liBase_le_one_add_inv_normScratch (rho : ℂ) :
    ‖liBaseScratch rho‖ ≤ 1 + ‖rho‖⁻¹ := by
  unfold liBaseScratch
  calc
    ‖1 - 1 / rho‖ ≤ ‖(1 : ℂ)‖ + ‖1 / rho‖ := norm_sub_le _ _
    _ = 1 + ‖rho‖⁻¹ := by simp

theorem norm_liBase_inv_le_one_add_reflected_inv_normScratch
    (rho : ℂ) (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    ‖(liBaseScratch rho)⁻¹‖ ≤ 1 + ‖1 - rho‖⁻¹ := by
  rw [← liBase_one_sub_eq_invScratch rho hrho0 hrho1]
  exact norm_liBase_le_one_add_inv_normScratch (1 - rho)

theorem zeroReciprocalRadius_leScratch
    (zeros : ZetaZeroEnumeration) (k : ℕ) :
    zeroReciprocalRadiusScratch zeros k ≤
      1 + max ‖(zeros.zero k).val‖⁻¹
        ‖1 - (zeros.zero k).val‖⁻¹ := by
  unfold zeroReciprocalRadiusScratch reciprocalRadiusScratch zeroLiBaseScratch
  apply max_le
  · exact (norm_liBase_le_one_add_inv_normScratch (zeros.zero k).val).trans
      (add_le_add_right (le_max_left _ _) 1)
  · exact (norm_liBase_inv_le_one_add_reflected_inv_normScratch
      (zeros.zero k).val
      (nontrivialZetaZero_val_ne_zeroScratch (zeros.zero k))
      (nontrivialZetaZero_val_ne_oneScratch (zeros.zero k))).trans
      (add_le_add_right (le_max_right _ _) 1)

theorem finite_zeroReciprocalRadius_superlevelScratch
    (zeros : ZetaZeroEnumeration) {r : ℝ} (hr : 1 < r) :
    {k : ℕ | r ≤ zeroReciprocalRadiusScratch zeros k}.Finite := by
  have hdirectSq : Summable (fun k : ℕ ↦
      ‖(zeros.zero k).val‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using zeros.summable_inv_norm_sq
  have hreflectedSq : Summable (fun k : ℕ ↦
      ‖1 - (zeros.zero k).val‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [ZetaZeroEnumeration.oneSub,
      oneSubNontrivialZetaZero_val, Real.rpow_two] using
      zeros.oneSub.summable_inv_norm_sq
  have hdirect := finite_superlevel_of_summable_sqScratch
    (fun k ↦ ‖(zeros.zero k).val‖⁻¹) hdirectSq (sub_pos.mpr hr)
  have hreflected := finite_superlevel_of_summable_sqScratch
    (fun k ↦ ‖1 - (zeros.zero k).val‖⁻¹) hreflectedSq (sub_pos.mpr hr)
  apply (hdirect.union hreflected).subset
  intro k hk
  change r ≤ zeroReciprocalRadiusScratch zeros k at hk
  have hbound := zeroReciprocalRadius_leScratch zeros k
  have hmax : r - 1 ≤ max ‖(zeros.zero k).val‖⁻¹
      ‖1 - (zeros.zero k).val‖⁻¹ := by linarith
  exact (le_max_iff.mp hmax)

theorem reciprocalPowerProduct_eqScratch
    (z : ℂ) (hz0 : z ≠ 0) (n : ℕ) :
    (z ^ n - 1) * ((z⁻¹) ^ n - 1) =
      2 - z ^ n - (z⁻¹) ^ n := by
  have hprod : z ^ n * (z⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
  rw [mul_sub, sub_mul]
  rw [hprod]
  ring

theorem exists_large_finite_reciprocalProduct_sum_re_leScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → UnitAddCircle) {M : ℝ} (hM : 1 < M) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι,
        ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n - 1) *
          ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ))⁻¹) ^ n - 1))).re ≤
        -(Fintype.card ι : ℝ) * M ^ n / 4 := by
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hM).eventually_gt_atTop (12 : ℝ)).exists
  obtain ⟨n, hn, hclose⟩ :=
    exists_large_simultaneous_circle_pow_close_one θ
      (by norm_num : (0 : ℝ) < 1 / 2) (max N k)
  have hNn : N ≤ n := (le_max_left N k).trans hn
  have hkn : k ≤ n := (le_max_right N k).trans hn
  have hMn : 12 < M ^ n :=
    hk.trans_le (pow_le_pow_right₀ hM.le hkn)
  refine ⟨n, hNn, ?_⟩
  change Complex.reCLM (∑ i : ι,
    ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n - 1) *
      ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ))⁻¹) ^ n - 1))) ≤
      -(Fintype.card ι : ℝ) * M ^ n / 4
  rw [map_sum Complex.reCLM]
  calc
    (∑ i : ι, Complex.reCLM
        (((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n - 1) *
          ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ))⁻¹) ^ n - 1)))) ≤
        ∑ _i : ι, -(M ^ n / 4) := by
      apply Finset.sum_le_sum
      intro i _hi
      let phase : ℂ := (AddCircle.toCircle (θ i) : ℂ)
      let z : ℂ := (M : ℂ) * phase
      let u : ℂ := phase ^ n
      have huclose : ‖u - 1‖ < 1 / 2 := by
        simpa only [u, phase] using hclose i
      have hureabs : |u.re - 1| < 1 / 2 := by
        have hrele : |u.re - 1| ≤ ‖u - 1‖ := by
          simpa only [Complex.sub_re, Complex.one_re] using
            Complex.abs_re_le_norm (u - 1)
        exact hrele.trans_lt huclose
      have hure : 1 / 2 < u.re := by
        have := (abs_lt.mp hureabs).1
        linarith
      have hMpos : 0 < M := by linarith
      have hMnp : 0 < M ^ n := pow_pos hMpos n
      have hz0 : z ≠ 0 := by
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hMpos.ne')
          (Circle.coe_ne_zero (AddCircle.toCircle (θ i)))
      have hzNorm : ‖z‖ = M := by
        dsimp only [z, phase]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hMpos, Circle.norm_coe, mul_one]
      have hzre : M ^ n / 2 < (z ^ n).re := by
        have hprod : M ^ n / 2 < M ^ n * u.re := by
          have hh := mul_lt_mul_of_pos_left hure hMnp
          nlinarith
        dsimp only [z]
        rw [mul_pow, show (M : ℂ) ^ n = (M ^ n : ℝ) by norm_cast]
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, u, phase] using hprod
      have hzinvNorm : ‖(z⁻¹) ^ n‖ ≤ 1 := by
        rw [norm_pow, norm_inv, hzNorm]
        exact pow_le_one₀ (inv_nonneg.mpr hMpos.le)
          (inv_le_one_of_one_le₀ hM.le)
      have hzinvRe : -1 ≤ ((z⁻¹) ^ n).re := by
        have hlower : -‖(z⁻¹) ^ n‖ ≤ ((z⁻¹) ^ n).re :=
          (abs_le.mp (Complex.abs_re_le_norm ((z⁻¹) ^ n))).1
        linarith
      change (((z ^ n - 1) * ((z⁻¹) ^ n - 1))).re ≤ -(M ^ n / 4)
      rw [reciprocalPowerProduct_eqScratch z hz0 n]
      change 2 - (z ^ n).re - ((z⁻¹) ^ n).re ≤ -(M ^ n / 4)
      linarith
    _ = -(Fintype.card ι : ℝ) * M ^ n / 4 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem exists_large_finite_reciprocalProduct_sum_re_negativeScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → UnitAddCircle) {M : ℝ} (hM : 1 < M) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι,
        ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n - 1) *
          ((((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ))⁻¹) ^ n - 1))).re < 0 := by
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_reciprocalProduct_sum_re_leScratch θ hM N
  refine ⟨n, hNn, hn.trans_lt ?_⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := by linarith
  have hMnp : 0 < M ^ n := pow_pos hMpos n
  have hpos : 0 < (Fintype.card ι : ℝ) * M ^ n / 4 := by
    positivity
  linarith

theorem exists_large_finite_equal_norm_reciprocalProduct_sum_re_leScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℂ)
    {M : ℝ} (hM : 1 < M) (hnorm : ∀ i, ‖z i‖ = M)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, ((z i) ^ n - 1) * (((z i)⁻¹) ^ n - 1)).re ≤
        -(Fintype.card ι : ℝ) * M ^ n / 4 := by
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := hMpos.ne'
  have hMcne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMne
  let u : ι → Circle := fun i ↦
    ⟨z i / (M : ℂ), by
      change z i / (M : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, norm_div, hnorm i,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos,
        div_self hMne]⟩
  let e := AddCircle.homeomorphCircle one_ne_zero
  let θ : ι → UnitAddCircle := fun i ↦ e.symm (u i)
  have hphase (i : ι) :
      (AddCircle.toCircle (θ i) : ℂ) = (u i : ℂ) := by
    apply congrArg ((↑) : Circle → ℂ)
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply (u i)
  have hbase (i : ι) :
      z i = (M : ℂ) * (AddCircle.toCircle (θ i) : ℂ) := by
    rw [hphase i]
    change z i = (M : ℂ) * (z i / (M : ℂ))
    rw [mul_comm, div_mul_cancel₀ _ hMcne]
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_reciprocalProduct_sum_re_leScratch
      θ hM N
  refine ⟨n, hNn, ?_⟩
  simpa only [← hbase] using hn

theorem exists_large_finite_equal_norm_reciprocalProduct_sum_re_negativeScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℂ)
    {M : ℝ} (hM : 1 < M) (hnorm : ∀ i, ‖z i‖ = M)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, ((z i) ^ n - 1) * (((z i)⁻¹) ^ n - 1)).re < 0 := by
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_equal_norm_reciprocalProduct_sum_re_leScratch
      z hM hnorm N
  refine ⟨n, hNn, hn.trans_lt ?_⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := by linarith
  have hMnp : 0 < M ^ n := pow_pos hMpos n
  have hpos : 0 < (Fintype.card ι : ℝ) * M ^ n / 4 := by
    positivity
  linarith

theorem exists_large_finite_equal_reciprocalRadius_sum_re_leScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℂ)
    {M : ℝ} (hM : 1 < M)
    (hradius : ∀ i, reciprocalRadiusScratch (w i) = M)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, ((w i) ^ n - 1) * (((w i)⁻¹) ^ n - 1)).re ≤
        -(Fintype.card ι : ℝ) * M ^ n / 4 := by
  let z : ι → ℂ := fun i ↦
    if ‖w i‖ = M then w i else (w i)⁻¹
  have hznorm (i : ι) : ‖z i‖ = M := by
    by_cases hi : ‖w i‖ = M
    · simpa only [z, if_pos hi] using hi
    · have hrad := hradius i
      unfold reciprocalRadiusScratch at hrad
      have hinv : ‖(w i)⁻¹‖ = M := by
        rcases max_choice ‖w i‖ ‖(w i)⁻¹‖ with hleft | hright
        · exact (hi (hleft.symm.trans hrad)).elim
        · exact hright.symm.trans hrad
      simpa only [z, if_neg hi] using hinv
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_equal_norm_reciprocalProduct_sum_re_leScratch
      z hM hznorm N
  refine ⟨n, hNn, ?_⟩
  have hsum :
      (∑ i : ι, ((w i) ^ n - 1) * (((w i)⁻¹) ^ n - 1)) =
        ∑ i : ι, ((z i) ^ n - 1) * (((z i)⁻¹) ^ n - 1) := by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hnorm : ‖w i‖ = M
    · simp only [z, if_pos hnorm]
    · simp only [z, if_neg hnorm, inv_inv]
      ring
  rw [hsum]
  exact hn

theorem exists_large_finite_equal_reciprocalRadius_sum_re_negativeScratch
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℂ)
    {M : ℝ} (hM : 1 < M)
    (hradius : ∀ i, reciprocalRadiusScratch (w i) = M)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, ((w i) ^ n - 1) * (((w i)⁻¹) ^ n - 1)).re < 0 := by
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_equal_reciprocalRadius_sum_re_leScratch
      w hM hradius N
  refine ⟨n, hNn, hn.trans_lt ?_⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := by linarith
  have hMnp : 0 < M ^ n := pow_pos hMpos n
  have hpos : 0 < (Fintype.card ι : ℝ) * M ^ n / 4 := by
    positivity
  linarith

def zeroPairedLiTermScratch
    (zeros : ZetaZeroEnumeration) (n k : ℕ) : ℂ :=
  pairedLiTermScratch n (zeros.zero k).val

theorem zeroPairedLiTerm_eq_reciprocalProductScratch
    (zeros : ZetaZeroEnumeration) (n k : ℕ) :
    zeroPairedLiTermScratch zeros n k =
      ((zeroLiBaseScratch zeros k) ^ n - 1) *
        (((zeroLiBaseScratch zeros k)⁻¹) ^ n - 1) := by
  exact pairedLiTerm_eq_reciprocalProductScratch n (zeros.zero k).val
    (nontrivialZetaZero_val_ne_zeroScratch (zeros.zero k))
    (nontrivialZetaZero_val_ne_oneScratch (zeros.zero k))

theorem summable_zeroPairedLiTermScratch
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    Summable (zeroPairedLiTermScratch zeros n) := by
  simpa only [zeroPairedLiTermScratch, pairedLiTermScratch] using
    zeros.liFunction_paired_summable n

theorem norm_zeroPairedLiTerm_leScratch
    (zeros : ZetaZeroEnumeration) {r : ℝ} (hr : 1 ≤ r)
    (n k : ℕ) (hk : zeroReciprocalRadiusScratch zeros k ≤ r) :
    ‖zeroPairedLiTermScratch zeros n k‖ ≤
      (n : ℝ) ^ 2 * r ^ (n - 1) *
        zeroReciprocalCoefficientScratch zeros k := by
  let w := zeroLiBaseScratch zeros k
  have hw0 : w ≠ 0 := liBase_ne_zeroScratch (zeros.zero k).val
    (nontrivialZetaZero_val_ne_zeroScratch (zeros.zero k))
    (nontrivialZetaZero_val_ne_oneScratch (zeros.zero k))
  have hw : ‖w‖ ≤ r := by
    exact (le_max_left ‖w‖ ‖w⁻¹‖).trans hk
  have hwinv : ‖w⁻¹‖ ≤ r := by
    exact (le_max_right ‖w‖ ‖w⁻¹‖).trans hk
  rw [zeroPairedLiTerm_eq_reciprocalProductScratch]
  simpa only [w, zeroReciprocalCoefficientScratch,
    reciprocalCoefficientScratch, mul_assoc] using
      norm_reciprocalPowerProduct_leScratch
        w hw0 r hr hw hwinv n

theorem norm_tsum_zeroPairedLiTerm_compl_leScratch
    (zeros : ZetaZeroEnumeration) (D : Finset ℕ)
    {r : ℝ} (hr : 1 ≤ r)
    (htail : ∀ k ∉ D, zeroReciprocalRadiusScratch zeros k ≤ r)
    (n : ℕ) :
    ‖∑' k : {k : ℕ // k ∉ D}, zeroPairedLiTermScratch zeros n k‖ ≤
      ((n : ℝ) ^ 2 * r ^ (n - 1)) *
        ∑' k : ℕ, zeroReciprocalCoefficientScratch zeros k := by
  let A : ℝ := (n : ℝ) ^ 2 * r ^ (n - 1)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hcoeff := summable_zeroReciprocalCoefficientScratch zeros
  have hcoeffCompl : Summable (fun k : {k : ℕ // k ∉ D} ↦
      zeroReciprocalCoefficientScratch zeros k) := by
    simpa only [Function.comp_apply] using
      hcoeff.subtype {k : ℕ | k ∉ D}
  have hmajor : Summable (fun k : {k : ℕ // k ∉ D} ↦
      A * zeroReciprocalCoefficientScratch zeros k) :=
    hcoeffCompl.mul_left A
  have hbound (k : {k : ℕ // k ∉ D}) :
      ‖zeroPairedLiTermScratch zeros n k‖ ≤
        A * zeroReciprocalCoefficientScratch zeros k := by
    exact norm_zeroPairedLiTerm_leScratch zeros hr n k
      (htail k k.property)
  have habs : Summable (fun k : {k : ℕ // k ∉ D} ↦
      ‖zeroPairedLiTermScratch zeros n k‖) := by
    exact hmajor.of_nonneg_of_le (fun _k ↦ norm_nonneg _) hbound
  have hcomplLe :
      (∑' k : {k : ℕ // k ∉ D},
        zeroReciprocalCoefficientScratch zeros k) ≤
      ∑' k : ℕ, zeroReciprocalCoefficientScratch zeros k := by
    have hsplit :
        (∑ k ∈ D, zeroReciprocalCoefficientScratch zeros k) +
          (∑' k : {k : ℕ // k ∉ D},
            zeroReciprocalCoefficientScratch zeros k) =
          ∑' k : ℕ, zeroReciprocalCoefficientScratch zeros k := by
      simpa only [Set.mem_compl_iff, Finset.mem_coe] using
        hcoeff.sum_add_tsum_compl (s := D)
    rw [← hsplit]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun _k _hk ↦ by
        unfold zeroReciprocalCoefficientScratch reciprocalCoefficientScratch
        positivity)
  calc
    ‖∑' k : {k : ℕ // k ∉ D}, zeroPairedLiTermScratch zeros n k‖ ≤
        ∑' k : {k : ℕ // k ∉ D},
          ‖zeroPairedLiTermScratch zeros n k‖ :=
      norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k : {k : ℕ // k ∉ D},
        A * zeroReciprocalCoefficientScratch zeros k :=
      habs.tsum_le_tsum hbound hmajor
    _ = A * (∑' k : {k : ℕ // k ∉ D},
        zeroReciprocalCoefficientScratch zeros k) := tsum_mul_left
    _ ≤ A * (∑' k : ℕ,
        zeroReciprocalCoefficientScratch zeros k) :=
      mul_le_mul_of_nonneg_left hcomplLe hA0

theorem eventually_polynomial_subdominant_ltScratch
    (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    {r M : ℝ} (hr : 1 ≤ r) (hrM : r < M) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 * r ^ (n - 1) < d * M ^ n / 4 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (hr.trans hrM.le)
  let a : ℝ := r / M
  have ha0 : 0 ≤ a := div_nonneg (zero_le_one.trans hr) hMpos.le
  have ha1 : a < 1 := (div_lt_one hMpos).2 hrM
  have hlim : Tendsto (fun n : ℕ ↦
      (4 * C / d) * ((n : ℝ) ^ 2 * a ^ n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 2 ha0 ha1).const_mul
        (4 * C / d)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (4 * C / d) * ((n : ℝ) ^ 2 * a ^ n) < 1 :=
    hlim.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hevent] with n hn
  have hMnp : 0 < M ^ n := pow_pos hMpos n
  have hden : 0 < d * M ^ n := mul_pos hd hMnp
  have hratio :
      4 * (C * (n : ℝ) ^ 2 * r ^ n) / (d * M ^ n) < 1 := by
    calc
      4 * (C * (n : ℝ) ^ 2 * r ^ n) / (d * M ^ n) =
          (4 * C / d) * ((n : ℝ) ^ 2 * a ^ n) := by
        dsimp only [a]
        rw [div_pow]
        field_simp [hd.ne', hMnp.ne']
      _ < 1 := hn
  have hmain : C * (n : ℝ) ^ 2 * r ^ n < d * M ^ n / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hcross := (div_lt_iff₀ hden).mp hratio
    simpa only [one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hcross
  have hpow : r ^ (n - 1) ≤ r ^ n :=
    pow_le_pow_right₀ hr (Nat.sub_le n 1)
  have hleft : C * (n : ℝ) ^ 2 * r ^ (n - 1) ≤
      C * (n : ℝ) ^ 2 * r ^ n := by
    exact mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hC (sq_nonneg (n : ℝ)))
  exact hleft.trans_lt hmain

theorem exists_large_zeroPaired_tsum_re_negative_of_gapScratch
    (zeros : ZetaZeroEnumeration) (D : Finset ℕ) (hD : D.Nonempty)
    {M r : ℝ} (hM : 1 < M) (hr : 1 ≤ r) (hrM : r < M)
    (hdominant : ∀ k ∈ D, zeroReciprocalRadiusScratch zeros k = M)
    (htail : ∀ k ∉ D, zeroReciprocalRadiusScratch zeros k ≤ r)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑' k : ℕ, zeroPairedLiTermScratch zeros n k).re < 0 := by
  let C : ℝ := ∑' k : ℕ, zeroReciprocalCoefficientScratch zeros k
  let d : ℝ := D.card
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact tsum_nonneg fun k ↦ by
      unfold zeroReciprocalCoefficientScratch reciprocalCoefficientScratch
      positivity
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Finset.card_pos.mpr hD)
  have hevent := eventually_polynomial_subdominant_ltScratch
    C d hC hd hr hrM
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  letI : Nonempty D := Finset.nonempty_coe_sort.mpr hD
  obtain ⟨n, hn, hdominantBoundSubtype⟩ :=
    exists_large_finite_equal_reciprocalRadius_sum_re_leScratch
      (fun i : D ↦ zeroLiBaseScratch zeros i) hM
      (fun i ↦ by
        simpa only [zeroReciprocalRadiusScratch] using
          hdominant i i.property)
      (max N N₀)
  have hNn : N ≤ n := (le_max_left N N₀).trans hn
  have hN₀n : N₀ ≤ n := (le_max_right N N₀).trans hn
  have hsmall :
      C * (n : ℝ) ^ 2 * r ^ (n - 1) < d * M ^ n / 4 :=
    hN₀ n hN₀n
  have hfiniteSumEq :
      (∑ k ∈ D, zeroPairedLiTermScratch zeros n k) =
        ∑ i : D, ((zeroLiBaseScratch zeros i) ^ n - 1) *
          (((zeroLiBaseScratch zeros i)⁻¹) ^ n - 1) := by
    calc
      (∑ k ∈ D, zeroPairedLiTermScratch zeros n k) =
          ∑ i : D, zeroPairedLiTermScratch zeros n i := by
        exact Finset.sum_subtype D (fun _k ↦ Iff.rfl)
          (zeroPairedLiTermScratch zeros n)
      _ = ∑ i : D, ((zeroLiBaseScratch zeros i) ^ n - 1) *
          (((zeroLiBaseScratch zeros i)⁻¹) ^ n - 1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact zeroPairedLiTerm_eq_reciprocalProductScratch zeros n i
  have hdominantBound :
      (∑ k ∈ D, zeroPairedLiTermScratch zeros n k).re ≤
        -d * M ^ n / 4 := by
    rw [hfiniteSumEq]
    simpa only [d, Fintype.card_coe] using hdominantBoundSubtype
  let tail : ℂ :=
    ∑' k : {k : ℕ // k ∉ D}, zeroPairedLiTermScratch zeros n k
  have htailNorm : ‖tail‖ ≤
      ((n : ℝ) ^ 2 * r ^ (n - 1)) * C := by
    simpa only [tail, C] using
      norm_tsum_zeroPairedLiTerm_compl_leScratch zeros D hr htail n
  have htailSmall : ‖tail‖ < d * M ^ n / 4 := by
    apply htailNorm.trans_lt
    calc
      (n : ℝ) ^ 2 * r ^ (n - 1) * C =
          C * (n : ℝ) ^ 2 * r ^ (n - 1) := by ring
      _ < d * M ^ n / 4 := hsmall
  have hseries := summable_zeroPairedLiTermScratch zeros n
  have hsplit :
      (∑ k ∈ D, zeroPairedLiTermScratch zeros n k) + tail =
        ∑' k : ℕ, zeroPairedLiTermScratch zeros n k := by
    simpa only [tail, Set.mem_compl_iff, Finset.mem_coe] using
      hseries.sum_add_tsum_compl (s := D)
  refine ⟨n, hNn, ?_⟩
  rw [← hsplit]
  simp only [Complex.add_re]
  have htailRe : tail.re ≤ ‖tail‖ := Complex.re_le_norm tail
  linarith

theorem exists_dominant_finset_gapScratch
    (q : ℕ → ℝ)
    (hsuper : ∀ {s : ℝ}, 1 < s → {k : ℕ | s ≤ q k}.Finite)
    (hoff : ∃ k : ℕ, 1 < q k) :
    ∃ (D : Finset ℕ) (M r : ℝ),
      D.Nonempty ∧ 1 < M ∧ 1 ≤ r ∧ r < M ∧
      (∀ k ∈ D, q k = M) ∧ (∀ k ∉ D, q k ≤ r) := by
  obtain ⟨k₀, hk₀⟩ := hoff
  let s₀ : ℝ := (1 + q k₀) / 2
  have hs₀ : 1 < s₀ := by
    dsimp only [s₀]
    linarith
  have hs₀q : s₀ < q k₀ := by
    dsimp only [s₀]
    linarith
  let hfinite : {k : ℕ | s₀ ≤ q k}.Finite := hsuper hs₀
  let S : Finset ℕ := hfinite.toFinset
  have hk₀S : k₀ ∈ S := by
    rw [show k₀ ∈ S ↔ s₀ ≤ q k₀ by
      exact hfinite.mem_toFinset]
    exact hs₀q.le
  have hS : S.Nonempty := ⟨k₀, hk₀S⟩
  obtain ⟨kmax, hkmaxS, hkmax⟩ := Finset.exists_max_image S q hS
  let M : ℝ := q kmax
  have hk₀M : q k₀ ≤ M := hkmax k₀ hk₀S
  have hM : 1 < M := hk₀.trans_le hk₀M
  have hs₀M : s₀ < M := hs₀q.trans_le hk₀M
  have hglobal (k : ℕ) : q k ≤ M := by
    by_cases hkS : k ∈ S
    · exact hkmax k hkS
    · have hklt : q k < s₀ := by
        by_contra hnot
        have hmem : s₀ ≤ q k := le_of_not_gt hnot
        exact hkS (hfinite.mem_toFinset.mpr hmem)
      exact hklt.le.trans hs₀M.le
  let D : Finset ℕ := S.filter (fun k ↦ q k = M)
  have hkmaxD : kmax ∈ D := by
    exact Finset.mem_filter.mpr ⟨hkmaxS, rfl⟩
  have hD : D.Nonempty := ⟨kmax, hkmaxD⟩
  have hDon (k : ℕ) (hk : k ∈ D) : q k = M :=
    (Finset.mem_filter.mp hk).2
  let T : Finset ℕ := S.filter (fun k ↦ q k < M)
  by_cases hT : T.Nonempty
  · obtain ⟨kt, hktT, hktmax⟩ := Finset.exists_max_image T q hT
    have hktM : q kt < M := (Finset.mem_filter.mp hktT).2
    let r : ℝ := max s₀ (q kt)
    have hr : 1 ≤ r := hs₀.le.trans (le_max_left _ _)
    have hrM : r < M := max_lt hs₀M hktM
    refine ⟨D, M, r, hD, hM, hr, hrM, hDon, ?_⟩
    intro k hkD
    by_cases hkS : k ∈ S
    · have hkne : q k ≠ M := by
        intro heq
        exact hkD (Finset.mem_filter.mpr ⟨hkS, heq⟩)
      have hklt : q k < M := lt_of_le_of_ne (hglobal k) hkne
      have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hkS, hklt⟩
      exact (hktmax k hkT).trans (le_max_right _ _)
    · have hklt : q k < s₀ := by
        by_contra hnot
        exact hkS (hfinite.mem_toFinset.mpr (le_of_not_gt hnot))
      exact hklt.le.trans (le_max_left _ _)
  · refine ⟨D, M, s₀, hD, hM, hs₀.le, hs₀M, hDon, ?_⟩
    intro k hkD
    by_cases hkS : k ∈ S
    · have hkne : q k ≠ M := by
        intro heq
        exact hkD (Finset.mem_filter.mpr ⟨hkS, heq⟩)
      have hklt : q k < M := lt_of_le_of_ne (hglobal k) hkne
      have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hkS, hklt⟩
      exact (hT ⟨k, hkT⟩).elim
    · have hklt : q k < s₀ := by
        by_contra hnot
        exact hkS (hfinite.mem_toFinset.mpr (le_of_not_gt hnot))
      exact hklt.le

theorem exists_large_zeroPaired_tsum_re_negative_of_radius_gt_oneScratch
    (zeros : ZetaZeroEnumeration)
    (hoff : ∃ k : ℕ, 1 < zeroReciprocalRadiusScratch zeros k)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑' k : ℕ, zeroPairedLiTermScratch zeros n k).re < 0 := by
  obtain ⟨D, M, r, hD, hM, hr, hrM, hdominant, htail⟩ :=
    exists_dominant_finset_gapScratch
      (zeroReciprocalRadiusScratch zeros)
      (fun hs ↦ finite_zeroReciprocalRadius_superlevelScratch zeros hs)
      hoff
  exact exists_large_zeroPaired_tsum_re_negative_of_gapScratch
    zeros D hD hM hr hrM hdominant htail N

theorem not_RH_exists_zeroReciprocalRadius_gt_oneScratch
    (zeros : ZetaZeroEnumeration) (hnot : ¬ RiemannHypothesis) :
    ∃ k : ℕ, 1 < zeroReciprocalRadiusScratch zeros k := by
  obtain ⟨rho, hrho⟩ := not_RH_exists_li_base_gt_one hnot
  obtain ⟨k, hk⟩ := zeros.exhaustive rho
  refine ⟨k, ?_⟩
  unfold zeroReciprocalRadiusScratch reciprocalRadiusScratch zeroLiBaseScratch
  rw [hk]
  exact hrho.trans_le (le_max_left _ _)

/-- Abstract dominant-modulus completion for the full paired Li series:
failure of RH forces arbitrarily late negative real parts of its absolutely
convergent exact-multiplicity zero sum. -/
theorem not_RH_exists_large_zeroPaired_tsum_re_negativeScratch
    (zeros : ZetaZeroEnumeration) (hnot : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑' k : ℕ, zeroPairedLiTermScratch zeros n k).re < 0 := by
  exact exists_large_zeroPaired_tsum_re_negative_of_radius_gt_oneScratch
    zeros (not_RH_exists_zeroReciprocalRadius_gt_oneScratch zeros hnot) N

theorem not_RH_exists_large_liFunction_paired_tsum_re_negativeScratch
    (zeros : ZetaZeroEnumeration) (hnot : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))).re < 0 := by
  simpa only [zeroPairedLiTermScratch, pairedLiTermScratch] using
    not_RH_exists_large_zeroPaired_tsum_re_negativeScratch zeros hnot N

theorem RH_of_liFunction_paired_tsum_re_nonnegativeScratch
    (zeros : ZetaZeroEnumeration)
    (hnonnegative : ∀ n : ℕ, 0 ≤
      (∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))).re) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨n, _hn, hneg⟩ :=
    not_RH_exists_large_liFunction_paired_tsum_re_negativeScratch
      zeros hnot 0
  exact (not_lt_of_ge (hnonnegative n)) hneg

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
