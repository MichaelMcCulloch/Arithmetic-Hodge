import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffSpectral
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSmoothSpectralTransfer
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroLogSummability
import ArithmeticHodge.Analysis.ZetaDeLaValleePoussin
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Exchanging Li cutoffs with the zeta-zero sum

The logarithmic de la Vallée-Poussin zero-free region supplies uniform
endpoint-correction majorants on the high-zero tail.  The remaining low zeros
form a finite set, so Tannery's theorem exchanges the shrinking cutoff with
the full exact-multiplicity zero sum.
-/

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A harmless `m`-dependent constant for endpoint-polynomial estimates. -/
def liLaplaceTailNormConstant : ℕ → ℝ
  | 0 => 1
  | m + 1 => 1 + (m + 1) * liLaplaceTailNormConstant m

private theorem liLaplaceTailNormConstant_nonneg (m : ℕ) :
    0 ≤ liLaplaceTailNormConstant m := by
  induction m with
  | zero => simp [liLaplaceTailNormConstant]
  | succ m ih =>
      simp only [liLaplaceTailNormConstant]
      positivity

/-- A uniform polynomial bound for the incomplete-Laplace endpoint factor. -/
theorem norm_liLaplaceTailPolynomial_le
    (m : ℕ) (s : ℂ) (L : ℝ) (hL : 0 ≤ L) (hs : 1 ≤ ‖s‖) :
    ‖liLaplaceTailPolynomial m s L‖ ≤
      liLaplaceTailNormConstant m * (1 + L) ^ m / ‖s‖ := by
  have hspos : 0 < ‖s‖ := zero_lt_one.trans_le hs
  have hbase : 1 ≤ 1 + L := by linarith
  induction m with
  | zero =>
      simp [liLaplaceTailPolynomial, liLaplaceTailNormConstant]
  | succ m ih =>
      have hpowSucc : L ^ (m + 1) ≤ (1 + L) ^ (m + 1) :=
        pow_le_pow_left₀ hL (by linarith) _
      have hpowMono : (1 + L) ^ m ≤ (1 + L) ^ (m + 1) :=
        pow_le_pow_right₀ hbase (Nat.le_succ m)
      have hinv : 1 / ‖s‖ ≤ 1 := (div_le_one hspos).2 hs
      have hinv0 : 0 ≤ 1 / ‖s‖ := by positivity
      have hinvSq : (1 / ‖s‖) ^ 2 ≤ 1 / ‖s‖ := by
        nlinarith
      have hC0 : 0 ≤ liLaplaceTailNormConstant m :=
        liLaplaceTailNormConstant_nonneg m
      rw [liLaplaceTailPolynomial]
      calc
        ‖(L : ℂ) ^ (m + 1) / s +
            (((m + 1 : ℕ) : ℂ) / s) *
              liLaplaceTailPolynomial m s L‖ ≤
            ‖(L : ℂ) ^ (m + 1) / s‖ +
              ‖(((m + 1 : ℕ) : ℂ) / s) *
                liLaplaceTailPolynomial m s L‖ := norm_add_le _ _
        _ = L ^ (m + 1) / ‖s‖ +
              ((m + 1 : ℕ) : ℝ) / ‖s‖ *
                ‖liLaplaceTailPolynomial m s L‖ := by
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hL, norm_mul, norm_div, Complex.norm_natCast]
        _ ≤ L ^ (m + 1) / ‖s‖ +
              ((m + 1 : ℕ) : ℝ) / ‖s‖ *
                (liLaplaceTailNormConstant m *
                  (1 + L) ^ m / ‖s‖) := by
          gcongr
        _ ≤ (1 + L) ^ (m + 1) / ‖s‖ +
              ((m + 1 : ℕ) : ℝ) *
                liLaplaceTailNormConstant m *
                  (1 + L) ^ (m + 1) / ‖s‖ := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right hpowSucc hspos.le
          · calc
              ((m + 1 : ℕ) : ℝ) / ‖s‖ *
                  (liLaplaceTailNormConstant m *
                    (1 + L) ^ m / ‖s‖) =
                  (((m + 1 : ℕ) : ℝ) *
                    liLaplaceTailNormConstant m *
                      (1 + L) ^ m) * (1 / ‖s‖) ^ 2 := by ring
              _ ≤ (((m + 1 : ℕ) : ℝ) *
                    liLaplaceTailNormConstant m *
                      (1 + L) ^ m) * (1 / ‖s‖) := by
                gcongr
              _ ≤ (((m + 1 : ℕ) : ℝ) *
                    liLaplaceTailNormConstant m *
                      (1 + L) ^ (m + 1)) * (1 / ‖s‖) := by
                gcongr
              _ = ((m + 1 : ℕ) : ℝ) *
                    liLaplaceTailNormConstant m *
                      (1 + L) ^ (m + 1) / ‖s‖ := by ring
        _ = liLaplaceTailNormConstant (m + 1) *
              (1 + L) ^ (m + 1) / ‖s‖ := by
          simp only [liLaplaceTailNormConstant]
          push_cast
          ring

private theorem exp_neg_mul_pow_le_factorial
    (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    Real.exp (-x) * x ^ m ≤ (Nat.factorial m : ℝ) := by
  have hfac : 0 < (Nat.factorial m : ℝ) := by positivity
  have hseries := Real.pow_div_factorial_le_exp x hx m
  have hpow : x ^ m ≤ (Nat.factorial m : ℝ) * Real.exp x :=
    by simpa only [mul_comm] using (div_le_iff₀ hfac).mp hseries
  calc
    Real.exp (-x) * x ^ m ≤
        Real.exp (-x) * ((Nat.factorial m : ℝ) * Real.exp x) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = (Nat.factorial m : ℝ) := by
      rw [show Real.exp (-x) * ((Nat.factorial m : ℝ) * Real.exp x) =
          (Nat.factorial m : ℝ) * (Real.exp (-x) * Real.exp x) by ring,
        ← Real.exp_add]
      simp

/-- Exponential cutoff decay absorbs every fixed logarithmic power. -/
theorem rpow_negLog_pow_le
    (epsilon sigma a : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (ha : 0 < a) (hsigma : a ≤ sigma) (m : ℕ) :
    epsilon ^ sigma * (-Real.log epsilon) ^ m ≤
      (Nat.factorial m : ℝ) / a ^ m := by
  let L : ℝ := -Real.log epsilon
  have hlogneg : Real.log epsilon < 0 :=
    Real.log_neg hepsilon0 hepsilon1
  have hL : 0 ≤ L := by
    dsimp only [L]
    linarith
  have haL : 0 ≤ a * L := mul_nonneg ha.le hL
  have hexp : epsilon ^ sigma ≤ Real.exp (-a * L) := by
    rw [Real.rpow_def_of_pos hepsilon0]
    apply Real.exp_le_exp.mpr
    dsimp only [L]
    have hmul := mul_le_mul_of_nonpos_left hsigma hlogneg.le
    linarith
  have hscaled := exp_neg_mul_pow_le_factorial (a * L) haL m
  have hapow : 0 < a ^ m := pow_pos ha m
  apply (le_div_iff₀ hapow).2
  calc
    (epsilon ^ sigma * (-Real.log epsilon) ^ m) * a ^ m =
        (epsilon ^ sigma * L ^ m) * a ^ m := by rfl
    _ = epsilon ^ sigma * (a * L) ^ m := by
      rw [mul_pow]
      ring
    _ ≤ Real.exp (-a * L) * (a * L) ^ m := by
      gcongr
    _ ≤ (Nat.factorial m : ℝ) := by
      simpa only [neg_mul] using hscaled

/-- The finite polynomial which uniformly bounds a cutoff logarithmic power
when the real part is bounded below by `a`. -/
def cutoffLogPowerMajorant (m : ℕ) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (Nat.choose m j : ℝ) * (Nat.factorial j : ℝ) / a ^ j

theorem rpow_one_add_negLog_pow_le
    (epsilon sigma a : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (ha : 0 < a) (hsigma : a ≤ sigma) (m : ℕ) :
    epsilon ^ sigma * (1 + (-Real.log epsilon)) ^ m ≤
      cutoffLogPowerMajorant m a := by
  let L : ℝ := -Real.log epsilon
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact neg_nonneg.mpr (Real.log_nonpos hepsilon0.le hepsilon1.le)
  rw [show (1 + (-Real.log epsilon)) ^ m = (L + 1) ^ m by
    congr 1
    dsimp only [L]
    ring]
  rw [add_pow]
  rw [Finset.mul_sum]
  unfold cutoffLogPowerMajorant
  apply Finset.sum_le_sum
  intro j hj
  have hjbound := rpow_negLog_pow_le
    epsilon sigma a hepsilon0 hepsilon1 ha hsigma j
  dsimp only [L]
  calc
    epsilon ^ sigma *
        (L ^ j * 1 ^ (m - j) * (Nat.choose m j : ℝ)) =
        (Nat.choose m j : ℝ) *
          (epsilon ^ sigma * (-Real.log epsilon) ^ j) := by
      dsimp only [L]
      simp only [one_pow, mul_one]
      ring
    _ ≤ (Nat.choose m j : ℝ) *
        ((Nat.factorial j : ℝ) / a ^ j) := by
      gcongr
    _ = (Nat.choose m j : ℝ) * (Nat.factorial j : ℝ) / a ^ j := by
      ring

/-- A cutoff-independent endpoint majorant at real-part lower bound `a`. -/
def liCutoffCorrectionMajorant
    (n : ℕ) (a R : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n,
    ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
      liLaplaceTailNormConstant m *
        cutoffLogPowerMajorant m a / R

/-- Uniform endpoint-correction bound once `Re(s) ≥ a` and `‖s‖ ≥ 1`. -/
theorem norm_liKernelCutoffCorrection_le_majorant
    (n : ℕ) (epsilon : ℝ) (s : ℂ) (a : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (ha : 0 < a) (hsre : a ≤ s.re) (hsnorm : 1 ≤ ‖s‖) :
    ‖liKernelCutoffCorrection n epsilon s‖ ≤
      liCutoffCorrectionMajorant n a ‖s‖ := by
  let L : ℝ := -Real.log epsilon
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact neg_nonneg.mpr (Real.log_nonpos hepsilon0.le hepsilon1.le)
  have hspos : 0 < ‖s‖ := zero_lt_one.trans_le hsnorm
  have heps0 : 0 ≤ epsilon ^ s.re := Real.rpow_nonneg hepsilon0.le _
  calc
    ‖liKernelCutoffCorrection n epsilon s‖ ≤
        epsilon ^ s.re *
          ∑ m ∈ Finset.range n,
            ‖(Nat.choose n (m + 1) : ℂ) /
                (Nat.factorial m : ℂ)‖ *
              ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ :=
      norm_liKernelCutoffCorrection_le n epsilon s hepsilon0
    _ = ∑ m ∈ Finset.range n,
          ‖(Nat.choose n (m + 1) : ℂ) /
              (Nat.factorial m : ℂ)‖ *
            (epsilon ^ s.re *
              ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ ≤ ∑ m ∈ Finset.range n,
          ‖(Nat.choose n (m + 1) : ℂ) /
              (Nat.factorial m : ℂ)‖ *
            liLaplaceTailNormConstant m *
              cutoffLogPowerMajorant m a / ‖s‖ := by
      apply Finset.sum_le_sum
      intro m _hm
      have hpoly := norm_liLaplaceTailPolynomial_le
        m s L hL hsnorm
      have hlog := rpow_one_add_negLog_pow_le
        epsilon s.re a hepsilon0 hepsilon1 ha hsre m
      have hweighted :
          epsilon ^ s.re *
              ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ ≤
            liLaplaceTailNormConstant m *
              cutoffLogPowerMajorant m a / ‖s‖ := by
        calc
          epsilon ^ s.re *
              ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ ≤
              epsilon ^ s.re *
                (liLaplaceTailNormConstant m *
                  (1 + L) ^ m / ‖s‖) := by
            gcongr
          _ = (liLaplaceTailNormConstant m / ‖s‖) *
                (epsilon ^ s.re * (1 + (-Real.log epsilon)) ^ m) := by
            dsimp only [L]
            ring
          _ ≤ (liLaplaceTailNormConstant m / ‖s‖) *
                cutoffLogPowerMajorant m a := by
            exact mul_le_mul_of_nonneg_left hlog
              (div_nonneg
                (liLaplaceTailNormConstant_nonneg m) hspos.le)
          _ = liLaplaceTailNormConstant m *
                cutoffLogPowerMajorant m a / ‖s‖ := by
            ring
      calc
        ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
            (epsilon ^ s.re *
              ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖) ≤
            ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
              (liLaplaceTailNormConstant m *
                cutoffLogPowerMajorant m a / ‖s‖) :=
          mul_le_mul_of_nonneg_left hweighted
            (norm_nonneg
              ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)))
        _ = ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
              liLaplaceTailNormConstant m *
                cutoffLogPowerMajorant m a / ‖s‖ := by
          ring
    _ = liCutoffCorrectionMajorant n a ‖s‖ := by
      rfl

private theorem finite_indices_norm_le_of_summable_inv_rpow
    (z : ℕ → ℂ) (hz : ∀ k, z k ≠ 0)
    (p : ℝ) (hp : 0 < p)
    (hsum : Summable (fun k ↦ ‖z k‖⁻¹ ^ p))
    (R : ℝ) (hR : 0 < R) :
    {k : ℕ | ‖z k‖ ≤ R}.Finite := by
  let d : ℝ := R⁻¹ ^ p
  have hd : 0 < d := Real.rpow_pos_of_pos (inv_pos.mpr hR) p
  have hevent : ∀ᶠ k : ℕ in cofinite, ‖z k‖⁻¹ ^ p < d :=
    hsum.tendsto_cofinite_zero.eventually_lt_const hd
  have hfinite : {k : ℕ | d ≤ ‖z k‖⁻¹ ^ p}.Finite := by
    simpa only [Filter.eventually_cofinite, Set.mem_setOf_eq, not_lt] using hevent
  apply hfinite.subset
  intro k hk
  have hzk : 0 < ‖z k‖ := norm_pos_iff.mpr (hz k)
  have hinv : R⁻¹ ≤ ‖z k‖⁻¹ :=
    (inv_le_inv₀ hR hzk).2 hk
  exact Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hinv hp.le

/-- Inverse-power summability forces the nonzero sequence to escape every
bounded norm set. -/
theorem tendsto_norm_atTop_of_summable_inv_rpow
    (z : ℕ → ℂ) (hz : ∀ k, z k ≠ 0)
    (p : ℝ) (hp : 0 < p)
    (hsum : Summable (fun k ↦ ‖z k‖⁻¹ ^ p)) :
    Tendsto (fun k ↦ ‖z k‖) atTop atTop := by
  rw [← Nat.cofinite_eq_atTop]
  apply tendsto_atTop.2
  intro R
  by_cases hR : 0 < R
  · have hfinite := finite_indices_norm_le_of_summable_inv_rpow
      z hz p hp hsum R hR
    have hsmall : {k : ℕ | ‖z k‖ < R}.Finite :=
      hfinite.subset (by
        intro k hk
        change ‖z k‖ ≤ R
        exact hk.le)
    have hmem : {k : ℕ | R ≤ ‖z k‖} ∈ cofinite := by
      rw [mem_cofinite]
      simpa only [compl_setOf, not_le] using hsmall
    exact hmem
  · exact Filter.Eventually.of_forall fun k ↦
      le_trans (le_of_not_gt hR) (norm_nonneg (z k))

private theorem summable_sq_finset_sum
    {ι : Type*} (S : Finset ι) (b : ι → ℕ → ℝ)
    (hb : ∀ i ∈ S, Summable (fun k ↦ (b i k) ^ 2)) :
    Summable (fun k ↦ (∑ i ∈ S, b i k) ^ 2) := by
  have hsq : Summable (fun k ↦ ∑ i ∈ S, (b i k) ^ 2) :=
    summable_sum hb
  have hmajor := hsq.mul_left (S.card : ℝ)
  apply hmajor.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    exact sq_sum_le_card_mul_sum_sq

/-- Multiplying a logarithmic monomial by a fixed constant preserves the
square-summability supplied by the inverse-square divisor estimate. -/
theorem summable_const_mul_log_pow_div_sq
    (R : ℕ → ℝ) (hR : ∀ k, R k ≠ 0)
    (hlog : ∀ q : ℕ, Summable (fun k ↦
      Real.log (R k + 2) ^ q * (R k)⁻¹ ^ 2))
    (C : ℝ) (q : ℕ) :
    Summable (fun k ↦
      (C * Real.log (R k + 2) ^ q / R k) ^ 2) := by
  have hs := (hlog (2 * q)).mul_left (C ^ 2)
  apply hs.congr
  intro k
  have hRk := hR k
  calc
    C ^ 2 *
          (Real.log (R k + 2) ^ (2 * q) * (R k)⁻¹ ^ 2) =
        (C * Real.log (R k + 2) ^ q / R k) ^ 2 := by
      rw [div_pow, mul_pow, ← pow_mul]
      field_simp
      ring

/-- One logarithmic monomial in the de la Vallee-Poussin endpoint bound. -/
def liCutoffDLVLogTerm
    (m j : ℕ) (c R : ℝ) : ℝ :=
  ((Nat.choose m j : ℝ) * (Nat.factorial j : ℝ) / c ^ j) *
    Real.log (R + 2) ^ j / R

def liCutoffDLVAtomMajorant
    (m : ℕ) (c R : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), liCutoffDLVLogTerm m j c R

/-- The fully expanded DLV majorant for one Li cutoff correction. -/
def liCutoffDLVMajorant
    (n : ℕ) (c R : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n,
    ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
      liLaplaceTailNormConstant m *
        liCutoffDLVAtomMajorant m c R

private theorem cutoffLogPowerMajorant_div_eq_dlvAtom
    (m : ℕ) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    cutoffLogPowerMajorant m (c / Real.log (R + 2)) / R =
      liCutoffDLVAtomMajorant m c R := by
  have hlog : 0 < Real.log (R + 2) := by
    apply Real.log_pos
    linarith
  unfold cutoffLogPowerMajorant liCutoffDLVAtomMajorant
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold liCutoffDLVLogTerm
  field_simp [hc.ne', hR.ne', hlog.ne']
  rw [mul_assoc, ← mul_pow, div_mul_cancel₀ c hlog.ne']

private theorem summable_sq_liCutoffDLVAtomMajorant
    (R : ℕ → ℝ) (hR : ∀ k, R k ≠ 0)
    (hlog : ∀ q : ℕ, Summable (fun k ↦
      Real.log (R k + 2) ^ q * (R k)⁻¹ ^ 2))
    (m : ℕ) (c : ℝ) :
    Summable (fun k ↦
      (liCutoffDLVAtomMajorant m c (R k)) ^ 2) := by
  unfold liCutoffDLVAtomMajorant
  apply summable_sq_finset_sum
  intro j _hj
  simpa only [liCutoffDLVLogTerm] using
    summable_const_mul_log_pow_div_sq R hR hlog
      ((Nat.choose m j : ℝ) * (Nat.factorial j : ℝ) / c ^ j) j

/-- Every expanded DLV correction majorant is square-summable against an
abstract logarithmically weighted inverse-square divisor. -/
theorem summable_sq_liCutoffDLVMajorant_of_log
    (R : ℕ → ℝ) (hR : ∀ k, R k ≠ 0)
    (hlog : ∀ q : ℕ, Summable (fun k ↦
      Real.log (R k + 2) ^ q * (R k)⁻¹ ^ 2))
    (n : ℕ) (c : ℝ) :
    Summable (fun k ↦ (liCutoffDLVMajorant n c (R k)) ^ 2) := by
  unfold liCutoffDLVMajorant
  apply summable_sq_finset_sum
  intro m _hm
  let C : ℝ :=
    ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
      liLaplaceTailNormConstant m
  have hatom := summable_sq_liCutoffDLVAtomMajorant
    R hR hlog m c
  have hscaled := hatom.mul_left (C ^ 2)
  apply hscaled.congr
  intro k
  dsimp only [C]
  ring

theorem ZetaZeroEnumeration.summable_sq_liCutoffDLVMajorant
    (zeros : ZetaZeroEnumeration) (n : ℕ) (c : ℝ) :
    Summable (fun k ↦
      (liCutoffDLVMajorant n c ‖(zeros.zero k).val‖) ^ 2) := by
  apply summable_sq_liCutoffDLVMajorant_of_log
  · intro k
    exact norm_ne_zero_iff.mpr (by
      intro hzero
      have hpos := (zeros.zero k).re_pos
      rw [hzero] at hpos
      norm_num at hpos)
  · exact zeros.summable_log_norm_add_two_pow_mul_inv_sq

theorem ZetaZeroEnumeration.summable_sq_liCutoffDLVOneSubMajorant
    (zeros : ZetaZeroEnumeration) (n : ℕ) (c : ℝ) :
    Summable (fun k ↦
      (liCutoffDLVMajorant n c
        ‖1 - (zeros.zero k).val‖) ^ 2) := by
  apply summable_sq_liCutoffDLVMajorant_of_log
  · intro k
    exact norm_ne_zero_iff.mpr (by
      intro hone
      have hlt := (zeros.zero k).re_lt_one
      have hrho : (zeros.zero k).val = 1 := (sub_eq_zero.mp hone).symm
      rw [hrho] at hlt
      norm_num at hlt)
  · exact zeros.summable_log_one_sub_norm_add_two_pow_mul_inv_sq

/-- The explicit endpoint correction is uniformly bounded by the expanded
DLV majorant. -/
theorem norm_liKernelCutoffCorrection_le_dlv
    (n : ℕ) (epsilon : ℝ) (s : ℂ) (c : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hc : 0 < c) (hsnorm : 1 ≤ ‖s‖)
    (hgap : c / Real.log (‖s‖ + 2) ≤ s.re) :
    ‖liKernelCutoffCorrection n epsilon s‖ ≤
      liCutoffDLVMajorant n c ‖s‖ := by
  have hspos : 0 < ‖s‖ := zero_lt_one.trans_le hsnorm
  have hlog : 0 < Real.log (‖s‖ + 2) := by
    apply Real.log_pos
    linarith
  have hbound := norm_liKernelCutoffCorrection_le_majorant
    n epsilon s (c / Real.log (‖s‖ + 2))
    hepsilon0 hepsilon1 (div_pos hc hlog) hgap hsnorm
  apply hbound.trans_eq
  unfold liCutoffCorrectionMajorant liCutoffDLVMajorant
  apply Finset.sum_congr rfl
  intro m _hm
  rw [show
      ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
          liLaplaceTailNormConstant m *
            cutoffLogPowerMajorant m
              (c / Real.log (‖s‖ + 2)) / ‖s‖ =
        (‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
          liLaplaceTailNormConstant m) *
            (cutoffLogPowerMajorant m
              (c / Real.log (‖s‖ + 2)) / ‖s‖) by ring]
  rw [cutoffLogPowerMajorant_div_eq_dlvAtom
    m c ‖s‖ hc hspos]

/-- Decisive domination package: one DLV pair controls both endpoint
corrections on the high-zero tail, and both majorants are square-summable. -/
theorem exists_two_sided_cutoffCorrection_dominators
    (zeros : ZetaZeroEnumeration) (n : ℕ) :
    ∃ c T : ℝ, 0 < c ∧ 1 ≤ T ∧
      Summable (fun k ↦
        (liCutoffDLVMajorant n c ‖(zeros.zero k).val‖) ^ 2) ∧
      Summable (fun k ↦
        (liCutoffDLVMajorant n c
          ‖1 - (zeros.zero k).val‖) ^ 2) ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ k : ℕ, T ≤ |(zeros.zero k).val.im| →
          ‖liKernelCutoffCorrection n epsilon (zeros.zero k).val‖ ≤
              liCutoffDLVMajorant n c ‖(zeros.zero k).val‖ ∧
          ‖liKernelCutoffCorrection n epsilon
              (1 - (zeros.zero k).val)‖ ≤
            liCutoffDLVMajorant n c
              ‖1 - (zeros.zero k).val‖ := by
  obtain ⟨c, T, hc, hT, hgap⟩ :=
    exists_nontrivialZetaZero_two_sided_log_norm_gap
  refine ⟨c, T, hc, hT,
    zeros.summable_sq_liCutoffDLVMajorant n c,
    zeros.summable_sq_liCutoffDLVOneSubMajorant n c, ?_⟩
  intro epsilon hepsilon0 hepsilon1 k hk
  have hdirectNorm : 1 ≤ ‖(zeros.zero k).val‖ := by
    calc
      1 ≤ T := hT
      _ ≤ |(zeros.zero k).val.im| := hk
      _ ≤ ‖(zeros.zero k).val‖ :=
        Complex.abs_im_le_norm (zeros.zero k).val
  have hreflectedNorm : 1 ≤ ‖1 - (zeros.zero k).val‖ := by
    calc
      1 ≤ T := hT
      _ ≤ |(zeros.zero k).val.im| := hk
      _ = |(1 - (zeros.zero k).val).im| := by simp
      _ ≤ ‖1 - (zeros.zero k).val‖ :=
        Complex.abs_im_le_norm (1 - (zeros.zero k).val)
  obtain ⟨hdirectGap, hreflectedGap⟩ := hgap (zeros.zero k) hk
  exact ⟨
    norm_liKernelCutoffCorrection_le_dlv
      n epsilon (zeros.zero k).val c hepsilon0 hepsilon1 hc
        hdirectNorm hdirectGap,
    norm_liKernelCutoffCorrection_le_dlv
      n epsilon (1 - (zeros.zero k).val) c hepsilon0 hepsilon1 hc
        hreflectedNorm hreflectedGap⟩

theorem finite_low_zero_indices
    (zeros : ZetaZeroEnumeration) (T : ℝ) (hT : 0 ≤ T) :
    {k : ℕ | |(zeros.zero k).val.im| < T}.Finite := by
  have hnormFinite := finite_indices_norm_le_of_summable_inv_rpow
    (fun k ↦ (zeros.zero k).val)
    (fun k ↦ by
      intro hzero
      change (zeros.zero k).val = 0 at hzero
      have hpos := (zeros.zero k).re_pos
      rw [hzero] at hpos
      norm_num at hpos)
    (3 / 2) (by norm_num)
    (zeros.summable_inv_norm_rpow (3 / 2) (by norm_num))
    (T + 1) (by linarith)
  apply hnormFinite.subset
  intro k hk
  change |(zeros.zero k).val.im| < T at hk
  change ‖(zeros.zero k).val‖ ≤ T + 1
  calc
    ‖(zeros.zero k).val‖ ≤
        |(zeros.zero k).val.re| + |(zeros.zero k).val.im| :=
      Complex.norm_le_abs_re_add_abs_im (zeros.zero k).val
    _ = (zeros.zero k).val.re + |(zeros.zero k).val.im| := by
      rw [abs_of_pos (zeros.zero k).re_pos]
    _ ≤ T + 1 := by
      linarith [(zeros.zero k).re_lt_one]

private theorem summable_sq_add
    (a b : ℕ → ℝ)
    (ha : Summable (fun k ↦ (a k) ^ 2))
    (hb : Summable (fun k ↦ (b k) ^ 2)) :
    Summable (fun k ↦ (a k + b k) ^ 2) := by
  have hmajor := (ha.add hb).mul_left 2
  apply hmajor.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    nlinarith [sq_nonneg (a k - b k)]

/-- A summable DLV majorant for the full quadratic cutoff spectral term. -/
def liCutoffSpectralDLVBound
    (zeros : ZetaZeroEnumeration) (n : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  (‖liFunction n (zeros.zero k).val‖ +
      liCutoffDLVMajorant n c ‖(zeros.zero k).val‖) ^ 2 +
    (‖liFunction n (1 - (zeros.zero k).val)‖ +
      liCutoffDLVMajorant n c
        ‖1 - (zeros.zero k).val‖) ^ 2

theorem ZetaZeroEnumeration.summable_liCutoffSpectralDLVBound
    (zeros : ZetaZeroEnumeration) (n : ℕ) (c : ℝ) :
    Summable (liCutoffSpectralDLVBound zeros n c) := by
  apply Summable.add
  · exact summable_sq_add
      (fun k ↦ ‖liFunction n (zeros.zero k).val‖)
      (fun k ↦ liCutoffDLVMajorant n c ‖(zeros.zero k).val‖)
      (zeros.summable_norm_liFunction_sq n)
      (zeros.summable_sq_liCutoffDLVMajorant n c)
  · exact summable_sq_add
      (fun k ↦ ‖liFunction n (1 - (zeros.zero k).val)‖)
      (fun k ↦ liCutoffDLVMajorant n c
        ‖1 - (zeros.zero k).val‖)
      (zeros.summable_norm_liFunction_one_sub_sq n)
      (zeros.summable_sq_liCutoffDLVOneSubMajorant n c)

/-- On the DLV tail, the full cutoff spectral product is dominated by a
single summable function, uniformly in the cutoff. -/
theorem norm_spectralTerm_liKernelCutoff_le_dlvBound
    (zeros : ZetaZeroEnumeration) (n : ℕ) (c T : ℝ)
    (hc : 0 < c) (hT : 1 ≤ T)
    (hgap : ∀ rho : NontrivialZetaZero,
      T ≤ |rho.val.im| →
        c / Real.log (‖rho.val‖ + 2) ≤ rho.val.re ∧
        c / Real.log (‖1 - rho.val‖ + 2) ≤ (1 - rho.val).re)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (k : ℕ) (hk : T ≤ |(zeros.zero k).val.im|) :
    ‖spectralTerm (liKernelCutoff n epsilon) (zeros.zero k).val‖ ≤
      liCutoffSpectralDLVBound zeros n c k := by
  let rho : ℂ := (zeros.zero k).val
  have hreflectedRe : 0 < (1 - rho).re := by
    dsimp only [rho]
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(zeros.zero k).re_lt_one]
  have hdirectNorm : 1 ≤ ‖rho‖ := by
    calc
      1 ≤ T := hT
      _ ≤ |rho.im| := hk
      _ ≤ ‖rho‖ := Complex.abs_im_le_norm rho
  have hreflectedNorm : 1 ≤ ‖1 - rho‖ := by
    calc
      1 ≤ T := hT
      _ ≤ |rho.im| := hk
      _ = |(1 - rho).im| := by simp
      _ ≤ ‖1 - rho‖ := Complex.abs_im_le_norm (1 - rho)
  obtain ⟨hdirectGap, hreflectedGap⟩ := hgap (zeros.zero k) hk
  have hdirectCorrection :
      ‖liKernelCutoffCorrection n epsilon rho‖ ≤
        liCutoffDLVMajorant n c ‖rho‖ :=
    norm_liKernelCutoffCorrection_le_dlv
      n epsilon rho c hepsilon0 hepsilon1 hc hdirectNorm
        (by simpa only [rho] using hdirectGap)
  have hreflectedCorrection :
      ‖liKernelCutoffCorrection n epsilon (1 - rho)‖ ≤
        liCutoffDLVMajorant n c ‖1 - rho‖ :=
    norm_liKernelCutoffCorrection_le_dlv
      n epsilon (1 - rho) c hepsilon0 hepsilon1 hc hreflectedNorm
        (by simpa only [rho] using hreflectedGap)
  have hdirectSub :
      ‖liFunction n rho - liKernelCutoffCorrection n epsilon rho‖ ≤
        ‖liFunction n rho‖ +
          liCutoffDLVMajorant n c ‖rho‖ :=
    (norm_sub_le _ _).trans
      (add_le_add le_rfl hdirectCorrection)
  have hreflectedSub :
      ‖liFunction n (1 - rho) -
          liKernelCutoffCorrection n epsilon (1 - rho)‖ ≤
        ‖liFunction n (1 - rho)‖ +
          liCutoffDLVMajorant n c ‖1 - rho‖ :=
    (norm_sub_le _ _).trans
      (add_le_add le_rfl hreflectedCorrection)
  let A : ℝ := ‖liFunction n rho‖ +
    liCutoffDLVMajorant n c ‖rho‖
  let B : ℝ := ‖liFunction n (1 - rho)‖ +
    liCutoffDLVMajorant n c ‖1 - rho‖
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (norm_nonneg _)
      ((norm_nonneg _).trans hdirectCorrection)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (norm_nonneg _)
      ((norm_nonneg _).trans hreflectedCorrection)
  rw [spectralTerm_liKernelCutoff]
  rw [mellin_liKernelCutoff_eq_liFunction_sub_correction
    n epsilon rho hepsilon0 hepsilon1 (zeros.zero k).re_pos]
  rw [mellin_liKernelCutoff_eq_liFunction_sub_correction
    n epsilon (1 - rho) hepsilon0 hepsilon1 hreflectedRe]
  rw [norm_mul]
  change _ ≤ A ^ 2 + B ^ 2
  calc
    ‖liFunction n rho - liKernelCutoffCorrection n epsilon rho‖ *
        ‖liFunction n (1 - rho) -
          liKernelCutoffCorrection n epsilon (1 - rho)‖ ≤
        A * B := mul_le_mul hdirectSub hreflectedSub
          (norm_nonneg _) hA0
    _ ≤ A ^ 2 + B ^ 2 := by
      nlinarith [sq_nonneg (A - B), mul_nonneg hA0 hB0]

/-- Full exchange of the Li cutoff limit with the exact-multiplicity zero
sum.  The only cutoff hypotheses are positivity, support below one, and
convergence to zero. -/
theorem tsum_spectralTerm_liKernelCutoff_tendsto_pairedLi
    (zeros : ZetaZeroEnumeration) (n : ℕ)
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ j, 0 < epsilon j)
    (hepsilon1 : ∀ j, epsilon j < 1)
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto
      (fun j ↦ ∑' k : ℕ,
        spectralTerm (liKernelCutoff n (epsilon j)) (zeros.zero k).val)
      atTop
      (𝓝 (∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val)))) := by
  let f : ℕ → ℕ → ℂ := fun j k ↦
    spectralTerm (liKernelCutoff n (epsilon j)) (zeros.zero k).val
  let g : ℕ → ℂ := fun k ↦
    liFunction n (zeros.zero k).val +
      liFunction n (1 - (zeros.zero k).val)
  obtain ⟨c, T, hc, hT, hgap⟩ :=
    exists_nontrivialZetaZero_two_sided_log_norm_gap
  let bound : ℕ → ℝ := fun k ↦
    if T ≤ |(zeros.zero k).val.im| then
      liCutoffSpectralDLVBound zeros n c k
    else ‖g k‖ + 1
  have hab (k : ℕ) : Tendsto (fun j ↦ f j k) atTop (𝓝 (g k)) := by
    simpa only [f, g] using
      spectralTerm_liKernelCutoff_tendsto_li_pair
        n (zeros.zero k) epsilon (fun j ↦ (hepsilon0 j).le) hepsilon
  have hlowFinite :
      {k : ℕ | |(zeros.zero k).val.im| < T}.Finite :=
    finite_low_zero_indices zeros T (zero_le_one.trans hT)
  have heventHigh : ∀ᶠ k : ℕ in cofinite,
      T ≤ |(zeros.zero k).val.im| := by
    simpa only [Filter.eventually_cofinite, Set.mem_setOf_eq, not_le] using
      hlowFinite
  have hboundSummable : Summable bound := by
    apply (zeros.summable_liCutoffSpectralDLVBound n c).congr_cofinite
    filter_upwards [heventHigh] with k hk
    simp only [bound, if_pos hk]
  have hlowEventually : ∀ᶠ j : ℕ in atTop,
      ∀ k ∈ {k : ℕ | |(zeros.zero k).val.im| < T},
        ‖f j k‖ ≤ ‖g k‖ + 1 := by
    apply hlowFinite.eventually_all.mpr
    intro k _hk
    have hnorm := tendsto_norm.comp (hab k)
    have hevent := hnorm.eventually
      (Iio_mem_nhds (lt_add_of_pos_right ‖g k‖ zero_lt_one))
    exact hevent.mono fun j hj ↦ hj.le
  have hbound : ∀ᶠ j : ℕ in atTop, ∀ k, ‖f j k‖ ≤ bound k := by
    filter_upwards [hlowEventually] with j hj
    intro k
    by_cases hk : T ≤ |(zeros.zero k).val.im|
    · simp only [bound, if_pos hk]
      exact norm_spectralTerm_liKernelCutoff_le_dlvBound
        zeros n c T hc hT hgap (epsilon j)
          (hepsilon0 j) (hepsilon1 j) k hk
    · simp only [bound, if_neg hk]
      exact hj k (lt_of_not_ge hk)
  have htannery := tendsto_tsum_of_dominated_convergence
    hboundSummable hab hbound
  simpa only [f, g] using htannery

/-- Failure of RH therefore produces an actual positive Li cutoff whose
exact-multiplicity spectral sum has negative real part. -/
theorem not_RH_exists_liKernelCutoff_tsum_re_negative
    (zeros : ZetaZeroEnumeration) (hnot : ¬ RiemannHypothesis) :
    ∃ n : ℕ, ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < 1 ∧
        (∑' k : ℕ,
          spectralTerm (liKernelCutoff n epsilon)
            (zeros.zero k).val).re < 0 := by
  obtain ⟨n, _hn, hnegative⟩ :=
    not_RH_exists_large_liFunction_paired_tsum_re_negative
      zeros hnot 0
  let epsilon : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 2)
  have hepsilon0 (j : ℕ) : 0 < epsilon j := by
    dsimp only [epsilon]
    positivity
  have hepsilon1 (j : ℕ) : epsilon j < 1 := by
    dsimp only [epsilon]
    apply (div_lt_one (by positivity)).2
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hepsilon : Tendsto epsilon atTop (𝓝 0) := by
    have hshift :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    exact Eventually.of_forall fun j ↦ by
      dsimp only [epsilon, Function.comp_apply]
      push_cast
      ring
  have hlimit := tsum_spectralTerm_liKernelCutoff_tendsto_pairedLi
    zeros n epsilon hepsilon0 hepsilon1 hepsilon
  have hlimitRe : Tendsto
      (fun j ↦ (∑' k : ℕ,
        spectralTerm (liKernelCutoff n (epsilon j))
          (zeros.zero k).val).re)
      atTop
      (𝓝 ((∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))).re)) := by
    exact Complex.reCLM.continuous.continuousAt.tendsto.comp hlimit
  have hevent : ∀ᶠ j : ℕ in atTop,
      (∑' k : ℕ,
        spectralTerm (liKernelCutoff n (epsilon j))
          (zeros.zero k).val).re < 0 :=
    hlimitRe.eventually (Iio_mem_nhds hnegative)
  obtain ⟨j, hj⟩ := hevent.exists
  exact ⟨n, epsilon j, hepsilon0 j, hepsilon1 j, hj⟩

/-- The cutoff exchange closes the off-critical witness input expected by the
production smooth-transfer theorem. -/
theorem bombieriOffCriticalSpectralNegativity_of_liKernelCutoffTsum
    (zeros : ZetaZeroEnumeration) :
    BombieriOffCriticalSpectralNegativity zeros :=
  bombieriOffCriticalSpectralNegativity_of_liKernelCutoff zeros
    (not_RH_exists_liKernelCutoff_tsum_re_negative zeros)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
