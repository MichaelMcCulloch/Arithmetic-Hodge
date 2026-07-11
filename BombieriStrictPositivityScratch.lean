import ArithmeticHodge.Analysis.MultiplicativeWeilZeros
import ArithmeticHodge.Analysis.ZetaZeroCount
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

/-- The Mellin transform is injective on Bombieri's test space.  This is the
unconditional uniqueness input needed after a zero-density argument has shown
that the Mellin transform vanishes identically. -/
theorem mellin_eq_zero_implies_test_eq_zero_scratch
    (g : BombieriTest)
    (hzero : ∀ s : ℂ, mellin (g : ℝ → ℂ) s = 0) :
    g = 0 := by
  let φ : SchwartzMap ℝ ℂ := g.logarithmicPullbackSchwartz 0
  have hfourier :
      (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) = 0 := by
    ext y
    rw [SchwartzMap.fourier_coe]
    have hm := mellin_eq_fourier (g : ℝ → ℂ)
      (s := (2 * Real.pi * y : ℝ) * Complex.I)
    rw [hzero] at hm
    have hfreq :
        ((↑(2 * Real.pi * y) * Complex.I : ℂ).im / (2 * Real.pi)) = y := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
      field_simp [Real.pi_ne_zero]
    rw [hfreq] at hm
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, add_zero,
      neg_zero, Real.exp_zero, one_smul] at hm
    norm_num at hm
    have hraw : (fun u : ℝ ↦ g (Real.exp (-u))) = (φ : ℝ → ℂ) := by
      funext u
      simp [φ, BombieriTest.logarithmicPullback]
    rw [hraw] at hm
    exact hm.symm
  have hφ : φ = 0 := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    simpa using hfourier
  apply TestFunction.ext
  intro x
  by_cases hx : 0 < x
  · have hpoint := DFunLike.congr_fun hφ (-Real.log x)
    simp only [φ, BombieriTest.logarithmicPullbackSchwartz_apply,
      BombieriTest.logarithmicPullback, zero_mul, neg_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul, Pi.zero_apply] at hpoint
    simpa [Real.exp_log hx] using hpoint
  · have hx_support : x ∉ Function.support (g : ℝ → ℂ) := by
      intro hxmem
      have hxt : x ∈ tsupport (g : ℝ → ℂ) := subset_tsupport g hxmem
      exact hx (g.tsupport_subset hxt)
    exact not_ne_iff.mp hx_support

#print axioms mellin_eq_zero_implies_test_eq_zero_scratch

/-- The exact lower-density input needed by the elementary exponential-type
argument: the number of *distinct* xi zeros in the critical strip grows
faster than every linear function.  The current repository has no theorem of
this form; `xiZeroCount` instead weights each point by analytic multiplicity.
-/
def XiDistinctZerosSuperlinearScratch : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ T : ℝ, 1 ≤ T ∧
    C * T < (xiZerosInRectangle 0 1 (-T) T).card

/-- A nonzero entire function of finite exponential type has this linear
distinct-zero bound.  The definition isolates the Mellin-growth half of the
strictness proof from the genuinely zeta-specific density half. -/
def MellinZeroCountLinearScratch (g : BombieriTest) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (S : Finset ℂ), 1 ≤ r →
    (∀ z ∈ S, ‖z‖ ≤ r ∧ mellin (g : ℝ → ℂ) z = 0) →
    (S.card : ℝ) ≤ C * r

private theorem zeroSet_finite_scratch (F : ℂ → ℂ)
    (hFdiff : Differentiable ℂ F) (hFne : ¬ F = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
  let D := MeromorphicOn.divisor F Set.univ
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hFdiff
  have hFmeromorphic : MeromorphicOn F Set.univ := hFanalytic.meromorphicOn
  have hzeroDiv : ∀ z : ℂ, F z = 0 → 1 ≤ D z := by
    intro z hFz
    rw [show D z = (meromorphicOrderAt F z).untop₀ by
      simp [D, MeromorphicOn.divisor_apply hFmeromorphic (Set.mem_univ z)]]
    have hzAnalytic := hFanalytic z (Set.mem_univ z)
    have horderNeZero : meromorphicOrderAt F z ≠ 0 := by
      intro horder
      exact (hzAnalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp horder) hFz
    have horderPos : 0 < meromorphicOrderAt F z :=
      lt_of_le_of_ne hzAnalytic.meromorphicOrderAt_nonneg (Ne.symm horderNeZero)
    have horderNeTop : meromorphicOrderAt F z ≠ ⊤ := by
      rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hzAnalytic.meromorphicAt]
      rcases hzAnalytic.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact (hFne
          (AnalyticOnNhd.eq_of_eventuallyEq hFanalytic analyticOnNhd_const h)).elim
      · exact h
    have heq := WithTop.coe_untop₀_of_ne_top horderNeTop
    rw [← heq] at horderPos
    exact_mod_cast horderPos
  have hsupport := (Function.locallyFinsuppWithin.toClosedBall R D).finiteSupport
    (isCompact_closedBall 0 |R|)
  apply Set.Finite.subset (s := ↑hsupport.toFinset) hsupport.toFinset.finite_toSet
  intro z hz
  rw [Finset.mem_coe, hsupport.mem_toFinset, Function.mem_support]
  have hzball : z ∈ Metric.closedBall (0 : ℂ) |R| := by
    simpa [Metric.mem_closedBall, abs_of_nonneg hR] using hz.1
  rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hzball]
  exact ne_of_gt (lt_of_lt_of_le Int.zero_lt_one (hzeroDiv z hz.2))

private theorem maxModulus_le_exp_of_bound_scratch
    (F : ℂ → ℂ) (A B r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ A * Real.exp (B * ‖z‖)) :
    EntireFunction.maxModulus F r ≤ A * Real.exp (B * r) := by
  unfold EntireFunction.maxModulus
  apply ciSup_le
  intro z
  by_cases hz : ‖z‖ ≤ r
  · rw [ciSup_pos hz]
    exact (hbound z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hB)) hA)
  · rw [ciSup_neg hz, Real.sSup_empty]
    positivity

private theorem finiteZeroBound_of_expGrowth_scratch
    (F : ℂ → ℂ) (hFdiff : Differentiable ℂ F)
    (hFne : ¬ F = 0) (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ A * Real.exp (B * ‖z‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (S : Finset ℂ), 1 ≤ r →
      (∀ z ∈ S, ‖z‖ ≤ r ∧ F z = 0) → (S.card : ℝ) ≤ C * r := by
  classical
  have hexists : ∃ c : ℂ, F c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hFne
    funext z
    exact h z
  obtain ⟨c, hc⟩ := hexists
  let H : ℂ → ℂ := fun z ↦ F (z + c)
  have hHdiff : Differentiable ℂ H :=
    hFdiff.comp (differentiable_id.add (differentiable_const (c := c)))
  have hHzero : H 0 ≠ 0 := by simpa [H] using hc
  let A' : ℝ := A * Real.exp (B * ‖c‖)
  have hA' : 0 < A' := mul_pos hA (Real.exp_pos _)
  have hHbound : ∀ z : ℂ, ‖H z‖ ≤ A' * Real.exp (B * ‖z‖) := by
    intro z
    calc
      ‖H z‖ ≤ A * Real.exp (B * ‖z + c‖) := hbound (z + c)
      _ ≤ A * Real.exp (B * (‖z‖ + ‖c‖)) := by
        gcongr
        exact norm_add_le z c
      _ = A' * Real.exp (B * ‖z‖) := by
        dsimp [A']
        rw [mul_add, Real.exp_add]
        ring
  let K : ℝ := 1 / Real.log 2
  let D : ℝ := |‖H 0‖.log| + |A'.log| + 2 * B
  let C : ℝ := K * D * (1 + ‖c‖)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hK hD) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro r S hr hS
  let R : ℝ := r + ‖c‖
  have hRone : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg c]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have hfinite : Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ H z = 0} :=
    zeroSet_finite_scratch H hHdiff (by
      intro hHeq
      have hpoint := congr_fun hHeq 0
      exact hHzero (by simpa using hpoint)) R hRpos.le
  have hcardNat : S.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun z : ℂ ↦ z - c)
    · intro z hz
      change z - c ∈ hfinite.toFinset
      rw [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · dsimp [R]
        linarith [norm_sub_le z c, (hS z hz).1]
      · simpa [H] using (hS z hz).2
    · intro z hz w hw hzw
      have := congr_arg (fun q : ℂ ↦ q + c) hzw
      simpa using this
  have hcard : (S.card : ℝ) ≤ (EntireFunction.zeroCount H R : ℝ) := by
    have hcardEq : EntireFunction.zeroCount H R = hfinite.toFinset.card := by
      unfold EntireFunction.zeroCount
      exact Nat.card_eq_card_finite_toFinset hfinite
    exact_mod_cast hcardNat.trans_eq hcardEq.symm
  have hJensen := EntireFunction.zeroCount_le_logMax H hHdiff hHzero R hRpos
  have hmax := maxModulus_le_exp_of_bound_scratch H A' B (2 * R)
    hA'.le hB (mul_nonneg (by norm_num) hRpos.le) hHbound
  have hmaxPos : 0 < EntireFunction.maxModulus H (2 * R) := by
    exact (norm_pos_iff.mpr hHzero).trans_le
      (EntireFunction.norm_le_maxModulus H hHdiff 0 (2 * R) (by positivity)
        (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRpos.le))
  have hlogMax : Real.log (EntireFunction.maxModulus H (2 * R)) ≤
      Real.log A' + 2 * B * R := by
    calc
      Real.log (EntireFunction.maxModulus H (2 * R))
          ≤ Real.log (A' * Real.exp (B * (2 * R))) :=
        Real.log_le_log hmaxPos hmax
      _ = Real.log A' + 2 * B * R := by
        rw [Real.log_mul hA'.ne' (Real.exp_ne_zero _), Real.log_exp]
        ring
  have hzeroBound : (EntireFunction.zeroCount H R : ℝ) ≤ K * D * R := by
    calc
      (EntireFunction.zeroCount H R : ℝ)
          ≤ K * (Real.log (EntireFunction.maxModulus H (2 * R)) -
              Real.log ‖H 0‖) := by simpa [K] using hJensen
      _ ≤ K * ((Real.log A' + 2 * B * R) - Real.log ‖H 0‖) := by
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlogMax _) hK
      _ ≤ K * D * R := by
        have hlogH : -Real.log ‖H 0‖ ≤ |Real.log ‖H 0‖| := neg_le_abs _
        have hlogA : Real.log A' ≤ |Real.log A'| := le_abs_self _
        have hconstNonneg : 0 ≤ |Real.log ‖H 0‖| + |Real.log A'| := by positivity
        have hconstScale : |Real.log ‖H 0‖| + |Real.log A'| ≤
            (|Real.log ‖H 0‖| + |Real.log A'|) * R :=
          le_mul_of_one_le_right hconstNonneg hRone
        have hinside : (Real.log A' + 2 * B * R) - Real.log ‖H 0‖ ≤
            D * R := by
          dsimp [D]
          nlinarith
        dsimp [D]
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinside hK
  calc
    (S.card : ℝ) ≤ (EntireFunction.zeroCount H R : ℝ) := hcard
    _ ≤ K * D * R := hzeroBound
    _ ≤ C * r := by
      dsimp [C, R]
      have hr0 : 0 ≤ r := zero_le_one.trans hr
      have hKD : 0 ≤ K * D := mul_nonneg hK hD
      have hnormScale : ‖c‖ ≤ ‖c‖ * r :=
        le_mul_of_one_le_right (norm_nonneg c) hr
      have hinside : r + ‖c‖ ≤ (1 + ‖c‖) * r := by nlinarith
      calc
        K * D * (r + ‖c‖) ≤ K * D * ((1 + ‖c‖) * r) :=
          mul_le_mul_of_nonneg_left hinside hKD
        _ = K * D * (1 + ‖c‖) * r := by ring

#print axioms finiteZeroBound_of_expGrowth_scratch

private theorem bombieri_mellin_differentiable_scratch (g : BombieriTest) :
    Differentiable ℂ (mellin (g : ℝ → ℂ)) := by
  have hlocal : LocallyIntegrableOn (g : ℝ → ℂ) (Ioi 0) :=
    g.contDiff.continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0)
  have hzeroNear : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Ioi 0))
      (g : ℝ → ℂ) 0 := by
    have hnot : (0 : ℝ) ∉ tsupport (g : ℝ → ℂ) := by
      intro hmem
      have hpos := g.tsupport_subset hmem
      change (0 : ℝ) < 0 at hpos
      exact (lt_irrefl 0) hpos
    exact ((notMem_tsupport_iff_eventuallyEq.mp hnot).filter_mono
      nhdsWithin_le_nhds)
  obtain ⟨R, hR⟩ := g.hasCompactSupport.isBounded.subset_closedBall (0 : ℝ)
  have hzeroTop : Filter.EventuallyEq atTop (g : ℝ → ℂ) 0 := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨R + 1, ?_⟩
    intro x hx
    by_contra hne
    have hxt : x ∈ tsupport (g : ℝ → ℂ) :=
      subset_tsupport g (Function.mem_support.mpr hne)
    have hball := hR hxt
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
    linarith [le_abs_self x]
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow
      (a := s.re + 1) (b := s.re - 1) hlocal
      (hzeroTop.isBigO.trans (Asymptotics.isBigO_zero
        (fun t : ℝ ↦ t ^ (-(s.re + 1))) atTop)) (by linarith)
      (hzeroNear.isBigO.trans (Asymptotics.isBigO_zero
        (fun t : ℝ ↦ t ^ (-(s.re - 1))) (nhdsWithin 0 (Ioi 0)))) (by linarith)

#print axioms bombieri_mellin_differentiable_scratch

/-- Conditional strictness bridge with no hidden analytic assumptions.  A
superlinear supply of distinct zeta zeros contradicts the linear zero count
of a nonzero Mellin transform unless at least one spectral value is nonzero.
-/
theorem exists_mellin_ne_zero_of_distinct_density_scratch
    (zeros : ZetaZeroEnumeration)
    (hdensity : XiDistinctZerosSuperlinearScratch)
    (g : BombieriTest) (hg : g ≠ 0)
    (hlinear : MellinZeroCountLinearScratch g) :
    ∃ n : ℕ, mellin (g : ℝ → ℂ) (zeros.zero n).val ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨C, hC, hlinear⟩ := hlinear
  obtain ⟨T, hT, hdense⟩ := hdensity (2 * C) (mul_nonneg (by norm_num) hC)
  have hzeros : ∀ z ∈ xiZerosInRectangle 0 1 (-T) T,
      ‖z‖ ≤ T + 1 ∧ mellin (g : ℝ → ℂ) z = 0 := by
    intro z hz
    have hzdata := (mem_xiZerosInRectangle_iff 0 1 (-T) T z).mp hz
    refine ⟨norm_le_height_add_one_of_mem_xiZeroRectangle (by linarith) hzdata.1, ?_⟩
    have hre := xiFunction_zero_re hzdata.2
    let ρ : NontrivialZetaZero :=
      ⟨z, (xiFunction_zero_iff hre.1 hre.2).mp hzdata.2, hre.1, hre.2⟩
    obtain ⟨n, hn⟩ := zeros.exhaustive ρ
    simpa [ρ, hn] using hnone n
  have hcount := hlinear (T + 1) (xiZerosInRectangle 0 1 (-T) T)
    (by linarith) hzeros
  have hscale : C * (T + 1) ≤ (2 * C) * T := by
    nlinarith
  linarith

#print axioms exists_mellin_ne_zero_of_distinct_density_scratch

end ArithmeticHodge.Analysis.MultiplicativeWeil
