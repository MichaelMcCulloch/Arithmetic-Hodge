/-
  Enumeration-independent zero counting for the Riemann xi function.

  The divisor of an entire function records distinct zeros together with their
  analytic multiplicities.  Restricting the xi divisor to a compact rectangle
  therefore gives a finite, enumeration-independent zero count suitable for a
  future Riemann--von Mangoldt theorem.
-/

import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Analysis.Meromorphic.NormalForm

open Complex Filter Topology

namespace ArithmeticHodge.Analysis

/-- The closed axis-parallel complex rectangle
`[sigmaLower, sigmaUpper] x [heightLower, heightUpper]`. -/
def xiZeroRectangle (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : Set ℂ :=
  Set.Icc sigmaLower sigmaUpper ×ℂ Set.Icc heightLower heightUpper

theorem isCompact_xiZeroRectangle (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    IsCompact (xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper) := by
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- The global meromorphic divisor of xi.  Since xi is entire, this divisor is
pointwise nonnegative and its values are zero multiplicities. -/
noncomputable def xiDivisor : Function.locallyFinsupp ℂ ℤ :=
  MeromorphicOn.divisor xiFunction Set.univ

private theorem analyticOnNhd_xiFunction_univ :
    AnalyticOnNhd ℂ xiFunction Set.univ :=
  differentiable_xiFunction.differentiableOn.analyticOnNhd isOpen_univ

theorem xiDivisor_nonneg (z : ℂ) : 0 ≤ xiDivisor z := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg analyticOnNhd_xiFunction_univ z

private theorem xiFunction_meromorphicOrderAt_ne_top (z : ℂ) :
    meromorphicOrderAt xiFunction z ≠ ⊤ := by
  have hnormal0 :=
    (analyticOnNhd_xiFunction_univ 0 (Set.mem_univ 0)).meromorphicNFAt
  have horder0 : meromorphicOrderAt xiFunction 0 = 0 :=
    hnormal0.meromorphicOrderAt_eq_zero_iff.mpr (by
      rw [xiFunction_zero_val]
      norm_num)
  have hfinite0 : meromorphicOrderAt xiFunction 0 ≠ ⊤ := by
    rw [horder0]
    exact WithTop.zero_ne_top
  exact analyticOnNhd_xiFunction_univ.meromorphicOn
    |>.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 0) (Set.mem_univ z) hfinite0

/-- The support of the xi divisor is exactly the zero set of xi. -/
theorem mem_xiDivisor_support_iff (z : ℂ) :
    z ∈ Function.support xiDivisor ↔ xiFunction z = 0 := by
  have hzeroSet := analyticOnNhd_xiFunction_univ.meromorphicNFOn
    |>.zero_set_eq_divisor_support (fun z => xiFunction_meromorphicOrderAt_ne_top z)
  have hz := Set.ext_iff.mp hzeroSet z
  simpa [xiDivisor] using hz.symm

/-- The analytic multiplicity of `z` as a zero of xi. -/
noncomputable def xiZeroMultiplicity (z : ℂ) : ℕ :=
  (xiDivisor z).toNat

/-- Positive multiplicity is equivalent to vanishing of xi. -/
theorem xiZeroMultiplicity_pos_iff (z : ℂ) :
    0 < xiZeroMultiplicity z ↔ xiFunction z = 0 := by
  constructor
  · intro hpos
    apply (mem_xiDivisor_support_iff z).mp
    rw [Function.mem_support]
    intro hzero
    simp [xiZeroMultiplicity, hzero] at hpos
  · intro hxi
    have hdiv_ne : xiDivisor z ≠ 0 := by
      simpa [Function.mem_support] using (mem_xiDivisor_support_iff z).mpr hxi
    have hnat_ne : xiZeroMultiplicity z ≠ 0 := by
      intro hzero
      have hle : xiDivisor z ≤ 0 := Int.toNat_eq_zero.mp hzero
      exact hdiv_ne (le_antisymm hle (xiDivisor_nonneg z))
    exact Nat.pos_of_ne_zero hnat_ne

/-- Multiplicity weight restricted to a compact rectangle. -/
noncomputable def xiZeroWeight
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) : ℕ := by
  classical
  exact if z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper then
      xiZeroMultiplicity z
    else
      0

/-- The restricted multiplicity weight has finite support. -/
theorem xiZeroWeight_hasFiniteSupport
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    Function.HasFiniteSupport
      (xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper) := by
  let rectangle := xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper
  have hfinite :
      (rectangle ∩ Function.support (xiDivisor : ℂ → ℤ)).Finite :=
    xiDivisor.locallyFiniteSupport.finite_inter_support_of_isCompact
      (isCompact_xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper)
  apply hfinite.subset
  intro z hz
  have hweight_ne :
      xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ≠ 0 := hz
  have hzrect : z ∈ rectangle := by
    by_contra hznot
    exact hweight_ne (by simp [xiZeroWeight, rectangle, hznot])
  have hmult_ne : xiZeroMultiplicity z ≠ 0 := by
    simpa [xiZeroWeight, rectangle, hzrect] using hweight_ne
  have hdiv_ne : xiDivisor z ≠ 0 := by
    intro hzero
    exact hmult_ne (by simp [xiZeroMultiplicity, hzero])
  exact ⟨hzrect, hdiv_ne⟩

/-- A multiplicity-weighted, enumeration-independent xi zero count in a
closed rectangle. -/
noncomputable def xiZeroCount
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z

/-- A point contributes positively precisely when it lies in the rectangle
and is a zero of xi. -/
theorem xiZeroWeight_pos_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    0 < xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper ∧
        xiFunction z = 0 := by
  by_cases hz : z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper
  · simp [xiZeroWeight, hz, xiZeroMultiplicity_pos_iff]
  · simp [xiZeroWeight, hz]

/-- The finite set of distinct xi zeros in the rectangle.  Multiplicity is
carried separately by `xiZeroMultiplicity`. -/
noncomputable def xiZerosInRectangle
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : Finset ℂ :=
  (xiZeroWeight_hasFiniteSupport sigmaLower sigmaUpper heightLower heightUpper).toFinset

theorem mem_xiZerosInRectangle_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper ∧
        xiFunction z = 0 := by
  rw [xiZerosInRectangle, Set.Finite.mem_toFinset]
  change xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ≠ 0 ↔ _
  rw [← Nat.pos_iff_ne_zero, xiZeroWeight_pos_iff]

/-- The `finsum` count is an ordinary finite sum of analytic multiplicities
over the distinct zeros in the rectangle. -/
theorem xiZeroCount_eq_sum
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    xiZeroCount sigmaLower sigmaUpper heightLower heightUpper =
      ∑ z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
        xiZeroMultiplicity z := by
  classical
  rw [xiZeroCount, finsum_eq_sum _
    (xiZeroWeight_hasFiniteSupport sigmaLower sigmaUpper heightLower heightUpper)]
  apply Finset.sum_congr rfl
  intro z hz
  have hzrect : z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper :=
    (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper heightLower heightUpper z).mp hz |>.1
  simp [xiZeroWeight, hzrect]

/-- The affine involution appearing in the xi functional equation. -/
def complexOneSubEquiv : ℂ ≃ ℂ where
  toFun z := 1 - z
  invFun z := 1 - z
  left_inv z := by ring
  right_inv z := by ring

/-- The functional equation preserves analytic zero multiplicity. -/
theorem xiDivisor_one_sub (z : ℂ) : xiDivisor (1 - z) = xiDivisor z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hgderiv : deriv (fun w : ℂ => 1 - w) z ≠ 0 := by
    change deriv ((fun _ : ℂ => (1 : ℂ)) - id) z ≠ 0
    rw [((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := xiFunction) hg hgderiv
  have hfun : xiFunction ∘ (fun w : ℂ => 1 - w) = xiFunction := by
    funext w
    exact xiFunction_one_sub w
  have horder :
      meromorphicOrderAt xiFunction (1 - z) = meromorphicOrderAt xiFunction z := by
    rw [← hcomp, hfun]
  rw [xiDivisor,
    MeromorphicOn.divisor_apply analyticOnNhd_xiFunction_univ.meromorphicOn (Set.mem_univ _),
    MeromorphicOn.divisor_apply analyticOnNhd_xiFunction_univ.meromorphicOn (Set.mem_univ _),
    horder]

theorem xiZeroMultiplicity_one_sub (z : ℂ) :
    xiZeroMultiplicity (1 - z) = xiZeroMultiplicity z := by
  simp [xiZeroMultiplicity, xiDivisor_one_sub]

theorem one_sub_mem_xiZeroRectangle_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    1 - z ∈ xiZeroRectangle (1 - sigmaUpper) (1 - sigmaLower)
        (-heightUpper) (-heightLower) ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper := by
  simp only [xiZeroRectangle, mem_reProdIm, Set.mem_Icc, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem xiZeroWeight_one_sub
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
        (complexOneSubEquiv z) =
      xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z := by
  classical
  change xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
      (1 - z) = xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z
  simp only [xiZeroWeight]
  rw [one_sub_mem_xiZeroRectangle_iff]
  split_ifs with hz
  · exact xiZeroMultiplicity_one_sub z
  · rfl

/-- Rectangle counts are invariant under the functional-equation symmetry
`z |-> 1 - z`, including analytic multiplicity. -/
theorem xiZeroCount_one_sub
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    xiZeroCount (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower) =
      xiZeroCount sigmaLower sigmaUpper heightLower heightUpper := by
  calc
    xiZeroCount (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower) =
        ∑ᶠ z : ℂ,
          xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
            (complexOneSubEquiv z) := by
              rw [xiZeroCount]
              exact (finsum_comp_equiv complexOneSubEquiv).symm
    _ = xiZeroCount sigmaLower sigmaUpper heightLower heightUpper := by
      rw [xiZeroCount]
      apply finsum_congr
      exact xiZeroWeight_one_sub sigmaLower sigmaUpper heightLower heightUpper

/-- Functional-equation symmetry exchanges the upper and lower halves of the
critical strip, with analytic multiplicities preserved. -/
theorem xiCriticalStripZeroCount_lower_eq_upper (T : ℝ) :
    xiZeroCount 0 1 (-T) 0 = xiZeroCount 0 1 0 T := by
  simpa using xiZeroCount_one_sub 0 1 0 T

/-! ### RH as a statement about the xi divisor -/

/-- Every point of positive xi divisor multiplicity lies on the critical
line.  This is an enumeration-independent formulation of RH. -/
def XiDivisorOnCriticalLine : Prop :=
  ∀ z : ℂ, 0 < xiZeroMultiplicity z → z.re = 1 / 2

theorem xiDivisorOnCriticalLine_iff_RH :
    XiDivisorOnCriticalLine ↔ RiemannHypothesis := by
  constructor
  · intro hline s hs_zero hs_not_trivial hs_ne_one
    have hre := nontrivial_zeta_zero_re s hs_zero hs_not_trivial hs_ne_one
    apply hline s
    exact (xiZeroMultiplicity_pos_iff s).mpr
      ((xiFunction_zero_iff hre.1 hre.2).mpr hs_zero)
  · intro hRH z hmult
    have hxi := (xiZeroMultiplicity_pos_iff z).mp hmult
    have hre := xiFunction_zero_re hxi
    have hzeta := (xiFunction_zero_iff hre.1 hre.2).mp hxi
    apply hRH z hzeta
    · rintro ⟨n, hn⟩
      rw [hn] at hre
      have htriv_re : (-2 * ((n : ℂ) + 1)).re =
          -2 * ((n : ℝ) + 1) := by
        simp [Complex.add_re, Complex.mul_re, Complex.neg_re,
          Complex.one_re, Complex.one_im]
      rw [htriv_re] at hre
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hz_one
      rw [hz_one] at hre
      norm_num at hre

/-! ### Principal logarithms do not encode unwrapped contour phase -/

/-- The principal logarithm cannot satisfy the unwrapped Stirling-phase
identity used by the legacy prefix-count proof.  At the concrete height
`T = 100`, the proposed right-hand side is greater than `π`, whereas
`Complex.log_im_le_pi` bounds the left-hand side by `π` for every input. -/
theorem no_principal_log_Gamma_stirling_phase_at_100 :
    ¬ ∃ ε : ℝ, |ε| ≤ 1 ∧
      (Complex.log (Complex.Gamma
        (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))).im =
        (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
          (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
  rintro ⟨ε, hε, heq⟩
  have hexp_three_lt_fifty : Real.exp 3 < 50 := by
    calc
      Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ < 3 ^ (3 : ℕ) := by
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ < 50 := by norm_num
  have hlog_fifty : 3 < Real.log 50 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 50)).mpr
      hexp_three_lt_fifty
  have hε_lower : -1 ≤ ε := neg_le_of_abs_le hε
  have hpi_upper : Real.pi < 4 := Real.pi_lt_four
  have hphase_gt_pi : Real.pi <
      (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
        (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
    norm_num at hlog_fifty ⊢
    nlinarith
  have hprincipal := Complex.log_im_le_pi
    (Complex.Gamma
      (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))
  rw [heq] at hprincipal
  exact (not_lt_of_ge hprincipal) hphase_gt_pi

end ArithmeticHodge.Analysis
