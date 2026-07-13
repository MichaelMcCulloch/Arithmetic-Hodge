import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeDomination

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped SchwartzMap

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeOverlap

noncomputable section

open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoParityRealification
open YoshidaFactorTwoPrimeCorrelationSymbol
open YoshidaFactorTwoPrimeDomination

/-!
# Disjoint overlap at the retained factor-two prime lag

A ratio-two seed has logarithmic pullback supported in an interval of length
at most `log 2`.  At the retained `p = 3` lag `log (3 / 2)`, the two end
pieces participating in the autocorrelation are disjoint.  This gives the
structural bounds

`0 <= C(0) + 2 C(log (3 / 2))` and
`0 <= C(0) - 2 C(log (3 / 2))`.

Consequently the real two-prime symbol is a positive combination of these
two folded overlap energies.  No positivity of the local critical form is
used here.
-/

private theorem crossCorrelation_norm_le_half_interval_mass
    (F : SchwartzMap ℝ ℂ) {ℓ r s : ℝ}
    (hℓr : ℓ ≤ r) (hwidth : r - ℓ ≤ 2 * s)
    (hsupport : ∀ x ∉ Set.Icc ℓ r, F x = 0) :
    2 * ‖crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) s‖ ≤
      ∫ x : ℝ in ℓ..r, Complex.normSq (F x) := by
  let p : ℝ → ℂ := fun x ↦ starRingEnd ℂ (F x) * F (s + x)
  let q : ℝ → ℝ := fun x ↦ Complex.normSq (F x)
  by_cases hoverlap : s ≤ r - ℓ
  · have hlohi : ℓ ≤ r - s := by linarith
    have hmid : r - s ≤ ℓ + s := by linarith
    have hright : ℓ + s ≤ r := by linarith
    have hpzero : ∀ x ∉ Set.Icc ℓ (r - s), p x = 0 := by
      intro x hx
      have hFx : F x = 0 ∨ F (s + x) = 0 := by
        by_contra hboth
        push_neg at hboth
        have hxmem : x ∈ Set.Icc ℓ r := by
          by_contra hxout
          exact hboth.1 (hsupport x hxout)
        have hsxmem : s + x ∈ Set.Icc ℓ r := by
          by_contra hsxout
          exact hboth.2 (hsupport (s + x) hsxout)
        apply hx
        exact ⟨hxmem.1, by linarith [hsxmem.2]⟩
      rcases hFx with hFx | hFsx
      · simp [p, hFx]
      · simp [p, hFsx]
    have hpcont : Continuous p := by
      dsimp only [p]
      exact F.continuous.star.mul
        (F.continuous.comp (continuous_const.add continuous_id))
    have hpint : Integrable p :=
      hpcont.continuousOn.integrableOn_Icc
        |>.integrable_of_forall_notMem_eq_zero hpzero
    have hqcont : Continuous q := by
      exact Complex.continuous_normSq.comp F.continuous
    have hqnonneg : ∀ x, 0 ≤ q x := fun x ↦ Complex.normSq_nonneg (F x)
    have hqleft : IntervalIntegrable q volume ℓ (r - s) :=
      hqcont.intervalIntegrable _ _
    have hqmid : IntervalIntegrable q volume (r - s) (ℓ + s) :=
      hqcont.intervalIntegrable _ _
    have hqright : IntervalIntegrable q volume (ℓ + s) r :=
      hqcont.intervalIntegrable _ _
    have hqshift : IntervalIntegrable (fun x : ℝ ↦ q (s + x)) volume
        ℓ (r - s) := by
      exact (hqcont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    have hcorr :
        crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) s =
          ∫ x : ℝ in ℓ..r - s, p x := by
      rw [crossCorrelation_apply]
      change (∫ x : ℝ, p x) = _
      rw [intervalIntegral.integral_of_le hlohi,
        ← integral_Icc_eq_integral_Ioc]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hpzero).symm
    rw [hcorr]
    calc
      2 * ‖∫ x : ℝ in ℓ..r - s, p x‖ ≤
          2 * ∫ x : ℝ in ℓ..r - s, ‖p x‖ := by
        gcongr
        exact intervalIntegral.norm_integral_le_integral_norm hlohi
      _ = ∫ x : ℝ in ℓ..r - s, 2 * ‖p x‖ := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x : ℝ in ℓ..r - s, q x + q (s + x) := by
        apply intervalIntegral.integral_mono_on hlohi
        · exact (hpint.norm.const_mul 2).intervalIntegrable
        · exact hqleft.add hqshift
        · intro x _hx
          dsimp only [p, q]
          rw [norm_mul]
          have hstar : ‖starRingEnd ℂ (F x)‖ = ‖F x‖ := by
            simpa only [starRingEnd_apply] using (RCLike.norm_conj (F x))
          rw [hstar, Complex.normSq_eq_norm_sq,
            Complex.normSq_eq_norm_sq]
          nlinarith [sq_nonneg (‖F x‖ - ‖F (s + x)‖)]
      _ = (∫ x : ℝ in ℓ..r - s, q x) +
          ∫ x : ℝ in ℓ + s..r, q x := by
        rw [intervalIntegral.integral_add hqleft hqshift,
          intervalIntegral.integral_comp_add_left]
        congr 2 <;> ring
      _ ≤ ((∫ x : ℝ in ℓ..r - s, q x) +
            ∫ x : ℝ in r - s..ℓ + s, q x) +
          ∫ x : ℝ in ℓ + s..r, q x := by
        have hnonneg : 0 ≤ ∫ x : ℝ in r - s..ℓ + s, q x :=
          intervalIntegral.integral_nonneg hmid fun x _hx ↦ hqnonneg x
        linarith
      _ = ∫ x : ℝ in ℓ..r, q x := by
        rw [intervalIntegral.integral_add_adjacent_intervals hqleft hqmid,
          intervalIntegral.integral_add_adjacent_intervals
            (hqleft.trans hqmid) hqright]
  · have hpzero : ∀ x, p x = 0 := by
      intro x
      have hFx : F x = 0 ∨ F (s + x) = 0 := by
        by_contra hboth
        push_neg at hboth
        have hxmem : x ∈ Set.Icc ℓ r := by
          by_contra hxout
          exact hboth.1 (hsupport x hxout)
        have hsxmem : s + x ∈ Set.Icc ℓ r := by
          by_contra hsxout
          exact hboth.2 (hsupport (s + x) hsxout)
        exfalso
        apply hoverlap
        linarith [hxmem.1, hsxmem.2]
      rcases hFx with hFx | hFsx
      · simp [p, hFx]
      · simp [p, hFsx]
    rw [crossCorrelation_apply]
    change 2 * ‖∫ x : ℝ, p x‖ ≤ _
    simp only [hpzero, integral_zero, norm_zero, mul_zero]
    exact intervalIntegral.integral_nonneg hℓr fun x _hx ↦
      Complex.normSq_nonneg (F x)

private theorem crossCorrelation_zero_re_eq_interval_mass
    (F : SchwartzMap ℝ ℂ) {ℓ r : ℝ} (hℓr : ℓ ≤ r)
    (hsupport : ∀ x ∉ Set.Icc ℓ r, F x = 0) :
    (crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) 0).re =
      ∫ x : ℝ in ℓ..r, Complex.normSq (F x) := by
  let q : ℝ → ℝ := fun x ↦ Complex.normSq (F x)
  have hqzero : ∀ x ∉ Set.Icc ℓ r, q x = 0 := by
    intro x hx
    simp [q, hsupport x hx]
  have hqcont : Continuous q := Complex.continuous_normSq.comp F.continuous
  have hqint : Integrable q :=
    hqcont.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero hqzero
  rw [crossCorrelation_apply]
  change (∫ x : ℝ, starRingEnd ℂ (F x) * F (0 + x)).re = _
  simp only [zero_add, ← Complex.normSq_eq_conj_mul_self]
  rw [integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  change (∫ x : ℝ, q x) = _
  rw [intervalIntegral.integral_of_le hℓr,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hqzero).symm

private theorem factorTwoPrimeShift_geometry :
    0 ≤ factorTwoLogLength / 2 ∧
      factorTwoLogLength / 2 ≤ factorTwoPrimeShift ∧
      factorTwoPrimeShift ≤ 2 * (factorTwoLogLength / 2) := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2lt : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hlog := Real.strictMonoOn_log hsqrt2pos (by norm_num) hsqrt2lt
  have hleft : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hright : Real.log (3 / 2 : ℝ) ≤ Real.log 2 := by
    exact Real.log_le_log (by norm_num) (by norm_num)
  unfold factorTwoLogLength factorTwoPrimeShift
  rw [hleft] at hlog
  refine ⟨by positivity, hlog.le, ?_⟩
  calc
    Real.log (3 / 2 : ℝ) ≤ Real.log 2 := hright
    _ = 2 * (Real.log 2 / 2) := by ring

/-- At the retained `p = 3` lag, the autocorrelation of a ratio-two seed is
at most half of its zero-lag mass.  This two-disjoint-cells estimate does not
use fixedness or any local-form positivity. -/
theorem two_mul_norm_factorTwoSelfCorrelation_primeShift_le_zero_re
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    2 * ‖factorTwoSelfCorrelation g factorTwoPrimeShift‖ ≤
      (factorTwoSelfCorrelation g 0).re := by
  let F : SchwartzMap ℝ ℂ :=
    g.logarithmicPullbackSchwartz (1 / 2)
  have hb : 0 < b := ha.trans_le hab
  have hℓr : -Real.log b ≤ -Real.log a := by
    have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    linarith
  have hlogRatio : Real.log (b / a) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hb ha) hratio
  rw [Real.log_div hb.ne' ha.ne'] at hlogRatio
  have hwidth0 :
      -Real.log a - -Real.log b ≤ factorTwoLogLength := by
    unfold factorTwoLogLength
    linarith
  have hlengthShift :
      factorTwoLogLength ≤ 2 * factorTwoPrimeShift := by
    linarith [factorTwoPrimeShift_geometry.2.1]
  have hwidth :
      -Real.log a - -Real.log b ≤ 2 * factorTwoPrimeShift :=
    hwidth0.trans hlengthShift
  have hFsupport :
      ∀ x ∉ Set.Icc (-Real.log b) (-Real.log a), F x = 0 := by
    intro x hx
    exact logarithmicPullbackSchwartz_eq_zero_outside
      g ha hsupport hx
  have hnorm := crossCorrelation_norm_le_half_interval_mass
    F hℓr hwidth hFsupport
  have hzero := crossCorrelation_zero_re_eq_interval_mass
    F hℓr hFsupport
  change
    2 * ‖crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ)
      factorTwoPrimeShift‖ ≤
      (crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) 0).re
  calc
    2 * ‖crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ)
        factorTwoPrimeShift‖ ≤
        ∫ x : ℝ in -Real.log b..-Real.log a,
          Complex.normSq (F x) := hnorm
    _ = (crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) 0).re :=
      hzero.symm

/-- The even folded overlap energy at the retained `p = 3` lag. -/
def factorTwoPrimeOverlapPlusEnergy (g : BombieriTest) : ℝ :=
  (factorTwoSelfCorrelation g 0).re +
    2 * (factorTwoSelfCorrelation g factorTwoPrimeShift).re

/-- The odd folded overlap energy at the retained `p = 3` lag. -/
def factorTwoPrimeOverlapMinusEnergy (g : BombieriTest) : ℝ :=
  (factorTwoSelfCorrelation g 0).re -
    2 * (factorTwoSelfCorrelation g factorTwoPrimeShift).re

theorem factorTwoPrimeOverlapPlusEnergy_nonneg
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoPrimeOverlapPlusEnergy g := by
  have hnorm :=
    two_mul_norm_factorTwoSelfCorrelation_primeShift_le_zero_re
      g ha hab hsupport hratio
  have hre :
      -‖factorTwoSelfCorrelation g factorTwoPrimeShift‖ ≤
        (factorTwoSelfCorrelation g factorTwoPrimeShift).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  unfold factorTwoPrimeOverlapPlusEnergy
  linarith

theorem factorTwoPrimeOverlapMinusEnergy_nonneg
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoPrimeOverlapMinusEnergy g := by
  have hnorm :=
    two_mul_norm_factorTwoSelfCorrelation_primeShift_le_zero_re
      g ha hab hsupport hratio
  have hre :
      (factorTwoSelfCorrelation g factorTwoPrimeShift).re ≤
        ‖factorTwoSelfCorrelation g factorTwoPrimeShift‖ :=
    (abs_le.mp (Complex.abs_re_le_norm _)).2
  unfold factorTwoPrimeOverlapMinusEnergy
  linarith

private theorem factorTwoPrimeThreeWeight_lt_two_mul_twoWeight :
    Real.log 3 / Real.sqrt 3 <
      2 * (Real.log 2 / Real.sqrt 2) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt3pos : 0 < Real.sqrt (3 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt23 : Real.sqrt (2 : ℝ) < Real.sqrt (3 : ℝ) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlog3lt : Real.log (3 : ℝ) < 2 * Real.log (2 : ℝ) := by
    calc
      Real.log (3 : ℝ) < Real.log (4 : ℝ) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = 2 * Real.log (2 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
        ring
  calc
    Real.log 3 / Real.sqrt 3 <
        (2 * Real.log 2) / Real.sqrt 2 := by
      rw [div_lt_div_iff₀ hsqrt3pos hsqrt2pos]
      calc
        Real.log 3 * Real.sqrt 2 <
            (2 * Real.log 2) * Real.sqrt 2 :=
          mul_lt_mul_of_pos_right hlog3lt hsqrt2pos
        _ < (2 * Real.log 2) * Real.sqrt 3 :=
          mul_lt_mul_of_pos_left hsqrt23
            (mul_pos (by norm_num) hlog2pos)
    _ = 2 * (Real.log 2 / Real.sqrt 2) := by ring

private theorem factorTwoPrimeOverlapPlusCoefficient_pos :
    0 <
      (2 * (Real.log 2 / Real.sqrt 2) +
        Real.log 3 / Real.sqrt 3) / 4 := by
  have htwo : 0 < Real.log 2 / Real.sqrt 2 := by positivity
  have hthree : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  positivity

private theorem factorTwoPrimeOverlapMinusCoefficient_pos :
    0 <
      (2 * (Real.log 2 / Real.sqrt 2) -
        Real.log 3 / Real.sqrt 3) / 4 := by
  exact div_pos
    (sub_pos.2 factorTwoPrimeThreeWeight_lt_two_mul_twoWeight)
    (by norm_num)

/-- The exact positive folded-overlap combination carried by the two retained
prime atoms. -/
def factorTwoPrimeWeightedOverlap (g : BombieriTest) : ℝ :=
  ((2 * (Real.log 2 / Real.sqrt 2) +
      Real.log 3 / Real.sqrt 3) / 4) *
      factorTwoPrimeOverlapPlusEnergy g +
    ((2 * (Real.log 2 / Real.sqrt 2) -
      Real.log 3 / Real.sqrt 3) / 4) *
      factorTwoPrimeOverlapMinusEnergy g

/-- The real two-prime cross symbol is exactly its folded-overlap energy. -/
theorem factorTwoPrimeCrossSymbol_re_eq_weightedOverlap
    (g : BombieriTest) :
    (factorTwoPrimeCrossSymbol g).re =
      factorTwoPrimeWeightedOverlap g := by
  rw [factorTwoPrimeCrossSymbol_eq_correlation]
  unfold factorTwoPrimeCorrelationSymbol factorTwoPrimeWeightedOverlap
    factorTwoPrimeOverlapPlusEnergy factorTwoPrimeOverlapMinusEnergy
    factorTwoPrimeShift
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem factorTwoPrimeWeightedOverlap_nonneg
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoPrimeWeightedOverlap g := by
  unfold factorTwoPrimeWeightedOverlap
  exact add_nonneg
    (mul_nonneg factorTwoPrimeOverlapPlusCoefficient_pos.le
      (factorTwoPrimeOverlapPlusEnergy_nonneg
        g ha hab hsupport hratio))
    (mul_nonneg factorTwoPrimeOverlapMinusCoefficient_pos.le
      (factorTwoPrimeOverlapMinusEnergy_nonneg
        g ha hab hsupport hratio))

/-- The retained real two-prime symbol is nonnegative on every ratio-two
seed, without a fixedness assumption. -/
theorem factorTwoPrimeCrossSymbol_re_nonneg
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ (factorTwoPrimeCrossSymbol g).re := by
  rw [factorTwoPrimeCrossSymbol_re_eq_weightedOverlap]
  exact factorTwoPrimeWeightedOverlap_nonneg
    g ha hab hsupport hratio

/-- The lower scalar-mass envelope obtained from the disjoint-overlap bound. -/
theorem factorTwoPrimeCrossSymbol_re_lower_mass_bound
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (Real.log 2 / Real.sqrt 2 -
        (Real.log 3 / Real.sqrt 3) / 2) *
        (factorTwoSelfCorrelation g 0).re ≤
      (factorTwoPrimeCrossSymbol g).re := by
  rw [factorTwoPrimeCrossSymbol_re_eq_weightedOverlap]
  have hplus := factorTwoPrimeOverlapPlusEnergy_nonneg
    g ha hab hsupport hratio
  have hterm :
      0 ≤ ((Real.log 3 / Real.sqrt 3) / 2) *
        factorTwoPrimeOverlapPlusEnergy g :=
    mul_nonneg (by positivity) hplus
  calc
    (Real.log 2 / Real.sqrt 2 -
        (Real.log 3 / Real.sqrt 3) / 2) *
        (factorTwoSelfCorrelation g 0).re ≤
      (Real.log 2 / Real.sqrt 2 -
          (Real.log 3 / Real.sqrt 3) / 2) *
          (factorTwoSelfCorrelation g 0).re +
        ((Real.log 3 / Real.sqrt 3) / 2) *
          factorTwoPrimeOverlapPlusEnergy g :=
      le_add_of_nonneg_right hterm
    _ = factorTwoPrimeWeightedOverlap g := by
      unfold factorTwoPrimeWeightedOverlap factorTwoPrimeOverlapPlusEnergy
        factorTwoPrimeOverlapMinusEnergy
      ring

/-- The upper scalar-mass envelope obtained from the disjoint-overlap bound. -/
theorem factorTwoPrimeCrossSymbol_re_upper_mass_bound
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (factorTwoPrimeCrossSymbol g).re ≤
      (Real.log 2 / Real.sqrt 2 +
        (Real.log 3 / Real.sqrt 3) / 2) *
        (factorTwoSelfCorrelation g 0).re := by
  rw [factorTwoPrimeCrossSymbol_re_eq_weightedOverlap]
  have hminus := factorTwoPrimeOverlapMinusEnergy_nonneg
    g ha hab hsupport hratio
  have hterm :
      0 ≤ ((Real.log 3 / Real.sqrt 3) / 2) *
        factorTwoPrimeOverlapMinusEnergy g :=
    mul_nonneg (by positivity) hminus
  calc
    factorTwoPrimeWeightedOverlap g =
        (Real.log 2 / Real.sqrt 2 +
            (Real.log 3 / Real.sqrt 3) / 2) *
            (factorTwoSelfCorrelation g 0).re -
          ((Real.log 3 / Real.sqrt 3) / 2) *
            factorTwoPrimeOverlapMinusEnergy g := by
      unfold factorTwoPrimeWeightedOverlap factorTwoPrimeOverlapPlusEnergy
        factorTwoPrimeOverlapMinusEnergy
      ring
    _ ≤ (Real.log 2 / Real.sqrt 2 +
          (Real.log 3 / Real.sqrt 3) / 2) *
          (factorTwoSelfCorrelation g 0).re :=
      sub_le_self _ hterm

/-- The antisymmetric endpoint is the exact local self-form plus the positive
folded two-prime overlap. -/
theorem factorTwoDiagonalCoordinate_sub_symmetric_eq_weightedOverlap
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g - normalizedDilation 2 (by norm_num) g)
            (g - normalizedDilation 2 (by norm_num) g)).re +
        factorTwoPrimeWeightedOverlap g := by
  rw [factorTwoDiagonalCoordinate_sub_symmetric_eq_localPrime
      g ha hab hsupport hratio,
    factorTwoPrimeCrossSymbol_re_eq_weightedOverlap]

/-- The symmetric endpoint is the exact local self-form minus the positive
folded two-prime overlap. -/
theorem factorTwoDiagonalCoordinate_add_symmetric_eq_weightedOverlap
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g + normalizedDilation 2 (by norm_num) g)
            (g + normalizedDilation 2 (by norm_num) g)).re -
        factorTwoPrimeWeightedOverlap g := by
  rw [factorTwoDiagonalCoordinate_add_symmetric_eq_localPrime
      g ha hab hsupport hratio,
    factorTwoPrimeCrossSymbol_re_eq_weightedOverlap]

/-- The remaining antisymmetric endpoint obligation after exact overlap
folding. -/
theorem factorTwoRealChannel_sub_nonneg_iff_weightedOverlap
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g ↔
      -factorTwoPrimeWeightedOverlap g ≤
        (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g - normalizedDilation 2 (by norm_num) g)
            (g - normalizedDilation 2 (by norm_num) g)).re := by
  rw [factorTwoDiagonalCoordinate_sub_symmetric_eq_weightedOverlap
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- The remaining symmetric endpoint obligation after exact overlap
folding. -/
theorem factorTwoRealChannel_add_nonneg_iff_weightedOverlap
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g ↔
      factorTwoPrimeWeightedOverlap g ≤
        (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g + normalizedDilation 2 (by norm_num) g)
            (g + normalizedDilation 2 (by norm_num) g)).re := by
  rw [factorTwoDiagonalCoordinate_add_symmetric_eq_weightedOverlap
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeOverlap
