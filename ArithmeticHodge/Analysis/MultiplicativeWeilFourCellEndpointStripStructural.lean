import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSingleProfileStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEndpointStripStructural

noncomputable section

open YoshidaCauchyPairing
open MultiplicativeWeilFourCellSingleProfileStructural

/-!
# Endpoint-strip form of the four-cell prime coupling

At lag `-log 2`, the support interval of the centered four-cell profile
overlaps its translate only in its outer quarter-log endpoint strips.  This
module records that localization exactly, before applying any inequality.
-/

/-- A negative-lag autocorrelation of a clipped profile is supported exactly
on the right endpoint overlap interval. -/
theorem crossCorrelation_neg_eq_rightEndpointStrip
    {a s : ℝ} (f g : YoshidaClippedSmooth a)
    (hs2 : s ≤ 2 * a) :
    crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) (-s) =
      ∫ x : ℝ in s - a..a, star (f x) * g (x - s) := by
  rw [crossCorrelation_apply]
  have hshift (x : ℝ) : -s + x = x - s := by ring
  simp_rw [hshift]
  have hle : s - a ≤ a := by linarith
  rw [intervalIntegral.integral_of_le hle,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    by_cases hxf : x ∈ Set.Icc (-a) a
    · have hxlt : x < s - a := by
        by_contra hnot
        exact hx ⟨le_of_not_gt hnot, hxf.2⟩
      have hxg : x - s ∉ Set.Icc (-a) a := by
        intro hmem
        linarith [hmem.1]
      rw [yoshidaClippedSmooth_eq_zero_outside g hxg, mul_zero]
    · rw [yoshidaClippedSmooth_eq_zero_outside f hxf, star_zero,
        zero_mul])).symm

private theorem endpointStripProduct_intervalIntegrable
    {a s : ℝ} (f g : YoshidaClippedSmooth a)
    (hs : 0 ≤ s) (hs2 : s ≤ 2 * a) :
    IntervalIntegrable (fun x : ℝ ↦ star (f x) * g (x - s)) volume
      (s - a) a := by
  have hle : s - a ≤ a := by linarith
  have hrightSubset : Set.Icc (s - a) a ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hshiftMap : Set.MapsTo (fun x : ℝ ↦ x - s)
      (Set.Icc (s - a) a) (Set.Icc (-a) a) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hfcont : ContinuousOn (f : ℝ → ℂ) (Set.Icc (s - a) a) :=
    f.property.1.continuousOn.mono hrightSubset
  have hgshiftcont : ContinuousOn (fun x : ℝ ↦ g (x - s))
      (Set.Icc (s - a) a) := by
    exact g.property.1.continuousOn.comp
      (continuous_id.sub continuous_const).continuousOn hshiftMap
  exact (hfcont.star.mul hgshiftcont).intervalIntegrable_of_Icc hle

/-- Pointwise real polarization in the orientation used by
`crossCorrelation`. -/
theorem star_mul_re_eq_quarter_normSq_add_sub (z w : ℂ) :
    (star z * w).re =
      (1 / 4 : ℝ) *
        (Complex.normSq (z + w) - Complex.normSq (z - w)) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact matched/antimatched diagonalization of the real endpoint coupling.
No absolute-value or Cauchy relaxation occurs in this identity. -/
theorem crossCorrelation_neg_re_eq_matched_sub_antimatched
    {a s : ℝ} (f g : YoshidaClippedSmooth a)
    (hs : 0 ≤ s) (hs2 : s ≤ 2 * a) :
    (crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) (-s)).re =
      (1 / 4 : ℝ) * ∫ x : ℝ in s - a..a,
        (Complex.normSq (f x + g (x - s)) -
          Complex.normSq (f x - g (x - s))) := by
  have hpint := endpointStripProduct_intervalIntegrable f g hs hs2
  rw [crossCorrelation_neg_eq_rightEndpointStrip f g hs2]
  calc
    (∫ x : ℝ in s - a..a, star (f x) * g (x - s)).re =
        ∫ x : ℝ in s - a..a, (star (f x) * g (x - s)).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hpint).symm
    _ = ∫ x : ℝ in s - a..a, (1 / 4 : ℝ) *
          (Complex.normSq (f x + g (x - s)) -
            Complex.normSq (f x - g (x - s))) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact star_mul_re_eq_quarter_normSq_add_sub _ _
    _ = (1 / 4 : ℝ) * ∫ x : ℝ in s - a..a,
          (Complex.normSq (f x + g (x - s)) -
            Complex.normSq (f x - g (x - s))) := by
      rw [intervalIntegral.integral_const_mul]

/-- Endpoint-strip Schur bound.  Only the two overlap strips enter; the
interior mass of either clipped profile is absent. -/
theorem two_mul_norm_crossCorrelation_neg_le_endpointEnergies
    {a s : ℝ} (f g : YoshidaClippedSmooth a)
    (hs : 0 ≤ s) (hs2 : s ≤ 2 * a) :
    2 * ‖crossCorrelation (f : ℝ → ℂ) (g : ℝ → ℂ) (-s)‖ ≤
      (∫ x : ℝ in s - a..a, Complex.normSq (f x)) +
        ∫ x : ℝ in -a..a - s, Complex.normSq (g x) := by
  let p : ℝ → ℂ := fun x ↦ star (f x) * g (x - s)
  let qf : ℝ → ℝ := fun x ↦ Complex.normSq (f x)
  let qg : ℝ → ℝ := fun x ↦ Complex.normSq (g x)
  have hle : s - a ≤ a := by linarith
  have hleftle : -a ≤ a - s := by linarith
  have hrightSubset : Set.Icc (s - a) a ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftSubset : Set.Icc (-a) (a - s) ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hfcont : ContinuousOn (f : ℝ → ℂ) (Set.Icc (s - a) a) :=
    f.property.1.continuousOn.mono hrightSubset
  have hgcont : ContinuousOn (g : ℝ → ℂ) (Set.Icc (-a) (a - s)) :=
    g.property.1.continuousOn.mono hleftSubset
  have hshiftMap : Set.MapsTo (fun x : ℝ ↦ x - s)
      (Set.Icc (s - a) a) (Set.Icc (-a) (a - s)) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgshiftcont : ContinuousOn (fun x : ℝ ↦ g (x - s))
      (Set.Icc (s - a) a) := by
    exact hgcont.comp (continuous_id.sub continuous_const).continuousOn hshiftMap
  have hpcont : ContinuousOn p (Set.Icc (s - a) a) := by
    exact hfcont.star.mul hgshiftcont
  have hqfcont : ContinuousOn qf (Set.Icc (s - a) a) := by
    simpa only [qf, Complex.normSq_eq_norm_sq] using hfcont.norm.pow 2
  have hqgcont : ContinuousOn qg (Set.Icc (-a) (a - s)) := by
    simpa only [qg, Complex.normSq_eq_norm_sq] using hgcont.norm.pow 2
  have hqgshiftcont : ContinuousOn (fun x : ℝ ↦ qg (x - s))
      (Set.Icc (s - a) a) := by
    exact hqgcont.comp (continuous_id.sub continuous_const).continuousOn hshiftMap
  have hpint : IntervalIntegrable p volume (s - a) a :=
    hpcont.intervalIntegrable_of_Icc hle
  have hqfint : IntervalIntegrable qf volume (s - a) a :=
    hqfcont.intervalIntegrable_of_Icc hle
  have hqgint : IntervalIntegrable qg volume (-a) (a - s) :=
    hqgcont.intervalIntegrable_of_Icc hleftle
  have hqgshiftint : IntervalIntegrable (fun x : ℝ ↦ qg (x - s))
      volume (s - a) a :=
    hqgshiftcont.intervalIntegrable_of_Icc hle
  rw [crossCorrelation_neg_eq_rightEndpointStrip f g hs2]
  change 2 * ‖∫ x : ℝ in s - a..a, p x‖ ≤ _
  calc
    2 * ‖∫ x : ℝ in s - a..a, p x‖ ≤
        2 * ∫ x : ℝ in s - a..a, ‖p x‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm hle
    _ = ∫ x : ℝ in s - a..a, 2 * ‖p x‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x : ℝ in s - a..a, qf x + qg (x - s) := by
      apply intervalIntegral.integral_mono_on hle
      · exact (hpint.norm.const_mul 2)
      · exact hqfint.add hqgshiftint
      · intro x _hx
        dsimp only [p, qf, qg]
        rw [norm_mul]
        have hstar : ‖star (f x)‖ = ‖f x‖ := by
          simpa only [starRingEnd_apply] using (RCLike.norm_conj (f x))
        rw [hstar, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖f x‖ - ‖g (x - s)‖)]
    _ = (∫ x : ℝ in s - a..a, qf x) +
          ∫ x : ℝ in -a..a - s, qg x := by
      rw [intervalIntegral.integral_add hqfint hqgshiftint,
        intervalIntegral.integral_comp_sub_right]
      have hbound : s - a - s = -a := by ring
      rw [hbound]
    _ = (∫ x : ℝ in s - a..a, Complex.normSq (f x)) +
          ∫ x : ℝ in -a..a - s, Complex.normSq (g x) := by
      rfl

/-- Exact endpoint interval for the prime-two autocorrelation of the complete
four-cell profile.  The right strip `[3 log 2 / 8, 5 log 2 / 8]` is paired
with the translated left strip `[-5 log 2 / 8, -3 log 2 / 8]`. -/
theorem fourCellWholeProfile_crossCorrelation_neg_log_eq_endpointStrip
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2) =
      ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
        star (fourCellWholeProfile parent k x) *
          fourCellWholeProfile parent k (x - Real.log 2) := by
  have hs2 : Real.log 2 ≤
      2 * fourCellWholeHalfWidth k := by
    rw [fourCellWholeHalfWidth_eq]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  rw [crossCorrelation_neg_eq_rightEndpointStrip
    (fourCellWholeProfile parent k) (fourCellWholeProfile parent k) hs2]
  have hlower : Real.log 2 - fourCellWholeHalfWidth k =
      3 * Real.log 2 / 8 := by
    rw [fourCellWholeHalfWidth_eq]
    ring
  have hupper : fourCellWholeHalfWidth k =
      5 * Real.log 2 / 8 := fourCellWholeHalfWidth_eq k
  rw [hlower]
  congr 1

/-- At the four-cell prime lag, the matched endpoint square and the
antimatched endpoint square are the two diagonal channels. -/
theorem fourCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    (crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)).re =
      (1 / 4 : ℝ) *
        ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
          (Complex.normSq
              (fourCellWholeProfile parent k x +
                fourCellWholeProfile parent k (x - Real.log 2)) -
            Complex.normSq
              (fourCellWholeProfile parent k x -
                fourCellWholeProfile parent k (x - Real.log 2))) := by
  have hs : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hs2 : Real.log 2 ≤
      2 * fourCellWholeHalfWidth k := by
    rw [fourCellWholeHalfWidth_eq]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  rw [crossCorrelation_neg_re_eq_matched_sub_antimatched
    (fourCellWholeProfile parent k) (fourCellWholeProfile parent k) hs hs2]
  have hlower : Real.log 2 - fourCellWholeHalfWidth k =
      3 * Real.log 2 / 8 := by
    rw [fourCellWholeHalfWidth_eq]
    ring
  have hupper : fourCellWholeHalfWidth k =
      5 * Real.log 2 / 8 := fourCellWholeHalfWidth_eq k
  congr 2

/-- Matched endpoint energy at the unique prime-two overlap. -/
def fourCellEndpointMatchedEnergy
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) : ℝ :=
  ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
    Complex.normSq
      (fourCellWholeProfile parent k x +
        fourCellWholeProfile parent k (x - Real.log 2))

/-- Antimatched endpoint energy at the unique prime-two overlap. -/
def fourCellEndpointAntimatchedEnergy
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) : ℝ :=
  ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
    Complex.normSq
      (fourCellWholeProfile parent k x -
        fourCellWholeProfile parent k (x - Real.log 2))

private theorem fourCellEndpointSquare_intervalIntegrable
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    IntervalIntegrable (fun x : ℝ ↦ Complex.normSq
        (fourCellWholeProfile parent k x +
          fourCellWholeProfile parent k (x - Real.log 2))) volume
        (3 * Real.log 2 / 8) (5 * Real.log 2 / 8) ∧
      IntervalIntegrable (fun x : ℝ ↦ Complex.normSq
        (fourCellWholeProfile parent k x -
          fourCellWholeProfile parent k (x - Real.log 2))) volume
        (3 * Real.log 2 / 8) (5 * Real.log 2 / 8) := by
  let f := fourCellWholeProfile parent k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : 3 * Real.log 2 / 8 ≤ 5 * Real.log 2 / 8 := by
    nlinarith
  have hrightSubset : Set.Icc (3 * Real.log 2 / 8)
      (5 * Real.log 2 / 8) ⊆
      Set.Icc (-fourCellWholeHalfWidth k) (fourCellWholeHalfWidth k) := by
    intro x hx
    rw [fourCellWholeHalfWidth_eq]
    constructor <;> linarith [hx.1, hx.2]
  have hshiftMap : Set.MapsTo (fun x : ℝ ↦ x - Real.log 2)
      (Set.Icc (3 * Real.log 2 / 8) (5 * Real.log 2 / 8))
      (Set.Icc (-fourCellWholeHalfWidth k) (fourCellWholeHalfWidth k)) := by
    intro x hx
    rw [fourCellWholeHalfWidth_eq]
    constructor <;> linarith [hx.1, hx.2]
  have hfcont : ContinuousOn (f : ℝ → ℂ)
      (Set.Icc (3 * Real.log 2 / 8) (5 * Real.log 2 / 8)) :=
    f.property.1.continuousOn.mono hrightSubset
  have hshiftcont : ContinuousOn (fun x : ℝ ↦ f (x - Real.log 2))
      (Set.Icc (3 * Real.log 2 / 8) (5 * Real.log 2 / 8)) := by
    exact f.property.1.continuousOn.comp
      (continuous_id.sub continuous_const).continuousOn hshiftMap
  constructor
  · simpa only [f, Complex.normSq_eq_norm_sq] using
      ((hfcont.add hshiftcont).norm.pow 2).intervalIntegrable_of_Icc hle
  · simpa only [f, Complex.normSq_eq_norm_sq] using
      ((hfcont.sub hshiftcont).norm.pow 2).intervalIntegrable_of_Icc hle

theorem fourCellEndpointMatchedEnergy_nonneg
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    0 ≤ fourCellEndpointMatchedEnergy parent k := by
  unfold fourCellEndpointMatchedEnergy
  exact intervalIntegral.integral_nonneg
    (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
    (fun x _hx ↦ Complex.normSq_nonneg _)

theorem fourCellEndpointAntimatchedEnergy_nonneg
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    0 ≤ fourCellEndpointAntimatchedEnergy parent k := by
  unfold fourCellEndpointAntimatchedEnergy
  exact intervalIntegral.integral_nonneg
    (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
    (fun x _hx ↦ Complex.normSq_nonneg _)

/-- The prime autocorrelation is exactly one quarter of matched energy minus
antimatched energy. -/
theorem fourCellWholeProfile_crossCorrelation_neg_log_re_eq_energyDifference
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    (crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)).re =
      (fourCellEndpointMatchedEnergy parent k -
        fourCellEndpointAntimatchedEnergy parent k) / 4 := by
  rw [fourCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares]
  unfold fourCellEndpointMatchedEnergy fourCellEndpointAntimatchedEnergy
  rw [intervalIntegral.integral_sub
    (fourCellEndpointSquare_intervalIntegrable parent k).1
    (fourCellEndpointSquare_intervalIntegrable parent k).2]
  ring

/-- The strip-local Schur estimate at the exact four-cell geometry. -/
theorem two_mul_norm_fourCellWholeProfile_crossCorrelation_le_endpointEnergies
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    2 * ‖crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)‖ ≤
      (∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
        Complex.normSq (fourCellWholeProfile parent k x)) +
      ∫ x : ℝ in -(5 * Real.log 2 / 8)..-(3 * Real.log 2 / 8),
        Complex.normSq (fourCellWholeProfile parent k x) := by
  have hs : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hs2 : Real.log 2 ≤
      2 * fourCellWholeHalfWidth k := by
    rw [fourCellWholeHalfWidth_eq]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h := two_mul_norm_crossCorrelation_neg_le_endpointEnergies
    (fourCellWholeProfile parent k) (fourCellWholeProfile parent k) hs hs2
  have hlower : Real.log 2 - fourCellWholeHalfWidth k =
      3 * Real.log 2 / 8 := by
    rw [fourCellWholeHalfWidth_eq]
    ring
  have hupper : fourCellWholeHalfWidth k =
      5 * Real.log 2 / 8 := fourCellWholeHalfWidth_eq k
  have hleftLower : -fourCellWholeHalfWidth k =
      -(5 * Real.log 2 / 8) := by rw [hupper]
  have hleftUpper : fourCellWholeHalfWidth k - Real.log 2 =
      -(3 * Real.log 2 / 8) := by
    rw [fourCellWholeHalfWidth_eq]
    ring
  calc
    2 * ‖crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (-Real.log 2)‖ ≤
        (∫ x : ℝ in Real.log 2 - fourCellWholeHalfWidth k..
            fourCellWholeHalfWidth k,
          Complex.normSq (fourCellWholeProfile parent k x)) +
        ∫ x : ℝ in -fourCellWholeHalfWidth k..
            fourCellWholeHalfWidth k - Real.log 2,
          Complex.normSq (fourCellWholeProfile parent k x) := h
    _ = _ := by congr 3

/-- A direct sufficient coercivity target: only the two endpoint-strip masses
must be absorbed, while the local critical quadratic remains coupled. -/
theorem fourCell_endpointEnergy_lowerBound
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    (yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
        (fourCellWholeHalfWidth_pos k)
        (fourCellWholeProfile parent k)
        (fourCellWholeProfile parent k)).re -
      (Real.sqrt 2 * Real.log 2 / 2) *
        ((∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
            Complex.normSq (fourCellWholeProfile parent k x)) +
          ∫ x : ℝ in -(5 * Real.log 2 / 8)..-(3 * Real.log 2 / 8),
            Complex.normSq (fourCellWholeProfile parent k x)) ≤
      (MultiplicativeWeil.bombieriFunctional
        (MultiplicativeWeil.bombieriQuadraticTest
          (MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural.monotoneQuarterFourBlock
            parent k))).re := by
  let C : ℝ := (crossCorrelation
    (fourCellWholeProfile parent k : ℝ → ℂ)
    (fourCellWholeProfile parent k : ℝ → ℂ)
    (-Real.log 2)).re
  let E : ℝ :=
    (∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
      Complex.normSq (fourCellWholeProfile parent k x)) +
    ∫ x : ℝ in -(5 * Real.log 2 / 8)..-(3 * Real.log 2 / 8),
      Complex.normSq (fourCellWholeProfile parent k x)
  have hnorm :=
    two_mul_norm_fourCellWholeProfile_crossCorrelation_le_endpointEnergies
      parent k
  have hre : C ≤ ‖crossCorrelation
      (fourCellWholeProfile parent k : ℝ → ℂ)
      (fourCellWholeProfile parent k : ℝ → ℂ)
      (-Real.log 2)‖ := by
    exact Complex.re_le_norm _
  have hCE : 2 * C ≤ E := by
    dsimp only [C, E] at hre ⊢
    linarith
  have hc : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_pos (by norm_num)).le
  have hc2 : 0 ≤ Real.sqrt 2 * Real.log 2 / 2 :=
    div_nonneg hc (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hCE hc2
  rw [bombieriFunctional_fourBlock_re_eq_singleProfile]
  dsimp only [C, E] at hscaled
  nlinarith

/-- The complete four-cell form with its unique prime channel diagonalized
into matched and antimatched endpoint squares.  The clipped local quadratic
is retained whole. -/
theorem bombieriFunctional_fourBlock_re_eq_endpointSquares
    (parent : MultiplicativeWeil.BombieriTest) (k : ℤ) :
    (MultiplicativeWeil.bombieriFunctional
        (MultiplicativeWeil.bombieriQuadraticTest
          (MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural.monotoneQuarterFourBlock
            parent k))).re =
      (yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
        (fourCellWholeHalfWidth_pos k)
        (fourCellWholeProfile parent k)
        (fourCellWholeProfile parent k)).re -
      (Real.sqrt 2 * Real.log 2 / 4) *
        ∫ x : ℝ in 3 * Real.log 2 / 8..5 * Real.log 2 / 8,
          (Complex.normSq
              (fourCellWholeProfile parent k x +
                fourCellWholeProfile parent k (x - Real.log 2)) -
            Complex.normSq
              (fourCellWholeProfile parent k x -
                fourCellWholeProfile parent k (x - Real.log 2))) := by
  rw [bombieriFunctional_fourBlock_re_eq_singleProfile,
    fourCellWholeProfile_crossCorrelation_neg_log_re_eq_endpointSquares]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEndpointStripStructural
