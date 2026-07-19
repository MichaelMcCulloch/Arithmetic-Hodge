import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevPotentialSignStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevRecombinationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilMangoldtDiscrepancyAbelStructural
open MultiplicativeWeilMonotoneChebyshevPotentialSignStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Recombining the complete monotone far contribution

Integration by parts must be applied to the Chebyshev-error and corrected-
potential terms together.  The result is not a positive remainder: it is the
signed Mangoldt sampling functional subtracted from a smooth physical
correlation pairing.  The smooth density itself has the exact sign threshold

`1 <= t * (t^2 - 1)`, where `t = r * x`.

Thus the first far lag has a genuine counter-sign region.  At larger lags the
density can become nonnegative on the correlation support, but it is still
paired with a signed directed correlation and accompanied by signed Mangoldt
samples.  No hypothesis on either sign is introduced here.
-/

/-- The conjugated normalized later--head directed correlation used by one
far monotone-cell entry. -/
def monotoneQuarterFarPhysicalCorrelation
    (parent : BombieriTest) (k lag : ℤ) (x : ℝ) : ℂ :=
  starRingEnd ℂ
    (bombieriDirectedCorrelation
      (monotoneQuarterNormalizedCell parent (k + lag))
      (monotoneQuarterNormalizedCell parent k) x)

/-- The discrete Stieltjes part of one far entry after Abel recombination. -/
def monotoneQuarterFarMangoldtPairing
    (parent : BombieriTest) (k lag : ℤ) : ℂ :=
  ∑' n : ℕ,
    ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
      monotoneQuarterFarPhysicalCorrelation parent k lag
        ((quarterLogLatticePoint lag)⁻¹ * (n + 1 : ℕ))

/-- The smooth archimedean density left after the linear part of
`psi(r*x) - r*x` is combined with the derivative of the corrected
potential. -/
def recombinedFarArchimedeanDensity (r x : ℝ) : ℝ :=
  r - (x * ((r * x) ^ 2 - 1))⁻¹

/-- Exact Stieltjes/integration-by-parts recombination of the *complete* far
numerator.  In particular, treating the corrected potential as an independent
favorable term loses the cancellation displayed here. -/
theorem monotoneQuarterFarChebyshevNumerator_eq_mass_sub_mangoldt_sub_physical
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    monotoneQuarterFarChebyshevNumerator parent k lag =
      ((quarterLogLatticePoint lag : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            monotoneQuarterFarPhysicalCorrelation parent k lag x) -
        monotoneQuarterFarMangoldtPairing parent k lag -
        monotoneQuarterFarPhysicalPotentialPairing parent k lag := by
  let f : BombieriTest :=
    monotoneQuarterNormalizedCell parent (k + lag)
  let g : BombieriTest := monotoneQuarterNormalizedCell parent k
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let r : ℝ := quarterLogLatticePoint lag
  have hAbel :=
    scaled_integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
      H (star_bombieriDirectedCorrelation_contDiff_one f g)
      (star_bombieriDirectedCorrelation_hasCompactSupport f g)
      (quarterLogLatticePoint_pos lag)
  have hPotential :=
    monotoneQuarterFarCorrectedPotentialPairing_eq_neg_physical
      parent k lag hfar
  change
    (∫ x : ℝ in Set.Ioi 0,
        (((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) * deriv H x)) +
      monotoneQuarterFarCorrectedPotentialPairing parent k lag = _
  rw [← hAbel, hPotential]
  rfl

/-- The two continuous terms in the recombined formula are one integral
against `recombinedFarArchimedeanDensity`. -/
theorem monotoneQuarterFar_mass_sub_physical_eq_integral_recombinedDensity
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    ((quarterLogLatticePoint lag : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            monotoneQuarterFarPhysicalCorrelation parent k lag x) -
        monotoneQuarterFarPhysicalPotentialPairing parent k lag =
      ∫ x : ℝ in Set.Ioi 0,
        ((recombinedFarArchimedeanDensity
          (quarterLogLatticePoint lag) x : ℝ) : ℂ) *
            monotoneQuarterFarPhysicalCorrelation parent k lag x := by
  let f : BombieriTest :=
    monotoneQuarterNormalizedCell parent (k + lag)
  let g : BombieriTest := monotoneQuarterNormalizedCell parent k
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let q₂ : ℝ := quarterLogLatticePoint 2
  let r : ℝ := quarterLogLatticePoint lag
  let K : Set ℝ := Set.Icc (1 / q₂) q₂
  have hq₂pos : 0 < q₂ := quarterLogLatticePoint_pos 2
  have hr : 0 < r := quarterLogLatticePoint_pos lag
  have hf : tsupport f ⊆ Set.Icc 1 q₂ := by
    exact monotoneQuarterNormalizedCell_tsupport_subset parent (k + lag)
  have hg : tsupport g ⊆ Set.Icc 1 q₂ := by
    exact monotoneQuarterNormalizedCell_tsupport_subset parent k
  have hHInt : IntegrableOn H (Set.Ioi 0) := by
    exact star_bombieriDirectedCorrelation_integrableOn_Ioi
      f g (by norm_num) (by norm_num) hq₂pos hf hg
  have hqfar : q₂ < r := by
    exact quarterLogLatticePoint_two_lt_of_three_le lag hfar
  have hsepLower : 1 < r * (1 / q₂) := by
    calc
      (1 : ℝ) = q₂ / q₂ := by field_simp [hq₂pos.ne']
      _ < r / q₂ := (div_lt_div_iff_of_pos_right hq₂pos).2 hqfar
      _ = r * (1 / q₂) := by ring
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro x hx
    exact (div_pos (by norm_num) hq₂pos).trans_le hx.1
  have hHsupport : tsupport H ⊆ K := by
    apply isClosed_Icc.closure_subset_iff.mpr
    intro x hx
    by_contra hout
    apply hx
    dsimp only [H]
    apply star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
      f g (by norm_num) (by norm_num) hq₂pos hf hg
    simpa only [K, div_one] using hout
  let kernel : ℝ → ℂ := fun x ↦
    ((((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x)
  have hscalarContinuous : ContinuousOn
      (fun x : ℝ ↦ (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ)) K := by
    intro x hx
    have hxpos : 0 < x := hKpos hx
    have hrx : 1 < r * x :=
      hsepLower.trans_le (mul_le_mul_of_nonneg_left hx.1 hr.le)
    have hden : x * ((r * x) ^ 2 - 1) ≠ 0 := by
      apply mul_ne_zero hxpos.ne'
      nlinarith [sq_nonneg (r * x - 1)]
    have hbase : ContinuousAt
        (fun y : ℝ ↦ y * ((r * y) ^ 2 - 1)) x := by
      fun_prop
    have hinv : ContinuousAt
        (fun y : ℝ ↦ (y * ((r * y) ^ 2 - 1))⁻¹) x :=
      hbase.inv₀ hden
    exact
      (Complex.ofRealCLM.continuous.continuousAt.comp hinv).continuousWithinAt
  have hkernelIntK : IntegrableOn kernel K := by
    dsimp only [kernel]
    exact (hHInt.mono_set hKpos).continuousOn_mul
      hscalarContinuous isCompact_Icc
  have hkernelSupport : Function.support kernel ⊆ K := by
    intro x hx
    apply hHsupport
    apply subset_tsupport H
    apply Function.mem_support.mpr
    exact right_ne_zero_of_mul hx
  have hkernelInt : IntegrableOn kernel (Set.Ioi 0) := by
    have hglobal : Integrable kernel :=
      (integrableOn_iff_integrable_of_support_subset hkernelSupport).mp
        hkernelIntK
    exact hglobal.integrableOn
  change
    (r : ℂ) * (∫ x : ℝ in Set.Ioi 0, H x) -
        ∫ x : ℝ in Set.Ioi 0, kernel x =
      ∫ x : ℝ in Set.Ioi 0,
        ((recombinedFarArchimedeanDensity r x : ℝ) : ℂ) * H x
  calc
    (r : ℂ) * (∫ x : ℝ in Set.Ioi 0, H x) -
          ∫ x : ℝ in Set.Ioi 0, kernel x =
        (∫ x : ℝ in Set.Ioi 0, (r : ℂ) * H x) -
          ∫ x : ℝ in Set.Ioi 0, kernel x := by
            congr 1
            exact (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Ioi 0)) (r : ℂ) H).symm
    _ = ∫ x : ℝ in Set.Ioi 0, (r : ℂ) * H x - kernel x := by
      rw [integral_sub (hHInt.const_mul (r : ℂ)) hkernelInt]
    _ = ∫ x : ℝ in Set.Ioi 0,
        ((recombinedFarArchimedeanDensity r x : ℝ) : ℂ) * H x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      dsimp only [kernel]
      unfold recombinedFarArchimedeanDensity
      push_cast
      ring

/-- Final one-row recombination: the complete far numerator is a smooth
signed correlation pairing minus the discrete Mangoldt sampling pairing. -/
theorem monotoneQuarterFarChebyshevNumerator_eq_integral_recombinedDensity_sub_mangoldt
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    monotoneQuarterFarChebyshevNumerator parent k lag =
      (∫ x : ℝ in Set.Ioi 0,
        ((recombinedFarArchimedeanDensity
          (quarterLogLatticePoint lag) x : ℝ) : ℂ) *
            monotoneQuarterFarPhysicalCorrelation parent k lag x) -
        monotoneQuarterFarMangoldtPairing parent k lag := by
  rw [
    monotoneQuarterFarChebyshevNumerator_eq_mass_sub_mangoldt_sub_physical
      parent k lag hfar]
  have hsmooth :=
    monotoneQuarterFar_mass_sub_physical_eq_integral_recombinedDensity
      parent k lag hfar
  calc
    ((quarterLogLatticePoint lag : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            monotoneQuarterFarPhysicalCorrelation parent k lag x) -
        monotoneQuarterFarMangoldtPairing parent k lag -
        monotoneQuarterFarPhysicalPotentialPairing parent k lag =
      (((quarterLogLatticePoint lag : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            monotoneQuarterFarPhysicalCorrelation parent k lag x) -
        monotoneQuarterFarPhysicalPotentialPairing parent k lag) -
          monotoneQuarterFarMangoldtPairing parent k lag := by ring
    _ = _ := by rw [hsmooth]

/-! ## The exact sign threshold of the smooth remainder -/

/-- Away from its pole, the recombined smooth density is nonnegative exactly
when the dimensionless coordinate `t = r*x` lies beyond the cubic threshold
`t*(t^2-1)=1`. -/
theorem recombinedFarArchimedeanDensity_nonnegative_iff
    {r x : ℝ} (hx : 0 < x) (hsep : 1 < r * x) :
    0 ≤ recombinedFarArchimedeanDensity r x ↔
      1 ≤ (r * x) * ((r * x) ^ 2 - 1) := by
  have hfactor : 0 < (r * x) ^ 2 - 1 := by
    nlinarith [sq_nonneg (r * x - 1)]
  have hden : 0 < x * ((r * x) ^ 2 - 1) := mul_pos hx hfactor
  unfold recombinedFarArchimedeanDensity
  rw [sub_nonneg, inv_le_iff_one_le_mul₀ hden]
  ring_nf

/-- The corresponding strict counter-sign criterion. -/
theorem recombinedFarArchimedeanDensity_negative_iff
    {r x : ℝ} (hx : 0 < x) (hsep : 1 < r * x) :
    recombinedFarArchimedeanDensity r x < 0 ↔
      (r * x) * ((r * x) ^ 2 - 1) < 1 := by
  rw [lt_iff_not_ge,
    recombinedFarArchimedeanDensity_nonnegative_iff hx hsep,
    not_le]

/-- One quarter-octave step is the positive fourth root of two. -/
theorem quarterLogLatticePoint_one_pow_four :
    quarterLogLatticePoint 1 ^ 4 = 2 := by
  unfold quarterLogLatticePoint
  norm_num
  rw [← Real.exp_nat_mul]
  convert Real.exp_log (by norm_num : (0 : ℝ) < 2) using 1
  ring_nf

/-- Two quarter-octave steps square to two. -/
theorem quarterLogLatticePoint_two_sq :
    quarterLogLatticePoint 2 ^ 2 = 2 := by
  unfold quarterLogLatticePoint
  norm_num
  rw [← Real.exp_nat_mul]
  convert Real.exp_log (by norm_num : (0 : ℝ) < 2) using 1
  ring_nf

/-- Removing two quarter steps is division by the fixed base-support ratio. -/
theorem quarterLogLatticePoint_mul_inv_two (lag : ℤ) :
    quarterLogLatticePoint lag * (quarterLogLatticePoint 2)⁻¹ =
      quarterLogLatticePoint (lag - 2) := by
  have h := quarterLogLatticePoint_add (lag - 2) 2
  have hindex : lag - 2 + 2 = lag := by ring
  rw [hindex] at h
  rw [h]
  field_simp [(quarterLogLatticePoint_pos 2).ne']

/-- Beyond the cubic threshold, the smooth recombined density has the
favorable pointwise sign. -/
theorem one_le_mul_sq_sub_one_of_quarterPoint_two_le
    {t : ℝ} (ht : quarterLogLatticePoint 2 ≤ t) :
    1 ≤ t * (t ^ 2 - 1) := by
  have hqOne : 1 ≤ quarterLogLatticePoint 2 := by
    simpa only [quarterLogLatticePoint_zero] using
      (quarterLogLatticePoint_mono
        (m := (0 : ℤ)) (n := 2) (by omega))
  have htOne : 1 ≤ t := hqOne.trans ht
  have hsq : quarterLogLatticePoint 2 ^ 2 ≤ t ^ 2 :=
    pow_le_pow_left₀ (quarterLogLatticePoint_pos 2).le ht 2
  rw [quarterLogLatticePoint_two_sq] at hsq
  have hsecond : 1 ≤ t ^ 2 - 1 := by linarith
  simpa only [one_mul] using
    mul_le_mul htOne hsecond (by norm_num : (0 : ℝ) ≤ 1) (by linarith)

/-- From lag four onward the smooth density is nonnegative throughout the
entire possible normalized correlation support.  This does not sign its
pairing, because the correlation itself is signed. -/
theorem recombinedFarArchimedeanDensity_nonnegative_of_four_le
    (lag : ℤ) (hfour : 4 ≤ lag) {x : ℝ}
    (hx : (quarterLogLatticePoint 2)⁻¹ ≤ x) :
    0 ≤ recombinedFarArchimedeanDensity
      (quarterLogLatticePoint lag) x := by
  let r : ℝ := quarterLogLatticePoint lag
  have hqInvPos : 0 < (quarterLogLatticePoint 2)⁻¹ :=
    inv_pos.mpr (quarterLogLatticePoint_pos 2)
  have hxPos : 0 < x := hqInvPos.trans_le hx
  have htLower : quarterLogLatticePoint 2 ≤ r * x := by
    calc
      quarterLogLatticePoint 2 ≤ quarterLogLatticePoint (lag - 2) :=
        quarterLogLatticePoint_mono (by omega)
      _ = r * (quarterLogLatticePoint 2)⁻¹ := by
        simpa only [r] using
          (quarterLogLatticePoint_mul_inv_two lag).symm
      _ ≤ r * x :=
        mul_le_mul_of_nonneg_left hx (quarterLogLatticePoint_pos lag).le
  have hsep : 1 < r * x := by
    have hqStrict : 1 < quarterLogLatticePoint 2 := by
      simpa only [quarterLogLatticePoint_zero] using
        (quarterLogLatticePoint_strictMono
          (a := (0 : ℤ)) (b := (2 : ℤ)) (by omega))
    exact hqStrict.trans_le htLower
  rw [recombinedFarArchimedeanDensity_nonnegative_iff hxPos hsep]
  exact one_le_mul_sq_sub_one_of_quarterPoint_two_le htLower

/-- A convenient rational point lies strictly above the first normalized
support quotient endpoint. -/
theorem quarterLogLatticePoint_one_lt_six_fifths :
    quarterLogLatticePoint 1 < (6 / 5 : ℝ) := by
  apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 6 / 5)
  rw [quarterLogLatticePoint_one_pow_four]
  norm_num

/-- At lag three the smooth remainder has a strict counter-sign point inside
the normalized correlation-support interval.  Hence the complete
recombination cannot obtain a pointwise-positive kernel at the first far
lag. -/
theorem exists_lag_three_recombined_density_negative_in_supportInterior :
    ∃ x ∈ Set.Ioo
        ((quarterLogLatticePoint 2)⁻¹) (quarterLogLatticePoint 2),
      recombinedFarArchimedeanDensity (quarterLogLatticePoint 3) x < 0 := by
  let r : ℝ := quarterLogLatticePoint 3
  let t : ℝ := 6 / 5
  let x : ℝ := r⁻¹ * t
  have hr : 0 < r := quarterLogLatticePoint_pos 3
  have ht : 0 < t := by norm_num [t]
  have hrt : r * x = t := by
    dsimp only [x]
    field_simp [hr.ne']
  have hsep : 1 < r * x := by rw [hrt]; norm_num [t]
  have htCounter : t * (t ^ 2 - 1) < 1 := by norm_num [t]
  have hneg : recombinedFarArchimedeanDensity r x < 0 := by
    rw [recombinedFarArchimedeanDensity_negative_iff
      (mul_pos (inv_pos.mpr hr) ht) hsep, hrt]
    exact htCounter
  refine ⟨x, ?_, hneg⟩
  constructor
  · have hqTwo : 0 < quarterLogLatticePoint 2 :=
      quarterLogLatticePoint_pos 2
    have hrFactor : r =
        quarterLogLatticePoint 2 * quarterLogLatticePoint 1 := by
      dsimp only [r]
      convert quarterLogLatticePoint_add 1 2 using 1
    rw [show (quarterLogLatticePoint 2)⁻¹ =
        r⁻¹ * quarterLogLatticePoint 1 by
      rw [hrFactor]
      field_simp [hqTwo.ne', (quarterLogLatticePoint_pos 1).ne']]
    exact mul_lt_mul_of_pos_left
      quarterLogLatticePoint_one_lt_six_fifths (inv_pos.mpr hr)
  · have hrOne : 1 < r := by
      dsimp only [r]
      simpa only [quarterLogLatticePoint_zero] using
        (quarterLogLatticePoint_strictMono
          (a := (0 : ℤ)) (b := (3 : ℤ)) (by omega))
    have hrInvLtOne : r⁻¹ < 1 := by
      rw [inv_lt_one₀ hr]
      exact hrOne
    have htLt : t < quarterLogLatticePoint 2 := by
      apply lt_of_pow_lt_pow_left₀ 2 (quarterLogLatticePoint_pos 2).le
      rw [quarterLogLatticePoint_two_sq]
      norm_num [t]
    calc
      x = r⁻¹ * t := rfl
      _ < 1 * t := mul_lt_mul_of_pos_right hrInvLtOne ht
      _ = t := one_mul t
      _ < quarterLogLatticePoint 2 := htLt

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevRecombinationStructural
