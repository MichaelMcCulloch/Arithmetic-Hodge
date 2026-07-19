import ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEndpointVarianceStructural

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold

noncomputable section

/-!
# Mean--variance control of the four-cell endpoint pairing

The lag `8/5` pairs the right endpoint strip `[3/5,1]` with the left
endpoint strip `[-1,-3/5]`.  This file bounds that pairing without splitting
the logarithmic energy into independent diagonal pieces.
-/

/-- The arithmetic mean of a profile on the centered interval. -/
def centeredIntervalMean (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x

/-- Variance about the arithmetic mean on the centered interval. -/
def centeredIntervalVariance (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, (w x - centeredIntervalMean w) ^ 2

/-- The normalized endpoint pairing exposed by the centered four-cell block. -/
def fourCellEndpointPairing (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (3 / 5 : ℝ)..1, w x * w (x - 8 / 5)

private theorem centeredRawLogEnergy_eq_setIntegral
    (w : ℝ → ℝ)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    centeredRawLogEnergy w =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        centeredLogDifferenceKernel w p.1 p.2
          ∂((volume : Measure ℝ).prod volume) := by
  unfold centeredRawLogEnergy centeredLogDifferenceKernel
  calc
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
        (w x - w y) ^ 2 / |x - y|) =
        ∫ x : ℝ in Icc (-1) 1,
          ∫ y : ℝ in Icc (-1) 1,
            (w x - w y) ^ 2 / |x - y| := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in -1..1,
          (w x - w y) ^ 2 / |x - y|) =
        ∫ y : ℝ in Icc (-1) 1,
          (w x - w y) ^ 2 / |x - y|
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
          (w p.1 - w p.2) ^ 2 / |p.1 - p.2| := by
      exact (setIntegral_prod _ henergy).symm

/-- Exact double-integral identity on an interval of length two. -/
theorem integral_integral_sq_sub_eq_four_mul_variance
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
      4 * centeredIntervalVariance w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x
  let S₂ : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hwInt : IntervalIntegrable w volume (-1 : ℝ) 1 :=
    hw.intervalIntegrable _ _
  have hwSqInt : IntervalIntegrable (fun x : ℝ ↦ w x ^ 2) volume (-1 : ℝ) 1 :=
    (hw.pow 2).intervalIntegrable _ _
  have hinner (x : ℝ) :
      (∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
        2 * w x ^ 2 - 2 * w x * M + S₂ := by
    have hconst : IntervalIntegrable (fun _y : ℝ ↦ w x ^ 2)
        volume (-1 : ℝ) 1 := intervalIntegrable_const
    have hlin : IntervalIntegrable (fun y : ℝ ↦ 2 * w x * w y)
        volume (-1 : ℝ) 1 := hwInt.const_mul (2 * w x)
    calc
      (∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
          ∫ y : ℝ in -1..1, (w x ^ 2 - 2 * w x * w y) + w y ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y _hy
        ring
      _ = (∫ y : ℝ in -1..1, w x ^ 2 - 2 * w x * w y) +
          ∫ y : ℝ in -1..1, w y ^ 2 := by
        rw [intervalIntegral.integral_add (hconst.sub hlin) hwSqInt]
      _ = ((∫ y : ℝ in -1..1, w x ^ 2) -
          ∫ y : ℝ in -1..1, 2 * w x * w y) + S₂ := by
        rw [intervalIntegral.integral_sub hconst hlin]
      _ = 2 * w x ^ 2 - 2 * w x * M + S₂ := by
        rw [intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul]
        dsimp only [M, S₂]
        norm_num
  have hdouble :
      (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
        4 * S₂ - 2 * M ^ 2 := by
    rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
        fun x ↦ 2 * w x ^ 2 - 2 * w x * M + S₂ by
      funext x
      exact hinner x]
    have htwoSq : IntervalIntegrable (fun x : ℝ ↦ 2 * w x ^ 2)
        volume (-1 : ℝ) 1 := hwSqInt.const_mul 2
    have htwoLin : IntervalIntegrable (fun x : ℝ ↦ 2 * w x * M)
        volume (-1 : ℝ) 1 :=
      (by fun_prop : Continuous (fun x : ℝ ↦ 2 * w x * M)).intervalIntegrable _ _
    have hconstS : IntervalIntegrable (fun _x : ℝ ↦ S₂)
        volume (-1 : ℝ) 1 := intervalIntegrable_const
    have hlinValue : (∫ x : ℝ in -1..1, 2 * w x * M) = 2 * M ^ 2 := by
      rw [show (fun x : ℝ ↦ 2 * w x * M) = fun x ↦ (2 * M) * w x by
        funext x
        ring,
        intervalIntegral.integral_const_mul]
      ring
    rw [intervalIntegral.integral_add (htwoSq.sub htwoLin) hconstS,
      intervalIntegral.integral_sub htwoSq htwoLin,
      intervalIntegral.integral_const_mul,
      hlinValue,
      intervalIntegral.integral_const]
    dsimp only [M, S₂]
    norm_num
    ring_nf
  have hvariance : centeredIntervalVariance w = S₂ - M ^ 2 / 2 := by
    unfold centeredIntervalVariance centeredIntervalMean
    have hlin : IntervalIntegrable (fun x : ℝ ↦
        2 * w x * ((1 / 2 : ℝ) * M)) volume (-1 : ℝ) 1 :=
      (by fun_prop : Continuous
        (fun x : ℝ ↦ 2 * w x * ((1 / 2 : ℝ) * M))).intervalIntegrable _ _
    have hconst : IntervalIntegrable (fun _x : ℝ ↦
        ((1 / 2 : ℝ) * M) ^ 2) volume (-1 : ℝ) 1 :=
      intervalIntegrable_const
    have hlinValue :
        (∫ x : ℝ in -1..1, 2 * w x * ((1 / 2 : ℝ) * M)) = M ^ 2 := by
      rw [show (fun x : ℝ ↦ 2 * w x * ((1 / 2 : ℝ) * M)) =
          fun x ↦ M * w x by
        funext x
        ring,
        intervalIntegral.integral_const_mul]
      ring
    calc
      (∫ x : ℝ in -1..1,
          (w x - (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x) ^ 2) =
          ∫ x : ℝ in -1..1,
            (w x ^ 2 - 2 * w x * ((1 / 2 : ℝ) * M)) +
              ((1 / 2 : ℝ) * M) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [M]
        ring
      _ = (∫ x : ℝ in -1..1,
            w x ^ 2 - 2 * w x * ((1 / 2 : ℝ) * M)) +
          ∫ _x : ℝ in -1..1, ((1 / 2 : ℝ) * M) ^ 2 := by
        rw [intervalIntegral.integral_add (hwSqInt.sub hlin) hconst]
      _ = S₂ - M ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub hwSqInt hlin,
          hlinValue,
          intervalIntegral.integral_const]
        dsimp only [M, S₂]
        norm_num
        ring_nf
  rw [hdouble, hvariance]
  ring

/-- The raw centered logarithmic energy controls twice the variance about the
interval mean.  This uses only `|x-y| ≤ 2` on the centered square and the
exact double-integral identity above. -/
theorem two_mul_variance_le_centeredRawLogEnergy
    (w : ℝ → ℝ) (hw : Continuous w)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    2 * centeredIntervalVariance w ≤ centeredRawLogEnergy w := by
  let S : Set ℝ := Icc (-1 : ℝ) 1
  let L : ℝ × ℝ → ℝ := fun p ↦ (1 / 2 : ℝ) * (w p.1 - w p.2) ^ 2
  let K : ℝ × ℝ → ℝ := fun p ↦ centeredLogDifferenceKernel w p.1 p.2
  have hLInt : IntegrableOn L (S ×ˢ S)
      ((volume : Measure ℝ).prod volume) := by
    exact (by fun_prop : Continuous L).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hpoint : ∀ p ∈ S ×ˢ S, L p ≤ K p := by
    intro p hp
    have hdist : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    dsimp only [L, K]
    unfold centeredLogDifferenceKernel
    by_cases hxy : |p.1 - p.2| = 0
    · have heq : p.1 = p.2 := sub_eq_zero.mp (abs_eq_zero.mp hxy)
      simp [heq]
    · have hxypos : 0 < |p.1 - p.2| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxy)
      rw [le_div_iff₀ hxypos]
      nlinarith [sq_nonneg (w p.1 - w p.2)]
  have hmono :
      (∫ p : ℝ × ℝ in S ×ˢ S, L p
          ∂((volume : Measure ℝ).prod volume)) ≤
        ∫ p : ℝ × ℝ in S ×ˢ S, K p
          ∂((volume : Measure ℝ).prod volume) := by
    exact setIntegral_mono_on hLInt henergy
      (measurableSet_Icc.prod measurableSet_Icc)
      hpoint
  have hLValue :
      (∫ p : ℝ × ℝ in S ×ˢ S, L p
          ∂((volume : Measure ℝ).prod volume)) =
        2 * centeredIntervalVariance w := by
    dsimp only [S, L]
    have hscale : (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
          (1 / 2 : ℝ) * (w p.1 - w p.2) ^ 2
            ∂((volume : Measure ℝ).prod volume)) =
        (1 / 2 : ℝ) *
          ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
            (w p.1 - w p.2) ^ 2
              ∂((volume : Measure ℝ).prod volume) := by
      change (∫ p : ℝ × ℝ,
          (1 / 2 : ℝ) * (w p.1 - w p.2) ^ 2
            ∂((volume : Measure ℝ).prod volume).restrict
              (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) = _
      rw [integral_const_mul]
    rw [hscale]
    have hdiffInt : IntegrableOn
        (fun p : ℝ × ℝ ↦ (w p.1 - w p.2) ^ 2)
        (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        ((volume : Measure ℝ).prod volume) := by
      exact (by fun_prop : Continuous
        (fun p : ℝ × ℝ ↦ (w p.1 - w p.2) ^ 2)).continuousOn
          |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [setIntegral_prod _ hdiffInt]
    have hnested :
        (∫ x : ℝ in Icc (-1 : ℝ) 1,
          ∫ y : ℝ in Icc (-1 : ℝ) 1, (w x - w y) ^ 2) =
        ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, (w x - w y) ^ 2 := by
      symm
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in -1..1, (w x - w y) ^ 2) =
        ∫ y : ℝ in Icc (-1 : ℝ) 1, (w x - w y) ^ 2
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [hnested, integral_integral_sq_sub_eq_four_mul_variance w hw]
    ring
  rw [hLValue] at hmono
  rw [centeredRawLogEnergy_eq_setIntegral w henergy]
  exact hmono

/-- Tunable mean--variance estimate for the normalized endpoint pairing.
The coefficient `1/10` is exactly the endpoint length `2/5` times the square
of the mean normalization `1/2`. -/
theorem fourCellEndpointPairing_le_rawLogEnergy_add_mean
    (w : ℝ → ℝ) (hw : Continuous w)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume))
    {ε : ℝ} (hε : 0 < ε) :
    fourCellEndpointPairing w ≤
      ((1 + ε) / 4) * centeredRawLogEnergy w +
        (1 / 10 : ℝ) * (1 + 1 / ε) *
          (∫ x : ℝ in -1..1, w x) ^ 2 := by
  let m : ℝ := centeredIntervalMean w
  let u : ℝ → ℝ := fun x ↦ w x - m
  have hu : Continuous u := hw.sub continuous_const
  have hpoint (x : ℝ) :
      w x * w (x - 8 / 5) ≤
        ((1 + ε) / 2) * (u x ^ 2 + u (x - 8 / 5) ^ 2) +
          (1 + 1 / ε) * m ^ 2 := by
    have hε0 : ε ≠ 0 := ne_of_gt hε
    dsimp only [u, m]
    have hyoung (z : ℝ) :
        (centeredIntervalMean w + z) ^ 2 ≤
          (1 + ε) * z ^ 2 + (1 + 1 / ε) * centeredIntervalMean w ^ 2 := by
      have hid : ε *
          ((1 + ε) * z ^ 2 + (1 + 1 / ε) * centeredIntervalMean w ^ 2 -
            (centeredIntervalMean w + z) ^ 2) =
          (ε * z - centeredIntervalMean w) ^ 2 := by
        field_simp [hε0]
        ring
      have hmul : 0 ≤ ε *
          ((1 + ε) * z ^ 2 + (1 + 1 / ε) * centeredIntervalMean w ^ 2 -
            (centeredIntervalMean w + z) ^ 2) := by
        rw [hid]
        positivity
      have hdiff : 0 ≤
          (1 + ε) * z ^ 2 + (1 + 1 / ε) * centeredIntervalMean w ^ 2 -
            (centeredIntervalMean w + z) ^ 2 :=
        nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hmul) hε
      linarith
    have hamgm : w x * w (x - 8 / 5) ≤
        (w x ^ 2 + w (x - 8 / 5) ^ 2) / 2 := by
      nlinarith [sq_nonneg (w x - w (x - 8 / 5))]
    have hx := hyoung (w x - centeredIntervalMean w)
    have hy := hyoung (w (x - 8 / 5) - centeredIntervalMean w)
    have hxid : centeredIntervalMean w +
        (w x - centeredIntervalMean w) = w x := by ring
    have hyid : centeredIntervalMean w +
        (w (x - 8 / 5) - centeredIntervalMean w) = w (x - 8 / 5) := by ring
    rw [hxid] at hx
    rw [hyid] at hy
    nlinarith
  have hpairInt : IntervalIntegrable
      (fun x : ℝ ↦ w x * w (x - 8 / 5)) volume (3 / 5 : ℝ) 1 :=
    (hw.mul (hw.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable
      (fun x : ℝ ↦ ((1 + ε) / 2) *
          (u x ^ 2 + u (x - 8 / 5) ^ 2) +
        (1 + 1 / ε) * m ^ 2) volume (3 / 5 : ℝ) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ ((1 + ε) / 2) *
        (u x ^ 2 + u (x - 8 / 5) ^ 2) +
          (1 + 1 / ε) * m ^ 2)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num :
      (3 / 5 : ℝ) ≤ 1) hpairInt hupperInt (fun x _hx ↦ hpoint x)
  unfold fourCellEndpointPairing
  calc
    (∫ x : ℝ in (3 / 5 : ℝ)..1, w x * w (x - 8 / 5)) ≤
        ∫ x : ℝ in (3 / 5 : ℝ)..1,
          ((1 + ε) / 2) * (u x ^ 2 + u (x - 8 / 5) ^ 2) +
            (1 + 1 / ε) * m ^ 2 := hmono
    _ = ((1 + ε) / 2) *
          ((∫ x : ℝ in (3 / 5 : ℝ)..1, u x ^ 2) +
            ∫ x : ℝ in (-1 : ℝ)..(-3 / 5), u x ^ 2) +
          (2 / 5 : ℝ) * (1 + 1 / ε) * m ^ 2 := by
      have hshift :
          (∫ x : ℝ in (3 / 5 : ℝ)..1, u (x - 8 / 5) ^ 2) =
            ∫ x : ℝ in (-1 : ℝ)..(-3 / 5), u x ^ 2 := by
        have h := intervalIntegral.integral_comp_sub_right
          (f := fun x : ℝ ↦ u x ^ 2)
          (a := (3 / 5 : ℝ)) (b := 1) (8 / 5 : ℝ)
        norm_num at h
        convert h using 1
        ring
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add,
        hshift,
        intervalIntegral.integral_const]
      · norm_num
        ring
      · exact (hu.pow 2).intervalIntegrable _ _
      · exact ((hu.comp (continuous_id.sub continuous_const)).pow 2).intervalIntegrable _ _
      · exact (((hu.pow 2).add
          ((hu.comp (continuous_id.sub continuous_const)).pow 2)).const_mul _).intervalIntegrable _ _
      · exact intervalIntegrable_const
    _ ≤ ((1 + ε) / 2) * centeredIntervalVariance w +
          (2 / 5 : ℝ) * (1 + 1 / ε) * m ^ 2 := by
      have hcoeff : 0 ≤ (1 + ε) / 2 := by positivity
      have hsub :
          (∫ x : ℝ in (3 / 5 : ℝ)..1, u x ^ 2) +
              ∫ x : ℝ in (-1 : ℝ)..(-3 / 5), u x ^ 2 ≤
            centeredIntervalVariance w := by
        unfold centeredIntervalVariance
        dsimp only [u, m]
        let q : ℝ → ℝ := fun x ↦ (w x - centeredIntervalMean w) ^ 2
        have hq : Continuous q := by
          dsimp only [q]
          fun_prop
        have hleft : IntervalIntegrable q volume (-1 : ℝ) (-3 / 5) :=
          hq.intervalIntegrable _ _
        have hmid : IntervalIntegrable q volume (-3 / 5 : ℝ) (3 / 5) :=
          hq.intervalIntegrable _ _
        have hright : IntervalIntegrable q volume (3 / 5 : ℝ) 1 :=
          hq.intervalIntegrable _ _
        have hleftMid : IntervalIntegrable q volume (-1 : ℝ) (3 / 5) :=
          hq.intervalIntegrable _ _
        have hsplitLeft :=
          intervalIntegral.integral_add_adjacent_intervals hleft hmid
        have hsplitAll :=
          intervalIntegral.integral_add_adjacent_intervals hleftMid hright
        have hmidNonneg : 0 ≤ ∫ x : ℝ in (-3 / 5)..(3 / 5), q x := by
          exact intervalIntegral.integral_nonneg (by norm_num) (fun x _hx ↦ sq_nonneg _)
        change (∫ x : ℝ in (3 / 5 : ℝ)..1, q x) +
            (∫ x : ℝ in (-1 : ℝ)..(-3 / 5), q x) ≤
          ∫ x : ℝ in (-1 : ℝ)..1, q x
        rw [← hsplitAll, ← hsplitLeft]
        linarith
      gcongr
    _ ≤ ((1 + ε) / 4) * centeredRawLogEnergy w +
          (2 / 5 : ℝ) * (1 + 1 / ε) * m ^ 2 := by
      have hvar := two_mul_variance_le_centeredRawLogEnergy w hw henergy
      have hcoeff : 0 ≤ (1 + ε) / 4 := by positivity
      nlinarith
    _ = ((1 + ε) / 4) * centeredRawLogEnergy w +
          (1 / 10 : ℝ) * (1 + 1 / ε) *
            (∫ x : ℝ in -1..1, w x) ^ 2 := by
      unfold m centeredIntervalMean
      ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellEndpointVarianceStructural
