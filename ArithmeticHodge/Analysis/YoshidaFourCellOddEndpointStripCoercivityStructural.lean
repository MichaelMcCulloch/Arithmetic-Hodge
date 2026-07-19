import ArithmeticHodge.Analysis.CenteredLogEnergyGap
import ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRawParityFoldStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddEndpointStripCoercivityStructural

noncomputable section

open CenteredLogEnergyGap
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellRawParityFoldStructural

/-!
# Odd four-cell endpoint-strip coercivity

The prime involution on the positive endpoint strip `[3/5,1]` is reflection
about `4/5`.  Its reflection-even component receives a favorable prime mass.
Only the reflection-odd component has the wrong prime sign, and the exact
mean-zero logarithmic gap on that strip pays for it while retaining a
strict reserve.
-/

/-- Pull the positive endpoint strip `[3/5,1]` back to `[-1,1]`. -/
def fourCellOddEndpointStripPullback (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  w (4 / 5 + z / 5)

/-- Reflection-even component for the endpoint-strip involution. -/
def fourCellOddEndpointStripEven (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  (fourCellOddEndpointStripPullback w z +
    fourCellOddEndpointStripPullback w (-z)) / 2

/-- Reflection-odd component for the endpoint-strip involution. -/
def fourCellOddEndpointStripOdd (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  (fourCellOddEndpointStripPullback w z -
    fourCellOddEndpointStripPullback w (-z)) / 2

/-- Physical `L²` mass of the strip-even component. -/
def fourCellOddEndpointStripEvenMass (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
    fourCellOddEndpointStripEven w z ^ 2

/-- Physical `L²` mass of the strip-odd component. -/
def fourCellOddEndpointStripOddMass (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
    fourCellOddEndpointStripOdd w z ^ 2

/-- Physical same-sign raw energy of the endpoint strip.  The factor `1/5`
is the single affine Jacobian left by the logarithmic kernel. -/
def fourCellOddEndpointStripRawEnergy (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) *
    centeredRawLogEnergy (fourCellOddEndpointStripPullback w)

/-- Raw energy of the strip-even reflection component. -/
def fourCellOddEndpointStripEvenRawEnergy (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) *
    centeredRawLogEnergy (fourCellOddEndpointStripEven w)

/-- Raw energy of the strip-odd reflection component. -/
def fourCellOddEndpointStripOddRawEnergy (w : ℝ → ℝ) : ℝ :=
  (1 / 5 : ℝ) *
    centeredRawLogEnergy (fourCellOddEndpointStripOdd w)

theorem fourCellOddEndpointStripEven_even (w : ℝ → ℝ) :
    Function.Even (fourCellOddEndpointStripEven w) := by
  intro z
  unfold fourCellOddEndpointStripEven
  rw [neg_neg]
  ring

theorem fourCellOddEndpointStripOdd_odd (w : ℝ → ℝ) :
    Function.Odd (fourCellOddEndpointStripOdd w) := by
  intro z
  unfold fourCellOddEndpointStripOdd
  rw [neg_neg]
  ring

theorem fourCellOddEndpointStripEven_add_odd
    (w : ℝ → ℝ) (z : ℝ) :
    fourCellOddEndpointStripEven w z +
        fourCellOddEndpointStripOdd w z =
      fourCellOddEndpointStripPullback w z := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripOdd
  ring

theorem continuous_fourCellOddEndpointStripPullback
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fourCellOddEndpointStripPullback w) := by
  unfold fourCellOddEndpointStripPullback
  fun_prop

theorem continuous_fourCellOddEndpointStripEven
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fourCellOddEndpointStripEven w) := by
  unfold fourCellOddEndpointStripEven
  exact ((continuous_fourCellOddEndpointStripPullback w hw).add
    ((continuous_fourCellOddEndpointStripPullback w hw).comp
      continuous_neg)).div_const 2

theorem continuous_fourCellOddEndpointStripOdd
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fourCellOddEndpointStripOdd w) := by
  unfold fourCellOddEndpointStripOdd
  exact ((continuous_fourCellOddEndpointStripPullback w hw).sub
    ((continuous_fourCellOddEndpointStripPullback w hw).comp
      continuous_neg)).div_const 2

/-- Orthogonal `L²` splitting under the endpoint-strip involution. -/
theorem fourCellOddEndpointStrip_mass_eq_even_add_odd
    (w : ℝ → ℝ) (hw : Continuous w) :
    (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
        fourCellOddEndpointStripPullback w z ^ 2 =
      fourCellOddEndpointStripEvenMass w +
        fourCellOddEndpointStripOddMass w := by
  let f := fourCellOddEndpointStripPullback w
  let e := fourCellOddEndpointStripEven w
  let o := fourCellOddEndpointStripOdd w
  have hf : Continuous f := continuous_fourCellOddEndpointStripPullback w hw
  have he : Continuous e := continuous_fourCellOddEndpointStripEven w hw
  have ho : Continuous o := continuous_fourCellOddEndpointStripOdd w hw
  have hcrossOdd : Function.Odd (fun z : ℝ ↦ e z * o z) := by
    intro z
    change e (-z) * o (-z) = -(e z * o z)
    change fourCellOddEndpointStripEven w (-z) *
        fourCellOddEndpointStripOdd w (-z) =
      -(fourCellOddEndpointStripEven w z *
        fourCellOddEndpointStripOdd w z)
    rw [fourCellOddEndpointStripEven_even w z,
      fourCellOddEndpointStripOdd_odd w z]
    ring
  have hcross : (∫ z : ℝ in -1..1, e z * o z) = 0 := by
    have hreflect := intervalIntegral.integral_comp_neg
      (f := fun z : ℝ ↦ e z * o z) (a := (-1 : ℝ)) (b := 1)
    rw [show (fun z : ℝ ↦ e (-z) * o (-z)) =
        fun z ↦ -(e z * o z) by
      funext z
      exact hcrossOdd z] at hreflect
    rw [intervalIntegral.integral_neg] at hreflect
    norm_num at hreflect
    linarith
  have hpoint : f = fun z ↦ e z + o z := by
    funext z
    exact (fourCellOddEndpointStripEven_add_odd w z).symm
  change (1 / 5 : ℝ) * ∫ z : ℝ in -1..1, f z ^ 2 = _
  rw [hpoint]
  have heSq : IntervalIntegrable (fun z : ℝ ↦ e z ^ 2)
      volume (-1) 1 := (he.pow 2).intervalIntegrable (-1) 1
  have hoSq : IntervalIntegrable (fun z : ℝ ↦ o z ^ 2)
      volume (-1) 1 := (ho.pow 2).intervalIntegrable (-1) 1
  have heo : IntervalIntegrable (fun z : ℝ ↦ e z * o z)
      volume (-1) 1 := (he.mul ho).intervalIntegrable (-1) 1
  rw [show (fun z : ℝ ↦ (e z + o z) ^ 2) =
      fun z ↦ e z ^ 2 + 2 * (e z * o z) + o z ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_add (heSq.add (heo.const_mul 2)) hoSq,
    intervalIntegral.integral_add heSq (heo.const_mul 2),
    intervalIntegral.integral_const_mul, hcross]
  unfold fourCellOddEndpointStripEvenMass fourCellOddEndpointStripOddMass
  ring

/-- Reflecting the centered profile preserves every fixed positive-distance
energy.  This is the one-dimensional measure-preserving reflection behind
the strip parity split. -/
theorem centeredPositiveDistanceEnergy_comp_neg
    (f : ℝ → ℝ) (t : ℝ) :
    centeredPositiveDistanceEnergy (fun z ↦ f (-z)) t =
      centeredPositiveDistanceEnergy f t := by
  let q : ℝ → ℝ := fun y ↦ (f (t + y) - f y) ^ 2
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := q) (a := (-1 : ℝ)) (b := 1 - t) (-t)
  unfold centeredPositiveDistanceEnergy
  calc
    (∫ x : ℝ in -1..1 - t,
        ((fun z ↦ f (-z)) (t + x) - (fun z ↦ f (-z)) x) ^ 2) =
        ∫ x : ℝ in -1..1 - t, q (-t - x) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          dsimp only [q]
          ring
    _ = ∫ x : ℝ in -1..1 - t, q x := by
      convert hreflect using 1
      all_goals ring
    _ = ∫ x : ℝ in -1..1 - t, (f (t + x) - f x) ^ 2 := by
      rfl

/-- At every positive distance, the endpoint-strip energy splits exactly
into its reflection-even and reflection-odd pieces. -/
theorem fourCellOddEndpointStrip_positiveDistanceEnergy_eq_even_add_odd
    (w : ℝ → ℝ) (hw : Continuous w) (t : ℝ) :
    centeredPositiveDistanceEnergy
        (fourCellOddEndpointStripPullback w) t =
      centeredPositiveDistanceEnergy
          (fourCellOddEndpointStripEven w) t +
        centeredPositiveDistanceEnergy
          (fourCellOddEndpointStripOdd w) t := by
  let f := fourCellOddEndpointStripPullback w
  let r : ℝ → ℝ := fun z ↦ f (-z)
  let e := fourCellOddEndpointStripEven w
  let o := fourCellOddEndpointStripOdd w
  have hf : Continuous f := continuous_fourCellOddEndpointStripPullback w hw
  have hr : Continuous r := hf.comp continuous_neg
  have he : Continuous e := continuous_fourCellOddEndpointStripEven w hw
  have ho : Continuous o := continuous_fourCellOddEndpointStripOdd w hw
  have heDiff : Continuous (fun x : ℝ ↦ (e (t + x) - e x) ^ 2) := by
    fun_prop
  have hoDiff : Continuous (fun x : ℝ ↦ (o (t + x) - o x) ^ 2) := by
    fun_prop
  have hfDiff : Continuous (fun x : ℝ ↦ (f (t + x) - f x) ^ 2) := by
    fun_prop
  have hrDiff : Continuous (fun x : ℝ ↦ (r (t + x) - r x) ^ 2) := by
    fun_prop
  have hreflect : centeredPositiveDistanceEnergy r t =
      centeredPositiveDistanceEnergy f t := by
    exact centeredPositiveDistanceEnergy_comp_neg f t
  have hpoint (x : ℝ) :
      (e (t + x) - e x) ^ 2 + (o (t + x) - o x) ^ 2 =
        (1 / 2 : ℝ) *
          ((f (t + x) - f x) ^ 2 + (r (t + x) - r x) ^ 2) := by
    dsimp only [e, o, f, r, fourCellOddEndpointStripEven,
      fourCellOddEndpointStripOdd]
    ring
  unfold centeredPositiveDistanceEnergy at hreflect ⊢
  calc
    (∫ x : ℝ in -1..1 - t, (f (t + x) - f x) ^ 2) =
        (1 / 2 : ℝ) *
          ((∫ x : ℝ in -1..1 - t, (f (t + x) - f x) ^ 2) +
            ∫ x : ℝ in -1..1 - t, (r (t + x) - r x) ^ 2) := by
              rw [hreflect]
              ring
    _ = ∫ x : ℝ in -1..1 - t,
        ((1 / 2 : ℝ) *
          ((f (t + x) - f x) ^ 2 + (r (t + x) - r x) ^ 2)) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add
                (hfDiff.intervalIntegrable _ _)
                (hrDiff.intervalIntegrable _ _)]
    _ = ∫ x : ℝ in -1..1 - t,
        ((e (t + x) - e x) ^ 2 + (o (t + x) - o x) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          exact (hpoint x).symm
    _ = (∫ x : ℝ in -1..1 - t, (e (t + x) - e x) ^ 2) +
        ∫ x : ℝ in -1..1 - t, (o (t + x) - o x) ^ 2 := by
          exact intervalIntegral.integral_add
            (heDiff.intervalIntegrable _ _)
            (hoDiff.intervalIntegrable _ _)

/-- The full logarithmic difference energy of the endpoint strip is the
orthogonal sum of the reflection-even and reflection-odd raw energies.  The
proof passes through the positive-distance triangle, so no singular-kernel
integral is rearranged without a form-domain theorem. -/
theorem fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellOddEndpointStripRawEnergy w =
      fourCellOddEndpointStripEvenRawEnergy w +
        fourCellOddEndpointStripOddRawEnergy w := by
  let f := fourCellOddEndpointStripPullback w
  let e := fourCellOddEndpointStripEven w
  let o := fourCellOddEndpointStripOdd w
  have hwcont : Continuous w := hw.continuous
  have hfDiff : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun z : ℝ ↦ w (4 / 5 + z / 5))
    fun_prop
  have heDiff : ContDiff ℝ 1 e := by
    change ContDiff ℝ 1 (fun z : ℝ ↦
      (w (4 / 5 + z / 5) + w (4 / 5 + (-z) / 5)) / 2)
    fun_prop
  have hoDiff : ContDiff ℝ 1 o := by
    change ContDiff ℝ 1 (fun z : ℝ ↦
      (w (4 / 5 + z / 5) - w (4 / 5 + (-z) / 5)) / 2)
    fun_prop
  have hfLocal : LocallyLipschitzOn (Icc (-1) 1) f :=
    hfDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have heLocal : LocallyLipschitzOn (Icc (-1) 1) e :=
    heDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hoLocal : LocallyLipschitzOn (Icc (-1) 1) o :=
    hoDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfInt :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      f hfLocal
  have heInt :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      e heLocal
  have hoInt :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      o hoLocal
  have hpoint (t : ℝ) :
      centeredPositiveDistanceEnergy f t / t =
        centeredPositiveDistanceEnergy e t / t +
          centeredPositiveDistanceEnergy o t / t := by
    have hsplit :=
      fourCellOddEndpointStrip_positiveDistanceEnergy_eq_even_add_odd
        w hwcont t
    dsimp only [f, e, o] at hsplit ⊢
    rw [hsplit]
    ring
  have houter :
      (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy f t / t) =
        (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy e t / t) +
          ∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy o t / t := by
    calc
      _ = ∫ t : ℝ in 0..2,
          (centeredPositiveDistanceEnergy e t / t +
            centeredPositiveDistanceEnergy o t / t) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              exact hpoint t
      _ = _ := intervalIntegral.integral_add heInt hoInt
  have hfFold :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      f hfLocal
  have heFold :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      e heLocal
  have hoFold :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      o hoLocal
  unfold fourCellOddEndpointStripRawEnergy
    fourCellOddEndpointStripEvenRawEnergy
    fourCellOddEndpointStripOddRawEnergy
  dsimp only [f, e, o] at hfFold heFold hoFold
  linarith

/-- The reflection-odd strip component has zero mean, so the complete
centered logarithmic gap pays four times its physical strip mass. -/
theorem four_mul_fourCellOddEndpointStripOddMass_le_rawEnergy
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    4 * fourCellOddEndpointStripOddMass w ≤
      fourCellOddEndpointStripOddRawEnergy w := by
  let o := fourCellOddEndpointStripOdd w
  have hoDiff : ContDiff ℝ 1 o := by
    change ContDiff ℝ 1 (fun z : ℝ ↦
      (w (4 / 5 + z / 5) - w (4 / 5 + (-z) / 5)) / 2)
    fun_prop
  have hoCont : Continuous o := hoDiff.continuous
  have hoLocal : LocallyLipschitzOn (Icc (-1) 1) o :=
    hoDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hoOdd : Function.Odd o := by
    simpa only [o] using fourCellOddEndpointStripOdd_odd w
  have hmean : (∫ z : ℝ in -1..1, o z) = 0 := by
    have hchange :
        (∫ z : ℝ in -1..1, o (-z)) = ∫ z : ℝ in -1..1, o z := by
      simpa only [neg_neg] using intervalIntegral.integral_comp_neg
        (f := o) (a := (-1 : ℝ)) (b := 1)
    have hoddIntegral :
        (∫ z : ℝ in -1..1, o (-z)) = -∫ z : ℝ in -1..1, o z := by
      rw [show (fun z : ℝ ↦ o (-z)) = fun z ↦ -o z by
        funext z
        exact hoOdd z]
      exact intervalIntegral.integral_neg
    rw [hoddIntegral] at hchange
    exact CharZero.neg_eq_self_iff.mp hchange
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback o hoLocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback o (t : ℝ)
  have hfCont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfMem : MemLp f 2 :=
    hfCont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hgap := four_mul_integral_sq_le_centeredRawLogEnergy o
    (by simpa only [f] using hfMem)
    (by simpa only [f] using henergy) hmean
  unfold fourCellOddEndpointStripOddMass
    fourCellOddEndpointStripOddRawEnergy
  dsimp only [o] at hgap
  norm_num at hgap ⊢
  linarith

/-- The retained matched endpoint square is exactly four times the
reflection-even strip mass after the affine pullback. -/
theorem integral_fourCellEndpointHalfMatched_sq_eq_four_mul_evenMass
    (w : ℝ → ℝ) :
    (∫ t : ℝ in 0..2 / 5, fourCellEndpointHalfMatched w t ^ 2) =
      4 * fourCellOddEndpointStripEvenMass w := by
  let e := fourCellOddEndpointStripEven w
  have hsubst := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 2 / 5)
    (fun z : ℝ ↦ (2 * e z) ^ 2)
    (by norm_num : (5 : ℝ) ≠ 0) (-1)
  calc
    (∫ t : ℝ in 0..2 / 5, fourCellEndpointHalfMatched w t ^ 2) =
        ∫ t : ℝ in 0..2 / 5, (2 * e (5 * t - 1)) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [e, fourCellOddEndpointStripEven,
            fourCellOddEndpointStripPullback]
          unfold fourCellEndpointHalfMatched
          congr 2
          all_goals ring
    _ = (1 / 5 : ℝ) * ∫ z : ℝ in -1..1, (2 * e z) ^ 2 := by
      convert hsubst using 1
      all_goals norm_num
    _ = 4 * fourCellOddEndpointStripEvenMass w := by
      rw [show (fun z : ℝ ↦ (2 * e z) ^ 2) =
          fun z ↦ 4 * e z ^ 2 by
        funext z
        ring,
        intervalIntegral.integral_const_mul]
      unfold fourCellOddEndpointStripEvenMass
      dsimp only [e]
      ring

/-- The symmetric endpoint half-mass is precisely the physical `L²` mass
of the pulled-back strip. -/
theorem fourCellEndpointHalfMass_eq_stripPullback_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEndpointHalfMass w =
      (1 / 5 : ℝ) * ∫ z : ℝ in -1..1,
        fourCellOddEndpointStripPullback w z ^ 2 := by
  let f := fourCellOddEndpointStripPullback w
  let g : ℝ → ℝ := fun t ↦ w (3 / 5 + t) ^ 2
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := g) (a := (0 : ℝ)) (b := 2 / 5) (2 / 5)
  have hright :
      (∫ t : ℝ in 0..2 / 5, w (1 - t) ^ 2) =
        ∫ t : ℝ in 0..2 / 5, w (3 / 5 + t) ^ 2 := by
    calc
      _ = ∫ t : ℝ in 0..2 / 5, g (2 / 5 - t) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [g]
        congr 2
        ring
      _ = ∫ t : ℝ in 0..2 / 5, g t := by
        convert hreflect using 1
        all_goals norm_num
      _ = _ := by rfl
  have hsubst := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 2 / 5)
    (fun z : ℝ ↦ f z ^ 2)
    (by norm_num : (5 : ℝ) ≠ 0) (-1)
  have hleft :
      (∫ t : ℝ in 0..2 / 5, w (3 / 5 + t) ^ 2) =
        (1 / 5 : ℝ) * ∫ z : ℝ in -1..1, f z ^ 2 := by
    calc
      _ = ∫ t : ℝ in 0..2 / 5, f (5 * t - 1) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [f, fourCellOddEndpointStripPullback]
        congr 2
        ring
      _ = _ := by
        convert hsubst using 1
        all_goals norm_num
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦ w (3 / 5 + t) ^ 2) volume 0 (2 / 5) := by
    have hcont : Continuous (fun t : ℝ ↦ w (3 / 5 + t) ^ 2) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (fun t : ℝ ↦ w (1 - t) ^ 2) volume 0 (2 / 5) := by
    have hcont : Continuous (fun t : ℝ ↦ w (1 - t) ^ 2) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  unfold fourCellEndpointHalfMass
  rw [intervalIntegral.integral_add hleftInt hrightInt,
    hright, hleft]
  dsimp only [f]
  ring

/-- Combining the preceding affine identity with strip reflection
orthogonality expresses the endpoint half-mass in parity coordinates. -/
theorem fourCellEndpointHalfMass_eq_evenMass_add_oddMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEndpointHalfMass w =
      fourCellOddEndpointStripEvenMass w +
        fourCellOddEndpointStripOddMass w := by
  rw [fourCellEndpointHalfMass_eq_stripPullback_mass w hw,
    fourCellOddEndpointStrip_mass_eq_even_add_odd w hw]

/-- In the ambient odd sector the prime atom is diagonal in endpoint-strip
reflection parity: it is favorable on the strip-even mass and unfavorable
on the strip-odd mass. -/
theorem neg_primePairing_eq_evenMass_sub_oddMass_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(Real.sqrt 2 * Real.log 2) * fourCellEndpointPairing w =
      Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w -
        Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripOddMass w := by
  calc
    _ = (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 5,
            fourCellEndpointHalfMatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w :=
      neg_primePairing_eq_halfMatched_sub_mass_of_odd w hw hodd
    _ = _ := by
      rw [integral_fourCellEndpointHalfMatched_sq_eq_four_mul_evenMass w,
        fourCellEndpointHalfMass_eq_evenMass_add_oddMass w hw]
      ring

/-- Retained endpoint-strip coercivity in the odd ambient sector.  Half of
the local same-sign raw energy pays the adverse strip-odd prime mass through
the exact mean-zero gap, while the favorable strip-even prime mass is kept
rather than discarded. -/
theorem fourCellOddEndpointStrip_retained_prime_coercivity
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
          Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
          (2 - Real.sqrt 2 * Real.log 2) *
            fourCellOddEndpointStripOddMass w ≤
      (1 / 2 : ℝ) * fourCellOddEndpointStripRawEnergy w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  have hraw := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have hgap := four_mul_fourCellOddEndpointStripOddMass_le_rawEnergy w hw
  have hprime := neg_primePairing_eq_evenMass_sub_oddMass_of_odd
    w hw.continuous hodd
  have hform :
      (1 / 2 : ℝ) * fourCellOddEndpointStripRawEnergy w -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
          (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w +
          Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w -
          Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripOddMass w := by
    rw [hraw]
    calc
      _ = (1 / 2 : ℝ) *
            (fourCellOddEndpointStripEvenRawEnergy w +
              fourCellOddEndpointStripOddRawEnergy w) +
          (Real.sqrt 2 * Real.log 2 *
              fourCellOddEndpointStripEvenMass w -
            Real.sqrt 2 * Real.log 2 *
              fourCellOddEndpointStripOddMass w) := by
        rw [← hprime]
        ring
      _ = _ := by ring
  rw [hform]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddEndpointStripCoercivityStructural
