import ArithmeticHodge.Analysis.YoshidaFiveCellCanonicalLowTailSchurStructural
import ArithmeticHodge.Analysis.ShiftedLegendreBasis
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedLowTailStructural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open MultiplicativeWeil
open MultiplicativeWeilFiveCellResidualFactorTwoStructural
open MultiplicativeWeilFiveCellSingleProfileStructural
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFiveCellCanonicalLowTailSchurStructural
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaFiveCellHighTailCoercivityStructural

/-!
# Endpoint-adapted cutoff-nine decomposition for the five-cell operator

The canonical cutoff-nine residual has the exact harmonic gap, but its two
endpoint traces need not vanish.  Degrees nine and ten are already in that
higher subspace and have opposite and equal endpoint signatures.  They can
therefore absorb both traces without destroying any moment below nine.
-/

/-- The first even reserve above the cutoff-nine low space. -/
def fiveCellEvenEndpointReserve (x : ℝ) : ℝ :=
  (shiftedLegendreReal 10).eval ((x + 1) / 2)

/-- The first odd reserve above the cutoff-nine low space. -/
def fiveCellOddEndpointReserve (x : ℝ) : ℝ :=
  (shiftedLegendreReal 9).eval ((x + 1) / 2)

private theorem shiftedLegendreReal_eval_one (n : ℕ) :
    (shiftedLegendreReal n).eval 1 = (-1 : ℝ) ^ n := by
  have h := Polynomial.shiftedLegendre_eval_symm n (1 : ℝ)
  have h' :
      (shiftedLegendreReal n).eval 1 =
        (-1 : ℝ) ^ n * (shiftedLegendreReal n).eval 0 := by
    simp only [shiftedLegendreReal, Polynomial.eval_map]
    change Polynomial.aeval (1 : ℝ) (Polynomial.shiftedLegendre n) =
      (-1 : ℝ) ^ n *
        Polynomial.aeval (0 : ℝ) (Polynomial.shiftedLegendre n)
    simpa using h
  rw [shiftedLegendreReal_eval_zero] at h'
  simpa using h'

theorem fiveCellEvenEndpointReserve_endpoints :
    fiveCellEvenEndpointReserve (-1) = 1 ∧
      fiveCellEvenEndpointReserve 1 = 1 := by
  constructor
  · simp [fiveCellEvenEndpointReserve]
  · rw [fiveCellEvenEndpointReserve]
    norm_num [shiftedLegendreReal_eval_one]

theorem fiveCellOddEndpointReserve_endpoints :
    fiveCellOddEndpointReserve (-1) = 1 ∧
      fiveCellOddEndpointReserve 1 = -1 := by
  constructor
  · simp [fiveCellOddEndpointReserve]
  · rw [fiveCellOddEndpointReserve]
    norm_num [shiftedLegendreReal_eval_one]

private theorem contDiff_fiveCellEvenEndpointReserve :
    ContDiff ℝ 1 fiveCellEvenEndpointReserve := by
  let p := shiftedLegendreReal 10
  have hp : ContDiff ℝ 1 (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) 1
  have haff : ContDiff ℝ 1 (fun x : ℝ ↦ (x + 1) / 2) := by fun_prop
  simpa only [fiveCellEvenEndpointReserve, p, Function.comp_apply] using
    hp.comp haff

private theorem contDiff_fiveCellOddEndpointReserve :
    ContDiff ℝ 1 fiveCellOddEndpointReserve := by
  let p := shiftedLegendreReal 9
  have hp : ContDiff ℝ 1 (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) 1
  have haff : ContDiff ℝ 1 (fun x : ℝ ↦ (x + 1) / 2) := by fun_prop
  simpa only [fiveCellOddEndpointReserve, p, Function.comp_apply] using
    hp.comp haff

@[simp]
theorem centeredPullback_fiveCellEvenEndpointReserve (t : ℝ) :
    centeredPullback fiveCellEvenEndpointReserve t =
      (shiftedLegendreReal 10).eval t := by
  unfold centeredPullback fiveCellEvenEndpointReserve
  congr 1
  ring

@[simp]
theorem centeredPullback_fiveCellOddEndpointReserve (t : ℝ) :
    centeredPullback fiveCellOddEndpointReserve t =
      (shiftedLegendreReal 9).eval t := by
  unfold centeredPullback fiveCellOddEndpointReserve
  congr 1
  ring

private theorem fiveCellEvenEndpointReserve_moment_zero
    (n : ℕ) (hn : n < 9) :
    (∫ t : unitInterval,
      centeredPullback fiveCellEvenEndpointReserve (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = 0 := by
  simp only [centeredPullback_fiveCellEvenEndpointReserve]
  calc
    (∫ t : unitInterval,
        (shiftedLegendreReal 10).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          (shiftedLegendreReal 10).eval t *
            (shiftedLegendreReal n).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ (shiftedLegendreReal 10).eval t *
          (shiftedLegendreReal n).eval t)
    _ = 0 := integral_shiftedLegendreReal_mul_eq_zero (by omega)

private theorem fiveCellOddEndpointReserve_moment_zero
    (n : ℕ) (hn : n < 9) :
    (∫ t : unitInterval,
      centeredPullback fiveCellOddEndpointReserve (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = 0 := by
  simp only [centeredPullback_fiveCellOddEndpointReserve]
  calc
    (∫ t : unitInterval,
        (shiftedLegendreReal 9).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          (shiftedLegendreReal 9).eval t *
            (shiftedLegendreReal n).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ (shiftedLegendreReal 9).eval t *
          (shiftedLegendreReal n).eval t)
    _ = 0 := integral_shiftedLegendreReal_mul_eq_zero (by omega)

/-- The two endpoint coordinates of the canonical cutoff-nine low part. -/
def fiveCellLowEndpointMean
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  (centeredLegendreLowProjection w hw 9 (-1) +
    centeredLegendreLowProjection w hw 9 1) / 2

def fiveCellLowEndpointAlternating
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  (centeredLegendreLowProjection w hw 9 (-1) -
    centeredLegendreLowProjection w hw 9 1) / 2

/-- Move the two endpoint traces from the low projection into degrees ten
and nine respectively. -/
def fiveCellEndpointAdaptedLow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ := fun x ↦
  centeredLegendreLowProjection w hw 9 x -
    fiveCellLowEndpointMean w hw * fiveCellEvenEndpointReserve x -
    fiveCellLowEndpointAlternating w hw * fiveCellOddEndpointReserve x

/-- The complementary endpoint-adapted higher residual. -/
def fiveCellEndpointAdaptedTail
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ := fun x ↦
  w x - fiveCellEndpointAdaptedLow w hw x

theorem fiveCellEndpointAdaptedLow_add_tail
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointAdaptedLow w hw +
        fiveCellEndpointAdaptedTail w hw = w := by
  funext x
  unfold fiveCellEndpointAdaptedTail
  simp only [Pi.add_apply]
  ring

theorem continuous_fiveCellEndpointAdaptedLow
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fiveCellEndpointAdaptedLow w hw) := by
  unfold fiveCellEndpointAdaptedLow
  exact ((continuous_centeredLegendreLowProjection w hw 9).sub
    (contDiff_fiveCellEvenEndpointReserve.continuous.const_mul _)).sub
      (contDiff_fiveCellOddEndpointReserve.continuous.const_mul _)

theorem continuous_fiveCellEndpointAdaptedTail
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fiveCellEndpointAdaptedTail w hw) := by
  unfold fiveCellEndpointAdaptedTail
  exact hw.sub (continuous_fiveCellEndpointAdaptedLow w hw)

theorem locallyLipschitzOn_fiveCellEndpointAdaptedLow
    (w : ℝ → ℝ) (hw : Continuous w) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellEndpointAdaptedLow w hw) := by
  have hEven : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ fiveCellLowEndpointMean w hw *
        fiveCellEvenEndpointReserve x) := by
    have h : ContDiff ℝ 1 (fun x ↦ fiveCellLowEndpointMean w hw *
        fiveCellEvenEndpointReserve x) :=
      contDiff_const.mul contDiff_fiveCellEvenEndpointReserve
    exact h.locallyLipschitz.locallyLipschitzOn
  have hOdd : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ fiveCellLowEndpointAlternating w hw *
        fiveCellOddEndpointReserve x) := by
    have h : ContDiff ℝ 1 (fun x ↦ fiveCellLowEndpointAlternating w hw *
        fiveCellOddEndpointReserve x) :=
      contDiff_const.mul contDiff_fiveCellOddEndpointReserve
    exact h.locallyLipschitz.locallyLipschitzOn
  unfold fiveCellEndpointAdaptedLow
  exact ((locallyLipschitzOn_centeredLegendreLowProjection w hw 9).sub
    hEven).sub hOdd

theorem locallyLipschitzOn_fiveCellEndpointAdaptedTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellEndpointAdaptedTail w hw) := by
  unfold fiveCellEndpointAdaptedTail
  exact hlocal.sub (locallyLipschitzOn_fiveCellEndpointAdaptedLow w hw)

theorem fiveCellEndpointAdaptedTail_eq_canonical_add_reserves
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointAdaptedTail w hw =
      centeredLegendreHigherResidual w hw 9 +
        fiveCellLowEndpointMean w hw • fiveCellEvenEndpointReserve +
        fiveCellLowEndpointAlternating w hw • fiveCellOddEndpointReserve := by
  funext x
  unfold fiveCellEndpointAdaptedTail fiveCellEndpointAdaptedLow
    centeredLegendreHigherResidual
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem centeredPullback_fiveCellEndpointAdaptedTail
    (w : ℝ → ℝ) (hw : Continuous w) (t : ℝ) :
    centeredPullback (fiveCellEndpointAdaptedTail w hw) t =
      centeredPullback (centeredLegendreHigherResidual w hw 9) t +
        fiveCellLowEndpointMean w hw *
          (shiftedLegendreReal 10).eval t +
        fiveCellLowEndpointAlternating w hw *
          (shiftedLegendreReal 9).eval t := by
  have h := congrFun
    (fiveCellEndpointAdaptedTail_eq_canonical_add_reserves w hw)
    (2 * t - 1)
  unfold centeredPullback
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  simpa only [fiveCellEvenEndpointReserve, fiveCellOddEndpointReserve,
    show (2 * t - 1 + 1) / 2 = t by ring] using h

/-- The endpoint correction uses only degrees nine and ten, so it preserves
every vanished shifted-Legendre moment below the original cutoff. -/
theorem fiveCellEndpointAdaptedTail_momentsVanishBelow
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredLegendreMomentsVanishBelow
      (fiveCellEndpointAdaptedTail w hw) 9 := by
  intro n hn
  let rTerm : unitInterval → ℝ := fun t ↦
    centeredPullback (centeredLegendreHigherResidual w hw 9) (t : ℝ) *
      (shiftedLegendreReal n).eval (t : ℝ)
  let eTerm : unitInterval → ℝ := fun t ↦
    (shiftedLegendreReal 10).eval (t : ℝ) *
      (shiftedLegendreReal n).eval (t : ℝ)
  let oTerm : unitInterval → ℝ := fun t ↦
    (shiftedLegendreReal 9).eval (t : ℝ) *
      (shiftedLegendreReal n).eval (t : ℝ)
  have hq : Continuous (fun t : unitInterval ↦
      (shiftedLegendreReal n).eval (t : ℝ)) :=
    (shiftedLegendreReal n).continuous.comp continuous_subtype_val
  have hrPull : Continuous (fun t : unitInterval ↦
      centeredPullback (centeredLegendreHigherResidual w hw 9) (t : ℝ)) := by
    unfold centeredPullback
    exact (continuous_centeredLegendreHigherResidual w hw 9).comp
      (((continuous_const.mul continuous_subtype_val).sub continuous_const))
  have hePull : Continuous (fun t : unitInterval ↦
      (shiftedLegendreReal 10).eval (t : ℝ)) :=
    (shiftedLegendreReal 10).continuous.comp continuous_subtype_val
  have hoPull : Continuous (fun t : unitInterval ↦
      (shiftedLegendreReal 9).eval (t : ℝ)) :=
    (shiftedLegendreReal 9).continuous.comp continuous_subtype_val
  have hrInt : Integrable rTerm :=
    (hrPull.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heInt : Integrable eTerm :=
    (hePull.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hoInt : Integrable oTerm :=
    (hoPull.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint :
      (fun t : unitInterval ↦
        centeredPullback (fiveCellEndpointAdaptedTail w hw) (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t ↦ rTerm t +
        (fiveCellLowEndpointMean w hw * eTerm t +
          fiveCellLowEndpointAlternating w hw * oTerm t) := by
    funext t
    rw [centeredPullback_fiveCellEndpointAdaptedTail]
    simp only [rTerm, eTerm, oTerm]
    ring
  have hrZero := centeredLegendreHigherResidual_momentsVanishBelow
    w hw 9 n hn
  have heZero := fiveCellEvenEndpointReserve_moment_zero n hn
  have hoZero := fiveCellOddEndpointReserve_moment_zero n hn
  have heZero' : (∫ t : unitInterval, eTerm t) = 0 := by
    simpa only [eTerm, centeredPullback_fiveCellEvenEndpointReserve] using heZero
  have hoZero' : (∫ t : unitInterval, oTerm t) = 0 := by
    simpa only [oTerm, centeredPullback_fiveCellOddEndpointReserve] using hoZero
  rw [hpoint]
  have hinnerInt : Integrable (fun t ↦
      fiveCellLowEndpointMean w hw * eTerm t +
        fiveCellLowEndpointAlternating w hw * oTerm t) :=
    (heInt.const_mul _).add (hoInt.const_mul _)
  calc
    (∫ t : unitInterval, rTerm t +
        (fiveCellLowEndpointMean w hw * eTerm t +
          fiveCellLowEndpointAlternating w hw * oTerm t)) =
        (∫ t : unitInterval, rTerm t) +
          ∫ t : unitInterval,
            (fiveCellLowEndpointMean w hw * eTerm t +
              fiveCellLowEndpointAlternating w hw * oTerm t) :=
      integral_add hrInt hinnerInt
    _ = (∫ t : unitInterval, rTerm t) +
        ((∫ t : unitInterval,
            fiveCellLowEndpointMean w hw * eTerm t) +
          ∫ t : unitInterval,
            fiveCellLowEndpointAlternating w hw * oTerm t) := by
      rw [integral_add (heInt.const_mul _) (hoInt.const_mul _)]
    _ = (∫ t : unitInterval, rTerm t) +
        (fiveCellLowEndpointMean w hw * (∫ t : unitInterval, eTerm t) +
          fiveCellLowEndpointAlternating w hw *
            (∫ t : unitInterval, oTerm t)) := by
      rw [integral_const_mul, integral_const_mul]
    _ = 0 := by
      simp only [rTerm, hrZero, heZero', hoZero', mul_zero, add_zero]

/-- The adapted residual retains the same unconditional infinite tail
coercivity as the canonical residual. -/
theorem fiveCellEndpointAdaptedTail_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    0 ≤ fiveCellEndpointOperator (fiveCellEndpointAdaptedTail w hw) := by
  exact fiveCellEndpointOperator_nonnegative_of_tailNine
    (fiveCellEndpointAdaptedTail w hw)
    (continuous_fiveCellEndpointAdaptedTail w hw)
    (locallyLipschitzOn_fiveCellEndpointAdaptedTail w hw hlocal)
    (fiveCellEndpointAdaptedTail_momentsVanishBelow w hw)

/-- Exact low--mixed--tail expansion with both production endpoint traces
kept inside the finite adapted block. -/
theorem fiveCellEndpointOperator_eq_endpointAdaptedLow_add_tail
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointOperator w =
      fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw) +
        2 * fiveCellEndpointOperatorCross
          (fiveCellEndpointAdaptedLow w hw)
          (fiveCellEndpointAdaptedTail w hw) +
        fiveCellEndpointOperator (fiveCellEndpointAdaptedTail w hw) := by
  rw [← fiveCellEndpointOperator_add]
  rw [fiveCellEndpointAdaptedLow_add_tail w hw]

/-- The endpoint-adapted finite block and one scalar mixed Schur inequality
are sufficient for the complete five-cell operator. -/
theorem fiveCellEndpointOperator_nonnegative_of_endpointAdaptedLowTailSchur
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hlow : 0 ≤ fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw))
    (hmixed : fiveCellEndpointOperatorCross
        (fiveCellEndpointAdaptedLow w hw)
        (fiveCellEndpointAdaptedTail w hw) ^ 2 ≤
      fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw) *
        fiveCellEndpointOperator (fiveCellEndpointAdaptedTail w hw)) :
    0 ≤ fiveCellEndpointOperator w := by
  rw [← fiveCellEndpointAdaptedLow_add_tail w hw]
  exact fiveCellEndpointOperator_add_nonnegative_of_schur
    (fiveCellEndpointAdaptedLow w hw) (fiveCellEndpointAdaptedTail w hw)
    hlow (fiveCellEndpointAdaptedTail_nonnegative w hw hlocal) hmixed

theorem fiveCellEndpointAdaptedLow_endpoints_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointAdaptedLow w hw (-1) = 0 ∧
      fiveCellEndpointAdaptedLow w hw 1 = 0 := by
  rcases fiveCellEvenEndpointReserve_endpoints with ⟨he0, he1⟩
  rcases fiveCellOddEndpointReserve_endpoints with ⟨ho0, ho1⟩
  unfold fiveCellEndpointAdaptedLow fiveCellLowEndpointMean
    fiveCellLowEndpointAlternating
  rw [he0, he1, ho0, ho1]
  constructor <;> ring

theorem fiveCellEndpointAdaptedTail_endpoints_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    fiveCellEndpointAdaptedTail w hw (-1) = 0 ∧
      fiveCellEndpointAdaptedTail w hw 1 = 0 := by
  rcases fiveCellEndpointAdaptedLow_endpoints_zero w hw with ⟨hl, hr⟩
  unfold fiveCellEndpointAdaptedTail
  rw [hend.1, hend.2, hl, hr]
  norm_num

/-! ## Production endpoint -/

/-- On every actual five-cell profile, both sides of the adapted split retain
the exact zero traces supplied by compact support. -/
theorem fiveCellProductionEndpointAdapted_traces_zero
    (parent : BombieriTest) (k : ℤ) :
    let w := fiveCellNormalizedRealProfile parent k
    let hw : Continuous w :=
      (fiveCellNormalizedRealProfile_contDiff parent k).continuous
    (fiveCellEndpointAdaptedLow w hw (-1) = 0 ∧
      fiveCellEndpointAdaptedLow w hw 1 = 0) ∧
    (fiveCellEndpointAdaptedTail w hw (-1) = 0 ∧
      fiveCellEndpointAdaptedTail w hw 1 = 0) := by
  dsimp only
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  exact ⟨fiveCellEndpointAdaptedLow_endpoints_zero w hw,
    fiveCellEndpointAdaptedTail_endpoints_zero w hw
      (fiveCellNormalizedRealProfile_endpoints_zero parent k)⟩

/-- The concrete remaining finite/mixed certificate after transferring both
endpoint traces into the degrees-nine/ten reserve. -/
def RealFiveCellProductionEndpointAdaptedLowTailSchur : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let w := fiveCellNormalizedRealProfile parent k
        let hw : Continuous w :=
          (fiveCellNormalizedRealProfile_contDiff parent k).continuous
        0 ≤ fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw) ∧
          fiveCellEndpointOperatorCross
              (fiveCellEndpointAdaptedLow w hw)
              (fiveCellEndpointAdaptedTail w hw) ^ 2 ≤
            fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw) *
              fiveCellEndpointOperator (fiveCellEndpointAdaptedTail w hw)

/-- The endpoint-adapted certificate implies the exact factor-two production
target; no arbitrary-profile or global Bombieri assumption is introduced. -/
theorem realFiveCellFactorTwoDomination_of_endpointAdaptedLowTailSchur
    (hcert : RealFiveCellProductionEndpointAdaptedLowTailSchur) :
    RealFiveCellFactorTwoDomination := by
  apply realFiveCellNormalizedEndpointOperatorNonnegative_iff_factorTwoDomination.mp
  intro parent hparent k
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  have h := hcert parent hparent k
  change 0 ≤ fiveCellEndpointOperator w
  exact fiveCellEndpointOperator_nonnegative_of_endpointAdaptedLowTailSchur
    w hw (fiveCellNormalizedRealProfile_locallyLipschitzOn parent k)
      h.1 h.2

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedLowTailStructural
