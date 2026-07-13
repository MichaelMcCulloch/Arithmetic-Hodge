import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks1
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks2
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks3
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks4
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks5
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotChunks6

set_option autoImplicit false
set_option maxHeartbeats 5000000

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

open RatInterval
open RationalIntervalSchur
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets

/-!
# Full even pivot certificate assembly

The packed checkpoints and forty kernel-checked transitions are elaborated in
bounded modules.  This module assembles six opaque continuations and applies
the interval-validity bridge to obtain the premise-free target theorem.
-/

set_option maxRecDepth 1000000 in
/-- Full rounded pivot replay assembled from forty independently checked
five-stage certificates. -/
theorem evenTarget_full_rounded_intervalPivots :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale
      evenTargetInitialDense := by
  apply evenTarget_chunks0_10
  apply evenTarget_chunks10_25
  apply evenTarget_chunks25_40
  apply evenTarget_chunks40_60
  apply evenTarget_chunks60_90
  exact evenTarget_chunks90_200

def IntervalTargetsValid (targets : ℕ → RatInterval) : ℕ → Prop
  | 0 => True
  | n + 1 => RatInterval.Valid (targets n) ∧ IntervalTargetsValid targets n

instance intervalTargetsValidDecidable (targets : ℕ → RatInterval) (N : ℕ) :
    Decidable (IntervalTargetsValid targets N) := by
  induction N with
  | zero => exact isTrue trivial
  | succ N ih =>
      rw [IntervalTargetsValid]
      letI : Decidable (IntervalTargetsValid targets N) := ih
      infer_instance

theorem intervalTargetValid_of_lt (targets : ℕ → RatInterval) :
    ∀ (N n : ℕ), n < N → IntervalTargetsValid targets N →
      RatInterval.Valid (targets n) := by
  intro N
  induction N with
  | zero => omega
  | succ N ih =>
      intro n hn hvalid
      rw [IntervalTargetsValid] at hvalid
      by_cases h : n = N
      · simpa [h] using hvalid.1
      · exact ih n (by omega) hvalid.2

private theorem yoshidaEvenSineTargets_valid_fin :
    IntervalTargetsValid yoshidaEvenSineTargets 200 := by
  decide +kernel

theorem yoshidaEvenSineTargets_valid {n : ℕ} (hn : n ≤ 199) :
    RatInterval.Valid (yoshidaEvenSineTargets n) := by
  exact intervalTargetValid_of_lt yoshidaEvenSineTargets 200 n
    (by omega) yoshidaEvenSineTargets_valid_fin

private theorem yoshidaEvenDiagonalTargets_valid_fin :
    IntervalTargetsValid yoshidaEvenDiagonalTargets 200 := by
  decide +kernel

theorem yoshidaEvenDiagonalTargets_valid {n : ℕ} (hn : n ≤ 199) :
    RatInterval.Valid (yoshidaEvenDiagonalTargets n) := by
  exact intervalTargetValid_of_lt yoshidaEvenDiagonalTargets 200 n
    (by omega) yoshidaEvenDiagonalTargets_valid_fin

theorem evenInvPiInterval_valid : evenInvPiInterval.Valid := by
  norm_num [evenInvPiInterval, RatInterval.Valid]

theorem evenInvSqrtTwoInterval_valid : evenInvSqrtTwoInterval.Valid := by
  apply valid_inv_of_pos (I := evenSqrtTwoInterval)
  · norm_num [evenSqrtTwoInterval]
  · norm_num [evenSqrtTwoInterval, RatInterval.Valid]

theorem evenMomentIntervalGram_valid
    (S D : ℕ → RatInterval)
    (hS : ∀ n, n ≤ 199 → (S n).Valid)
    (hD : ∀ n, n ≤ 199 → (D n).Valid) :
    ∀ i j, (evenMomentIntervalGram S D i j).Valid := by
  intro i j
  by_cases hi : i.1 = 0
  · by_cases hj : j.1 = 0
    · simpa [evenMomentIntervalGram, hi, hj] using hD 0 (by omega)
    · simp only [evenMomentIntervalGram, hi, hj, ↓reduceIte]
      exact valid_mul
        (valid_mul
          (valid_mul (valid_pure _) evenInvPiInterval_valid)
          evenInvSqrtTwoInterval_valid)
        (hS j.1 (by omega))
  · by_cases hj : j.1 = 0
    · simp only [evenMomentIntervalGram, hi, hj, ↓reduceIte]
      exact valid_mul
        (valid_mul
          (valid_mul (valid_pure _) evenInvPiInterval_valid)
          evenInvSqrtTwoInterval_valid)
        (hS i.1 (by omega))
    · by_cases hij : i = j
      · subst j
        simp only [evenMomentIntervalGram, hi, ↓reduceIte]
        exact valid_sub (hD i.1 (by omega))
          (valid_mul
            (valid_mul (valid_pure _) evenInvPiInterval_valid)
            (hS i.1 (by omega)))
      · simp only [evenMomentIntervalGram, hi, hj, hij, ↓reduceIte]
        exact valid_mul
          (valid_mul (valid_pure _) evenInvPiInterval_valid)
          (valid_sub
            (valid_mul (valid_pure _) (hS j.1 (by omega)))
            (valid_mul (valid_pure _) (hS i.1 (by omega))))

theorem inflateInterval_valid {r : ℚ} (hr : 0 ≤ r)
    {I : RatInterval} (hI : I.Valid) : (inflateInterval r I).Valid := by
  norm_num [inflateInterval, RatInterval.Valid] at hI ⊢
  linarith

theorem evenTarget_initial_intervalGram_valid :
    ∀ i j,
      (inflatedEvenMomentIntervalGram evenCorrectionRadius
        yoshidaEvenSineTargets yoshidaEvenDiagonalTargets i j).Valid := by
  intro i j
  apply inflateInterval_valid (by norm_num [evenCorrectionRadius])
  exact evenMomentIntervalGram_valid
    yoshidaEvenSineTargets yoshidaEvenDiagonalTargets
    (fun n hn ↦ yoshidaEvenSineTargets_valid hn)
    (fun n hn ↦ yoshidaEvenDiagonalTargets_valid hn) i j

/-- Premise-free full 200-stage interval pivot certificate for the exact
target Gram matrix. -/
theorem evenTarget_full_intervalPivots : YoshidaEvenFullTargetPivots := by
  unfold YoshidaEvenFullTargetPivots
  let M := inflatedEvenMomentIntervalGram evenCorrectionRadius
    yoshidaEvenSineTargets yoshidaEvenDiagonalTargets
  have hrounded :
      DenseLeadingRoundedPositivePivots evenPivotRoundScale
        (denseOfMatrix M) := by
    simpa [M, evenTargetInitialDense] using
      evenTarget_full_rounded_intervalPivots
  have h := positivePivots_of_denseLeadingRounded (α := Fin 200)
    evenPivotRoundScale (by norm_num [evenPivotRoundScale])
    M (fun i ↦ i) (denseOfMatrix M)
    hrounded
    (fun i j ↦ evenTarget_initial_intervalGram_valid i j)
    (fun i j ↦ by
      simpa [matrixOfDense, denseOfMatrix] using
        evenTarget_initial_intervalGram_valid i j)
    (fun i j ↦ by simp [Refines, matrixOfDense, denseOfMatrix])
  simpa [M, evenPivotOrder] using h

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
