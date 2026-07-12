import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
import Mathlib.Analysis.PSeries

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries

noncomputable section

open ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

/-!
# Shifted presentation of the renormalized geometric series

The digamma expansion isolates its `k = 0` Laplace term and indexes the
remaining harmonic subtraction from `k + 1`.  The abstract geometric-kernel
identity instead sums `A k - C0 / (k + 1)`.  Their finite partial sums differ
by one vanishing harmonic tail.  This module proves that reindexing exactly,
including absolute summability of the telescoping correction.
-/

def geometricIntegralTerm (L : ℝ) (C : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 * (∫ u in 0..L, Real.exp (-oddRate k * u) * C u)

def harmonicShiftCorrection (C0 : ℝ) (k : ℕ) : ℝ :=
  C0 / (k + 2 : ℕ) - C0 / (k + 1 : ℕ)

theorem renormalizedTerm_eq_geometricIntegralTerm
    (L C0 : ℝ) (C : ℝ → ℝ) (k : ℕ) :
    renormalizedTerm L C0 C k =
      geometricIntegralTerm L C k - C0 / (k + 1 : ℕ) := by
  rw [renormalizedTerm, geometricIntegralTerm]
  push_cast
  rfl

private theorem correction_eq
    (C0 : ℝ) (k : ℕ) :
    harmonicShiftCorrection C0 k =
      -C0 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
  rw [harmonicShiftCorrection]
  push_cast
  field_simp
  ring_nf

private theorem summable_norm_harmonicShiftCorrection (C0 : ℝ) :
    Summable (fun k : ℕ ↦ ‖harmonicShiftCorrection C0 k‖) := by
  have hp : Summable (fun k : ℕ ↦
      ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num))
  have hmajor : Summable (fun k : ℕ ↦
      |C0| * ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := hp.mul_left |C0|
  apply hmajor.of_nonneg_of_le
  · intro k
    exact norm_nonneg _
  · intro k
    have hden_nonneg : 0 ≤
        (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by positivity
    rw [correction_eq, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_nonneg hden_nonneg]
    have hk1 : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    have hk2 : (((k + 1 : ℕ) : ℝ)) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (k + 1)
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg C0)
    apply (inv_le_inv₀ (mul_pos hk1 (lt_of_lt_of_le hk1 hk2))
      (sq_pos_of_pos hk1)).2
    nlinarith

theorem hasSum_harmonicShiftCorrection (C0 : ℝ) :
    HasSum (harmonicShiftCorrection C0) (-C0) := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_harmonicShiftCorrection C0)]
  have hzero : Tendsto (fun n : ℕ ↦ C0 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C0)
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.range n, harmonicShiftCorrection C0 k) =
        C0 / ((n : ℝ) + 1) - C0 := by
    calc
      (∑ k ∈ Finset.range n, harmonicShiftCorrection C0 k) =
          ∑ k ∈ Finset.range n,
            ((fun j : ℕ ↦ C0 / (j + 1 : ℕ)) (k + 1) -
              (fun j : ℕ ↦ C0 / (j + 1 : ℕ)) k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [harmonicShiftCorrection]
      _ = C0 / (n + 1 : ℕ) - C0 / (0 + 1 : ℕ) :=
        Finset.sum_range_sub (fun k : ℕ ↦ C0 / (k + 1 : ℕ)) n
      _ = C0 / ((n : ℝ) + 1) - C0 := by
        push_cast
        norm_num
  convert hzero.sub tendsto_const_nhds using 1
  · funext n
    exact hsum n
  · ring_nf

theorem hasSum_shifted_geometric_of_hasSum_renormalized
    {L C0 S : ℝ} {C : ℝ → ℝ}
    (h : HasSum (renormalizedTerm L C0 C) S) :
    HasSum
      (fun k : ℕ ↦ geometricIntegralTerm L C (k + 1) -
        C0 / (k + 1 : ℕ))
      (S - geometricIntegralTerm L C 0) := by
  have htail : HasSum (fun k : ℕ ↦ renormalizedTerm L C0 C (k + 1))
      (S - renormalizedTerm L C0 C 0) := by
    simpa only [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).2 h
  have hcombined := htail.add (hasSum_harmonicShiftCorrection C0)
  convert hcombined using 1
  · funext k
    rw [renormalizedTerm_eq_geometricIntegralTerm,
      harmonicShiftCorrection]
    ring_nf
  · rw [renormalizedTerm_eq_geometricIntegralTerm]
    norm_num
    ring_nf

theorem geometricIntegralTerm_zero_add_tsum_shifted_eq
    {L C0 S : ℝ} {C : ℝ → ℝ}
    (h : HasSum (renormalizedTerm L C0 C) S) :
    geometricIntegralTerm L C 0 +
        ∑' k : ℕ, (geometricIntegralTerm L C (k + 1) -
          C0 / (k + 1 : ℕ)) = S := by
  rw [(hasSum_shifted_geometric_of_hasSum_renormalized h).tsum_eq]
  ring_nf

end

end ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
