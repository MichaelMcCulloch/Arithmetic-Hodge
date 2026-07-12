import ArithmeticHodge.Analysis.YoshidaZeroModeStructuralCore
import Mathlib.Analysis.Real.Pi.Leibniz

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaZeroModeStieltjesIdentity

noncomputable section

open Filter Topology
open scoped BigOperators

open YoshidaRenormalizedGeometricKernel
open YoshidaZeroModeStructuralCore
private theorem summable_zeroRawTail :
    Summable (fun j : ℕ ↦ structuralZeroRawTerm (j + 1)) := by
  exact (summable_nat_add_iff 1).2 summable_structuralZeroRawTerm

private def quarterRationalTerm (k : ℕ) : ℝ :=
  4 / (4 * k + 1 : ℕ) - 1 / (k + 1 : ℕ)

private def quarterLeibnizTerm (k : ℕ) : ℝ :=
  1 / (4 * k + 1 : ℕ) - 1 / (4 * k + 3 : ℕ)

private def quarterHarmonicTerm (k : ℕ) : ℝ :=
  2 / (4 * k + 1 : ℕ) + 2 / (4 * k + 3 : ℕ) - 1 / (k + 1 : ℕ)

private theorem quarterRationalTerm_eq (k : ℕ) :
    quarterRationalTerm k =
      2 * quarterLeibnizTerm k + quarterHarmonicTerm k := by
  unfold quarterRationalTerm quarterLeibnizTerm quarterHarmonicTerm
  push_cast
  field_simp
  ring

private theorem sum_range_quarterLeibnizTerm (N : ℕ) :
    ∑ k ∈ Finset.range N, quarterLeibnizTerm k =
      ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i / (2 * i + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      unfold quarterLeibnizTerm
      rw [Even.neg_one_pow (by exact even_two_mul N),
        Odd.neg_one_pow (by exact odd_two_mul_add_one N)]
      push_cast
      ring

private theorem sum_range_quarterHarmonicTerm (N : ℕ) :
    ∑ k ∈ Finset.range N, quarterHarmonicTerm k =
      2 * (harmonic (4 * N) : ℝ) - (harmonic (2 * N) : ℝ) -
        (harmonic N : ℝ) := by
  induction N with
  | zero => norm_num [harmonic]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 4 * (N + 1) = (4 * N + 3) + 1 by omega,
        harmonic_succ (4 * N + 3), harmonic_succ (4 * N + 2),
        harmonic_succ (4 * N + 1), harmonic_succ (4 * N),
        show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        harmonic_succ (2 * N + 1), harmonic_succ (2 * N),
        harmonic_succ N]
      unfold quarterHarmonicTerm
      push_cast
      field_simp
      ring

private theorem tendsto_sum_quarterHarmonicTerm :
    Tendsto (fun N : ℕ ↦
      ∑ k ∈ Finset.range N, quarterHarmonicTerm k)
      atTop (nhds (3 * structuralYoshidaLength)) := by
  have hindex4 : Tendsto (fun n : ℕ ↦ 4 * n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by simp only [id_eq]; omega)
      (tendsto_id : Tendsto (fun n : ℕ ↦ n) atTop atTop)
  have hindex2 : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by simp only [id_eq]; omega)
      (tendsto_id : Tendsto (fun n : ℕ ↦ n) atTop atTop)
  have h4 := Real.tendsto_harmonic_sub_log.comp hindex4
  have h2 := Real.tendsto_harmonic_sub_log.comp hindex2
  have h1 := Real.tendsto_harmonic_sub_log
  have hzero := ((h4.const_mul 2).sub h2).sub h1
  have hzero' : Tendsto
      (fun n : ℕ ↦
        2 * (((harmonic (4 * n) : ℝ) - Real.log (4 * n : ℕ))) -
          ((harmonic (2 * n) : ℝ) - Real.log (2 * n : ℕ)) -
          ((harmonic n : ℝ) - Real.log n))
      atTop (nhds 0) := by
    have hgamma :
        2 * Real.eulerMascheroniConstant - Real.eulerMascheroniConstant -
          Real.eulerMascheroniConstant = 0 := by ring
    rw [hgamma] at hzero
    simpa only [Function.comp_apply] using hzero
  have hconst := hzero'.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ 3 * structuralYoshidaLength) atTop
      (nhds (3 * structuralYoshidaLength)))
  have hevent :
      (fun n : ℕ ↦
        2 * ((harmonic (4 * n) : ℝ) - Real.log (4 * n : ℕ)) -
            ((harmonic (2 * n) : ℝ) - Real.log (2 * n : ℕ)) -
            ((harmonic n : ℝ) - Real.log n) +
              3 * structuralYoshidaLength) =ᶠ[atTop]
        (fun N : ℕ ↦ ∑ k ∈ Finset.range N, quarterHarmonicTerm k) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
    rw [sum_range_quarterHarmonicTerm]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [show ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) by push_cast; ring,
      show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hn0,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
      show Real.log (4 : ℝ) = 2 * structuralYoshidaLength by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
          structuralYoshidaLength]
        norm_num,
      structuralYoshidaLength]
    ring
  simpa only [zero_add] using hconst.congr' hevent

private theorem tendsto_sum_quarterLeibnizTerm :
    Tendsto (fun N : ℕ ↦
      ∑ k ∈ Finset.range N, quarterLeibnizTerm k)
      atTop (nhds (Real.pi / 4)) := by
  have hindex2 : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by simp only [id_eq]; omega)
      (tendsto_id : Tendsto (fun n : ℕ ↦ n) atTop atTop)
  have h := Real.tendsto_sum_pi_div_four.comp hindex2
  apply h.congr'
  exact Eventually.of_forall (fun N => (sum_range_quarterLeibnizTerm N).symm)

private theorem tendsto_sum_quarterRationalTerm :
    Tendsto (fun N : ℕ ↦
      ∑ k ∈ Finset.range N, quarterRationalTerm k)
      atTop (nhds (Real.pi / 2 + 3 * structuralYoshidaLength)) := by
  have h := (tendsto_sum_quarterLeibnizTerm.const_mul 2).add
    tendsto_sum_quarterHarmonicTerm
  have hevent :
      (fun N : ℕ ↦
        2 * (∑ k ∈ Finset.range N, quarterLeibnizTerm k) +
          ∑ k ∈ Finset.range N, quarterHarmonicTerm k) =ᶠ[atTop]
        (fun N : ℕ ↦ ∑ k ∈ Finset.range N, quarterRationalTerm k) := by
    exact Eventually.of_forall (fun N => by
      simp_rw [quarterRationalTerm_eq]
      rw [Finset.sum_add_distrib, Finset.mul_sum])
  convert h.congr' hevent using 1
  ring_nf

private theorem quarterRationalTerm_nonneg (k : ℕ) :
    0 ≤ quarterRationalTerm k := by
  unfold quarterRationalTerm
  push_cast
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk4 : (0 : ℝ) < 4 * (k : ℝ) + 1 := by positivity
  rw [sub_nonneg, div_le_div_iff₀ hk1 hk4]
  linarith

private theorem hasSum_quarterRationalTerm :
    HasSum quarterRationalTerm
      (Real.pi / 2 + 3 * structuralYoshidaLength) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg quarterRationalTerm_nonneg]
  exact tendsto_sum_quarterRationalTerm

private def zeroStieltjesTerm (k : ℕ) : ℝ :=
  (2 * (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
    (oddRate k ^ 2)) / structuralYoshidaLength

private theorem zeroRawTerm_eq_rational_sub_stieltjes (k : ℕ) :
    structuralZeroRawTerm k = quarterRationalTerm k - zeroStieltjesTerm k := by
  unfold structuralZeroRawTerm quarterRationalTerm zeroStieltjesTerm
    structuralDiagonalRampClosed oddRate
  push_cast
  field_simp [structuralYoshidaLength_pos.ne']
  ring

private theorem summable_zeroStieltjesTail :
    Summable (fun j : ℕ ↦ zeroStieltjesTerm (j + 1)) := by
  have hc : Summable (fun j : ℕ ↦ quarterRationalTerm (j + 1)) :=
    (summable_nat_add_iff 1).2 hasSum_quarterRationalTerm.summable
  have h := hc.sub summable_zeroRawTail
  apply h.congr
  intro j
  rw [zeroRawTerm_eq_rational_sub_stieltjes]
  ring

private theorem summable_zeroStieltjesTerm : Summable zeroStieltjesTerm := by
  exact (summable_nat_add_iff 1).1 summable_zeroStieltjesTail

private theorem hasSum_quarterRationalTail :
    HasSum (fun j : ℕ ↦ quarterRationalTerm (j + 1))
      (Real.pi / 2 + 3 * structuralYoshidaLength - 3) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_quarterRationalTerm
  convert h using 1
  norm_num [quarterRationalTerm]

private theorem tsum_zeroRawTail_eq_rationalTail_sub_stieltjesTail :
    (∑' j : ℕ, structuralZeroRawTerm (j + 1)) =
      (Real.pi / 2 + 3 * structuralYoshidaLength - 3) -
        ∑' j : ℕ, zeroStieltjesTerm (j + 1) := by
  have hc := hasSum_quarterRationalTail.summable
  calc
    (∑' j : ℕ, structuralZeroRawTerm (j + 1)) =
        ∑' j : ℕ,
          (quarterRationalTerm (j + 1) - zeroStieltjesTerm (j + 1)) := by
      apply tsum_congr
      intro j
      exact zeroRawTerm_eq_rational_sub_stieltjes (j + 1)
    _ = (∑' j : ℕ, quarterRationalTerm (j + 1)) -
        ∑' j : ℕ, zeroStieltjesTerm (j + 1) :=
      hc.tsum_sub summable_zeroStieltjesTail
    _ = _ := by rw [hasSum_quarterRationalTail.tsum_eq]

private theorem yoshidaStieltjesProfile_zero_div_length :
    structuralYoshidaStieltjesProfile 0 / structuralYoshidaLength =
      (8 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2)) /
          structuralYoshidaLength +
        ∑' k : ℕ, zeroStieltjesTerm k := by
  unfold structuralYoshidaStieltjesProfile zeroStieltjesTerm
  rw [add_div]
  congr 1
  · field_simp [structuralYoshidaLength_pos.ne']
    ring
  · rw [← tsum_div_const]
    apply tsum_congr
    intro k
    congr 2
    unfold oddRate
    ring

private theorem zeroPolarRamp_add_four :
    2 * structuralDiagonalRampClosed structuralYoshidaLength 0
        (-1 / 2) (Real.sqrt 2) + 4 =
      8 * (Real.sqrt 2 - 1) / structuralYoshidaLength := by
  unfold structuralDiagonalRampClosed
  field_simp [structuralYoshidaLength_pos.ne']
  ring

private theorem zeroStieltjesTerm_zero :
    zeroStieltjesTerm 0 =
      8 * (1 - (Real.sqrt 2)⁻¹) / structuralYoshidaLength := by
  unfold zeroStieltjesTerm oddRate
  norm_num
  field_simp [structuralYoshidaLength_pos.ne']
  ring

/-- The even zero-mode diagonal is the zero-node Stieltjes energy minus a
closed archimedean constant. -/
theorem structuralYoshidaDiagonalMoment_zero_eq_stieltjesProfile_zero_sub_constant :
    structuralYoshidaDiagonalMoment 0 =
      structuralYoshidaStieltjesProfile 0 / structuralYoshidaLength -
        (Real.eulerMascheroniConstant + Real.log Real.pi +
          Real.pi / 2 + 3 * structuralYoshidaLength) := by
  have hsplit := summable_zeroStieltjesTerm.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [structuralYoshidaDiagonalMoment_zero_eq_positiveRamp_sub_rawTail,
    tsum_zeroRawTail_eq_rationalTail_sub_stieltjesTail,
    yoshidaStieltjesProfile_zero_div_length, ← hsplit,
    zeroStieltjesTerm_zero]
  have hpolar := zeroPolarRamp_add_four
  have hcombine :
      8 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2) /
            structuralYoshidaLength +
          8 * (1 - (Real.sqrt 2)⁻¹) / structuralYoshidaLength =
        2 * structuralDiagonalRampClosed structuralYoshidaLength 0
            (-1 / 2) (Real.sqrt 2) + 4 := by
    rw [hpolar]
    ring
  ring_nf at hcombine ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaZeroModeStieltjesIdentity
