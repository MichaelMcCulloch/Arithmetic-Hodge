import ArithmeticHodge.Analysis.ZetaZeroCount
import Mathlib.Order.Interval.Set.Infinite

open Complex Filter Set

namespace ArithmeticHodge.Analysis

/-- Every nonempty positive height interval contains a height whose upper and
lower horizontal edges avoid every xi zero over an arbitrary closed real-part
interval. -/
theorem exists_xi_zero_free_horizontal_pair_between_scratch
    (sigmaLower sigmaUpper A B : ℝ) (hA : 0 ≤ A) (hAB : A < B) :
    ∃ T ∈ Set.Ioo A B,
      (∀ σ ∈ Set.Icc sigmaLower sigmaUpper, xiFunction (σ + T * I) ≠ 0) ∧
      (∀ σ ∈ Set.Icc sigmaLower sigmaUpper, xiFunction (σ - T * I) ≠ 0) := by
  classical
  let Z := xiZerosInRectangle sigmaLower sigmaUpper (-B) B
  let H : Finset ℝ := Z.image (fun z => |z.im|)
  have hIoo : (Set.Ioo A B).Infinite := Set.Ioo_infinite hAB
  obtain ⟨T, hT, hTH⟩ : ∃ T ∈ Set.Ioo A B, T ∉ H := by
    have hnot : ¬ Set.Ioo A B ⊆ (H : Set ℝ) := by
      intro hsub
      exact hIoo (H.finite_toSet.subset hsub)
    simpa only [Set.not_subset] using hnot
  refine ⟨T, hT, ?_, ?_⟩
  · intro σ hσ hzero
    have hzrect : (σ + T * I : ℂ) ∈
        xiZeroRectangle sigmaLower sigmaUpper (-B) B := by
      rw [xiZeroRectangle, mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, add_im, mul_im, zero_add]
      exact ⟨hσ, by constructor <;> linarith [hT.1, hT.2]⟩
    have hzmem : (σ + T * I : ℂ) ∈ Z := by
      exact (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper (-B) B _).2
        ⟨hzrect, hzero⟩
    apply hTH
    simp only [H, Finset.mem_image]
    refine ⟨(σ + T * I : ℂ), hzmem, ?_⟩
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, zero_mul, add_zero,
      zero_add, mul_one]
    rw [abs_of_nonneg (hA.trans hT.1.le)]
  · intro σ hσ hzero
    have hzrect : (σ - T * I : ℂ) ∈
        xiZeroRectangle sigmaLower sigmaUpper (-B) B := by
      rw [xiZeroRectangle, mem_reProdIm]
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, sub_im, mul_im]
      exact ⟨hσ, by constructor <;> linarith [hT.1, hT.2]⟩
    have hzmem : (σ - T * I : ℂ) ∈ Z := by
      exact (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper (-B) B _).2
        ⟨hzrect, hzero⟩
    apply hTH
    simp only [H, Finset.mem_image]
    refine ⟨(σ - T * I : ℂ), hzmem, ?_⟩
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, zero_mul,
      add_zero, mul_one, zero_sub]
    rw [abs_neg, abs_of_nonneg (hA.trans hT.1.le)]

/-- Every positive unit height interval contains a height whose upper and lower
horizontal critical-strip edges avoid every xi zero. -/
theorem exists_xi_zero_free_horizontal_pair_scratch (A : ℝ) (hA : 0 ≤ A) :
    ∃ T ∈ Set.Ioo A (A + 1),
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ + T * I) ≠ 0) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ - T * I) ≠ 0) := by
  classical
  let Z := xiZerosInRectangle 0 1 (-(A + 1)) (A + 1)
  let H : Finset ℝ := Z.image (fun z => |z.im|)
  have hIoo : (Set.Ioo A (A + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨T, hT, hTH⟩ : ∃ T ∈ Set.Ioo A (A + 1), T ∉ H := by
    have hnot : ¬ Set.Ioo A (A + 1) ⊆ (H : Set ℝ) := by
      intro hsub
      exact hIoo (H.finite_toSet.subset hsub)
    simpa only [Set.not_subset] using hnot
  refine ⟨T, hT, ?_, ?_⟩
  · intro σ hσ hzero
    have hzrect : (σ + T * I : ℂ) ∈ xiZeroRectangle 0 1 (-(A + 1)) (A + 1) := by
      rw [xiZeroRectangle, mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, add_im, mul_im, zero_add]
      exact ⟨hσ, by constructor <;> linarith [hT.1, hT.2]⟩
    have hzmem : (σ + T * I : ℂ) ∈ Z := by
      exact (mem_xiZerosInRectangle_iff 0 1 (-(A + 1)) (A + 1) _).2 ⟨hzrect, hzero⟩
    apply hTH
    simp only [H, Finset.mem_image]
    refine ⟨(σ + T * I : ℂ), hzmem, ?_⟩
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, zero_mul, add_zero,
      zero_add, mul_one]
    rw [abs_of_nonneg (hA.trans hT.1.le)]
  · intro σ hσ hzero
    have hzrect : (σ - T * I : ℂ) ∈ xiZeroRectangle 0 1 (-(A + 1)) (A + 1) := by
      rw [xiZeroRectangle, mem_reProdIm]
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, sub_im, mul_im]
      exact ⟨hσ, by constructor <;> linarith [hT.1, hT.2]⟩
    have hzmem : (σ - T * I : ℂ) ∈ Z := by
      exact (mem_xiZerosInRectangle_iff 0 1 (-(A + 1)) (A + 1) _).2 ⟨hzrect, hzero⟩
    apply hTH
    simp only [H, Finset.mem_image]
    refine ⟨(σ - T * I : ℂ), hzmem, ?_⟩
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, zero_mul,
      add_zero, mul_one, zero_sub]
    rw [abs_neg, abs_of_nonneg (hA.trans hT.1.le)]

/-- Avoiding xi zeros on the two horizontal edges upgrades every zero in the
closed critical-strip rectangle to a zero in its strict interior.  The two
vertical edges are automatically zero-free because all xi zeros have real part
strictly between zero and one. -/
theorem xiZerosInRectangle_strict_interior_of_horizontal_pair_scratch
    {T : ℝ}
    (hupper : ∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ + T * I) ≠ 0)
    (hlower : ∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ - T * I) ≠ 0) :
    ∀ rho ∈ xiZerosInRectangle 0 1 (-T) T,
      0 < rho.re ∧ rho.re < 1 ∧ -T < rho.im ∧ rho.im < T := by
  intro rho hrho
  have hdata := (mem_xiZerosInRectangle_iff 0 1 (-T) T rho).1 hrho
  have hrect := hdata.1
  rw [xiZeroRectangle, mem_reProdIm] at hrect
  have hre := xiFunction_zero_re hdata.2
  refine ⟨hre.1, hre.2, ?_, ?_⟩
  · apply lt_of_le_of_ne hrect.2.1
    intro heq
    have hrho_eq : (rho.re : ℂ) - T * I = rho := by
      apply Complex.ext
      · simp
      · simp [← heq]
    exact hlower rho.re hrect.1 (by simpa only [hrho_eq] using hdata.2)
  · apply lt_of_le_of_ne hrect.2.2
    intro heq
    have hrho_eq : (rho.re : ℂ) + T * I = rho := by
      apply Complex.ext
      · simp
      · simp [heq]
    exact hupper rho.re hrect.1 (by simpa only [hrho_eq] using hdata.2)

/-- There is a sequence of paired zero-free horizontal critical-strip edges,
with the `n`th height lying strictly between `n` and `n + 1`, and hence tending
to positive infinity. -/
theorem exists_xi_zero_free_horizontal_pair_sequence_scratch :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      ∀ n : ℕ,
        (n : ℝ) < T n ∧ T n < (n : ℝ) + 1 ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ + T n * I) ≠ 0) ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ - T n * I) ≠ 0) := by
  classical
  let T : ℕ → ℝ := fun n =>
    Classical.choose
      (exists_xi_zero_free_horizontal_pair_scratch (n : ℝ) (Nat.cast_nonneg n))
  have hspec (n : ℕ) :
      T n ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ + T n * I) ≠ 0) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ - T n * I) ≠ 0) := by
    exact Classical.choose_spec
      (exists_xi_zero_free_horizontal_pair_scratch (n : ℝ) (Nat.cast_nonneg n))
  refine ⟨T, ?_, fun n => ⟨(hspec n).1.1, (hspec n).1.2, (hspec n).2⟩⟩
  exact tendsto_atTop_mono (fun n => (hspec n).1.1.le)
    (tendsto_natCast_atTop_atTop (R := ℝ))

end ArithmeticHodge.Analysis

#print axioms ArithmeticHodge.Analysis.exists_xi_zero_free_horizontal_pair_between_scratch
#print axioms ArithmeticHodge.Analysis.exists_xi_zero_free_horizontal_pair_scratch
#print axioms ArithmeticHodge.Analysis.xiZerosInRectangle_strict_interior_of_horizontal_pair_scratch
#print axioms ArithmeticHodge.Analysis.exists_xi_zero_free_horizontal_pair_sequence_scratch
