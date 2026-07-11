/-
  The finite prime contribution in Bombieri's multiplicative explicit formula.

  A positive-half-line test and its transpose both have compact support, so
  their evaluations on positive integers vanish outside a finite set.  The
  von Mangoldt series is therefore an actual finite sum and defines a complex-
  linear functional without any totalized infinite-sum convention.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose

set_option autoImplicit false

open Complex Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The source-faithful prime kernel at the positive integer `k + 1`. -/
def primeKernel (f : BombieriTest) (k : ℕ) : ℂ :=
  f (k + 1 : ℕ) + transpose (f : ℝ → ℂ) (k + 1 : ℕ)

/-- The von-Mangoldt-weighted prime summand in Bombieri's explicit formula. -/
def vonMangoldtPrimeSummand (f : BombieriTest) (k : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) * primeKernel f k

/-- Evaluation of a compactly supported Bombieri test on positive integers
has finite support. -/
theorem directIntegerSupport_finite (f : BombieriTest) :
    {k : ℕ | f (k + 1 : ℕ) ≠ 0}.Finite := by
  rw [Set.finite_iff_bddAbove]
  obtain ⟨B, hB⟩ := f.hasCompactSupport.bddAbove
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
  refine ⟨N, ?_⟩
  intro k hk
  have hmem : ((k + 1 : ℕ) : ℝ) ∈ tsupport f :=
    subset_tsupport f (Function.mem_support.mpr hk)
  have hkB : ((k + 1 : ℕ) : ℝ) ≤ B := hB hmem
  have hkN : (k : ℝ) < (N : ℝ) := by
    calc
      (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self k
      _ ≤ B := hkB
      _ < (N : ℝ) := hN
  exact_mod_cast hkN.le

/-- Evaluation of the transpose on positive integers also has finite support. -/
theorem transposeIntegerSupport_finite (f : BombieriTest) :
    {k : ℕ | transpose (f : ℝ → ℂ) (k + 1 : ℕ) ≠ 0}.Finite := by
  simpa only [BombieriTest.transposeTest_apply] using
    directIntegerSupport_finite (BombieriTest.transposeTest f)

/-- The unweighted prime kernel has finite support in its natural-number
index. -/
theorem primeKernel_hasFiniteSupport (f : BombieriTest) :
    Function.HasFiniteSupport (primeKernel f) := by
  refine ((directIntegerSupport_finite f).union
    (transposeIntegerSupport_finite f)).subset ?_
  intro k hk
  change primeKernel f k ≠ 0 at hk
  change f (k + 1 : ℕ) ≠ 0 ∨
    transpose (f : ℝ → ℂ) (k + 1 : ℕ) ≠ 0
  by_contra hnot
  rw [not_or] at hnot
  apply hk
  unfold primeKernel
  rw [not_ne_iff.mp hnot.1, not_ne_iff.mp hnot.2, zero_add]

/-- Multiplication by the von Mangoldt coefficient cannot enlarge support. -/
theorem vonMangoldtPrimeSummand_hasFiniteSupport (f : BombieriTest) :
    Function.HasFiniteSupport (vonMangoldtPrimeSummand f) := by
  exact (primeKernel_hasFiniteSupport f).subset fun k hk ↦ by
    simpa only [Function.mem_support, vonMangoldtPrimeSummand] using
      right_ne_zero_of_mul hk

/-- The prime series is summable because it is actually a finite sum. -/
theorem vonMangoldtPrimeSummand_summable (f : BombieriTest) :
    Summable (vonMangoldtPrimeSummand f) :=
  summable_of_hasFiniteSupport (vonMangoldtPrimeSummand_hasFiniteSupport f)

/-- The unsigned prime contribution to Bombieri's multiplicative explicit
formula.  The full functional subtracts this quantity. -/
def primeSum (f : BombieriTest) : ℂ :=
  ∑' k : ℕ, vonMangoldtPrimeSummand f k

@[simp]
theorem primeKernel_zero (k : ℕ) : primeKernel (0 : BombieriTest) k = 0 := by
  simp [primeKernel, transpose]

theorem primeKernel_add (f g : BombieriTest) (k : ℕ) :
    primeKernel (f + g) k = primeKernel f k + primeKernel g k := by
  simp only [primeKernel, transpose, TestFunction.coe_add, Pi.add_apply]
  ring

theorem primeKernel_smul (c : ℂ) (f : BombieriTest) (k : ℕ) :
    primeKernel (c • f) k = c * primeKernel f k := by
  simp only [primeKernel, transpose, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

@[simp]
theorem vonMangoldtPrimeSummand_zero (k : ℕ) :
    vonMangoldtPrimeSummand (0 : BombieriTest) k = 0 := by
  simp [vonMangoldtPrimeSummand]

theorem vonMangoldtPrimeSummand_add (f g : BombieriTest) (k : ℕ) :
    vonMangoldtPrimeSummand (f + g) k =
      vonMangoldtPrimeSummand f k + vonMangoldtPrimeSummand g k := by
  simp only [vonMangoldtPrimeSummand, primeKernel_add]
  ring

theorem vonMangoldtPrimeSummand_smul (c : ℂ) (f : BombieriTest) (k : ℕ) :
    vonMangoldtPrimeSummand (c • f) k =
      c * vonMangoldtPrimeSummand f k := by
  simp only [vonMangoldtPrimeSummand, primeKernel_smul]
  ring

@[simp]
theorem primeSum_zero : primeSum (0 : BombieriTest) = 0 := by
  simp [primeSum]

theorem primeSum_add (f g : BombieriTest) :
    primeSum (f + g) = primeSum f + primeSum g := by
  rw [primeSum, primeSum, primeSum,
    ← (vonMangoldtPrimeSummand_summable f).tsum_add
      (vonMangoldtPrimeSummand_summable g)]
  exact tsum_congr (vonMangoldtPrimeSummand_add f g)

theorem primeSum_smul (c : ℂ) (f : BombieriTest) :
    primeSum (c • f) = c * primeSum f := by
  rw [primeSum, primeSum,
    ← (vonMangoldtPrimeSummand_summable f).tsum_mul_left c]
  exact tsum_congr (vonMangoldtPrimeSummand_smul c f)

/-- The prime contribution as a genuine complex-linear functional. -/
def primeSumLinearMap : BombieriTest →ₗ[ℂ] ℂ where
  toFun := primeSum
  map_add' := primeSum_add
  map_smul' c f := by simpa only [smul_eq_mul] using primeSum_smul c f

@[simp]
theorem primeSumLinearMap_apply (f : BombieriTest) :
    primeSumLinearMap f = primeSum f := rfl

/-- A bundled transpose swaps the two terms of the prime kernel. -/
theorem primeKernel_transposeData (data : TransposeData)
    (f : BombieriTest) (k : ℕ) :
    primeKernel (data.toLinearMap f) k = primeKernel f k := by
  let n : ℝ := (k + 1 : ℕ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hfirst : data.toLinearMap f n = transpose (f : ℝ → ℂ) n :=
    data.apply_pos f hn
  have hsecond : transpose (data.toLinearMap f : ℝ → ℂ) n = f n := by
    calc
      transpose (data.toLinearMap f : ℝ → ℂ) n =
          data.toLinearMap f n⁻¹ / n := transpose_apply_of_pos _ hn
      _ = transpose (f : ℝ → ℂ) n⁻¹ / n := by
        rw [data.apply_pos f (inv_pos.mpr hn)]
      _ = transpose (transpose (f : ℝ → ℂ)) n := by
        rw [transpose_apply_of_pos (transpose (f : ℝ → ℂ)) hn]
      _ = f n := transpose_involutive_on_pos (f : ℝ → ℂ) hn
  change data.toLinearMap f n + transpose (data.toLinearMap f : ℝ → ℂ) n =
    f n + transpose (f : ℝ → ℂ) n
  rw [hfirst, hsecond]
  exact add_comm _ _

/-- The prime sum is invariant under any bundled Bombieri transpose. -/
theorem primeSum_transposeData (data : TransposeData) (f : BombieriTest) :
    primeSum (data.toLinearMap f) = primeSum f := by
  unfold primeSum
  apply tsum_congr
  intro k
  simp only [vonMangoldtPrimeSummand, primeKernel_transposeData data f k]

@[simp]
theorem primeSum_transposeLinearMap (f : BombieriTest) :
    primeSum (transposeLinearMap f) = primeSum f :=
  primeSum_transposeData canonicalTransposeData f

end


end ArithmeticHodge.Analysis.MultiplicativeWeil
