import ArithmeticHodge.Analysis.MultiplicativeWeil

open Complex Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriPrimeSupportScratch

noncomputable section

/-- The source-faithful prime kernel at the positive integer `k + 1`.

Bombieri's multiplicative explicit formula pairs the test with its linear
transpose.  Indexing by `k : ℕ` avoids the exceptional integer zero. -/
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
      (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
      _ ≤ B := hkB
      _ < (N : ℝ) := hN
  exact_mod_cast hkN.le

/-- Evaluation of the linear transpose on positive integers also has finite
support.  This is the endpoint-zero half of compact support: inversion maps
the compact topological support to another compact, hence bounded, set. -/
theorem transposeIntegerSupport_finite (f : BombieriTest) :
    {k : ℕ | transpose (f : ℝ → ℂ) (k + 1 : ℕ) ≠ 0}.Finite := by
  have hinvContinuous :
      ContinuousOn (fun x : ℝ ↦ x⁻¹) (tsupport f) :=
    continuousOn_id.inv₀ fun x hx ↦ (f.tsupport_subset hx).ne'
  have hinvCompact : IsCompact ((fun x : ℝ ↦ x⁻¹) '' tsupport f) :=
    f.hasCompactSupport.image_of_continuousOn hinvContinuous
  rw [Set.finite_iff_bddAbove]
  obtain ⟨B, hB⟩ := hinvCompact.bddAbove
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
  refine ⟨N, ?_⟩
  intro k hk
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hfne : f (((k + 1 : ℕ) : ℝ)⁻¹) ≠ 0 := by
    change transpose (f : ℝ → ℂ) (((k + 1 : ℕ) : ℝ)) ≠ 0 at hk
    rw [transpose_apply_of_pos (f : ℝ → ℂ) hkpos] at hk
    exact (div_ne_zero_iff.mp hk).1
  have hmem : (((k + 1 : ℕ) : ℝ)⁻¹) ∈ tsupport f :=
    subset_tsupport f (Function.mem_support.mpr hfne)
  have himage : ((k + 1 : ℕ) : ℝ) ∈
      (fun x : ℝ ↦ x⁻¹) '' tsupport f := by
    refine ⟨(((k + 1 : ℕ) : ℝ)⁻¹), hmem, ?_⟩
    simp
  have hkB : ((k + 1 : ℕ) : ℝ) ≤ B := hB himage
  have hkN : (k : ℝ) < (N : ℝ) := by
    calc
      (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
      _ ≤ B := hkB
      _ < (N : ℝ) := hN
  exact_mod_cast hkN.le

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
      (right_ne_zero_of_mul hk)

/-- The prime series is summable because it is actually a finite sum. -/
theorem vonMangoldtPrimeSummand_summable (f : BombieriTest) :
    Summable (vonMangoldtPrimeSummand f) :=
  summable_of_hasFiniteSupport (vonMangoldtPrimeSummand_hasFiniteSupport f)

/-- The prime contribution to Bombieri's multiplicative explicit formula. -/
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

/-- The prime contribution is a genuine complex-linear functional. -/
def primeSumLinearMap : BombieriTest →ₗ[ℂ] ℂ where
  toFun := primeSum
  map_add' := primeSum_add
  map_smul' c f := by simpa only [smul_eq_mul] using primeSum_smul c f

@[simp]
theorem primeSumLinearMap_apply (f : BombieriTest) :
    primeSumLinearMap f = primeSum f := rfl

/-- A bundled transpose acts on the prime kernel by swapping its two
summands. -/
theorem primeKernel_transposeData (transposeData : TransposeData)
    (f : BombieriTest) (k : ℕ) :
    primeKernel (transposeData.toLinearMap f) k = primeKernel f k := by
  let n : ℝ := (k + 1 : ℕ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hfirst : transposeData.toLinearMap f n = transpose (f : ℝ → ℂ) n :=
    transposeData.apply_pos f hn
  have hsecond :
      transpose (transposeData.toLinearMap f : ℝ → ℂ) n = f n := by
    calc
      transpose (transposeData.toLinearMap f : ℝ → ℂ) n =
          transposeData.toLinearMap f n⁻¹ / n :=
        transpose_apply_of_pos _ hn
      _ = transpose (f : ℝ → ℂ) n⁻¹ / n := by
        rw [transposeData.apply_pos f (inv_pos.mpr hn)]
      _ = transpose (transpose (f : ℝ → ℂ)) n := by
        rw [transpose_apply_of_pos (transpose (f : ℝ → ℂ)) hn]
      _ = f n := transpose_involutive_on_pos (f : ℝ → ℂ) hn
  change transposeData.toLinearMap f n +
      transpose (transposeData.toLinearMap f : ℝ → ℂ) n =
    f n + transpose (f : ℝ → ℂ) n
  rw [hfirst, hsecond]
  exact add_comm _ _

/-- The prime sum is invariant under any bundled realization of Bombieri's
linear transpose. -/
theorem primeSum_transposeData (transposeData : TransposeData)
    (f : BombieriTest) :
    primeSum (transposeData.toLinearMap f) = primeSum f := by
  unfold primeSum
  apply tsum_congr
  intro k
  simp only [vonMangoldtPrimeSummand,
    primeKernel_transposeData transposeData f k]

#print axioms directIntegerSupport_finite
#print axioms transposeIntegerSupport_finite
#print axioms primeKernel_hasFiniteSupport
#print axioms vonMangoldtPrimeSummand_hasFiniteSupport
#print axioms vonMangoldtPrimeSummand_summable
#print axioms primeSum_add
#print axioms primeSum_smul
#print axioms primeSumLinearMap_apply
#print axioms primeSum_transposeData

end

end ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriPrimeSupportScratch
