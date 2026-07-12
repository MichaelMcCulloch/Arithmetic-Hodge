import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceCheckDefs

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

noncomputable section

open RatInterval
open SparseCongruenceCertificate
open SparseEntriesCertificate
open YoshidaEvenIntervalCertificate
open YoshidaEvenSparseCongruenceData

/-- Interval multiplication is commutative even though `RatInterval` only
installs the bare `Mul` operation. -/
private theorem ratInterval_mul_comm (I J : RatInterval) : I * J = J * I := by
  rcases I with ⟨il, iu⟩
  rcases J with ⟨jl, ju⟩
  apply congrArg₂ RatInterval.mk
  · change
      min (min (il * jl) (il * ju)) (min (iu * jl) (iu * ju)) =
        min (min (jl * il) (jl * iu)) (min (ju * il) (ju * iu))
    simp only [mul_comm]
    ac_rfl
  · change
      max (max (il * jl) (il * ju)) (max (iu * jl) (iu * ju)) =
        max (max (jl * il) (jl * iu)) (max (ju * il) (ju * iu))
    simp only [mul_comm]
    ac_rfl

/-- Negating the left factor negates the complete interval product. -/
private theorem ratInterval_neg_mul (I J : RatInterval) : (-I) * J = -(I * J) := by
  rcases I with ⟨il, iu⟩
  rcases J with ⟨jl, ju⟩
  apply congrArg₂ RatInterval.mk
  · change
      min (min ((-iu) * jl) ((-iu) * ju))
          (min ((-il) * jl) ((-il) * ju)) =
        -max (max (il * jl) (il * ju)) (max (iu * jl) (iu * ju))
    simp only [neg_mul, min_neg_neg]
    congr 1
    ac_rfl
  · change
      max (max ((-iu) * jl) ((-iu) * ju))
          (max ((-il) * jl) ((-il) * ju)) =
        -min (min (il * jl) (il * ju)) (min (iu * jl) (iu * ju))
    simp only [neg_mul, max_neg_neg]
    congr 1
    ac_rfl

private theorem ratInterval_neg_neg (I : RatInterval) : -(-I) = I := by
  rcases I with ⟨il, iu⟩
  change RatInterval.mk (-(-il)) (-(-iu)) = RatInterval.mk il iu
  congr <;> ring

private theorem ratInterval_mul_neg (I J : RatInterval) : I * (-J) = -(I * J) := by
  calc
    I * (-J) = (-J) * I := ratInterval_mul_comm I (-J)
    _ = -(J * I) := ratInterval_neg_mul J I
    _ = -(I * J) := congrArg (fun K : RatInterval ↦ -K) (ratInterval_mul_comm J I)

/-- The two sign changes appearing when an off-diagonal Gram entry is
transposed cancel exactly, including the outward interval hull. -/
private theorem ratInterval_neg_mul_neg (I J : RatInterval) :
    (-I) * (-J) = I * J := by
  calc
    (-I) * (-J) = -(I * (-J)) := ratInterval_neg_mul I (-J)
    _ = -(-(I * J)) := congrArg (fun K : RatInterval ↦ -K) (ratInterval_mul_neg I J)
    _ = I * J := ratInterval_neg_neg (I * J)

private theorem ratInterval_sub_swap (I J : RatInterval) :
    J - I = -(I - J) := by
  rcases I with ⟨il, iu⟩
  rcases J with ⟨jl, ju⟩
  change RatInterval.mk (jl - iu) (ju - il) =
    RatInterval.mk (-(iu - jl)) (-(il - ju))
  congr <;> ring

private theorem ratInterval_pure_neg (q : ℚ) :
    pure (-q) = -(pure q) := rfl

private theorem evenOffDiagonalCoeffQ_swap (n m : ℕ) :
    evenOffDiagonalCoeffQ m n = -evenOffDiagonalCoeffQ n m := by
  unfold evenOffDiagonalCoeffQ
  rw [Nat.add_comm m n]
  have hden : (m : ℚ) ^ 2 - (n : ℚ) ^ 2 =
      -((n : ℚ) ^ 2 - (m : ℚ) ^ 2) := by ring
  rw [hden, div_neg]

/-- The interval formula for the even moment Gram is analytically symmetric.
This avoids reducing the 40,000 entries of the concrete target matrix. -/
private theorem evenMomentIntervalGram_comm
    (S D : ℕ → RatInterval) (i j : YoshidaEvenIndex) :
    evenMomentIntervalGram S D i j = evenMomentIntervalGram S D j i := by
  by_cases hi : i.1 = 0
  · by_cases hj : j.1 = 0
    · have hij : i = j := Fin.ext (hi.trans hj.symm)
      subst j
      rfl
    · simp [evenMomentIntervalGram, hi, hj]
  · by_cases hj : j.1 = 0
    · simp [evenMomentIntervalGram, hi, hj]
    · by_cases hij : i = j
      · subst j
        rfl
      · have hji : j ≠ i := Ne.symm hij
        simp only [evenMomentIntervalGram, hi, hj, hij, hji, ↓reduceIte]
        have hcoeff :
            pure (evenOffDiagonalCoeffQ j.1 i.1) * evenInvPiInterval =
              -(pure (evenOffDiagonalCoeffQ i.1 j.1) * evenInvPiInterval) := by
          rw [evenOffDiagonalCoeffQ_swap i.1 j.1, ratInterval_pure_neg,
            ratInterval_neg_mul]
        have hdiff :
            pure (i.1 : ℚ) * S i.1 - pure (j.1 : ℚ) * S j.1 =
              -(pure (j.1 : ℚ) * S j.1 - pure (i.1 : ℚ) * S i.1) :=
          ratInterval_sub_swap _ _
        rw [hcoeff, hdiff, ratInterval_neg_mul_neg]

private theorem evenTargetInterval_comm (i j : YoshidaEvenIndex) :
    evenTargetInterval i j = evenTargetInterval j i := by
  unfold evenTargetInterval inflatedEvenMomentIntervalGram
  rw [evenMomentIntervalGram_comm]

/-- Every concrete target center entry is equal to its transpose, proved from
the analytic interval formula rather than by a 200-by-200 table check. -/
theorem evenTargetCenterSymmetricAt (i j : YoshidaEvenIndex) :
    EvenTargetCenterSymmetricAt i j := by
  unfold EvenTargetCenterSymmetricAt evenTargetCenter
  rw [evenTargetInterval_comm]

theorem evenTargetCenterSymmetricRow (i : YoshidaEvenIndex) :
    EvenTargetCenterSymmetricRow i :=
  fun j ↦ evenTargetCenterSymmetricAt i j

theorem evenTargetCenterSymmetric :
    ∀ i j : YoshidaEvenIndex, EvenTargetCenterSymmetricAt i j :=
  evenTargetCenterSymmetricAt

private abbrev EvenSparseEntriesCheckAt (i : YoshidaEvenIndex) : Prop :=
  0 < evenSparseWeights i ∧
    ((evenSparseEntries i).map Prod.fst).all
      (fun j ↦ decide (j ≤ i)) = true ∧
    0 < entriesValue (evenSparseEntries i) i

private def evenSparseIndices : List YoshidaEvenIndex := List.ofFn id

/- The structural checker reduces only the 762 canonical pair-list entries,
never the noncomputable support fields of `Finsupp.single`. -/
set_option maxHeartbeats 2000000 in
private theorem evenSparseEntries_check (i : YoshidaEvenIndex) :
    EvenSparseEntriesCheckAt i := by
  have hcheck : evenSparseIndices.all
      (fun k ↦ decide (EvenSparseEntriesCheckAt k)) = true := by
    decide +kernel
  have hiMem : i ∈ evenSparseIndices := by
    rw [evenSparseIndices, List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) i hiMem)

/-- Every generated row has positive weight, lower-triangular support, and a
positive diagonal. -/
theorem evenSparseRowStructureAt (i : YoshidaEvenIndex) :
    EvenSparseRowStructureAt i := by
  rcases evenSparseEntries_check i with ⟨hweight, hkeys, hdiag⟩
  unfold EvenSparseRowStructureAt
  refine ⟨hweight, ?_, ?_⟩
  · intro j
    unfold EvenSparseLowerTriangularAt
    intro hnonzero
    change rowOfEntries (evenSparseEntries i) j ≠ 0 at hnonzero
    have hjMem : j ∈ (evenSparseEntries i).map Prod.fst :=
      mem_map_fst_of_rowOfEntries_apply_ne_zero hnonzero
    exact of_decide_eq_true ((List.all_eq_true.mp hkeys) j hjMem)
  · unfold EvenSparseDiagonalPositiveAt
    change 0 < rowOfEntries (evenSparseEntries i) i
    rw [rowOfEntries_apply]
    exact hdiag

theorem evenSparseRowStructure :
    ∀ i : YoshidaEvenIndex, EvenSparseRowStructureAt i :=
  evenSparseRowStructureAt

example (i j : YoshidaEvenIndex) : EvenTargetCenterSymmetricAt i j :=
  evenTargetCenterSymmetricAt i j

example (i : YoshidaEvenIndex) : EvenTargetCenterSymmetricRow i :=
  evenTargetCenterSymmetricRow i

example (i : YoshidaEvenIndex) : EvenSparseRowStructureAt i :=
  evenSparseRowStructureAt i

end

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
