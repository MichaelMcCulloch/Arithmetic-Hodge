import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalFourCellBlockStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLogLatticeCovarianceStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellYoshidaBridgeStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalFourCellBlockStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoParityRealification
open YoshidaFactorTwoPrimeDomination
open YoshidaEndpointHyperbolicBound

/-!
# Four monotone cells in centered Yoshida coordinates

The four-cell block splits into two ratio-two halves.  Centering each half
puts both diagonal terms in the existing Yoshida endpoint channel.  The
complete cross, however, becomes a cross between two independent centered
profiles at relative dilation `2^(-1/2)`, not the same-seed factor-two
coordinate `g` against `D₂ g`.

The resulting theorem is an exact total balance: it retains both positive
Yoshida diagonal reserves and the complete independent cross.  A separate
range lemma shows that representing the canonical half split as the existing
same-seed factor-two pencil would force the common parent to vanish on an
entire middle quarter interval.  Thus endpoint-channel positivity cannot be
applied to four monotone cells without a new independent-profile,
half-factor-two cross estimate.
-/

/-! ## Canonical halves and their support boxes -/

def fourCellLeftHalf (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 2

def fourCellRightHalf (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 2 2

private theorem monotoneQuarterFiniteBlock_eq_shifted_sum
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock parent lo start len =
      ∑ i ∈ Finset.range len,
        monotoneQuarterCell parent
          (lo + (start : ℤ) + (i : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock
  apply Finset.sum_congr rfl
  intro i _hi
  have hindex : lo + ((start + i : ℕ) : ℤ) =
      lo + (start : ℤ) + (i : ℤ) := by
    push_cast
    ring
  rw [hindex]

theorem monotoneQuarterFourBlock_eq_halves
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock parent k =
      fourCellLeftHalf parent k + fourCellRightHalf parent k := by
  unfold monotoneQuarterFourBlock fourCellLeftHalf fourCellRightHalf
  simpa using
    (monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent k 0 4 2 (by omega))

private theorem tsupport_finset_sum_subset_Icc
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → BombieriTest) (a b : ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ Set.Icc a b) :
    tsupport (((∑ i ∈ s, f i) : BombieriTest) : ℝ → ℂ) ⊆
      Set.Icc a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add (f i : ℝ → ℂ)
          (∑ j ∈ s, f j : BombieriTest)).trans
        (union_subset (hf i (by simp))
          (ih (fun j hj ↦ hf j (by simp [hj]))))

theorem fourCellLeftHalf_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (fourCellLeftHalf parent k) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 4)) := by
  rw [fourCellLeftHalf, monotoneQuarterFiniteBlock_eq_shifted_sum]
  apply tsupport_finset_sum_subset_Icc
  intro i hi
  have hiTwo : i < 2 := Finset.mem_range.mp hi
  apply (monotoneQuarterCell_tsupport_subset parent
    (k + (0 : ℤ) + (i : ℤ))).trans
  apply Set.Icc_subset_Icc
  · apply quarterLogLatticePoint_mono
    omega
  · apply quarterLogLatticePoint_mono
    omega

theorem fourCellRightHalf_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (fourCellRightHalf parent k) ⊆
      Set.Icc (quarterLogLatticePoint (k + 2))
        (quarterLogLatticePoint (k + 6)) := by
  rw [fourCellRightHalf, monotoneQuarterFiniteBlock_eq_shifted_sum]
  apply tsupport_finset_sum_subset_Icc
  intro i hi
  have hiTwo : i < 2 := Finset.mem_range.mp hi
  apply (monotoneQuarterCell_tsupport_subset parent
    (k + (2 : ℤ) + (i : ℤ))).trans
  apply Set.Icc_subset_Icc
  · apply quarterLogLatticePoint_mono
    omega
  · apply quarterLogLatticePoint_mono
    omega

theorem fourCellLeftHalf_endpoint_ratio (k : ℤ) :
    quarterLogLatticePoint (k + 4) / quarterLogLatticePoint k = 2 := by
  rw [quarterLogLatticePoint_add_four]
  exact mul_div_cancel_right₀ 2 (quarterLogLatticePoint_pos k).ne'

theorem fourCellRightHalf_endpoint_ratio (k : ℤ) :
    quarterLogLatticePoint (k + 6) /
        quarterLogLatticePoint (k + 2) = 2 := by
  rw [show k + 6 = (k + 2) + 4 by ring,
    quarterLogLatticePoint_add_four]
  exact mul_div_cancel_right₀ 2
    (quarterLogLatticePoint_pos (k + 2)).ne'

/-! ## Logarithmic centers and the half-factor-two lag -/

def fourCellLeftCenter (k : ℤ) : ℝ :=
  logarithmicCenter (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 4))

def fourCellRightCenter (k : ℤ) : ℝ :=
  logarithmicCenter (quarterLogLatticePoint (k + 2))
    (quarterLogLatticePoint (k + 6))

def fourCellLeftCenteredHalf
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  normalizedDilation (fourCellLeftCenter k)
    (logarithmicCenter_pos _ _) (fourCellLeftHalf parent k)

def fourCellRightCenteredHalf
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  normalizedDilation (fourCellRightCenter k)
    (logarithmicCenter_pos _ _) (fourCellRightHalf parent k)

/-- Relative dilation after the two halves have been centered separately. -/
def fourCellCenteredRelativeLag (k : ℤ) : ℝ :=
  fourCellLeftCenter k / fourCellRightCenter k

private theorem logarithmicCenter_mul
    {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    logarithmicCenter (c * a) (c * b) =
      c * logarithmicCenter a b := by
  unfold logarithmicCenter
  rw [Real.log_mul hc.ne' ha.ne', Real.log_mul hc.ne' hb.ne']
  rw [show (Real.log c + Real.log a +
      (Real.log c + Real.log b)) / 2 =
        Real.log c + (Real.log a + Real.log b) / 2 by ring,
    Real.exp_add, Real.exp_log hc]

/-- The right half center is `2^(1/2)` times the left half center. -/
theorem fourCellRightCenter_eq_quarterPointTwo_mul_leftCenter
    (k : ℤ) :
    fourCellRightCenter k =
      quarterLogLatticePoint 2 * fourCellLeftCenter k := by
  unfold fourCellLeftCenter fourCellRightCenter
  rw [show k + 6 = (k + 4) + 2 by ring,
    quarterLogLatticePoint_add,
    quarterLogLatticePoint_add]
  exact logarithmicCenter_mul
    (quarterLogLatticePoint_pos 2)
    (quarterLogLatticePoint_pos k)
    (quarterLogLatticePoint_pos (k + 4))

theorem fourCellCenteredRelativeLag_eq_inv_quarterPointTwo
    (k : ℤ) :
    fourCellCenteredRelativeLag k =
      (quarterLogLatticePoint 2)⁻¹ := by
  rw [fourCellCenteredRelativeLag,
    fourCellRightCenter_eq_quarterPointTwo_mul_leftCenter]
  field_simp [(quarterLogLatticePoint_pos 2).ne',
    (logarithmicCenter_pos
      (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 4))).ne']
  exact div_self (logarithmicCenter_pos _ _).ne'

private theorem quarterLogLatticePoint_two_sq :
    quarterLogLatticePoint 2 ^ 2 = 2 := by
  unfold quarterLogLatticePoint
  norm_num
  rw [← Real.exp_nat_mul]
  convert Real.exp_log (by norm_num : (0 : ℝ) < 2) using 1
  ring_nf

/-- The centered relative lag has square exactly `1/2`. -/
theorem fourCellCenteredRelativeLag_sq (k : ℤ) :
    fourCellCenteredRelativeLag k ^ 2 = (1 / 2 : ℝ) := by
  rw [fourCellCenteredRelativeLag_eq_inv_quarterPointTwo, inv_pow,
    quarterLogLatticePoint_two_sq]
  norm_num

/-- Consequently it is not the lag `2` consumed by the same-seed Yoshida
endpoint channel. -/
theorem fourCellCenteredRelativeLag_ne_two (k : ℤ) :
    fourCellCenteredRelativeLag k ≠ 2 := by
  intro htwo
  have hsquare := fourCellCenteredRelativeLag_sq k
  rw [htwo] at hsquare
  norm_num at hsquare

/-! ## Each diagonal is an existing Yoshida endpoint channel -/

/-- Generic exact bridge from a ratio-two Bombieri diagonal to the clean sum
of its canonically centered real and imaginary Yoshida profiles. -/
theorem bombieriRealQuadraticValue_eq_centeredEndpointChannelCleanSum
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    bombieriRealQuadraticValue g =
      yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile (bombieriRealPartTest gc))
        (factorTwoCenteredProfile (bombieriImagPartTest gc)) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  have haC : 0 < a / lambda := div_pos ha hlambda
  have habC : a / lambda ≤ b / lambda :=
    div_le_div_of_nonneg_right hab hlambda.le
  have hsupportC : tsupport gc ⊆ Set.Icc (a / lambda) (b / lambda) :=
    normalizedDilation_tsupport_subset_Icc lambda hlambda g hsupport
  have hratioC : (b / lambda) / (a / lambda) ≤ 2 := by
    rw [div_div_div_cancel_right₀ hlambda.ne' b a]
    exact hratio
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc, lambda, hlambda] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  calc
    bombieriRealQuadraticValue g = factorTwoDiagonalCoordinate g := by
      unfold bombieriRealQuadraticValue
      rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
        g ha hab hsupport hratio]
      exact (factorTwoDiagonalCoordinate_eq_localCriticalForm
        g ha hab hsupport hratio).symm
    _ = factorTwoDiagonalCoordinate gc :=
      (factorTwoDiagonalCoordinate_normalizedDilation
        lambda hlambda g).symm
    _ = yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile (bombieriRealPartTest gc))
        (factorTwoCenteredProfile (bombieriImagPartTest gc)) :=
      factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
        gc haC habC hsupportC hratioC hcritical

theorem fourCellLeftHalf_diagonal_eq_yoshidaChannel
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (fourCellLeftHalf parent k) =
      yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile
          (bombieriRealPartTest (fourCellLeftCenteredHalf parent k)))
        (factorTwoCenteredProfile
          (bombieriImagPartTest (fourCellLeftCenteredHalf parent k))) := by
  simpa only [fourCellLeftCenteredHalf, fourCellLeftCenter] using
    bombieriRealQuadraticValue_eq_centeredEndpointChannelCleanSum
      (fourCellLeftHalf parent k)
      (quarterLogLatticePoint_pos k)
      (quarterLogLatticePoint_mono (by omega))
      (fourCellLeftHalf_tsupport_subset parent k)
      (fourCellLeftHalf_endpoint_ratio k).le

theorem fourCellRightHalf_diagonal_eq_yoshidaChannel
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (fourCellRightHalf parent k) =
      yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile
          (bombieriRealPartTest (fourCellRightCenteredHalf parent k)))
        (factorTwoCenteredProfile
          (bombieriImagPartTest (fourCellRightCenteredHalf parent k))) := by
  simpa only [fourCellRightCenteredHalf, fourCellRightCenter] using
    bombieriRealQuadraticValue_eq_centeredEndpointChannelCleanSum
      (fourCellRightHalf parent k)
      (quarterLogLatticePoint_pos (k + 2))
      (quarterLogLatticePoint_mono (by omega))
      (fourCellRightHalf_tsupport_subset parent k)
      (fourCellRightHalf_endpoint_ratio k).le

/-! ## Exact total centered balance -/

/-- The out-of-range coordinate left after both halves are centered. -/
def fourCellCenteredIndependentCross
    (parent : BombieriTest) (k : ℤ) : ℂ :=
  bombieriTwoBlockGlobalCrossSymbol
    (fourCellLeftCenteredHalf parent k)
    (normalizedDilation (fourCellCenteredRelativeLag k)
      (div_pos (logarithmicCenter_pos _ _)
        (logarithmicCenter_pos _ _))
      (fourCellRightCenteredHalf parent k))

private theorem normalizedDilation_relativeLag_rightCentered
    (parent : BombieriTest) (k : ℤ) :
    normalizedDilation (fourCellCenteredRelativeLag k)
        (div_pos (logarithmicCenter_pos _ _)
          (logarithmicCenter_pos _ _))
        (fourCellRightCenteredHalf parent k) =
      normalizedDilation (fourCellLeftCenter k)
        (logarithmicCenter_pos _ _) (fourCellRightHalf parent k) := by
  let lambdaL := fourCellLeftCenter k
  let lambdaR := fourCellRightCenter k
  have hlambdaL : 0 < lambdaL := logarithmicCenter_pos _ _
  have hlambdaR : 0 < lambdaR := logarithmicCenter_pos _ _
  have hproduct : (lambdaL / lambdaR) * lambdaR = lambdaL := by
    exact div_mul_cancel₀ lambdaL hlambdaR.ne'
  calc
    normalizedDilation (fourCellCenteredRelativeLag k)
        (div_pos (logarithmicCenter_pos _ _)
          (logarithmicCenter_pos _ _))
        (fourCellRightCenteredHalf parent k) =
      normalizedDilation (lambdaL / lambdaR)
        (div_pos hlambdaL hlambdaR)
        (normalizedDilation lambdaR hlambdaR
          (fourCellRightHalf parent k)) := by rfl
    _ = normalizedDilation ((lambdaL / lambdaR) * lambdaR)
        (mul_pos (div_pos hlambdaL hlambdaR) hlambdaR)
        (fourCellRightHalf parent k) :=
      normalizedDilation_comp (lambdaL / lambdaR) lambdaR
        (div_pos hlambdaL hlambdaR) hlambdaR
        (fourCellRightHalf parent k)
    _ = normalizedDilation lambdaL hlambdaL
        (fourCellRightHalf parent k) := by
      apply TestFunction.ext
      intro x
      simp only [normalizedDilation_apply, hproduct]

/-- Simultaneous dilation covariance identifies the original half cross with
the independent centered cross at lag `2^(-1/2)`. -/
theorem fourCell_globalHalfCross_eq_centeredIndependentCross
    (parent : BombieriTest) (k : ℤ) :
    bombieriTwoBlockGlobalCrossSymbol
        (fourCellLeftHalf parent k) (fourCellRightHalf parent k) =
      fourCellCenteredIndependentCross parent k := by
  unfold fourCellCenteredIndependentCross fourCellLeftCenteredHalf
  rw [normalizedDilation_relativeLag_rightCentered]
  exact (bombieriTwoBlockGlobalCrossSymbol_normalizedDilation
    (fourCellLeftCenter k) (logarithmicCenter_pos _ _)
    (fourCellLeftHalf parent k) (fourCellRightHalf parent k)).symm

/-- Exact four-cell total balance in centered endpoint coordinates.  Both
diagonals are existing Yoshida clean-channel sums; the final term is the
independent half-factor-two coordinate, not an endpoint same-seed radius. -/
theorem bombieriRealQuadraticValue_fourBlock_eq_centeredYoshidaBalance
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterFourBlock parent k) =
      yoshidaEndpointA * factorTwoEndpointChannelCleanSum
          (factorTwoCenteredProfile
            (bombieriRealPartTest (fourCellLeftCenteredHalf parent k)))
          (factorTwoCenteredProfile
            (bombieriImagPartTest (fourCellLeftCenteredHalf parent k))) +
        yoshidaEndpointA * factorTwoEndpointChannelCleanSum
          (factorTwoCenteredProfile
            (bombieriRealPartTest (fourCellRightCenteredHalf parent k)))
          (factorTwoCenteredProfile
            (bombieriImagPartTest (fourCellRightCenteredHalf parent k))) +
        2 * (fourCellCenteredIndependentCross parent k).re := by
  rw [monotoneQuarterFourBlock_eq_halves,
    bombieriRealQuadraticValue_add,
    fourCellLeftHalf_diagonal_eq_yoshidaChannel,
    fourCellRightHalf_diagonal_eq_yoshidaChannel,
    fourCell_globalHalfCross_eq_centeredIndependentCross]

/-! ## Why the canonical split is not a same-seed factor-two pencil -/

/-- Membership in the already-existing same-seed pencil using the canonical
upper half as seed. -/
def FourCellCanonicalSameSeedPencil
    (parent : BombieriTest) (k : ℤ) : Prop :=
  ∃ c : ℂ,
    monotoneQuarterFourBlock parent k =
      fourCellRightHalf parent k +
        c • normalizedDilation 2 (by norm_num)
          (fourCellRightHalf parent k)

/-- Exact range equation for that membership: the lower half must literally
be a scalar multiple of the factor-two dilation of the upper half. -/
theorem fourCellCanonicalSameSeedPencil_iff_halfRange
    (parent : BombieriTest) (k : ℤ) :
    FourCellCanonicalSameSeedPencil parent k ↔
      ∃ c : ℂ,
        fourCellLeftHalf parent k =
          c • normalizedDilation 2 (by norm_num)
            (fourCellRightHalf parent k) := by
  rw [FourCellCanonicalSameSeedPencil,
    monotoneQuarterFourBlock_eq_halves]
  constructor
  · rintro ⟨c, h⟩
    refine ⟨c, ?_⟩
    calc
      fourCellLeftHalf parent k =
          (fourCellLeftHalf parent k + fourCellRightHalf parent k) -
            fourCellRightHalf parent k := by abel
      _ = (fourCellRightHalf parent k +
            c • normalizedDilation 2 (by norm_num)
              (fourCellRightHalf parent k)) -
            fourCellRightHalf parent k := by rw [h]
      _ = c • normalizedDilation 2 (by norm_num)
          (fourCellRightHalf parent k) := by abel
  · rintro ⟨c, h⟩
    refine ⟨c, ?_⟩
    rw [h]
    abel

private theorem fourCellLeftHalf_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) :
    fourCellLeftHalf parent k =
      monotoneQuarterCutoff parent k -
        monotoneQuarterCutoff parent (k + 2) := by
  unfold fourCellLeftHalf monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  exact sum_range_monotoneQuarterCell_eq_cutoff_sub parent k 2

private theorem fourCellRightHalf_eq_cutoff_sub
    (parent : BombieriTest) (k : ℤ) :
    fourCellRightHalf parent k =
      monotoneQuarterCutoff parent (k + 2) -
        monotoneQuarterCutoff parent (k + 4) := by
  rw [fourCellRightHalf, monotoneQuarterFiniteBlock_eq_shifted_sum]
  norm_num only [Nat.cast_ofNat]
  have h := sum_range_monotoneQuarterCell_eq_cutoff_sub parent (k + 2) 2
  have hindex : k + 2 + ((2 : ℕ) : ℤ) = k + 4 := by
    norm_num
    ring
  rw [hindex] at h
  exact h

private theorem fourCellLeftHalf_apply_middle
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint (k + 1))
      (quarterLogLatticePoint (k + 2))) :
    fourCellLeftHalf parent k x = parent x := by
  rw [fourCellLeftHalf_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  rw [monotoneQuarterStep_eq_one_of_le k hx.1,
    monotoneQuarterStep_eq_zero_of_le (k + 2) hx.2]
  simp

private theorem fourCellRightHalf_apply_two_mul_middle
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint (k + 1))
      (quarterLogLatticePoint (k + 2))) :
    fourCellRightHalf parent k (2 * x) = 0 := by
  rw [fourCellRightHalf_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  have hlast : quarterLogLatticePoint (k + 5) ≤ 2 * x := by
    rw [show k + 5 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four]
    exact mul_le_mul_of_nonneg_left hx.1 (by norm_num)
  rw [monotoneQuarterStep_eq_one_of_le (k + 2)
      ((quarterLogLatticePoint_mono (by omega)).trans hlast),
    monotoneQuarterStep_eq_one_of_le (k + 4)
      (by simpa only [add_assoc] using hlast)]
  simp

/-- The exact range obstruction: canonical same-seed membership forces the
common parent to vanish throughout the middle quarter interval. -/
theorem fourCellCanonicalSameSeedPencil_forces_parent_zero_middle
    (parent : BombieriTest) (k : ℤ)
    (hsame : FourCellCanonicalSameSeedPencil parent k) :
    ∀ x ∈ Set.Icc (quarterLogLatticePoint (k + 1))
        (quarterLogLatticePoint (k + 2)),
      parent x = 0 := by
  obtain ⟨c, hhalf⟩ :=
    (fourCellCanonicalSameSeedPencil_iff_halfRange parent k).mp hsame
  intro x hx
  have heval := congrArg (fun f : BombieriTest ↦ f x) hhalf
  change fourCellLeftHalf parent k x =
    (c • normalizedDilation 2 (by norm_num)
      (fourCellRightHalf parent k)) x at heval
  rw [fourCellLeftHalf_apply_middle parent k hx,
    TestFunction.coe_smul, Pi.smul_apply, normalizedDilation_apply,
    fourCellRightHalf_apply_two_mul_middle parent k hx,
    mul_zero, smul_eq_mul, mul_zero] at heval
  exact heval

/-- Any nonzero parent value on that middle interval excludes the four-cell
block from the canonical same-seed factor-two pencil. -/
theorem fourCellCanonicalSameSeedPencil_false_of_parent_nonzero_middle
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint (k + 1))
      (quarterLogLatticePoint (k + 2)))
    (hparent : parent x ≠ 0) :
    ¬ FourCellCanonicalSameSeedPencil parent k := by
  intro hsame
  exact hparent
    (fourCellCanonicalSameSeedPencil_forces_parent_zero_middle
      parent k hsame x hx)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellYoshidaBridgeStructural
