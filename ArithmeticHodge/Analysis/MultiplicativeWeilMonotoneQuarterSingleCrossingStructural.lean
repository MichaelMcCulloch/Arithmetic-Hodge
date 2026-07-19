import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterStepTotalPositivityStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterSingleCrossingStructural

noncomputable section

open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Single crossing of real nested quarter-step multipliers

The multiplier `step k + d * step (k+1)` first rises from zero to one and
then moves monotonically from one to `1+d`.  Hence `d = -1` is the exact
threshold for nonnegative products at every ordered pair.  Below that
threshold, an ordered product is negative precisely when the first point is
on the positive side of the unique sign transition and the second point is
on the negative side.  Monotonicity suffices for this sign classification;
no unproved strict-monotonicity property is used.
-/

/-- A real linear combination of two adjacent nested boundary steps. -/
def monotoneQuarterNestedMultiplier (k : ℤ) (d t : ℝ) : ℝ :=
  monotoneQuarterStep k t + d * monotoneQuarterStep (k + 1) t

/-- The same multiplier in head-cell plus suffix coordinates. -/
def monotoneQuarterHeadSuffixMultiplier (k : ℤ) (a t : ℝ) : ℝ :=
  monotoneQuarterWeight k t + a * monotoneQuarterStep (k + 1) t

theorem monotoneQuarterHeadSuffixMultiplier_eq_nested
    (k : ℤ) (a t : ℝ) :
    monotoneQuarterHeadSuffixMultiplier k a t =
      monotoneQuarterNestedMultiplier k (a - 1) t := by
  unfold monotoneQuarterHeadSuffixMultiplier monotoneQuarterNestedMultiplier
    monotoneQuarterWeight
  ring

/-- At the shared lattice point only the earlier step has switched on. -/
theorem monotoneQuarterNestedMultiplier_shared
    (k : ℤ) (d : ℝ) :
    monotoneQuarterNestedMultiplier k d
        (quarterLogLatticePoint (k + 1)) = 1 := by
  unfold monotoneQuarterNestedMultiplier
  rw [monotoneQuarterStep_eq_one_of_le k le_rfl,
    monotoneQuarterStep_eq_zero_of_le (k + 1) le_rfl]
  ring

/-- At the next lattice point both steps have switched on. -/
theorem monotoneQuarterNestedMultiplier_upper
    (k : ℤ) (d : ℝ) :
    monotoneQuarterNestedMultiplier k d
        (quarterLogLatticePoint (k + 2)) = 1 + d := by
  unfold monotoneQuarterNestedMultiplier
  rw [monotoneQuarterStep_eq_one_of_le k
      (quarterLogLatticePoint_mono (by omega)),
    monotoneQuarterStep_eq_one_of_le (k + 1) (by
      simpa only [add_assoc] using
        (le_refl (quarterLogLatticePoint ((k + 1) + 1))))]
  ring

/-- Before the shared lattice point the later step is zero, so every real
nested multiplier is nonnegative there. -/
theorem monotoneQuarterNestedMultiplier_nonnegative_of_le_shared
    (k : ℤ) (d : ℝ) {t : ℝ}
    (ht : t ≤ quarterLogLatticePoint (k + 1)) :
    0 ≤ monotoneQuarterNestedMultiplier k d t := by
  unfold monotoneQuarterNestedMultiplier
  rw [monotoneQuarterStep_eq_zero_of_le (k + 1) ht, mul_zero, add_zero]
  exact monotoneQuarterStep_nonneg k t

/-- `d = -1` is the sharp lower parameter threshold for global pointwise
nonnegativity. -/
theorem monotoneQuarterNestedMultiplier_nonnegative_of_neg_one_le
    (k : ℤ) {d : ℝ} (hd : -1 ≤ d) (t : ℝ) :
    0 ≤ monotoneQuarterNestedMultiplier k d t := by
  by_cases ht : t ≤ quarterLogLatticePoint (k + 1)
  · exact monotoneQuarterNestedMultiplier_nonnegative_of_le_shared k d ht
  · have hqt : quarterLogLatticePoint (k + 1) ≤ t := (not_le.mp ht).le
    unfold monotoneQuarterNestedMultiplier
    rw [monotoneQuarterStep_eq_one_of_le k hqt]
    have hs0 : 0 ≤ monotoneQuarterStep (k + 1) t :=
      monotoneQuarterStep_nonneg (k + 1) t
    have hs1 : monotoneQuarterStep (k + 1) t ≤ 1 :=
      monotoneQuarterStep_le_one (k + 1) t
    by_cases hd0 : 0 ≤ d
    · exact add_nonneg zero_le_one (mul_nonneg hd0 hs0)
    · have haux : 0 ≤ (-d) * (1 - monotoneQuarterStep (k + 1) t) :=
        mul_nonneg (neg_nonneg.mpr (le_of_not_ge hd0)) (sub_nonneg.mpr hs1)
      nlinarith

/-- For a negative coefficient, the multiplier is antitone after the shared
lattice point.  Its initial rise occurs entirely before this region. -/
theorem monotoneQuarterNestedMultiplier_antitoneOn_right
    (k : ℤ) {d : ℝ} (hd : d ≤ 0) :
    AntitoneOn (monotoneQuarterNestedMultiplier k d)
      (Set.Ici (quarterLogLatticePoint (k + 1))) := by
  intro y hy z hz hyz
  simp only [Set.mem_Ici] at hy hz
  unfold monotoneQuarterNestedMultiplier
  rw [monotoneQuarterStep_eq_one_of_le k hy,
    monotoneQuarterStep_eq_one_of_le k hz]
  have hs := monotoneQuarterStep_monotone (k + 1) hyz
  simpa only [add_comm] using
    (add_le_add_left (mul_le_mul_of_nonpos_left hs hd) 1)

/-- Once a multiplier with `d < -1` is negative, it stays negative at every
later point. -/
theorem monotoneQuarterNestedMultiplier_neg_forward
    (k : ℤ) {d y z : ℝ} (hd : d < -1) (hyz : y ≤ z)
    (hy : monotoneQuarterNestedMultiplier k d y < 0) :
    monotoneQuarterNestedMultiplier k d z < 0 := by
  have hyRight : quarterLogLatticePoint (k + 1) ≤ y := by
    by_contra hnot
    have hyLeft : y ≤ quarterLogLatticePoint (k + 1) := le_of_not_ge hnot
    exact (not_lt_of_ge
      (monotoneQuarterNestedMultiplier_nonnegative_of_le_shared
        k d hyLeft)) hy
  have hzRight : quarterLogLatticePoint (k + 1) ≤ z := hyRight.trans hyz
  have hanti := monotoneQuarterNestedMultiplier_antitoneOn_right
    k (show d ≤ 0 by linarith) hyRight hzRight hyz
  exact hanti.trans_lt hy

/-- The exact crossing level in the later step. -/
def monotoneQuarterNestedCrossingLevel (d : ℝ) : ℝ :=
  -1 / d

theorem monotoneQuarterNestedCrossingLevel_mem_Ioo
    {d : ℝ} (hd : d < -1) :
    monotoneQuarterNestedCrossingLevel d ∈ Set.Ioo (0 : ℝ) 1 := by
  have hd0 : d < 0 := hd.trans (by norm_num)
  constructor
  · exact div_pos_of_neg_of_neg (by norm_num) hd0
  · unfold monotoneQuarterNestedCrossingLevel
    apply (div_lt_iff_of_neg hd0).2
    simpa only [one_mul] using hd

/-- For every negative `d`, the sign is classified exactly by whether the
later step has passed the crossing level. -/
theorem monotoneQuarterNestedMultiplier_nonnegative_iff_step_le_crossingLevel
    (k : ℤ) {d : ℝ} (hd : d < 0) (t : ℝ) :
    0 ≤ monotoneQuarterNestedMultiplier k d t ↔
      monotoneQuarterStep (k + 1) t ≤
        monotoneQuarterNestedCrossingLevel d := by
  by_cases ht : t ≤ quarterLogLatticePoint (k + 1)
  · have hleft :=
      monotoneQuarterNestedMultiplier_nonnegative_of_le_shared k d ht
    have hstep : monotoneQuarterStep (k + 1) t = 0 :=
      monotoneQuarterStep_eq_zero_of_le (k + 1) ht
    have hlevel : 0 < monotoneQuarterNestedCrossingLevel d :=
      div_pos_of_neg_of_neg (by norm_num) hd
    rw [hstep]
    exact iff_of_true hleft hlevel.le
  · have hqt : quarterLogLatticePoint (k + 1) ≤ t := (not_le.mp ht).le
    unfold monotoneQuarterNestedMultiplier
    rw [monotoneQuarterStep_eq_one_of_le k hqt]
    unfold monotoneQuarterNestedCrossingLevel
    constructor
    · intro hm
      apply (le_div_iff_of_neg hd).2
      nlinarith
    · intro hs
      have hs' := (le_div_iff_of_neg hd).1 hs
      nlinarith

theorem monotoneQuarterNestedMultiplier_neg_iff_crossingLevel_lt_step
    (k : ℤ) {d : ℝ} (hd : d < 0) (t : ℝ) :
    monotoneQuarterNestedMultiplier k d t < 0 ↔
      monotoneQuarterNestedCrossingLevel d <
        monotoneQuarterStep (k + 1) t := by
  simpa only [not_le] using not_congr
    (monotoneQuarterNestedMultiplier_nonnegative_iff_step_le_crossingLevel
      k hd t)

/-- For `d < -1` the transition really occurs inside the later quarter-step
interval.  Monotonicity gives a single sign crossing even though uniqueness
of the zero is not needed. -/
theorem exists_monotoneQuarterNestedMultiplier_zero
    (k : ℤ) {d : ℝ} (hd : d < -1) :
    ∃ t ∈ Set.Icc (quarterLogLatticePoint (k + 1))
        (quarterLogLatticePoint (k + 2)),
      monotoneQuarterNestedMultiplier k d t = 0 := by
  let q₁ := quarterLogLatticePoint (k + 1)
  let q₂ := quarterLogLatticePoint (k + 2)
  let s := monotoneQuarterStep (k + 1)
  have hq : q₁ ≤ q₂ := quarterLogLatticePoint_mono (by omega)
  have hsCont : ContinuousOn s (Set.Icc q₁ q₂) :=
    (monotoneQuarterStep_contDiff (k + 1)).continuous.continuousOn
  have hsLeft : s q₁ = 0 :=
    monotoneQuarterStep_eq_zero_of_le (k + 1) le_rfl
  have hsRight : s q₂ = 1 := by
    apply monotoneQuarterStep_eq_one_of_le (k + 1)
    dsimp only [q₂]
    rw [show k + 1 + 1 = k + 2 by ring]
  have hlevel := monotoneQuarterNestedCrossingLevel_mem_Ioo hd
  have hmem : monotoneQuarterNestedCrossingLevel d ∈ Set.Icc (s q₁) (s q₂) := by
    rw [hsLeft, hsRight]
    exact ⟨hlevel.1.le, hlevel.2.le⟩
  obtain ⟨t, ht, hst⟩ := (intermediate_value_Icc hq hsCont) hmem
  refine ⟨t, ht, ?_⟩
  have htShared : quarterLogLatticePoint (k + 1) ≤ t := ht.1
  unfold monotoneQuarterNestedMultiplier
  rw [monotoneQuarterStep_eq_one_of_le k htShared]
  change 1 + d * s t = 0
  rw [hst]
  unfold monotoneQuarterNestedCrossingLevel
  field_simp [show d ≠ 0 by linarith]
  ring

/-- Sharp ordered-pair classification below the threshold: a product is
negative exactly for a positive-to-negative crossing.  The reverse sign
pattern is forbidden by the one-crossing order. -/
theorem monotoneQuarterNestedMultiplier_mul_neg_iff
    (k : ℤ) {d y z : ℝ} (hd : d < -1) (hyz : y ≤ z) :
    monotoneQuarterNestedMultiplier k d y *
        monotoneQuarterNestedMultiplier k d z < 0 ↔
      0 < monotoneQuarterNestedMultiplier k d y ∧
        monotoneQuarterNestedMultiplier k d z < 0 := by
  constructor
  · intro hmul
    rcases (mul_neg_iff.mp hmul) with hforward | hreverse
    · exact hforward
    · have hzneg := monotoneQuarterNestedMultiplier_neg_forward
        k hd hyz hreverse.1
      exact ((not_lt_of_ge hzneg.le) hreverse.2).elim
  · rintro ⟨hy, hz⟩
    exact mul_neg_of_pos_of_neg hy hz

/-- The unfavorable ordered correlations can be read directly from the later
step: the first multiplier is positive and the second point has passed the
crossing level. -/
theorem monotoneQuarterNestedMultiplier_mul_neg_iff_crossingLevel
    (k : ℤ) {d y z : ℝ} (hd : d < -1) (hyz : y ≤ z) :
    monotoneQuarterNestedMultiplier k d y *
        monotoneQuarterNestedMultiplier k d z < 0 ↔
      0 < monotoneQuarterNestedMultiplier k d y ∧
        monotoneQuarterNestedCrossingLevel d <
          monotoneQuarterStep (k + 1) z := by
  rw [monotoneQuarterNestedMultiplier_mul_neg_iff k hd hyz,
    monotoneQuarterNestedMultiplier_neg_iff_crossingLevel_lt_step
      k (hd.trans (by norm_num)) z]

/-- Complementary favorable classification: an ordered product is
nonnegative exactly when the first point is already nonpositive, or the
second point has not yet passed the crossing level. -/
theorem monotoneQuarterNestedMultiplier_mul_nonnegative_iff_crossingLevel
    (k : ℤ) {d y z : ℝ} (hd : d < -1) (hyz : y ≤ z) :
    0 ≤ monotoneQuarterNestedMultiplier k d y *
        monotoneQuarterNestedMultiplier k d z ↔
      monotoneQuarterNestedMultiplier k d y ≤ 0 ∨
        monotoneQuarterStep (k + 1) z ≤
          monotoneQuarterNestedCrossingLevel d := by
  have h := not_congr
    (monotoneQuarterNestedMultiplier_mul_neg_iff_crossingLevel k hd hyz)
  simpa only [not_lt, not_and_or] using h

/-- Exact global classification: all ordered products are nonnegative if and
only if `d ≥ -1`.  For `d < -1`, the two lattice endpoints give the sharp
negative product `1+d`. -/
theorem monotoneQuarterNestedMultiplier_all_ordered_products_nonnegative_iff
    (k : ℤ) (d : ℝ) :
    (∀ ⦃y z : ℝ⦄, y ≤ z →
      0 ≤ monotoneQuarterNestedMultiplier k d y *
        monotoneQuarterNestedMultiplier k d z) ↔
      -1 ≤ d := by
  constructor
  · intro hall
    by_contra hd
    have hd' : d < -1 := lt_of_not_ge hd
    have hpair := hall
      (quarterLogLatticePoint_mono (show k + 1 ≤ k + 2 by omega))
    rw [monotoneQuarterNestedMultiplier_shared,
      monotoneQuarterNestedMultiplier_upper, one_mul] at hpair
    linarith
  · intro hd y z _hyz
    exact mul_nonneg
      (monotoneQuarterNestedMultiplier_nonnegative_of_neg_one_le k hd y)
      (monotoneQuarterNestedMultiplier_nonnegative_of_neg_one_le k hd z)

/-- In head-plus-suffix coordinates the exact favorable real-phase range is
`a ≥ 0`; every negative real suffix coefficient has an explicit unfavorable
ordered correlation across the later transition. -/
theorem monotoneQuarterHeadSuffixMultiplier_all_ordered_products_nonnegative_iff
    (k : ℤ) (a : ℝ) :
    (∀ ⦃y z : ℝ⦄, y ≤ z →
      0 ≤ monotoneQuarterHeadSuffixMultiplier k a y *
        monotoneQuarterHeadSuffixMultiplier k a z) ↔
      0 ≤ a := by
  simp_rw [monotoneQuarterHeadSuffixMultiplier_eq_nested]
  rw [monotoneQuarterNestedMultiplier_all_ordered_products_nonnegative_iff]
  constructor <;> intro h <;> linarith

/-- In head--suffix coordinates, a negative real phase crosses when the later
step exceeds `1 / (1-a)`. -/
theorem monotoneQuarterHeadSuffixMultiplier_mul_neg_iff_crossingLevel
    (k : ℤ) {a y z : ℝ} (ha : a < 0) (hyz : y ≤ z) :
    monotoneQuarterHeadSuffixMultiplier k a y *
        monotoneQuarterHeadSuffixMultiplier k a z < 0 ↔
      0 < monotoneQuarterHeadSuffixMultiplier k a y ∧
        (1 - a)⁻¹ < monotoneQuarterStep (k + 1) z := by
  have hd : a - 1 < -1 := by linarith
  have hlevel : monotoneQuarterNestedCrossingLevel (a - 1) = (1 - a)⁻¹ := by
    unfold monotoneQuarterNestedCrossingLevel
    field_simp [show a - 1 ≠ 0 by linarith, show 1 - a ≠ 0 by linarith]
    ring
  rw [monotoneQuarterHeadSuffixMultiplier_eq_nested,
    monotoneQuarterHeadSuffixMultiplier_eq_nested,
    monotoneQuarterNestedMultiplier_mul_neg_iff_crossingLevel k hd hyz,
    hlevel]

/-- For a negative head--suffix phase, the shared and upper lattice points
have product exactly `a`, exhibiting the unfavorable prime-correlation sign. -/
theorem monotoneQuarterHeadSuffixMultiplier_endpoint_product
    (k : ℤ) (a : ℝ) :
    monotoneQuarterHeadSuffixMultiplier k a
        (quarterLogLatticePoint (k + 1)) *
      monotoneQuarterHeadSuffixMultiplier k a
        (quarterLogLatticePoint (k + 2)) = a := by
  rw [monotoneQuarterHeadSuffixMultiplier_eq_nested,
    monotoneQuarterHeadSuffixMultiplier_eq_nested,
    monotoneQuarterNestedMultiplier_shared,
    monotoneQuarterNestedMultiplier_upper]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterSingleCrossingStructural
