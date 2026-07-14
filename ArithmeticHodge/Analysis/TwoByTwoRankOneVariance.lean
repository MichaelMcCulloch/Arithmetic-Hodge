import ArithmeticHodge.Analysis.TwoByTwoSchur

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.TwoByTwoRankOneVariance

/-!
# Rank-one updates of real `2 x 2` Gram forms

The determinant of a two-dimensional Gram form is a variance, not an
entrywise quantity.  The identities below keep that structure exact.  They
are useful when a positive form is built from an infinite ordered family of
rank-one rows: adding one row changes the determinant and every adjugate
quadratic by explicit oriented-area squares.
-/

/-- Determinant of the symmetric form with entries `(q00,q02,q22)`. -/
def twoByTwoDet (q00 q02 q22 : ℝ) : ℝ :=
  q00 * q22 - q02 ^ 2

/-- Evaluation of the adjugate form on the vector `(h0,h2)`. -/
def twoByTwoAdjugate
    (q00 q02 q22 h0 h2 : ℝ) : ℝ :=
  q22 * h0 ^ 2 - 2 * q02 * h0 * h2 + q00 * h2 ^ 2

/-- Oriented area of the two vectors `(a,b)` and `(h0,h2)`. -/
def twoByTwoArea (a b h0 h2 : ℝ) : ℝ :=
  b * h0 - a * h2

/-- Matrix-determinant lemma for a weighted rank-one update, written without
an inverse. -/
theorem det_add_rankOne
    (q00 q02 q22 weight a b : ℝ) :
    twoByTwoDet
        (q00 + weight * a ^ 2)
        (q02 + weight * a * b)
        (q22 + weight * b ^ 2) =
      twoByTwoDet q00 q02 q22 +
        weight * twoByTwoAdjugate q00 q02 q22 a b := by
  unfold twoByTwoDet twoByTwoAdjugate
  ring

/-- A rank-one update changes an adjugate quadratic by one exact area
square. -/
theorem adjugate_add_rankOne
    (q00 q02 q22 weight a b h0 h2 : ℝ) :
    twoByTwoAdjugate
        (q00 + weight * a ^ 2)
        (q02 + weight * a * b)
        (q22 + weight * b ^ 2) h0 h2 =
      twoByTwoAdjugate q00 q02 q22 h0 h2 +
        weight * twoByTwoArea a b h0 h2 ^ 2 := by
  unfold twoByTwoAdjugate twoByTwoArea
  ring

/-- Exact determinant of the sum of two symmetric `2 x 2` forms.  The final
term is the determinant (variance) of the added form and must not be dropped
in a sharp estimate. -/
theorem det_add_symmetric
    (q00 q02 q22 g00 g02 g22 : ℝ) :
    twoByTwoDet (q00 + g00) (q02 + g02) (q22 + g22) =
      twoByTwoDet q00 q02 q22 +
        (q00 * g22 + q22 * g00 - 2 * q02 * g02) +
        twoByTwoDet g00 g02 g22 := by
  unfold twoByTwoDet
  ring

/-- Exact update of the determinant-minus-dual-norm gap.  This is the
inverse-free form in which a sharp rank-one domination proof can be iterated. -/
theorem det_sub_scaledAdjugate_add_rankOne
    (q00 q02 q22 weight a b scale h0 h2 : ℝ) :
    twoByTwoDet
        (q00 + weight * a ^ 2)
        (q02 + weight * a * b)
        (q22 + weight * b ^ 2) -
        scale * twoByTwoAdjugate
          (q00 + weight * a ^ 2)
          (q02 + weight * a * b)
          (q22 + weight * b ^ 2) h0 h2 =
      (twoByTwoDet q00 q02 q22 -
          scale * twoByTwoAdjugate q00 q02 q22 h0 h2) +
        weight *
          (twoByTwoAdjugate q00 q02 q22 a b -
            scale * twoByTwoArea a b h0 h2 ^ 2) := by
  rw [det_add_rankOne, adjugate_add_rankOne]
  ring

/-- A nonnegative row satisfying the exact adjugate comparison cannot
decrease the determinant-minus-dual-norm gap. -/
theorem det_sub_scaledAdjugate_mono_add_rankOne
    (q00 q02 q22 weight a b scale h0 h2 : ℝ)
    (hweight : 0 ≤ weight)
    (hrow : scale * twoByTwoArea a b h0 h2 ^ 2 ≤
      twoByTwoAdjugate q00 q02 q22 a b) :
    twoByTwoDet q00 q02 q22 -
        scale * twoByTwoAdjugate q00 q02 q22 h0 h2 ≤
      twoByTwoDet
          (q00 + weight * a ^ 2)
          (q02 + weight * a * b)
          (q22 + weight * b ^ 2) -
        scale * twoByTwoAdjugate
          (q00 + weight * a ^ 2)
          (q02 + weight * a * b)
          (q22 + weight * b ^ 2) h0 h2 := by
  rw [det_sub_scaledAdjugate_add_rankOne]
  exact le_add_of_nonneg_right (mul_nonneg hweight (sub_nonneg.mpr hrow))

/-! ## Finite weighted slope families -/

/-- Total weight of a finite scalar family. -/
def weightedMass {ι : Type*} (s : Finset ι) (μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, μ i

/-- First weighted slope moment. -/
def weightedFirst {ι : Type*}
    (s : Finset ι) (μ r : ι → ℝ) : ℝ :=
  ∑ i ∈ s, μ i * r i

/-- Second weighted slope moment. -/
def weightedSecond {ι : Type*}
    (s : Finset ι) (μ r : ι → ℝ) : ℝ :=
  ∑ i ∈ s, μ i * r i ^ 2

/-- The adjugate quadratic of a weighted slope Gram is the sum of squared
oriented distances from the tested direction. -/
theorem weighted_adjugate_eq_sum_area_sq {ι : Type*}
    (s : Finset ι) (μ r : ι → ℝ) (h0 h2 : ℝ) :
    twoByTwoAdjugate
        (weightedMass s μ)
        (weightedFirst s μ r)
        (weightedSecond s μ r) h0 h2 =
      ∑ i ∈ s, μ i * (r i * h0 - h2) ^ 2 := by
  unfold twoByTwoAdjugate weightedMass weightedFirst weightedSecond
  rw [show (∑ i ∈ s, μ i * (r i * h0 - h2) ^ 2) =
      ∑ i ∈ s,
        (μ i * r i ^ 2 * h0 ^ 2 -
          2 * (μ i * r i) * h0 * h2 + μ i * h2 ^ 2) by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  have htwo :
      2 * (∑ i ∈ s, μ i * r i) =
        ∑ i ∈ s, μ i * (r i * 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [htwo]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Centering a weighted family does not change its determinant.  This is
the exact finite weighted-variance identity. -/
theorem weighted_det_eq_centered_variance {ι : Type*}
    (s : Finset ι) (μ r : ι → ℝ) (center : ℝ) :
    twoByTwoDet
        (weightedMass s μ)
        (weightedFirst s μ r)
        (weightedSecond s μ r) =
      weightedMass s μ *
          (∑ i ∈ s, μ i * (r i - center) ^ 2) -
        (∑ i ∈ s, μ i * (r i - center)) ^ 2 := by
  have hfirst :
      (∑ i ∈ s, μ i * (r i - center)) =
        weightedFirst s μ r - center * weightedMass s μ := by
    unfold weightedFirst weightedMass
    calc
      (∑ i ∈ s, μ i * (r i - center)) =
          ∑ i ∈ s, (μ i * r i - μ i * center) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, μ i * r i) -
          ∑ i ∈ s, μ i * center := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [← Finset.sum_mul]
        ring
  have hsecond :
      (∑ i ∈ s, μ i * (r i - center) ^ 2) =
        weightedSecond s μ r -
          2 * center * weightedFirst s μ r +
          center ^ 2 * weightedMass s μ := by
    unfold weightedSecond weightedFirst weightedMass
    calc
      (∑ i ∈ s, μ i * (r i - center) ^ 2) =
          ∑ i ∈ s,
            (μ i * r i ^ 2 - 2 * center * (μ i * r i) +
              center ^ 2 * μ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, μ i * r i ^ 2) -
          (∑ i ∈ s, 2 * center * (μ i * r i)) +
          ∑ i ∈ s, center ^ 2 * μ i := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by
        simp_rw [← Finset.mul_sum]
  rw [hfirst, hsecond]
  unfold twoByTwoDet
  ring

/-- Adding a finite weighted slope family to an arbitrary base form keeps
the base--family cross term and the family's complete variance exactly. -/
theorem det_base_add_weighted_eq
    {ι : Type*} (s : Finset ι) (μ r : ι → ℝ)
    (q00 q02 q22 : ℝ) :
    twoByTwoDet
        (q00 + weightedMass s μ)
        (q02 + weightedFirst s μ r)
        (q22 + weightedSecond s μ r) =
      twoByTwoDet q00 q02 q22 +
        (q00 * weightedSecond s μ r +
          q22 * weightedMass s μ -
          2 * q02 * weightedFirst s μ r) +
        twoByTwoDet
          (weightedMass s μ)
          (weightedFirst s μ r)
          (weightedSecond s μ r) := by
  exact det_add_symmetric q00 q02 q22
    (weightedMass s μ) (weightedFirst s μ r)
    (weightedSecond s μ r)

/-- Centered form of the preceding identity.  Any chosen center is legal;
choosing it near the adverse rank direction exposes the useful spread of an
ordered family. -/
theorem det_base_add_weighted_eq_centered
    {ι : Type*} (s : Finset ι) (μ r : ι → ℝ)
    (q00 q02 q22 center : ℝ) :
    twoByTwoDet
        (q00 + weightedMass s μ)
        (q02 + weightedFirst s μ r)
        (q22 + weightedSecond s μ r) =
      twoByTwoDet q00 q02 q22 +
        (q00 * weightedSecond s μ r +
          q22 * weightedMass s μ -
          2 * q02 * weightedFirst s μ r) +
        weightedMass s μ *
            (∑ i ∈ s, μ i * (r i - center) ^ 2) -
          (∑ i ∈ s, μ i * (r i - center)) ^ 2 := by
  rw [det_base_add_weighted_eq,
    weighted_det_eq_centered_variance s μ r center]
  ring

/-- A finite Gram made from nonnegative weighted slopes has nonnegative
determinant.  The proof adds rows structurally; it does not inspect them. -/
theorem weighted_det_nonneg {ι : Type*}
    (s : Finset ι) (μ r : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    0 ≤ twoByTwoDet
      (weightedMass s μ)
      (weightedFirst s μ r)
      (weightedSecond s μ r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedMass, weightedFirst, weightedSecond, twoByTwoDet]
  | @insert a s ha ih =>
      have hμa : 0 ≤ μ a := hμ a (by simp)
      have hμs : ∀ i ∈ s, 0 ≤ μ i := by
        intro i hi
        exact hμ i (by simp [hi])
      have ih' := ih hμs
      have hadj : 0 ≤ twoByTwoAdjugate
          (weightedMass s μ)
          (weightedFirst s μ r)
          (weightedSecond s μ r) 1 (r a) := by
        rw [weighted_adjugate_eq_sum_area_sq]
        exact Finset.sum_nonneg fun i hi ↦
          mul_nonneg (hμs i hi) (sq_nonneg _)
      rw [weightedMass, weightedFirst, weightedSecond]
      simp only [Finset.sum_insert ha]
      rw [show
          twoByTwoDet
              (μ a + ∑ x ∈ s, μ x)
              (μ a * r a + ∑ x ∈ s, μ x * r x)
              (μ a * r a ^ 2 + ∑ x ∈ s, μ x * r x ^ 2) =
            twoByTwoDet
              ((∑ x ∈ s, μ x) + μ a * 1 ^ 2)
              ((∑ x ∈ s, μ x * r x) + μ a * 1 * r a)
              ((∑ x ∈ s, μ x * r x ^ 2) + μ a * (r a) ^ 2) by
        congr 1 <;> ring,
        det_add_rankOne]
      exact add_nonneg ih' (mul_nonneg hμa hadj)

/-! ## Summable weighted slope families -/

/-- Infinite counterpart of `weighted_adjugate_eq_sum_area_sq`.  The three
natural weighted moments are the only summability assumptions. -/
theorem tsum_adjugate_eq_tsum_area_sq {ι : Type*}
    (μ r : ι → ℝ) (h0 h2 : ℝ)
    (hs0 : Summable μ)
    (hs1 : Summable (fun i ↦ μ i * r i))
    (hs2 : Summable (fun i ↦ μ i * r i ^ 2)) :
    twoByTwoAdjugate
        (∑' i, μ i)
        (∑' i, μ i * r i)
        (∑' i, μ i * r i ^ 2) h0 h2 =
      ∑' i, μ i * (r i * h0 - h2) ^ 2 := by
  have hs2' := hs2.mul_right (h0 ^ 2)
  have hs1' := hs1.mul_right (2 * h0 * h2)
  have hs0' := hs0.mul_right (h2 ^ 2)
  have hsum := (hs2'.sub hs1').add hs0'
  rw [show (fun i ↦ μ i * (r i * h0 - h2) ^ 2) =
      fun i ↦
        (μ i * r i ^ 2) * h0 ^ 2 -
          (μ i * r i) * (2 * h0 * h2) + μ i * h2 ^ 2 by
    funext i
    ring,
    Summable.tsum_add (hs2'.sub hs1') hs0',
    Summable.tsum_sub hs2' hs1',
    hs2.tsum_mul_right, hs1.tsum_mul_right, hs0.tsum_mul_right]
  unfold twoByTwoAdjugate
  ring

/-- Infinite weighted-variance identity.  It is obtained by exact centering
of the three convergent moments, so no double-series rearrangement or cutoff
is hidden in the statement. -/
theorem tsum_det_eq_centered_variance {ι : Type*}
    (μ r : ι → ℝ) (center : ℝ)
    (hs0 : Summable μ)
    (hs1 : Summable (fun i ↦ μ i * r i))
    (hs2 : Summable (fun i ↦ μ i * r i ^ 2)) :
    twoByTwoDet
        (∑' i, μ i)
        (∑' i, μ i * r i)
        (∑' i, μ i * r i ^ 2) =
      (∑' i, μ i) *
          (∑' i, μ i * (r i - center) ^ 2) -
        (∑' i, μ i * (r i - center)) ^ 2 := by
  have hcenter1 : Summable (fun i ↦ μ i * (r i - center)) := by
    apply (hs1.sub (hs0.mul_left center)).congr
    intro i
    ring
  have hcenter2 : Summable (fun i ↦ μ i * (r i - center) ^ 2) := by
    apply ((hs2.sub (hs1.mul_left (2 * center))).add
      (hs0.mul_left (center ^ 2))).congr
    intro i
    ring
  have hfirst :
      (∑' i, μ i * (r i - center)) =
        (∑' i, μ i * r i) - center * ∑' i, μ i := by
    rw [show (fun i ↦ μ i * (r i - center)) =
        fun i ↦ μ i * r i - center * μ i by
      funext i
      ring,
      Summable.tsum_sub hs1 (hs0.mul_left center),
      hs0.tsum_mul_left]
  have hsecond :
      (∑' i, μ i * (r i - center) ^ 2) =
        (∑' i, μ i * r i ^ 2) -
          2 * center * (∑' i, μ i * r i) +
          center ^ 2 * ∑' i, μ i := by
    have hs1c := hs1.mul_left (2 * center)
    have hs0c := hs0.mul_left (center ^ 2)
    rw [show (fun i ↦ μ i * (r i - center) ^ 2) =
        fun i ↦
          (μ i * r i ^ 2 - (2 * center) * (μ i * r i)) +
            center ^ 2 * μ i by
      funext i
      ring,
      Summable.tsum_add (hs2.sub hs1c) hs0c,
      Summable.tsum_sub hs2 hs1c,
      hs1.tsum_mul_left, hs0.tsum_mul_left]
  rw [hfirst, hsecond]
  unfold twoByTwoDet
  ring

/-- Exact determinant after adding an arbitrary base form to a complete
summable weighted slope family.  The last term is the full infinite
variance, retained without mode selection. -/
theorem det_base_add_tsum_weighted_eq_centered {ι : Type*}
    (μ r : ι → ℝ) (q00 q02 q22 center : ℝ)
    (hs0 : Summable μ)
    (hs1 : Summable (fun i ↦ μ i * r i))
    (hs2 : Summable (fun i ↦ μ i * r i ^ 2)) :
    twoByTwoDet
        (q00 + ∑' i, μ i)
        (q02 + ∑' i, μ i * r i)
        (q22 + ∑' i, μ i * r i ^ 2) =
      twoByTwoDet q00 q02 q22 +
        (q00 * (∑' i, μ i * r i ^ 2) +
          q22 * (∑' i, μ i) -
          2 * q02 * (∑' i, μ i * r i)) +
        (∑' i, μ i) *
            (∑' i, μ i * (r i - center) ^ 2) -
          (∑' i, μ i * (r i - center)) ^ 2 := by
  rw [det_add_symmetric,
    tsum_det_eq_centered_variance μ r center hs0 hs1 hs2]
  ring

end ArithmeticHodge.Analysis.TwoByTwoRankOneVariance
