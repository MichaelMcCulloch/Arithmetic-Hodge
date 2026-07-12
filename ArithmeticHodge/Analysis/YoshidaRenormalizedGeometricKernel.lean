import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

noncomputable section

/-!
# Renormalized odd geometric kernels

This module proves an abstract summation identity for the unshifted series
`A k - C0 / (k + 1)`, where `A k` is an exponentially weighted correlation
integral.  The local-critical digamma series uses the shifted presentation
`A 0 + ∑ k, (A (k + 1) - C0 / (k + 1))`.  Identifying those two limits still
requires a separate telescoping/reindexing theorem.  Likewise, callers must
separately fold the whole-line cross-correlation integral and assemble the
polar and `log π` terms.
-/

def oddRate (k : ℕ) : ℝ := 2 * k + 1 / 2

def referenceRate (k : ℕ) : ℝ := 2 * (k + 1)

def oddKernel (u : ℝ) : ℝ :=
  2 * Real.exp (u / 2) / (Real.exp u - Real.exp (-u))

def oddKernelSeriesForm (u : ℝ) : ℝ :=
  2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

def referenceKernel (u : ℝ) : ℝ :=
  2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u))

def renormalizedTerm (L C0 : ℝ) (C : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 * (∫ u in 0..L, Real.exp (-oddRate k * u) * C u) -
    C0 / (k + 1)

def pairedIntegrand (C0 : ℝ) (C : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  2 * (Real.exp (-oddRate k * u) * C u -
    Real.exp (-referenceRate k * u) * C0)

def tailTerm (L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-referenceRate k * L) / (k + 1)

theorem oddRate_pos (k : ℕ) : 0 < oddRate k := by
  unfold oddRate
  positivity

theorem referenceRate_pos (k : ℕ) : 0 < referenceRate k := by
  unfold referenceRate
  positivity

theorem integral_two_exp_neg_mul {b L : ℝ} (hb : b ≠ 0) :
    (∫ u in 0..L, 2 * Real.exp (-b * u)) =
      2 * (1 - Real.exp (-b * L)) / b := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun x : ℝ ↦ -(2 / b) * Real.exp (-b * x))
        (2 * Real.exp (-b * u)) u := by
    intro u _
    convert (((Real.hasDerivAt_exp (-b * u)).comp u
      (((hasDerivAt_id u).const_mul (-b)))).const_mul (-(2 / b))) using 1
    field_simp [hb]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  calc
    (∫ u in 0..L, 2 * Real.exp (-b * u)) =
        -(2 / b) * Real.exp (-b * L) -
          -(2 / b) * Real.exp (-b * 0) := h
    _ = 2 * (1 - Real.exp (-b * L)) / b := by
      simp only [mul_zero, Real.exp_zero]
      field_simp [hb]
      ring

theorem referenceCounterterm_split (L : ℝ) (k : ℕ) :
    (∫ u in 0..L, 2 * Real.exp (-referenceRate k * u)) +
        Real.exp (-referenceRate k * L) / (k + 1) =
      1 / (k + 1 : ℝ) := by
  rw [integral_two_exp_neg_mul (referenceRate_pos k).ne']
  unfold referenceRate
  field_simp
  ring

theorem renormalizedTerm_eq_paired
    {L C0 : ℝ} {C : ℝ → ℝ} (hC : Continuous C) (k : ℕ) :
    renormalizedTerm L C0 C k =
      (∫ u in 0..L, pairedIntegrand C0 C k u) - C0 * tailTerm L k := by
  have hOdd : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-oddRate k * u) * C u) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hRef : IntervalIntegrable
      (fun u : ℝ ↦ 2 * Real.exp (-referenceRate k * u)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  rw [renormalizedTerm]
  rw [div_eq_mul_inv]
  rw [show ((k + 1 : ℝ))⁻¹ =
      (∫ u in 0..L, 2 * Real.exp (-referenceRate k * u)) +
        tailTerm L k by
      simpa only [tailTerm, one_div] using
        (referenceCounterterm_split L k).symm]
  rw [mul_add, sub_add_eq_sub_sub]
  calc
    2 * (∫ u in 0..L, Real.exp (-oddRate k * u) * C u) -
          C0 * (∫ u in 0..L, 2 * Real.exp (-referenceRate k * u)) -
          C0 * tailTerm L k =
        (∫ u in 0..L,
          2 * (Real.exp (-oddRate k * u) * C u) -
            C0 * (2 * Real.exp (-referenceRate k * u))) -
          C0 * tailTerm L k := by
      rw [intervalIntegral.integral_sub
        (hOdd.const_mul 2) (hRef.const_mul C0)]
      simp only [intervalIntegral.integral_const_mul]
    _ = (∫ u in 0..L, pairedIntegrand C0 C k u) -
          C0 * tailTerm L k := by
      congr 2
      funext u
      rw [pairedIntegrand]
      ring

theorem pairedIntegrand_intervalIntegrable
    {L C0 : ℝ} {C : ℝ → ℝ} (hC : Continuous C) (k : ℕ) :
    IntervalIntegrable (pairedIntegrand C0 C k) volume 0 L := by
  apply Continuous.intervalIntegrable
  unfold pairedIntegrand
  fun_prop

/-- Exact finite-N identity with the harmonic counterterm represented by a
matched exponential on `[0,L]` and an explicit geometric tail. -/
theorem finite_renormalized_sum_identity
    {L C0 : ℝ} {C : ℝ → ℝ} (hC : Continuous C) (N : ℕ) :
    (∑ k ∈ Finset.range N, renormalizedTerm L C0 C k) =
      (∫ u in 0..L,
        ∑ k ∈ Finset.range N, pairedIntegrand C0 C k u) -
      C0 * ∑ k ∈ Finset.range N, tailTerm L k := by
  simp_rw [renormalizedTerm_eq_paired hC]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  intro k hk
  exact pairedIntegrand_intervalIntegrable hC k

theorem oddKernelSeriesForm_eq_oddKernel {u : ℝ} (hu : u ≠ 0) :
    oddKernelSeriesForm u = oddKernel u := by
  have hdenSeries : 1 - Real.exp (-2 * u) ≠ 0 := by
    intro h
    have hexp : Real.exp (-2 * u) = Real.exp 0 := by
      simpa only [Real.exp_zero] using (sub_eq_zero.mp h).symm
    have : -2 * u = 0 := Real.exp_injective hexp
    exact hu (by linarith)
  have hdenOdd : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    have : u = -u := Real.exp_injective heq
    exact hu (by linarith)
  have hmul : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdenrel : Real.exp u - Real.exp (-u) =
      Real.exp u * (1 - Real.exp (-2 * u)) := by
    rw [mul_sub, mul_one, hmul]
  rw [oddKernelSeriesForm, oddKernel, hdenrel]
  field_simp [hdenSeries, Real.exp_ne_zero]
  rw [show Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) by
    simpa only [neg_div] using hhalf]

theorem hasSum_oddExponentials {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ ↦ 2 * Real.exp (-oddRate k * u))
      (oddKernelSeriesForm u) := by
  let r : ℝ := Real.exp (-2 * u)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (2 * Real.exp (-u / 2))
  have hterm : (fun k : ℕ ↦ 2 * Real.exp (-oddRate k * u)) =
      fun k : ℕ ↦ (2 * Real.exp (-u / 2)) * r ^ k := by
    funext k
    rw [oddRate]
    rw [show -(2 * (k : ℝ) + 1 / 2) * u =
        -u / 2 + (k : ℝ) * (-2 * u) by ring]
    rw [Real.exp_add, Real.exp_nat_mul]
    dsimp [r]
    ring
  rw [hterm]
  simpa only [oddKernelSeriesForm, r, div_eq_mul_inv] using hgeom

theorem hasSum_referenceExponentials {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ ↦ 2 * Real.exp (-referenceRate k * u))
      (referenceKernel u) := by
  let r : ℝ := Real.exp (-2 * u)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * r)
  have hterm : (fun k : ℕ ↦ 2 * Real.exp (-referenceRate k * u)) =
      fun k : ℕ ↦ (2 * r) * r ^ k := by
    funext k
    rw [referenceRate]
    rw [show -(2 * ((k : ℝ) + 1)) * u =
        ((k : ℝ) + 1) * (-2 * u) by ring]
    rw [show ((k : ℝ) + 1) * (-2 * u) =
        ((k + 1 : ℕ) : ℝ) * (-2 * u) by push_cast; rfl]
    rw [Real.exp_nat_mul]
    dsimp [r]
    rw [pow_succ']
    ring
  rw [hterm]
  simpa only [referenceKernel, r, div_eq_mul_inv] using hgeom

theorem hasSum_pairedIntegrand
    {C0 u : ℝ} (C : ℝ → ℝ) (hu : 0 < u) :
    HasSum (fun k : ℕ ↦ pairedIntegrand C0 C k u)
      (oddKernel u * C u - referenceKernel u * C0) := by
  have hOdd := (hasSum_oddExponentials hu).mul_right (C u)
  have hRef := (hasSum_referenceExponentials hu).mul_right C0
  have h := hOdd.sub hRef
  rw [oddKernelSeriesForm_eq_oddKernel hu.ne'] at h
  have hterm : (fun k : ℕ ↦ pairedIntegrand C0 C k u) =
      fun k : ℕ ↦
        2 * Real.exp (-oddRate k * u) * C u -
          2 * Real.exp (-referenceRate k * u) * C0 := by
    funext k
    rw [pairedIntegrand]
    ring
  rw [hterm]
  exact h

theorem tailTerm_hasSum {L : ℝ} (hL : 0 < L) :
    HasSum (tailTerm L) (-Real.log (1 - Real.exp (-2 * L))) := by
  let r : ℝ := Real.exp (-2 * L)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have habs : |r| < 1 := by simpa [abs_of_pos hr0] using hr1
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hterm : tailTerm L = fun k : ℕ ↦ r ^ (k + 1) / (k + 1) := by
    funext k
    rw [tailTerm, referenceRate]
    rw [show -(2 * ((k : ℝ) + 1)) * L =
        ((k : ℝ) + 1) * (-2 * L) by ring]
    rw [show ((k : ℝ) + 1) * (-2 * L) =
        ((k + 1 : ℕ) : ℝ) * (-2 * L) by push_cast; rfl]
    rw [Real.exp_nat_mul]
  rw [hterm]
  simpa only [r] using h

/-- The only convergence input still needed after pairing each harmonic
counterterm with a reference exponential. -/
def PairedIntegralInterchange (L C0 : ℝ) (C : ℝ → ℝ) : Prop :=
  HasSum
    (fun k : ℕ ↦ ∫ u in 0..L, pairedIntegrand C0 C k u)
    (∫ u in 0..L, oddKernel u * C u - referenceKernel u * C0)

/-- A direct dominated-convergence discharge rule for the remaining
interchange.  The pointwise limit is already proved above; callers only need
to supply a summable majorant whose pointwise sum is interval-integrable. -/
theorem pairedIntegralInterchange_of_dominated
    {L C0 : ℝ} {C : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (bound : ℕ → ℝ → ℝ)
    (hbound : ∀ k : ℕ, ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.uIoc 0 L → ‖pairedIntegrand C0 C k u‖ ≤ bound k u)
    (hboundSummable : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.uIoc 0 L → Summable (fun k : ℕ ↦ bound k u))
    (hboundIntegrable : IntervalIntegrable
      (fun u : ℝ ↦ ∑' k : ℕ, bound k u) volume 0 L) :
    PairedIntegralInterchange L C0 C := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence bound
  · intro k
    exact (show Continuous (pairedIntegrand C0 C k) by
      unfold pairedIntegrand
      fun_prop).aestronglyMeasurable
  · simpa only [Set.uIoc_of_le hL.le] using hbound
  · simpa only [Set.uIoc_of_le hL.le] using hboundSummable
  · exact hboundIntegrable
  · filter_upwards [] with u hu
    rw [Set.uIoc_of_le hL.le] at hu
    exact hasSum_pairedIntegrand C hu.1

def removableMajorant (C0 : ℝ) (D : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (2 * Real.exp (-oddRate k * u)) * (u * |D u|) +
    |C0| * (2 * Real.exp (-oddRate k * u) -
      2 * Real.exp (-referenceRate k * u))

def removableMajorantLimit (C0 : ℝ) (D : ℝ → ℝ) (u : ℝ) : ℝ :=
  oddKernel u * (u * |D u|) +
    |C0| * (oddKernel u - referenceKernel u)

theorem oddRate_lt_referenceRate (k : ℕ) :
    oddRate k < referenceRate k := by
  unfold oddRate referenceRate
  linarith

theorem pairedIntegrand_norm_le_removableMajorant
    {C0 u : ℝ} {C D : ℝ → ℝ} (hu : 0 ≤ u)
    (hrem : C u = C0 + u * D u) (k : ℕ) :
    ‖pairedIntegrand C0 C k u‖ ≤ removableMajorant C0 D k u := by
  have harg : -referenceRate k * u ≤ -oddRate k * u := by
    have hr := oddRate_lt_referenceRate k
    nlinarith
  have hexp : Real.exp (-referenceRate k * u) ≤
      Real.exp (-oddRate k * u) := Real.exp_le_exp.mpr harg
  have hodd0 : 0 ≤ 2 * Real.exp (-oddRate k * u) := by positivity
  have hdiff0 : 0 ≤
      2 * Real.exp (-oddRate k * u) -
        2 * Real.exp (-referenceRate k * u) := by linarith
  have halg : pairedIntegrand C0 C k u =
      (2 * Real.exp (-oddRate k * u)) * (u * D u) +
        (2 * Real.exp (-oddRate k * u) -
          2 * Real.exp (-referenceRate k * u)) * C0 := by
    rw [pairedIntegrand, hrem]
    ring
  rw [halg, Real.norm_eq_abs]
  calc
    |(2 * Real.exp (-oddRate k * u)) * (u * D u) +
        (2 * Real.exp (-oddRate k * u) -
          2 * Real.exp (-referenceRate k * u)) * C0| ≤
      |(2 * Real.exp (-oddRate k * u)) * (u * D u)| +
        |(2 * Real.exp (-oddRate k * u) -
          2 * Real.exp (-referenceRate k * u)) * C0| := abs_add_le _ _
    _ = removableMajorant C0 D k u := by
      rw [removableMajorant]
      simp only [abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos (Real.exp_pos _), abs_of_nonneg hu,
        abs_of_nonneg hdiff0]
      ring

theorem removableMajorant_hasSum
    (C0 : ℝ) (D : ℝ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    HasSum (fun k : ℕ ↦ removableMajorant C0 D k u)
      (removableMajorantLimit C0 D u) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [removableMajorant, removableMajorantLimit, oddKernel,
      referenceKernel]
  · have hOdd := hasSum_oddExponentials hu
    have hRef := hasSum_referenceExponentials hu
    have h := (hOdd.mul_right (u * |D u|)).add
      ((hOdd.sub hRef).mul_right |C0|)
    rw [oddKernelSeriesForm_eq_oddKernel hu.ne'] at h
    have hterm : (fun k : ℕ ↦ removableMajorant C0 D k u) =
        fun k : ℕ ↦
          2 * Real.exp (-oddRate k * u) * (u * |D u|) +
            (2 * Real.exp (-oddRate k * u) -
              2 * Real.exp (-referenceRate k * u)) * |C0| := by
      funext k
      rw [removableMajorant]
      ring
    rw [hterm]
    simpa only [removableMajorantLimit, mul_comm] using h

theorem tsum_removableMajorant_eq
    (C0 : ℝ) (D : ℝ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ∑' k : ℕ, removableMajorant C0 D k u =
      removableMajorantLimit C0 D u :=
  (removableMajorant_hasSum C0 D hu).tsum_eq

/-- Concrete discharge rule for a removable numerator
`C(u) = C0 + u D(u)`.  Only integrability of the displayed summed majorant
remains for a particular correlation. -/
theorem pairedIntegralInterchange_of_removable
    {L C0 : ℝ} {C D : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (hrem : ∀ u ∈ Set.Icc 0 L, C u = C0 + u * D u)
    (hmajorant : IntervalIntegrable (removableMajorantLimit C0 D) volume 0 L) :
    PairedIntegralInterchange L C0 C := by
  apply pairedIntegralInterchange_of_dominated hL hC (removableMajorant C0 D)
  · intro k
    filter_upwards [] with u hu
    rw [Set.uIoc_of_le hL.le] at hu
    exact pairedIntegrand_norm_le_removableMajorant hu.1.le
      (hrem u ⟨hu.1.le, hu.2⟩) k
  · filter_upwards [] with u hu
    rw [Set.uIoc_of_le hL.le] at hu
    exact (removableMajorant_hasSum C0 D hu.1.le).summable
  · apply hmajorant.congr
    intro u hu
    rw [Set.uIoc_of_le hL.le] at hu
    exact (tsum_removableMajorant_eq C0 D hu.1.le).symm

/-- Once the paired exponential series may be integrated termwise, the
renormalized series has an exact limit.  Notice that no Euler constant is
created here; it is the separate constant term in the digamma expansion. -/
theorem renormalizedSeries_hasSum_of_pairedIntegralInterchange
    {L C0 : ℝ} {C : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (hinterchange : PairedIntegralInterchange L C0 C) :
    HasSum (renormalizedTerm L C0 C)
      ((∫ u in 0..L, oddKernel u * C u - referenceKernel u * C0) +
        C0 * Real.log (1 - Real.exp (-2 * L))) := by
  have htail := (tailTerm_hasSum hL).mul_left C0
  have h := hinterchange.sub htail
  have hterm : renormalizedTerm L C0 C =
      fun k : ℕ ↦
        (∫ u in 0..L, pairedIntegrand C0 C k u) - C0 * tailTerm L k := by
    funext k
    exact renormalizedTerm_eq_paired hC k
  rw [hterm]
  convert h using 1
  ring

def referenceRegularized (u : ℝ) : ℝ :=
  1 / u - referenceKernel u

def referencePrimitive (u : ℝ) : ℝ :=
  Real.log u - Real.log (1 - Real.exp (-2 * u))

theorem hasDerivAt_log_one_sub_exp_neg_two {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ ↦ Real.log (1 - Real.exp (-2 * x)))
      (referenceKernel u) u := by
  have hlin : HasDerivAt (fun x : ℝ ↦ -2 * x) (-2) u :=
    by simpa using (hasDerivAt_id u).const_mul (-2)
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-2 * x))
      (-2 * Real.exp (-2 * u)) u := by
    (convert (Real.hasDerivAt_exp (-2 * u)).comp u hlin using 1; ring)
  have hinner : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-2 * x))
      (2 * Real.exp (-2 * u)) u := by
    (convert (hasDerivAt_const u (1 : ℝ)).sub hexp using 1; ring)
  have hdenpos : 0 < 1 - Real.exp (-2 * u) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hlog := (Real.hasDerivAt_log hdenpos.ne').comp u hinner
  convert hlog using 1
  rw [referenceKernel]
  field_simp [hdenpos.ne']

theorem referencePrimitive_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt referencePrimitive (referenceRegularized u) u := by
  have h := (Real.hasDerivAt_log hu.ne').sub
    (hasDerivAt_log_one_sub_exp_neg_two hu)
  simpa only [referencePrimitive, referenceRegularized, one_div] using h

theorem referenceRegularized_continuousOn
    {ε L : ℝ} (hε : 0 < ε) (hεL : ε ≤ L) :
    ContinuousOn referenceRegularized (Set.uIcc ε L) := by
  rw [Set.uIcc_of_le hεL]
  intro u hu
  have hu0 : u ≠ 0 := (hε.trans_le hu.1).ne'
  have hden : 1 - Real.exp (-2 * u) ≠ 0 := by
    have hupos : 0 < u := hε.trans_le hu.1
    have hpos : 0 < 1 - Real.exp (-2 * u) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    exact hpos.ne'
  have hOneDiv : ContinuousAt (fun x : ℝ ↦ 1 / x) u :=
    continuousAt_const.div continuousAt_id hu0
  have hNum : ContinuousAt (fun x : ℝ ↦ 2 * Real.exp (-2 * x)) u := by
    fun_prop
  have hDen : ContinuousAt (fun x : ℝ ↦ 1 - Real.exp (-2 * x)) u := by
    fun_prop
  have hRef : ContinuousAt
      (fun x : ℝ ↦ 2 * Real.exp (-2 * x) / (1 - Real.exp (-2 * x))) u :=
    hNum.div hDen hden
  exact (hOneDiv.sub hRef).continuousWithinAt

/-- Exact cutoff identity for the reference subtraction. -/
theorem integral_referenceRegularized
    {ε L : ℝ} (hε : 0 < ε) (hεL : ε ≤ L) :
    (∫ u in ε..L, referenceRegularized u) =
      referencePrimitive L - referencePrimitive ε := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [Set.uIcc_of_le hεL] at hu
    exact referencePrimitive_hasDerivAt (hε.trans_le hu.1)
  · exact (referenceRegularized_continuousOn hε hεL).intervalIntegrable

theorem reference_cutoff_balance
    {ε L : ℝ} (hε : 0 < ε) (hεL : ε ≤ L) :
    (∫ u in ε..L, referenceRegularized u) +
        Real.log (1 - Real.exp (-2 * L)) =
      Real.log L - Real.log ε + Real.log (1 - Real.exp (-2 * ε)) := by
  rw [integral_referenceRegularized hε hεL]
  unfold referencePrimitive
  ring

theorem tendsto_one_sub_exp_neg_two_div :
    Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-2 * ε)) / ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
  have hlin : HasDerivAt (fun x : ℝ ↦ -2 * x) (-2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-2)
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-2 * x)) (-2) 0 := by
    (convert (Real.hasDerivAt_exp (-2 * 0)).comp 0 hlin using 1; norm_num)
  have hderiv : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-2 * x)) 2 0 := by
    (convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hexp using 1; norm_num)
  have h := hderiv.tendsto_slope_zero_right
  simpa only [slope, zero_add, mul_zero, neg_zero, sub_zero, Real.exp_zero,
    sub_self, smul_eq_mul, inv_mul_eq_div] using h

theorem tendsto_log_reference_ratio :
    Tendsto
      (fun ε : ℝ ↦ Real.log (1 - Real.exp (-2 * ε)) - Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 2)) := by
  have hratio := tendsto_one_sub_exp_neg_two_div
  have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hratio
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hnum : 1 - Real.exp (-2 * ε) ≠ 0 := by
    have hpos : 0 < 1 - Real.exp (-2 * ε) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    exact hpos.ne'
  simp only [Function.comp_apply]
  rw [Real.log_div hnum hε.ne']

theorem tendsto_reference_cutoff_expression (L : ℝ) :
    Tendsto
      (fun ε : ℝ ↦
        Real.log L +
          (Real.log (1 - Real.exp (-2 * ε)) - Real.log ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log L + Real.log 2)) := by
  exact tendsto_const_nhds.add tendsto_log_reference_ratio

/-- Under the natural local integrability hypothesis, the reference
subtraction contributes exactly `log L + log 2`. -/
theorem integral_referenceRegularized_add_log_tail
    {L : ℝ} (hL : 0 < L)
    (hint : IntervalIntegrable referenceRegularized volume 0 L) :
    (∫ u in 0..L, referenceRegularized u) +
        Real.log (1 - Real.exp (-2 * L)) =
      Real.log L + Real.log 2 := by
  have hbase := intervalIntegral.continuousOn_primitive_interval'
    (f := referenceRegularized) (a := L) hint right_mem_uIcc
  have hleft : ContinuousOn
      (fun ε : ℝ ↦ ∫ u in ε..L, referenceRegularized u)
      (Set.uIcc 0 L) := by
    refine hbase.neg.congr ?_
    intro ε _
    exact (intervalIntegral.integral_symm
      (f := referenceRegularized) (μ := volume) L ε)
  rw [Set.uIcc_of_le hL.le] at hleft
  have hwithin := hleft.continuousWithinAt
    (show (0 : ℝ) ∈ Set.Icc 0 L by exact ⟨le_rfl, hL.le⟩)
  have hIoo := hwithin.mono_left
    (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsGT hL] at hIoo
  have hconst : Tendsto
      (fun _ : ℝ ↦ Real.log (1 - Real.exp (-2 * L)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log (1 - Real.exp (-2 * L)))) := tendsto_const_nhds
  have hlimitLeft := hIoo.add hconst
  have hagree :
      (fun ε : ℝ ↦ Real.log L +
          (Real.log (1 - Real.exp (-2 * ε)) - Real.log ε)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ ↦
        (∫ u in ε..L, referenceRegularized u) +
          Real.log (1 - Real.exp (-2 * L))) := by
    filter_upwards [Ioo_mem_nhdsGT hL] with ε hε
    rw [reference_cutoff_balance hε.1 hε.2.le]
    ring
  have hlimitRight := (tendsto_reference_cutoff_expression L).congr' hagree
  exact tendsto_nhds_unique hlimitLeft hlimitRight

def stableGeometricIntegrand (C0 : ℝ) (C : ℝ → ℝ) (u : ℝ) : ℝ :=
  oddKernel u * C u - C0 / u

theorem pairedLimit_eq_stable_add_reference (C0 : ℝ) (C : ℝ → ℝ) :
    (fun u : ℝ ↦ oddKernel u * C u - referenceKernel u * C0) =
      fun u : ℝ ↦ stableGeometricIntegrand C0 C u +
        C0 * referenceRegularized u := by
  funext u
  unfold stableGeometricIntegrand referenceRegularized
  ring

/-- Main conditional renormalized geometric-kernel identity.  The remaining
input `PairedIntegralInterchange` is exactly the dominated-convergence step. -/
theorem renormalizedSeries_hasSum_stable
    {L C0 : ℝ} {C : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (hinterchange : PairedIntegralInterchange L C0 C)
    (hstable : IntervalIntegrable (stableGeometricIntegrand C0 C) volume 0 L)
    (href : IntervalIntegrable referenceRegularized volume 0 L) :
    HasSum (renormalizedTerm L C0 C)
      ((∫ u in 0..L, stableGeometricIntegrand C0 C u) +
        (Real.log L + Real.log 2) * C0) := by
  have hsum := renormalizedSeries_hasSum_of_pairedIntegralInterchange
    hL hC hinterchange
  have hIntegral :
      (∫ u in 0..L, oddKernel u * C u - referenceKernel u * C0) =
        (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
          C0 * (∫ u in 0..L, referenceRegularized u) := by
    rw [pairedLimit_eq_stable_add_reference]
    rw [intervalIntegral.integral_add hstable (href.const_mul C0),
      intervalIntegral.integral_const_mul]
  have hrefValue := integral_referenceRegularized_add_log_tail hL href
  have hlimit :
      (∫ u in 0..L, oddKernel u * C u - referenceKernel u * C0) +
          C0 * Real.log (1 - Real.exp (-2 * L)) =
        (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
          (Real.log L + Real.log 2) * C0 := by
    rw [hIntegral]
    calc
      (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
            C0 * (∫ u in 0..L, referenceRegularized u) +
            C0 * Real.log (1 - Real.exp (-2 * L)) =
          (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
            C0 * ((∫ u in 0..L, referenceRegularized u) +
              Real.log (1 - Real.exp (-2 * L))) := by ring
      _ = (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
            C0 * (Real.log L + Real.log 2) := by rw [hrefValue]
      _ = (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
            (Real.log L + Real.log 2) * C0 := by ring
  rw [hlimit] at hsum
  exact hsum

/-- Restoring the separate Euler constant in the digamma expansion gives
the exact `log L + gamma + log 2` coefficient. -/
theorem gamma_add_tsum_renormalized_eq_stable
    {L C0 : ℝ} {C : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (hinterchange : PairedIntegralInterchange L C0 C)
    (hstable : IntervalIntegrable (stableGeometricIntegrand C0 C) volume 0 L)
    (href : IntervalIntegrable referenceRegularized volume 0 L) :
    Real.eulerMascheroniConstant * C0 +
        ∑' k : ℕ, renormalizedTerm L C0 C k =
      (∫ u in 0..L, stableGeometricIntegrand C0 C u) +
        (Real.log L + Real.eulerMascheroniConstant + Real.log 2) * C0 := by
  rw [(renormalizedSeries_hasSum_stable hL hC hinterchange hstable href).tsum_eq]
  ring

/-- The sign orientation needed by the downstream Yoshida weight: the
geometric kernel is negated and the removable counterterm appears as
`+ C0 / u`.  This theorem concerns the unshifted `renormalizedTerm` series;
the production digamma series additionally needs the reindexing bridge
described in the module header. -/
theorem negated_geometric_identity
    {L C0 : ℝ} {C : ℝ → ℝ} (hL : 0 < L) (hC : Continuous C)
    (hinterchange : PairedIntegralInterchange L C0 C)
    (hstable : IntervalIntegrable (stableGeometricIntegrand C0 C) volume 0 L)
    (href : IntervalIntegrable referenceRegularized volume 0 L) :
    -Real.eulerMascheroniConstant * C0 -
        ∑' k : ℕ, renormalizedTerm L C0 C k =
      (∫ u in 0..L, -oddKernel u * C u + C0 / u) -
        (Real.log L + Real.eulerMascheroniConstant + Real.log 2) * C0 := by
  have h := gamma_add_tsum_renormalized_eq_stable
    hL hC hinterchange hstable href
  have hfun : (fun u : ℝ ↦ -oddKernel u * C u + C0 / u) =
      fun u : ℝ ↦ -stableGeometricIntegrand C0 C u := by
    funext u
    unfold stableGeometricIntegrand
    ring
  rw [hfun, intervalIntegral.integral_neg]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
