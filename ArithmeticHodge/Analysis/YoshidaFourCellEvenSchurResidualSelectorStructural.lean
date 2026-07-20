import ArithmeticHodge.Analysis.YoshidaFourCellEvenFiniteSevenTailAssemblyStructural
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators InnerProductSpace Interval unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenSchurResidualSelectorStructural

noncomputable section

open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreBasis
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenFiniteSevenTailAssemblyStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# The canonical degree-fourteen Schur-residual selector

The quotient selector in the even four-cell endpoint argument can be chosen
canonically: pull the exact Schur residual to `[0,1]` and take its genuine
Hilbert-space projection onto the first fourteen shifted Legendre modes.
This file constructs that selector without enumerating its coefficients.
-/

theorem memLp_fourCellEvenFiniteSevenSchurResidualRepresenter
    (w : ℝ → ℝ) (hw : Continuous w) :
    MemLp (fourCellEvenFiniteSevenSchurResidualRepresenter w hw) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let q : ℝ[X] := fourCellEvenFiniteSevenSchurResidualSelector w hw 0
  have hq := memLp_fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q
  have heq :
      fourCellEvenFiniteSevenProjectedBorderRepresenter w hw q =
        fourCellEvenFiniteSevenSchurResidualRepresenter w hw := by
    funext x
    rw [show q = fourCellEvenFiniteSevenSchurResidualSelector w hw 0 by rfl,
      fourCellEvenFiniteSevenProjectedBorderRepresenter_schurResidualSelector_eq]
    simp [ShiftedLegendreLogEnergyOrthogonalProjection.centeredPolynomialLift]
  rwa [heq] at hq

private theorem even_yoshidaEndpointPotential :
    Function.Even yoshidaEndpointPotential := by
  intro x
  unfold yoshidaEndpointPotential
  rw [neg_sq]

private theorem even_factorTwoFixedLagK_of_even
    (tau : ℝ) (p : ℝ → ℝ) (hp : Function.Even p) :
    Function.Even (factorTwoFixedLagK tau p) := by
  intro x
  unfold factorTwoFixedLagK
  rw [factorTwoFixedLagRightRepresenter_neg_of_even hp,
    factorTwoFixedLagLeftRepresenter_neg_of_even hp]
  ring

private theorem factorTwoContinuousLagRightRepresenter_neg_of_even
    (q p : ℝ → ℝ) (hp : Function.Even p) (x : ℝ) :
    factorTwoContinuousLagRightRepresenter q p (-x) =
      factorTwoContinuousLagLeftRepresenter q p x := by
  unfold factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y + x) * p y)
    (a := (-1 : ℝ)) (b := x)
  have heq : (fun y : ℝ ↦ q (-y + x) * p (-y)) =
      fun y ↦ q (x - y) * p y := by
    funext y
    rw [hp y]
    rw [show -y + x = x - y by ring]
  rw [heq] at h
  calc
    (∫ y : ℝ in -x..1, q (y - -x) * p y) =
        ∫ y : ℝ in -x..1, q (y + x) * p y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      change q (y - -x) * p y = q (y + x) * p y
      rw [show y - -x = y + x by ring]
    _ = _ := by simpa only [neg_neg] using h.symm

private theorem factorTwoContinuousLagLeftRepresenter_neg_of_even
    (q p : ℝ → ℝ) (hp : Function.Even p) (x : ℝ) :
    factorTwoContinuousLagLeftRepresenter q p (-x) =
      factorTwoContinuousLagRightRepresenter q p x := by
  unfold factorTwoContinuousLagLeftRepresenter
    factorTwoContinuousLagRightRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y - x) * p y)
    (a := (-1 : ℝ)) (b := -x)
  have heq : (fun y : ℝ ↦ q (-y - x) * p (-y)) =
      fun y ↦ q (-x - y) * p y := by
    funext y
    rw [hp y]
    congr 2
    ring
  rw [heq] at h
  simpa only [neg_neg] using h

private theorem even_factorTwoContinuousLagK_of_even
    (q p : ℝ → ℝ) (hp : Function.Even p) :
    Function.Even (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [factorTwoContinuousLagRightRepresenter_neg_of_even q p hp,
    factorTwoContinuousLagLeftRepresenter_neg_of_even q p hp]
  ring

private theorem even_fourCellEvenFiniteSevenNonsingularOperatorRepresenter
    (u : ℝ → ℝ) (hu : Function.Even u) :
    Function.Even
      (fourCellEvenFiniteSevenNonsingularOperatorRepresenter u) := by
  intro x
  unfold fourCellEvenFiniteSevenNonsingularOperatorRepresenter
  rw [even_yoshidaEndpointPotential x, hu x,
    even_factorTwoFixedLagK_of_even (8 / 5) u hu x,
    even_factorTwoContinuousLagK_of_even
      fourCellEvenFiniteSevenRegularLagWeight u hu x]

/-- On the actual even low space the complete Schur residual is itself
even.  Hence its canonical fourteen-mode selector has only seven potentially
nonzero coordinates. -/
theorem even_fourCellEvenFiniteSevenSchurResidualRepresenter
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    Function.Even (fourCellEvenFiniteSevenSchurResidualRepresenter w hw) := by
  have hlow : Function.Even
      (fourCellEvenFiniteSevenCanonicalLow w hw) := by
    simpa only [fourCellEvenFiniteSevenCanonicalLow] using
      centeredLegendreLowProjection_even w hw heven 14
  have hopLow :=
    even_fourCellEvenFiniteSevenNonsingularOperatorRepresenter
      (fourCellEvenFiniteSevenCanonicalLow w hw) hlow
  have hopSeed :=
    even_fourCellEvenFiniteSevenNonsingularOperatorRepresenter
      fourCellEvenEndpointCoshSeed fourCellEvenEndpointCoshSeed_even
  intro x
  unfold fourCellEvenFiniteSevenSchurResidualRepresenter
  rw [hopLow x, hopSeed x]

/-- The ordinary centered `L²` moment of the Schur residual in degree `n`. -/
def fourCellEvenSchurResidualMoment
    (w : ℝ → ℝ) (hw : Continuous w) (n : ℕ) : ℝ :=
  ∫ x : ℝ in -1..1,
    fourCellEvenFiniteSevenSchurResidualRepresenter w hw x *
      centeredPolynomialLift (shiftedLegendreReal n) x

private theorem odd_centeredPolynomialLift_shiftedLegendreReal
    {n : ℕ} (hn : Odd n) :
    Function.Odd (centeredPolynomialLift (shiftedLegendreReal n)) := by
  intro x
  rw [show centeredPolynomialLift (shiftedLegendreReal n) (-x) =
      (centeredShiftedLegendreReal n).eval (-x) by
    exact (eval_centeredShiftedLegendreReal n (-x)).symm,
    eval_centeredShiftedLegendreReal_neg, hn.neg_one_pow,
    show (centeredShiftedLegendreReal n).eval x =
      centeredPolynomialLift (shiftedLegendreReal n) x by
        exact eval_centeredShiftedLegendreReal n x]
  ring

/-- Odd selector moments vanish identically on the actual even low space.
Thus the nominal fourteen-coordinate projection has only the seven even
coordinates `0,2,...,12`. -/
theorem fourCellEvenSchurResidualMoment_eq_zero_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    {n : ℕ} (hn : Odd n) :
    fourCellEvenSchurResidualMoment w hw n = 0 := by
  let G := fourCellEvenFiniteSevenSchurResidualRepresenter w hw
  let P := centeredPolynomialLift (shiftedLegendreReal n)
  have hG : Function.Even G := by
    simpa only [G] using
      even_fourCellEvenFiniteSevenSchurResidualRepresenter w hw heven
  have hP : Function.Odd P := by
    simpa only [P] using
      odd_centeredPolynomialLift_shiftedLegendreReal hn
  have hreflect :
      (∫ x : ℝ in -1..1, G (-x) * P (-x)) =
        ∫ x : ℝ in -1..1, G x * P x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := fun x : ℝ ↦ G x * P x)
        (a := (-1 : ℝ)) (b := 1))
  rw [show (fun x : ℝ ↦ G (-x) * P (-x)) =
      fun x ↦ -(G x * P x) by
    funext x
    rw [hG x, hP x]
    ring,
    intervalIntegral.integral_neg] at hreflect
  dsimp only [fourCellEvenSchurResidualMoment, G, P]
  linarith

/-- The genuine centered Legendre projection of the Schur residual through
degree thirteen.  The coefficient `(2n+1)/2` is the inverse of the exact
centered Legendre squared norm `2/(2n+1)`. -/
def fourCellEvenSchurResidualCanonicalSelector
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ[X] :=
  ∑ n ∈ Finset.range 14,
    (((2 * (n : ℝ) + 1) / 2) *
      fourCellEvenSchurResidualMoment w hw n) • shiftedLegendreReal n

theorem natDegree_fourCellEvenSchurResidualCanonicalSelector_lt_fourteen
    (w : ℝ → ℝ) (hw : Continuous w) :
    (fourCellEvenSchurResidualCanonicalSelector w hw).natDegree < 14 := by
  unfold fourCellEvenSchurResidualCanonicalSelector
  refine (Polynomial.natDegree_sum_le_of_forall_le (n := 13)
    (Finset.range 14) _ ?_).trans_lt
    (by norm_num)
  intro n hn
  have hnlt : n < 14 := Finset.mem_range.mp hn
  apply (Polynomial.natDegree_smul_le _ _).trans
  rw [natDegree_shiftedLegendreReal]
  omega

private theorem memLp_two_restrict_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem intervalIntegrable_schurResidual_mul_centeredPolynomialLift
    (w : ℝ → ℝ) (hw : Continuous w) (p : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ ↦
      fourCellEvenFiniteSevenSchurResidualRepresenter w hw x *
        centeredPolynomialLift p x) volume (-1) 1 := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hG : MemLp
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw) 2 μ := by
    simpa only [μ] using
      memLp_fourCellEvenFiniteSevenSchurResidualRepresenter w hw
  have hP : MemLp (centeredPolynomialLift p) 2 μ := by
    dsimp only [μ]
    apply memLp_two_restrict_of_continuous
    unfold centeredPolynomialLift
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (hP.mul' hG : MemLp (fun x : ℝ ↦
    fourCellEvenFiniteSevenSchurResidualRepresenter w hw x *
      centeredPolynomialLift p x) 1 μ).integrable (by norm_num)

private theorem intervalIntegrable_centeredPolynomialLift_mul
    (p q : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ ↦
      centeredPolynomialLift p x * centeredPolynomialLift q x)
      volume (-1) 1 := by
  exact ((by
    unfold centeredPolynomialLift
    fun_prop : Continuous (centeredPolynomialLift p)).mul (by
      unfold centeredPolynomialLift
      fun_prop : Continuous (centeredPolynomialLift q))).intervalIntegrable _ _

/-- Exact ordinary `L²(-1,1)` Gram matrix of the transported selector
basis. -/
theorem integral_centeredPolynomialLift_shiftedLegendreReal_mul
    (m n : ℕ) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift (shiftedLegendreReal m) x *
        centeredPolynomialLift (shiftedLegendreReal n) x) =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  simpa only [centeredPolynomialLift,
    ← eval_centeredShiftedLegendreReal] using
    centeredLegendreL2Gram m n

/-- Pointwise expansion of the canonical selector in the transported
Legendre basis. -/
theorem centeredPolynomialLift_fourCellEvenSchurResidualCanonicalSelector
    (w : ℝ → ℝ) (hw : Continuous w) (x : ℝ) :
    centeredPolynomialLift
        (fourCellEvenSchurResidualCanonicalSelector w hw) x =
      ∑ n ∈ Finset.range 14,
        (((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n) *
            centeredPolynomialLift (shiftedLegendreReal n) x := by
  simp only [fourCellEvenSchurResidualCanonicalSelector,
    centeredPolynomialLift, Polynomial.eval_finset_sum,
    Polynomial.eval_smul, smul_eq_mul]

/-- The canonical selector has exactly the same first fourteen ordinary
Legendre moments as the Schur residual. -/
theorem integral_canonicalSelector_mul_shiftedLegendreReal
    (w : ℝ → ℝ) (hw : Continuous w) (m : ℕ) (hm : m < 14) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x *
        centeredPolynomialLift (shiftedLegendreReal m) x) =
      fourCellEvenSchurResidualMoment w hw m := by
  rw [show (fun x : ℝ ↦
      centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x *
        centeredPolynomialLift (shiftedLegendreReal m) x) =
      fun x ↦ ∑ n ∈ Finset.range 14,
        (((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n) *
            (centeredPolynomialLift (shiftedLegendreReal n) x *
              centeredPolynomialLift (shiftedLegendreReal m) x) by
    funext x
    rw [centeredPolynomialLift_fourCellEvenSchurResidualCanonicalSelector]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul,
      integral_centeredPolynomialLift_shiftedLegendreReal_mul]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl]
      have hden : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hden]
    · intro n hn hne
      rw [if_neg hne]
      ring
    · intro hmnot
      exact (hmnot (Finset.mem_range.mpr hm)).elim
  · intro n _hn
    exact (intervalIntegrable_centeredPolynomialLift_mul
      (shiftedLegendreReal n) (shiftedLegendreReal m)).const_mul _

/-- Subtracting the canonical selector annihilates every ordinary Legendre
coordinate below fourteen. -/
theorem fourCellEvenSchurResidualCanonicalSelector_momentsVanishBelow
    (w : ℝ → ℝ) (hw : Continuous w) (m : ℕ) (hm : m < 14) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift (shiftedLegendreReal m) x) = 0 := by
  rw [show (fun x : ℝ ↦
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift (shiftedLegendreReal m) x) =
      fun x ↦
        fourCellEvenFiniteSevenSchurResidualRepresenter w hw x *
            centeredPolynomialLift (shiftedLegendreReal m) x -
          centeredPolynomialLift
              (fourCellEvenSchurResidualCanonicalSelector w hw) x *
            centeredPolynomialLift (shiftedLegendreReal m) x by
    funext x
    ring,
    intervalIntegral.integral_sub
      (intervalIntegrable_schurResidual_mul_centeredPolynomialLift
        w hw (shiftedLegendreReal m))
      (intervalIntegrable_centeredPolynomialLift_mul
        (fourCellEvenSchurResidualCanonicalSelector w hw)
        (shiftedLegendreReal m)),
    integral_canonicalSelector_mul_shiftedLegendreReal w hw m hm]
  simp only [fourCellEvenSchurResidualMoment, sub_self]

private theorem intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift
    (w : ℝ → ℝ) (hw : Continuous w) (p : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ ↦
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift p x) volume (-1) 1 := by
  convert
    (intervalIntegrable_schurResidual_mul_centeredPolynomialLift w hw p).sub
      (intervalIntegrable_centeredPolynomialLift_mul
        (fourCellEvenSchurResidualCanonicalSelector w hw) p) using 1
  funext x
  ring

/-- The canonical residual is orthogonal to the selector itself.  This is
the finite projection identity needed for Pythagoras, proved from the whole
degree-`<14` moment family rather than by inspecting fourteen entries. -/
theorem integral_canonicalResidual_mul_canonicalSelector_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) = 0 := by
  rw [show (fun x : ℝ ↦
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) =
      fun x ↦ ∑ n ∈ Finset.range 14,
        (((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n) *
            ((fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
                centeredPolynomialLift
                  (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
              centeredPolynomialLift (shiftedLegendreReal n) x) by
    funext x
    rw [centeredPolynomialLift_fourCellEvenSchurResidualCanonicalSelector]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro n hn
    rw [intervalIntegral.integral_const_mul,
      fourCellEvenSchurResidualCanonicalSelector_momentsVanishBelow
        w hw n (Finset.mem_range.mp hn), mul_zero]
  · intro n _hn
    exact (intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift
      w hw (shiftedLegendreReal n)).const_mul _

private theorem intervalIntegrable_schurResidual_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable (fun x : ℝ ↦
      fourCellEvenFiniteSevenSchurResidualRepresenter w hw x ^ 2)
      volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have h :=
    (memLp_fourCellEvenFiniteSevenSchurResidualRepresenter w hw)
      |>.integrable_norm_pow (by norm_num)
  simpa only [Real.norm_eq_abs, sq_abs] using h

private theorem intervalIntegrable_centeredPolynomialLift_sq (p : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ ↦ centeredPolynomialLift p x ^ 2)
      volume (-1) 1 := by
  have h := intervalIntegrable_centeredPolynomialLift_mul p p
  convert h using 1
  funext x
  ring

private theorem intervalIntegrable_canonicalResidual_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable (fun x : ℝ ↦
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2)
      volume (-1) 1 := by
  let G := fourCellEvenFiniteSevenSchurResidualRepresenter w hw
  let P := centeredPolynomialLift
    (fourCellEvenSchurResidualCanonicalSelector w hw)
  have hG := intervalIntegrable_schurResidual_sq w hw
  have hGP := intervalIntegrable_schurResidual_mul_centeredPolynomialLift
    w hw (fourCellEvenSchurResidualCanonicalSelector w hw)
  have hP := intervalIntegrable_centeredPolynomialLift_sq
    (fourCellEvenSchurResidualCanonicalSelector w hw)
  convert (hG.sub (hGP.const_mul 2)).add hP using 1
  funext x
  dsimp only [G, P]
  ring

/-- Exact Pythagorean decomposition of the Schur-residual norm into its
degree-`<14` selector and genuine `P14+` quotient tail. -/
theorem fourCellEvenSchurResidualCanonicalSelector_pythagorean
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1,
      fourCellEvenFiniteSevenSchurResidualRepresenter w hw x ^ 2) =
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) +
      ∫ x : ℝ in -1..1,
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x ^ 2 := by
  let G := fourCellEvenFiniteSevenSchurResidualRepresenter w hw
  let P := centeredPolynomialLift
    (fourCellEvenSchurResidualCanonicalSelector w hw)
  let R := fun x ↦ G x - P x
  have hR := intervalIntegrable_canonicalResidual_sq w hw
  have hRP := intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift
    w hw (fourCellEvenSchurResidualCanonicalSelector w hw)
  have hP := intervalIntegrable_centeredPolynomialLift_sq
    (fourCellEvenSchurResidualCanonicalSelector w hw)
  have hcross :=
    integral_canonicalResidual_mul_canonicalSelector_eq_zero w hw
  rw [show (fun x : ℝ ↦ G x ^ 2) =
      fun x ↦ R x ^ 2 + 2 * (R x * P x) + P x ^ 2 by
    funext x
    dsimp only [R]
    ring,
    intervalIntegral.integral_add (hR.add (hRP.const_mul 2)) hP,
    intervalIntegral.integral_add hR (hRP.const_mul 2),
    intervalIntegral.integral_const_mul, hcross]
  ring

/-- Closed finite trace of the selector norm.  This is a basis formula, not
a table of fourteen computed moments. -/
theorem integral_canonicalSelector_sq_eq_moment_sum
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
        (fourCellEvenSchurResidualCanonicalSelector w hw) x ^ 2) =
      ∑ n ∈ Finset.range 14,
        ((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n ^ 2 := by
  rw [show (fun x : ℝ ↦
      centeredPolynomialLift
        (fourCellEvenSchurResidualCanonicalSelector w hw) x ^ 2) =
      fun x ↦ ∑ n ∈ Finset.range 14,
        (((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n) *
            (centeredPolynomialLift
                (fourCellEvenSchurResidualCanonicalSelector w hw) x *
              centeredPolynomialLift (shiftedLegendreReal n) x) by
    funext x
    rw [pow_two,
      centeredPolynomialLift_fourCellEvenSchurResidualCanonicalSelector]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul,
      integral_canonicalSelector_mul_shiftedLegendreReal
        w hw n (Finset.mem_range.mp hn)]
    ring
  · intro n _hn
    exact (intervalIntegrable_centeredPolynomialLift_mul
      (fourCellEvenSchurResidualCanonicalSelector w hw)
      (shiftedLegendreReal n)).const_mul _

/-- On even profiles the selector norm is the seven-coordinate trace over
the even degrees below fourteen. -/
theorem integral_canonicalSelector_sq_eq_even_moment_sum
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
        (fourCellEvenSchurResidualCanonicalSelector w hw) x ^ 2) =
      ∑ n ∈ (Finset.range 14).filter Even,
        ((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n ^ 2 := by
  rw [integral_canonicalSelector_sq_eq_moment_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hnEven : Even n
  · rw [if_pos hnEven]
  · rw [if_neg hnEven,
      fourCellEvenSchurResidualMoment_eq_zero_of_odd
        w hw heven (Nat.not_even_iff_odd.mp hnEven)]
    ring

/-- Exact scalar form of the remaining quotient norm: the genuine tail is
the full residual mass minus its first fourteen centered Legendre squares. -/
theorem integral_canonicalResidual_sq_eq_full_sub_moment_sum
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) =
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenSchurResidualRepresenter w hw x ^ 2) -
      ∑ n ∈ Finset.range 14,
        ((2 * (n : ℝ) + 1) / 2) *
          fourCellEvenSchurResidualMoment w hw n ^ 2 := by
  have hpyth :=
    fourCellEvenSchurResidualCanonicalSelector_pythagorean w hw
  rw [integral_canonicalSelector_sq_eq_moment_sum] at hpyth
  linarith

/-- The canonical residual annihilates every degree-`<14` selector, not only
the basis generators.  The proof uses the all-degree polynomial-sequence
span theorem, so no list of low degrees appears. -/
theorem integral_canonicalResidual_mul_selector_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (Q : ℝ[X]) (hQ : Q.natDegree < 14) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
        centeredPolynomialLift Q x) = 0 := by
  have hspan : Q ∈ Submodule.span ℝ
      (shiftedLegendreRealSequence '' Iio 14) := by
    rw [shiftedLegendreRealSequence.span_degreeLT
      (fun i _hi ↦ shiftedLegendreReal_leadingCoeff_isUnit i)]
    by_cases hzero : Q = 0
    · subst Q
      exact Submodule.zero_mem _
    · rw [Polynomial.mem_degreeLT,
        ← Polynomial.natDegree_lt_iff_degree_lt hzero]
      exact hQ
  refine Submodule.span_induction
    (p := fun R _hR ↦
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
            centeredPolynomialLift
              (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
          centeredPolynomialLift R x) = 0)
    ?_ ?_ ?_ ?_ hspan
  · intro R hR
    obtain ⟨n, hn, rfl⟩ := hR
    simpa only [shiftedLegendreRealSequence_apply] using
      fourCellEvenSchurResidualCanonicalSelector_momentsVanishBelow
        w hw n (Set.mem_Iio.mp hn)
  · simp [centeredPolynomialLift]
  · intro R S _hR _hS hRzero hSzero
    rw [show (fun x : ℝ ↦
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
            centeredPolynomialLift
              (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
          centeredPolynomialLift (R + S) x) =
        fun x ↦
          (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
              centeredPolynomialLift
                (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
              centeredPolynomialLift R x +
            (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
              centeredPolynomialLift
                (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
              centeredPolynomialLift S x by
      funext x
      unfold centeredPolynomialLift
      rw [Polynomial.eval_add]
      ring,
      intervalIntegral.integral_add
        (intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift
          w hw R)
        (intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift
          w hw S), hRzero, hSzero, add_zero]
  · intro a R _hR hRzero
    rw [show (fun x : ℝ ↦
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
            centeredPolynomialLift
              (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
          centeredPolynomialLift (a • R) x) =
        fun x ↦ a *
          ((fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
              centeredPolynomialLift
                (fourCellEvenSchurResidualCanonicalSelector w hw) x) *
            centeredPolynomialLift R x) by
      funext x
      unfold centeredPolynomialLift
      simp only [Polynomial.eval_smul, smul_eq_mul]
      ring,
      intervalIntegral.integral_const_mul, hRzero, mul_zero]

/-- Pythagoras against an arbitrary admissible selector.  The second summand
is the exact squared distance from that selector to the canonical one. -/
theorem integral_selectorResidual_sq_eq_canonical_add_distance
    (w : ℝ → ℝ) (hw : Continuous w)
    (Q : ℝ[X]) (hQ : Q.natDegree < 14) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift Q x) ^ 2) =
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) +
      ∫ x : ℝ in -1..1,
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw - Q) x ^ 2 := by
  let P := fourCellEvenSchurResidualCanonicalSelector w hw
  let D := P - Q
  let R := fun x : ℝ ↦
    fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
      centeredPolynomialLift P x
  have hP : P.natDegree < 14 := by
    simpa only [P] using
      natDegree_fourCellEvenSchurResidualCanonicalSelector_lt_fourteen w hw
  have hD : D.natDegree < 14 := by
    unfold D
    exact (Polynomial.natDegree_sub_le P Q).trans_lt (max_lt hP hQ)
  have horth : (∫ x : ℝ in -1..1,
      R x * centeredPolynomialLift D x) = 0 := by
    simpa only [R, P] using
      integral_canonicalResidual_mul_selector_eq_zero w hw D hD
  have hR := intervalIntegrable_canonicalResidual_sq w hw
  have hRD :=
    intervalIntegrable_canonicalResidual_mul_centeredPolynomialLift w hw D
  have hDsq := intervalIntegrable_centeredPolynomialLift_sq D
  rw [show (fun x : ℝ ↦
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift Q x) ^ 2) =
      fun x ↦ R x ^ 2 +
        2 * (R x * centeredPolynomialLift D x) +
          centeredPolynomialLift D x ^ 2 by
    funext x
    dsimp only [R, D, P]
    unfold centeredPolynomialLift
    rw [Polynomial.eval_sub]
    ring,
    intervalIntegral.integral_add (hR.add (hRD.const_mul 2)) hDsq,
    intervalIntegral.integral_add hR (hRD.const_mul 2),
    intervalIntegral.integral_const_mul, horth]
  dsimp only [D, P]
  ring

/-- The canonical selector minimizes the genuine quotient norm among all
degree-`<14` selectors. -/
theorem integral_canonicalResidual_sq_le_selectorResidual_sq
    (w : ℝ → ℝ) (hw : Continuous w)
    (Q : ℝ[X]) (hQ : Q.natDegree < 14) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) ≤
      ∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift Q x) ^ 2 := by
  have hid := integral_selectorResidual_sq_eq_canonical_add_distance
    w hw Q hQ
  have hnonneg : 0 ≤ ∫ x : ℝ in -1..1,
      centeredPolynomialLift
        (fourCellEvenSchurResidualCanonicalSelector w hw - Q) x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  linarith

/-- Existence of any successful low selector is equivalent to the one
canonical quotient-tail inequality.  Selector search has therefore been
removed completely from the even length-four frontier. -/
theorem exists_schurResidualSelectorNorm_iff_canonical
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∃ Q : ℝ[X], Q.natDegree < 14 ∧
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift Q x) ^ 2) ≤
        ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
          fourCellEvenFiniteSevenExactLowDiagonal w hw) ↔
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) ≤
        ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
          fourCellEvenFiniteSevenExactLowDiagonal w hw := by
  constructor
  · rintro ⟨Q, hQ, hbound⟩
    exact (integral_canonicalResidual_sq_le_selectorResidual_sq
      w hw Q hQ).trans hbound
  · intro hbound
    exact ⟨fourCellEvenSchurResidualCanonicalSelector w hw,
      natDegree_fourCellEvenSchurResidualCanonicalSelector_lt_fourteen w hw,
      hbound⟩

/-- The exact remaining even length-four analytic statement after canonical
projection.  It is a Loewner bound on the cosh-orthogonal even low space;
there is no selector existential and no tail profile in its formulation. -/
def FourCellEvenCanonicalSchurResidualLoewner : Prop :=
  ∀ (w : ℝ → ℝ) (hw : Continuous w),
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) w →
    Function.Even w →
    fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0 →
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
        centeredPolynomialLift
          (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) ≤
      ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
        fourCellEvenFiniteSevenExactLowDiagonal w hw

/-- The canonical Loewner bound immediately discharges the exact endpoint
seed row. -/
theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_canonical
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hnorm :
      (∫ x : ℝ in -1..1,
        (fourCellEvenFiniteSevenSchurResidualRepresenter w hw x -
          centeredPolynomialLift
            (fourCellEvenSchurResidualCanonicalSelector w hw) x) ^ 2) ≤
        ((49 / 10000 : ℝ) * (harmonic 14 : ℝ)) *
          fourCellEvenFiniteSevenExactLowDiagonal w hw) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w := by
  exact
    fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_schurResidualNorm
      w hw hlocal heven hzero
      (fourCellEvenSchurResidualCanonicalSelector w hw)
      (natDegree_fourCellEvenSchurResidualCanonicalSelector_lt_fourteen w hw)
      hnorm

theorem fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_canonicalLoewner
    (hloewner : FourCellEvenCanonicalSchurResidualLoewner)
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      fourCellEvenFiniteSevenSeedDiagonal *
        fourCellEvenPolarFreeOperator w :=
  fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_canonical
    w hw hlocal heven hzero (hloewner w hw hlocal heven hzero)

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenSchurResidualSelectorStructural
