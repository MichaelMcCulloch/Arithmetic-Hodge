import ArithmeticHodge.Analysis.ShiftedLegendreBasis
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

set_option autoImplicit false

open Polynomial Set Submodule
open scoped ENNReal InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreL2Basis

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open MeasureTheory

/-!
# The shifted-Legendre Hilbert basis of `L²([0,1], ℝ)`

This file passes from the algebraic shifted-Legendre polynomial basis to a
complete orthonormal family in real `L²` on the unit interval.  Completeness
is structural: Stone--Weierstrass makes polynomial restrictions dense among
continuous functions, and continuous functions are dense in `L²`.
-/

/-- Real `L²` on the unit interval with its canonical volume measure. -/
abbrev UnitIntervalL2 := Lp ℝ 2 (volume : Measure unitInterval)

/-- Restriction of a real polynomial to the unit interval. -/
def polynomialToContinuous : ℝ[X] →ₗ[ℝ] C(unitInterval, ℝ) :=
  (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)).toLinearMap

@[simp]
theorem polynomialToContinuous_apply (p : ℝ[X]) (x : unitInterval) :
    polynomialToContinuous p x = p.eval (x : ℝ) := rfl

/-- Polynomial restriction followed by the canonical map to `L²`. -/
def polynomialToL2 : ℝ[X] →ₗ[ℝ] UnitIntervalL2 :=
  (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ).toLinearMap.comp
    polynomialToContinuous

/-- The unnormalized shifted-Legendre family in `L²([0,1])`. -/
def shiftedLegendreL2 (n : ℕ) : UnitIntervalL2 :=
  polynomialToL2 (shiftedLegendreReal n)

/-- Polynomial restrictions are uniformly dense on the unit interval. -/
theorem polynomialToContinuous_denseRange :
    DenseRange polynomialToContinuous := by
  rw [denseRange_iff_closure_range]
  have hclosure :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (polynomialFunctions (Set.Icc (0 : ℝ) 1))
      (polynomialFunctions_separatesPoints (Set.Icc (0 : ℝ) 1))
  rw [SetLike.ext'_iff] at hclosure
  simpa [polynomialFunctions_coe] using hclosure

/-- Polynomial `L²` classes are dense in `L²([0,1])`. -/
theorem polynomialToL2_denseRange : DenseRange polynomialToL2 := by
  change DenseRange
    ((ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ) ∘
      polynomialToContinuous)
  exact DenseRange.comp
    (ContinuousMap.toLp_denseRange ℝ (volume : Measure unitInterval) ℝ
      (p := 2) (by norm_num))
    polynomialToContinuous_denseRange
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ).continuous

/-- The algebraic span of the unnormalized shifted-Legendre `L²` family is
the range of all polynomial `L²` classes. -/
theorem span_shiftedLegendreL2_eq_range_polynomialToL2 :
    Submodule.span ℝ (Set.range shiftedLegendreL2) =
      LinearMap.range polynomialToL2 := by
  calc
    Submodule.span ℝ (Set.range shiftedLegendreL2) =
        Submodule.span ℝ (polynomialToL2 '' Set.range shiftedLegendreReal) := by
      rw [← Set.range_comp]
      rfl
    _ = (Submodule.span ℝ (Set.range shiftedLegendreReal)).map polynomialToL2 := by
      rw [Submodule.map_span]
    _ = LinearMap.range polynomialToL2 := by
      rw [shiftedLegendreReal_span_eq_top, Submodule.map_top]

/-- The unnormalized shifted-Legendre family has dense linear span in
`L²([0,1])`. -/
theorem topologicalClosure_span_shiftedLegendreL2_eq_top :
    (Submodule.span ℝ (Set.range shiftedLegendreL2)).topologicalClosure = ⊤ := by
  rw [span_shiftedLegendreL2_eq_range_polynomialToL2]
  rw [SetLike.ext'_iff]
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe,
    LinearMap.coe_range, ← dense_iff_closure_eq]
  exact polynomialToL2_denseRange

/-- A continuous function on the unit interval which is nonzero at the left
endpoint represents a nonzero `L²` class.  The proof uses a positive-measure
relative interval contained in its open support. -/
theorem continuousMap_toLp_ne_zero_of_apply_zero_ne
    (f : C(unitInterval, ℝ)) (h0 : f 0 ≠ 0) :
    ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ f ≠ 0 := by
  intro h
  have haeLp := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (μ := (volume : Measure unitInterval)) (𝕜 := ℝ) f
  have hae : (f : unitInterval → ℝ) =ᵐ[volume]
      (0 : unitInterval → ℝ) := by
    calc
      (f : unitInterval → ℝ) =ᵐ[volume]
          (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ f :
            unitInterval → ℝ) := haeLp.symm
      _ =ᵐ[volume] 0 := by
        rw [h]
        exact Lp.coeFn_zero ℝ 2 volume
  have hsupp_zero : volume (Function.support f) = 0 :=
    (Measure.measure_support_eq_zero_iff
      (volume : Measure unitInterval)).2 hae
  have hnhds : Function.support f ∈ nhds (0 : unitInterval) :=
    f.continuous.isOpen_support.mem_nhds h0
  rcases nhds_bot_basis.mem_iff.mp hnhds with ⟨a, ha, hsub⟩
  have hIio_zero : volume (Set.Iio a) = 0 :=
    measure_mono_null hsub hsupp_zero
  have hIio_pos : 0 < volume (Set.Iio a) := by
    rw [unitInterval.volume_Iio, ENNReal.ofReal_pos]
    exact_mod_cast ha
  exact (ne_of_gt hIio_pos) hIio_zero

@[simp]
theorem shiftedLegendreReal_eval_zero (n : ℕ) :
    (shiftedLegendreReal n).eval 0 = 1 := by
  rw [show (shiftedLegendreReal n).eval 0 =
      (shiftedLegendreReal n).coeff 0 by
    exact Polynomial.eval₂_at_zero (RingHom.id ℝ)]
  simp [shiftedLegendreReal, Polynomial.coeff_shiftedLegendre]

/-- No shifted-Legendre polynomial disappears in the `L²` quotient. -/
theorem shiftedLegendreL2_ne_zero (n : ℕ) :
    shiftedLegendreL2 n ≠ 0 := by
  apply continuousMap_toLp_ne_zero_of_apply_zero_ne
  change (shiftedLegendreReal n).eval 0 ≠ 0
  simp

/-- Distinct unnormalized shifted-Legendre `L²` vectors are orthogonal. -/
theorem inner_shiftedLegendreL2_eq_zero
    {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (shiftedLegendreL2 m) (shiftedLegendreL2 n) = 0 := by
  change inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal m)))
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal n))) = 0
  have hinner := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval)
    (polynomialToContinuous (shiftedLegendreReal m))
    (polynomialToContinuous (shiftedLegendreReal n))
  calc
    _ = ∫ x : unitInterval,
        (polynomialToContinuous (shiftedLegendreReal n)) x *
          starRingEnd ℝ
            ((polynomialToContinuous (shiftedLegendreReal m)) x) := hinner
    _ = 0 := by
      change (∫ x : unitInterval,
        (shiftedLegendreReal n).eval (x : ℝ) *
          (shiftedLegendreReal m).eval (x : ℝ)) = 0
      calc
        _ = ∫ x : ℝ in Set.Icc 0 1,
            (shiftedLegendreReal n).eval x *
              (shiftedLegendreReal m).eval x :=
          unitInterval.measurePreserving_coe.integral_comp
            unitInterval.measurableEmbedding_coe _
        _ = ∫ x : ℝ in 0..1,
            (shiftedLegendreReal n).eval x *
              (shiftedLegendreReal m).eval x := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        _ = 0 := integral_shiftedLegendreReal_mul_eq_zero hmn.symm

/-- The shifted-Legendre `L²` family normalized by its Hilbert norm. -/
def normalizedShiftedLegendreL2 (n : ℕ) : UnitIntervalL2 :=
  ‖shiftedLegendreL2 n‖⁻¹ • shiftedLegendreL2 n

@[simp]
theorem norm_normalizedShiftedLegendreL2 (n : ℕ) :
    ‖normalizedShiftedLegendreL2 n‖ = 1 := by
  have hnorm : ‖shiftedLegendreL2 n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero n)
  simp [normalizedShiftedLegendreL2, norm_smul, hnorm]

/-- The normalized shifted-Legendre family is orthonormal. -/
theorem orthonormal_normalizedShiftedLegendreL2 :
    Orthonormal ℝ normalizedShiftedLegendreL2 := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    rw [real_inner_self_eq_norm_sq, norm_normalizedShiftedLegendreL2,
      one_pow]
  · rw [if_neg hmn]
    change inner ℝ
      (‖shiftedLegendreL2 m‖⁻¹ • shiftedLegendreL2 m)
      (‖shiftedLegendreL2 n‖⁻¹ • shiftedLegendreL2 n) = 0
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_shiftedLegendreL2_eq_zero hmn, mul_zero, mul_zero]

/-- Normalization does not change the closed linear span. -/
theorem topologicalClosure_span_normalizedShiftedLegendreL2_eq_top :
    (Submodule.span ℝ
      (Set.range normalizedShiftedLegendreL2)).topologicalClosure = ⊤ := by
  have hraw_le :
      Submodule.span ℝ (Set.range shiftedLegendreL2) ≤
        Submodule.span ℝ (Set.range normalizedShiftedLegendreL2) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    have hnormalized : normalizedShiftedLegendreL2 n ∈
        Submodule.span ℝ (Set.range normalizedShiftedLegendreL2) :=
      Submodule.subset_span (Set.mem_range_self n)
    have hscaled := (Submodule.span ℝ
      (Set.range normalizedShiftedLegendreL2)).smul_mem
        ‖shiftedLegendreL2 n‖ hnormalized
    have hnorm : ‖shiftedLegendreL2 n‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero n)
    simpa only [normalizedShiftedLegendreL2, smul_smul,
      mul_inv_cancel₀ hnorm, one_smul] using hscaled
  apply le_antisymm le_top
  rw [← topologicalClosure_span_shiftedLegendreL2_eq_top]
  exact Submodule.topologicalClosure_mono hraw_le

/-- The complete normalized shifted-Legendre Hilbert basis of real
`L²([0,1])`. -/
def shiftedLegendreHilbertBasis : HilbertBasis ℕ ℝ UnitIntervalL2 :=
  HilbertBasis.mk orthonormal_normalizedShiftedLegendreL2
    topologicalClosure_span_normalizedShiftedLegendreL2_eq_top.ge

@[simp]
theorem shiftedLegendreHilbertBasis_apply (n : ℕ) :
    shiftedLegendreHilbertBasis n = normalizedShiftedLegendreL2 n := by
  simpa only [shiftedLegendreHilbertBasis] using congrFun
    (HilbertBasis.coe_mk orthonormal_normalizedShiftedLegendreL2
      topologicalClosure_span_normalizedShiftedLegendreL2_eq_top.ge) n

end

end ArithmeticHodge.Analysis.ShiftedLegendreL2Basis
