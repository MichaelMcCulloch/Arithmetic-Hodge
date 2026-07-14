import Mathlib.Analysis.Calculus.Taylor
import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchurClosure

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseEvenSchurClosure
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Intrinsic Taylor-residual bounds for the hyperbolic rank family

The low centered Legendre coefficients kill the corresponding Taylor jet of
the hyperbolic moment.  Thus the even `P₀/P₂` residual sees only
`cosh (lambda * x) - 1 - (lambda * x) ^ 2 / 2`, while the odd `P₁/P₃`
residual sees only
`sinh (lambda * x) - lambda * x - (lambda * x) ^ 3 / 6`.

Everything below is rank-uniform and structural: exact cancellation,
Cauchy--Schwarz, and Lagrange Taylor remainders.  No rank enumeration enters.
-/

/-- The fourth-order Taylor residual relevant to an even `P₀/P₂` residual. -/
def evenCoshTaylorResidual (lambda x : ℝ) : ℝ :=
  Real.cosh (lambda * x) - 1 - (lambda * x) ^ 2 / 2

/-- The fifth-order Taylor residual relevant to an odd `P₁/P₃` residual. -/
def oddSinhTaylorResidual (lambda x : ℝ) : ℝ :=
  Real.sinh (lambda * x) - lambda * x - (lambda * x) ^ 3 / 6

/-- Squared `L²[-1,1]` mass of the even Taylor residual. -/
def evenCoshTaylorResidualMass (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, evenCoshTaylorResidual lambda x ^ 2

/-- Squared `L²[-1,1]` mass of the odd Taylor residual. -/
def oddSinhTaylorResidualMass (lambda : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, oddSinhTaylorResidual lambda x ^ 2

private theorem continuous_evenCoshTaylorResidual (lambda : ℝ) :
    Continuous (evenCoshTaylorResidual lambda) := by
  unfold evenCoshTaylorResidual
  fun_prop

private theorem continuous_oddSinhTaylorResidual (lambda : ℝ) :
    Continuous (oddSinhTaylorResidual lambda) := by
  unfold oddSinhTaylorResidual
  fun_prop

private theorem abs_cosh_sub_quadratic_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    |Real.cosh u - 1 - u ^ 2 / 2| ≤
      Real.cosh u * u ^ 4 / 24 := by
  rcases eq_or_lt_of_le hu with rfl | hupos
  · norm_num
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 3) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 3 (Icc 0 u) 0 u =
          1 + u ^ 2 / 2 := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hw0 : 0 ≤ w := hw.1.le
    have hwu : w ≤ u := hw.2.le
    have hcosh : Real.cosh w ≤ Real.cosh u := by
      rw [Real.cosh_le_cosh]
      simpa [abs_of_nonneg hw0, abs_of_nonneg hu] using hwu
    have hrem0 : 0 ≤ Real.cosh w * u ^ 4 / 24 := by positivity
    have hrem : Real.cosh u - 1 - u ^ 2 / 2 =
        Real.cosh w * u ^ 4 / 24 := by
      linarith
    rw [hrem]
    rw [abs_of_nonneg hrem0]
    gcongr

private theorem abs_sinh_sub_cubic_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    |Real.sinh u - u - u ^ 3 / 6| ≤
      Real.cosh u * u ^ 5 / 120 := by
  rcases eq_or_lt_of_le hu with rfl | hupos
  · norm_num
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.sinh) (x₀ := 0) (x := u) (n := 4) hupos
        Real.contDiff_sinh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.sinh 4 (Icc 0 u) 0 u =
          u + u ^ 3 / 6 := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.sinh (Icc 0 u) 0 =
            iteratedDeriv n Real.sinh 0 :=
        Real.iteratedDerivWithin_sinh_Icc n hupos ⟨le_rfl, hu⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_odd_sinh] at hTaylor
    have hw0 : 0 ≤ w := hw.1.le
    have hwu : w ≤ u := hw.2.le
    have hcosh : Real.cosh w ≤ Real.cosh u := by
      rw [Real.cosh_le_cosh]
      simpa [abs_of_nonneg hw0, abs_of_nonneg hu] using hwu
    have hrem0 : 0 ≤ Real.cosh w * u ^ 5 / 120 := by positivity
    have hrem : Real.sinh u - u - u ^ 3 / 6 =
        Real.cosh w * u ^ 5 / 120 := by
      linarith
    rw [hrem]
    rw [abs_of_nonneg hrem0]
    gcongr

/-- Global fourth-order Taylor bound for the even residual. -/
theorem abs_cosh_sub_quadratic_le (z : ℝ) :
    |Real.cosh z - 1 - z ^ 2 / 2| ≤
      Real.cosh |z| * |z| ^ 4 / 24 := by
  have h := abs_cosh_sub_quadratic_of_nonneg (abs_nonneg z)
  simpa [Real.cosh_abs, sq_abs] using h

/-- Global fifth-order Taylor bound for the odd residual. -/
theorem abs_sinh_sub_cubic_le (z : ℝ) :
    |Real.sinh z - z - z ^ 3 / 6| ≤
      Real.cosh |z| * |z| ^ 5 / 120 := by
  by_cases hz : 0 ≤ z
  · simpa [abs_of_nonneg hz] using abs_sinh_sub_cubic_of_nonneg hz
  · have hzlt : z < 0 := lt_of_not_ge hz
    have hneg : 0 ≤ -z := neg_nonneg.mpr hzlt.le
    have h := abs_sinh_sub_cubic_of_nonneg hneg
    have hid :
        Real.sinh (-z) - (-z) - (-z) ^ 3 / 6 =
          -(Real.sinh z - z - z ^ 3 / 6) := by
      rw [Real.sinh_neg]
      ring
    have habs :
        |Real.sinh (-z) - (-z) - (-z) ^ 3 / 6| =
          |Real.sinh z - z - z ^ 3 / 6| := by
      rw [hid, abs_neg]
    rw [habs] at h
    simpa [abs_of_neg hzlt] using h

/-! ## Exact annihilation of the low Taylor jets -/

private theorem even_integral_one_eq_zero
    (e : ℝ → ℝ) (he0 : centeredEvenP0Coefficient e = 0) :
    (∫ x : ℝ in -1..1, e x) = 0 := by
  unfold centeredEvenP0Coefficient at he0
  linarith

private theorem even_integral_sq_eq_zero
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) :
    (∫ x : ℝ in -1..1, e x * x ^ 2) = 0 := by
  have hone := even_integral_one_eq_zero e he0
  have hp2 := integral_mul_centeredEvenP2_eq e
  rw [he2] at hp2
  have hfun :
      (fun x : ℝ ↦ e x * centeredEvenP2 x) =
        fun x ↦ (3 / 2 : ℝ) * (e x * x ^ 2) - (1 / 2 : ℝ) * e x := by
    funext x
    unfold centeredEvenP2
    ring
  rw [hfun,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hone] at hp2
  norm_num at hp2 ⊢
  linarith

private theorem odd_integral_linear_eq_zero
    (o : ℝ → ℝ) (ho1 : centeredOddP1Coefficient o = 0) :
    (∫ x : ℝ in -1..1, o x * x) = 0 := by
  have hp1 := integral_mul_centeredP1_eq o
  rw [ho1] at hp1
  simpa [centeredP1] using hp1

private theorem odd_integral_cubic_eq_zero
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) :
    (∫ x : ℝ in -1..1, o x * x ^ 3) = 0 := by
  have hlinear := odd_integral_linear_eq_zero o ho1
  have hp3 := integral_mul_centeredP3_eq o
  rw [ho3] at hp3
  have hfun :
      (fun x : ℝ ↦ o x * centeredP3 x) =
        fun x ↦ (5 / 2 : ℝ) * (o x * x ^ 3) -
          (3 / 2 : ℝ) * (o x * x) := by
    funext x
    unfold centeredP3
    ring
  rw [hfun,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hlinear] at hp3
  norm_num at hp3 ⊢
  linarith

/-- Vanishing `P₀/P₂` coefficients remove the constant and quadratic Taylor
jet from every centered cosh moment, at an arbitrary real rank parameter. -/
theorem centeredCoshMoment_eq_evenTaylorResidual
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) (lambda : ℝ) :
    centeredCoshMoment e lambda =
      ∫ x : ℝ in -1..1, evenCoshTaylorResidual lambda x * e x := by
  have hone := even_integral_one_eq_zero e he0
  have hsq := even_integral_sq_eq_zero e hec he0 he2
  have hfun :
      (fun x : ℝ ↦ evenCoshTaylorResidual lambda x * e x) =
        fun x ↦
          Real.cosh (lambda * x) * e x - e x -
            (lambda ^ 2 / 2) * (e x * x ^ 2) := by
    funext x
    unfold evenCoshTaylorResidual
    ring
  unfold centeredCoshMoment
  rw [hfun,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul, hone, hsq]
  ring

/-- Vanishing `P₁/P₃` coefficients remove the linear and cubic Taylor jet
from every centered sinh moment, at an arbitrary real rank parameter. -/
theorem centeredSinhMoment_eq_oddTaylorResidual
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) (lambda : ℝ) :
    centeredSinhMoment o lambda =
      ∫ x : ℝ in -1..1, oddSinhTaylorResidual lambda x * o x := by
  have hlinear := odd_integral_linear_eq_zero o ho1
  have hcubic := odd_integral_cubic_eq_zero o hoc ho1 ho3
  have hfun :
      (fun x : ℝ ↦ oddSinhTaylorResidual lambda x * o x) =
        fun x ↦
          Real.sinh (lambda * x) * o x -
            lambda * (o x * x) -
              (lambda ^ 3 / 6) * (o x * x ^ 3) := by
    funext x
    unfold oddSinhTaylorResidual
    ring
  unfold centeredSinhMoment
  rw [hfun,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hlinear, hcubic]
  ring

/-! ## Rankwise Cauchy--Schwarz and Taylor bounds -/

private theorem sq_intervalIntegral_mul_le
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in -1..1, f x * g x) ^ 2 ≤
      (∫ x : ℝ in -1..1, f x ^ 2) *
        (∫ x : ℝ in -1..1, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

/-- Cauchy--Schwarz after the exact even Taylor-jet cancellation. -/
theorem centeredCoshMoment_sq_le_residualMass_mul_energy
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) (lambda : ℝ) :
    centeredCoshMoment e lambda ^ 2 ≤
      evenCoshTaylorResidualMass lambda *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
  rw [centeredCoshMoment_eq_evenTaylorResidual e hec he0 he2 lambda]
  exact sq_intervalIntegral_mul_le _ _
    (continuous_evenCoshTaylorResidual lambda) hec

/-- Cauchy--Schwarz after the exact odd Taylor-jet cancellation. -/
theorem centeredSinhMoment_sq_le_residualMass_mul_energy
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) (lambda : ℝ) :
    centeredSinhMoment o lambda ^ 2 ≤
      oddSinhTaylorResidualMass lambda *
        (∫ x : ℝ in -1..1, o x ^ 2) := by
  rw [centeredSinhMoment_eq_oddTaylorResidual o hoc ho1 ho3 lambda]
  exact sq_intervalIntegral_mul_le _ _
    (continuous_oddSinhTaylorResidual lambda) hoc

/-- Uniform pointwise Taylor control on the centered interval for the even
residual, valid at every real rank parameter. -/
theorem abs_evenCoshTaylorResidual_le
    (lambda x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |evenCoshTaylorResidual lambda x| ≤
      Real.cosh |lambda| * |lambda| ^ 4 / 24 := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hlx : |lambda * x| ≤ |lambda| := by
    rw [abs_mul]
    nlinarith [abs_nonneg lambda]
  have h := abs_cosh_sub_quadratic_le (lambda * x)
  unfold evenCoshTaylorResidual
  calc
    _ ≤ Real.cosh |lambda * x| * |lambda * x| ^ 4 / 24 := h
    _ ≤ Real.cosh |lambda| * |lambda| ^ 4 / 24 := by
      have hcosh : Real.cosh |lambda * x| ≤ Real.cosh |lambda| := by
        rw [Real.cosh_le_cosh]
        simpa only [abs_abs] using hlx
      gcongr

/-- Uniform pointwise Taylor control on the centered interval for the odd
residual, valid at every real rank parameter. -/
theorem abs_oddSinhTaylorResidual_le
    (lambda x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |oddSinhTaylorResidual lambda x| ≤
      Real.cosh |lambda| * |lambda| ^ 5 / 120 := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hlx : |lambda * x| ≤ |lambda| := by
    rw [abs_mul]
    nlinarith [abs_nonneg lambda]
  have h := abs_sinh_sub_cubic_le (lambda * x)
  unfold oddSinhTaylorResidual
  calc
    _ ≤ Real.cosh |lambda * x| * |lambda * x| ^ 5 / 120 := h
    _ ≤ Real.cosh |lambda| * |lambda| ^ 5 / 120 := by
      have hcosh : Real.cosh |lambda * x| ≤ Real.cosh |lambda| := by
        rw [Real.cosh_le_cosh]
        simpa only [abs_abs] using hlx
      gcongr

/-- Integrated fourth-order Taylor majorant for the even residual. -/
theorem evenCoshTaylorResidualMass_le (lambda : ℝ) :
    evenCoshTaylorResidualMass lambda ≤
      2 * (Real.cosh |lambda| * |lambda| ^ 4 / 24) ^ 2 := by
  let C : ℝ := Real.cosh |lambda| * |lambda| ^ 4 / 24
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      evenCoshTaylorResidual lambda x ^ 2 ≤ C ^ 2 := by
    have h := abs_evenCoshTaylorResidual_le lambda x hx
    change |evenCoshTaylorResidual lambda x| ≤ C at h
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC0).2 h
  unfold evenCoshTaylorResidualMass
  calc
    (∫ x : ℝ in -1..1, evenCoshTaylorResidual lambda x ^ 2) ≤
        ∫ _x : ℝ in -1..1, C ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_evenCoshTaylorResidual lambda).pow 2
          |>.intervalIntegrable (-1) 1)
        (Continuous.intervalIntegrable continuous_const (-1) 1)
      exact hpoint
    _ = 2 * (Real.cosh |lambda| * |lambda| ^ 4 / 24) ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      dsimp only [C]
      norm_num

/-- Integrated fifth-order Taylor majorant for the odd residual. -/
theorem oddSinhTaylorResidualMass_le (lambda : ℝ) :
    oddSinhTaylorResidualMass lambda ≤
      2 * (Real.cosh |lambda| * |lambda| ^ 5 / 120) ^ 2 := by
  let C : ℝ := Real.cosh |lambda| * |lambda| ^ 5 / 120
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      oddSinhTaylorResidual lambda x ^ 2 ≤ C ^ 2 := by
    have h := abs_oddSinhTaylorResidual_le lambda x hx
    change |oddSinhTaylorResidual lambda x| ≤ C at h
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC0).2 h
  unfold oddSinhTaylorResidualMass
  calc
    (∫ x : ℝ in -1..1, oddSinhTaylorResidual lambda x ^ 2) ≤
        ∫ _x : ℝ in -1..1, C ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_oddSinhTaylorResidual lambda).pow 2
          |>.intervalIntegrable (-1) 1)
        (Continuous.intervalIntegrable continuous_const (-1) 1)
      exact hpoint
    _ = 2 * (Real.cosh |lambda| * |lambda| ^ 5 / 120) ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      dsimp only [C]
      norm_num

/-- Explicit arbitrary-rank fourth-order bound for an even `P₀/P₂`
residual. -/
theorem centeredCoshMoment_sq_le_taylor_mul_energy
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) (lambda : ℝ) :
    centeredCoshMoment e lambda ^ 2 ≤
      2 * (Real.cosh |lambda| * |lambda| ^ 4 / 24) ^ 2 *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
  have hcs := centeredCoshMoment_sq_le_residualMass_mul_energy
    e hec he0 he2 lambda
  have hmass := evenCoshTaylorResidualMass_le lambda
  have henergy : 0 ≤ ∫ x : ℝ in -1..1, e x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦ sq_nonneg (e x)
  exact hcs.trans (mul_le_mul_of_nonneg_right hmass henergy)

/-- Explicit arbitrary-rank fifth-order bound for an odd `P₁/P₃`
residual. -/
theorem centeredSinhMoment_sq_le_taylor_mul_energy
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) (lambda : ℝ) :
    centeredSinhMoment o lambda ^ 2 ≤
      2 * (Real.cosh |lambda| * |lambda| ^ 5 / 120) ^ 2 *
        (∫ x : ℝ in -1..1, o x ^ 2) := by
  have hcs := centeredSinhMoment_sq_le_residualMass_mul_energy
    o hoc ho1 ho3 lambda
  have hmass := oddSinhTaylorResidualMass_le lambda
  have henergy : 0 ≤ ∫ x : ℝ in -1..1, o x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦ sq_nonneg (o x)
  exact hcs.trans (mul_le_mul_of_nonneg_right hmass henergy)

/-! ## Arbitrary finite rank families and the genuine infinite reduction -/

/-- The exact Cauchy--Schwarz mass attached to the first `N` even ranks. -/
def factorTwoEvenResidualPartialMass (N : ℕ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        evenCoshTaylorResidualMass (yoshidaEndpointA / 2) +
      ∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          evenCoshTaylorResidualMass
            (yoshidaEndpointA * oddRate (m + 1)))

/-- The exact Cauchy--Schwarz mass attached to the first `N` odd ranks. -/
def factorTwoOddResidualPartialMass (N : ℕ) : ℝ :=
  yoshidaEndpointA *
    (Real.exp yoshidaEndpointA *
        oddSinhTaylorResidualMass (yoshidaEndpointA / 2) +
      ∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          oddSinhTaylorResidualMass
            (yoshidaEndpointA * oddRate (m + 1)))

/-- Structural residual bound for every finite initial even rank family.  The
rank cutoff is universally quantified; no particular ranks are enumerated. -/
theorem factorTwoEvenRankPartialSquares_le_residualMass_mul_energy
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) (N : ℕ) :
    yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
          ∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment e
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      factorTwoEvenResidualPartialMass N *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  have hhead := centeredCoshMoment_sq_le_residualMass_mul_energy
    e hec he0 he2 (yoshidaEndpointA / 2)
  have hhead' :
      Real.exp yoshidaEndpointA *
          centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 ≤
        Real.exp yoshidaEndpointA *
          (evenCoshTaylorResidualMass (yoshidaEndpointA / 2) * E) :=
    mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
  have htail :
      (∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredCoshMoment e
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      ∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (evenCoshTaylorResidualMass
            (yoshidaEndpointA * oddRate (m + 1)) * E) := by
    apply Finset.sum_le_sum
    intro m hm
    exact mul_le_mul_of_nonneg_left
      (centeredCoshMoment_sq_le_residualMass_mul_energy
        e hec he0 he2 (yoshidaEndpointA * oddRate (m + 1)))
      (Real.exp_pos _).le
  have hinside := add_le_add hhead' htail
  have hfactor :
      Real.exp yoshidaEndpointA *
            (evenCoshTaylorResidualMass (yoshidaEndpointA / 2) * E) +
          (∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (evenCoshTaylorResidualMass
                (yoshidaEndpointA * oddRate (m + 1)) * E)) =
        (Real.exp yoshidaEndpointA *
              evenCoshTaylorResidualMass (yoshidaEndpointA / 2) +
            ∑ m ∈ Finset.range N,
              Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
                evenCoshTaylorResidualMass
                  (yoshidaEndpointA * oddRate (m + 1))) * E := by
    calc
      _ = (Real.exp yoshidaEndpointA *
              evenCoshTaylorResidualMass (yoshidaEndpointA / 2)) * E +
            ∑ m ∈ Finset.range N,
              (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
                evenCoshTaylorResidualMass
                  (yoshidaEndpointA * oddRate (m + 1))) * E := by
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro m hm
          ring
      _ = _ := by
        rw [← Finset.sum_mul]
        ring
  rw [hfactor] at hinside
  have hscaled := mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  simpa only [factorTwoEvenResidualPartialMass, E, mul_assoc] using hscaled

/-- Structural residual bound for every finite initial odd rank family. -/
theorem factorTwoOddRankPartialSquares_le_residualMass_mul_energy
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) (N : ℕ) :
    yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2 +
          ∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment o
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      factorTwoOddResidualPartialMass N *
        (∫ x : ℝ in -1..1, o x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  have hhead := centeredSinhMoment_sq_le_residualMass_mul_energy
    o hoc ho1 ho3 (yoshidaEndpointA / 2)
  have hhead' :
      Real.exp yoshidaEndpointA *
          centeredSinhMoment o (yoshidaEndpointA / 2) ^ 2 ≤
        Real.exp yoshidaEndpointA *
          (oddSinhTaylorResidualMass (yoshidaEndpointA / 2) * E) :=
    mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
  have htail :
      (∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          centeredSinhMoment o
            (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      ∑ m ∈ Finset.range N,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (oddSinhTaylorResidualMass
            (yoshidaEndpointA * oddRate (m + 1)) * E) := by
    apply Finset.sum_le_sum
    intro m hm
    exact mul_le_mul_of_nonneg_left
      (centeredSinhMoment_sq_le_residualMass_mul_energy
        o hoc ho1 ho3 (yoshidaEndpointA * oddRate (m + 1)))
      (Real.exp_pos _).le
  have hinside := add_le_add hhead' htail
  have hfactor :
      Real.exp yoshidaEndpointA *
            (oddSinhTaylorResidualMass (yoshidaEndpointA / 2) * E) +
          (∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (oddSinhTaylorResidualMass
                (yoshidaEndpointA * oddRate (m + 1)) * E)) =
        (Real.exp yoshidaEndpointA *
              oddSinhTaylorResidualMass (yoshidaEndpointA / 2) +
            ∑ m ∈ Finset.range N,
              Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
                oddSinhTaylorResidualMass
                  (yoshidaEndpointA * oddRate (m + 1))) * E := by
    calc
      _ = (Real.exp yoshidaEndpointA *
              oddSinhTaylorResidualMass (yoshidaEndpointA / 2)) * E +
            ∑ m ∈ Finset.range N,
              (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
                oddSinhTaylorResidualMass
                  (yoshidaEndpointA * oddRate (m + 1))) * E := by
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro m hm
          ring
      _ = _ := by
        rw [← Finset.sum_mul]
        ring
  rw [hfactor] at hinside
  have hscaled := mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  simpa only [factorTwoOddResidualPartialMass, E, mul_assoc] using hscaled

/-- Exact all-rank even reduction: every moment in the genuine `tsum` is a
fourth-order Taylor residual once `P₀/P₂` vanish. -/
theorem factorTwoEvenRankEnergy_eq_taylorResidual
    (e : ℝ → ℝ) (hec : Continuous e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) :
    factorTwoEvenRankEnergy e =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            (∫ x : ℝ in -1..1,
              evenCoshTaylorResidual (yoshidaEndpointA / 2) x * e x) ^ 2 +
          ∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (∫ x : ℝ in -1..1,
                evenCoshTaylorResidual
                  (yoshidaEndpointA * oddRate (m + 1)) x * e x) ^ 2) := by
  unfold factorTwoEvenRankEnergy
  simp_rw [centeredCoshMoment_eq_evenTaylorResidual e hec he0 he2]

/-- Exact all-rank odd reduction: every moment in the genuine `tsum` is a
fifth-order Taylor residual once `P₁/P₃` vanish. -/
theorem factorTwoOddRankEnergy_eq_taylorResidual
    (o : ℝ → ℝ) (hoc : Continuous o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0) :
    factorTwoOddRankEnergy o =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            (∫ x : ℝ in -1..1,
              oddSinhTaylorResidual (yoshidaEndpointA / 2) x * o x) ^ 2 +
          ∑' m : ℕ,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              (∫ x : ℝ in -1..1,
                oddSinhTaylorResidual
                  (yoshidaEndpointA * oddRate (m + 1)) x * o x) ^ 2) := by
  unfold factorTwoOddRankEnergy
  simp_rw [centeredSinhMoment_eq_oddTaylorResidual o hoc ho1 ho3]

/-! ## Complete even-rank sharpening -/

/-- The existing infinite Schur closure handles the complete decaying even
tail, while Taylor cancellation gives a fourth-order bound for the growing
head.  This is a genuine all-rank estimate with no cutoff. -/
theorem factorTwoEvenRankEnergy_le_intrinsic_residual
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0) :
    factorTwoEvenRankEnergy e ≤
      ((Real.pi / 2 + 1 / 8 : ℝ) +
        yoshidaEndpointA * Real.exp yoshidaEndpointA *
          (2 * (Real.cosh (yoshidaEndpointA / 2) *
            (yoshidaEndpointA / 2) ^ 4 / 24) ^ 2)) *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let C : ℝ :=
    2 * (Real.cosh (yoshidaEndpointA / 2) *
      (yoshidaEndpointA / 2) ^ 4 / 24) ^ 2
  have hhead0 := centeredCoshMoment_sq_le_taylor_mul_energy
    e hec he0 he2 (yoshidaEndpointA / 2)
  have habsA : |yoshidaEndpointA / 2| = yoshidaEndpointA / 2 :=
    abs_of_pos (div_pos yoshidaEndpointA_pos (by norm_num))
  have hhead :
      centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 ≤ C * E := by
    simpa only [habsA, C, E] using hhead0
  have hheadScaled :
      yoshidaEndpointA * Real.exp yoshidaEndpointA *
          centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 ≤
        yoshidaEndpointA * Real.exp yoshidaEndpointA * (C * E) := by
    exact mul_le_mul_of_nonneg_left hhead
      (mul_nonneg yoshidaEndpointA_pos.le (Real.exp_pos _).le)
  have htail := factorTwoEvenDecayingRankTail_le_schur_energy
    e hec heven
  change factorTwoEvenDecayingRankTail e ≤
      (Real.pi / 2 + 1 / 8 : ℝ) * E at htail
  calc
    factorTwoEvenRankEnergy e =
        yoshidaEndpointA * Real.exp yoshidaEndpointA *
            centeredCoshMoment e (yoshidaEndpointA / 2) ^ 2 +
          factorTwoEvenDecayingRankTail e := by
      unfold factorTwoEvenRankEnergy factorTwoEvenDecayingRankTail
      ring
    _ ≤ yoshidaEndpointA * Real.exp yoshidaEndpointA * (C * E) +
        (Real.pi / 2 + 1 / 8 : ℝ) * E :=
      add_le_add hheadScaled htail
    _ = ((Real.pi / 2 + 1 / 8 : ℝ) +
        yoshidaEndpointA * Real.exp yoshidaEndpointA *
          (2 * (Real.cosh (yoshidaEndpointA / 2) *
            (yoshidaEndpointA / 2) ^ 4 / 24) ^ 2)) *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
      dsimp only [C, E]
      ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound
