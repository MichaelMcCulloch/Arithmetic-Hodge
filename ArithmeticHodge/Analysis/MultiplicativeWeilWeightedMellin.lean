/-
  Real-space forms of Bombieri's weighted Mellin atoms.

  Splitting the Mellin integral at `1` and applying multiplicative inversion
  identifies each Cauchy-weighted atom with the direct-plus-transpose kernel
  used in Bombieri's archimedean series.  The ordinary inverse-power form is
  chosen so the subsequent sum over `m` is geometric.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilGammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def weightedAtomIntegrand
    (f : BombieriTest) (m : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    bombieriCauchyWeight f (2 * m + 1 / 2) x

private theorem real_rpow_atom_eq_inv_pow
    (m : ℕ) (x : ℝ) :
    ((x ^ (-(2 * m + 1 : ℝ)) : ℝ) : ℂ) =
      ((x : ℂ)⁻¹) ^ (2 * m + 1) := by
  rw [show -(2 * (m : ℝ) + 1) = -((2 * m + 1 : ℕ) : ℝ) by
    push_cast
    ring]
  rw [Real.rpow_neg_natCast]
  rw [zpow_neg, inv_pow]
  norm_cast

private theorem weightedAtomIntegrand_eq_inv_pow_mul
    (f : BombieriTest) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    weightedAtomIntegrand f m x =
      ((x : ℂ)⁻¹) ^ (2 * m + 1) * f x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [weightedAtomIntegrand,
    bombieriCauchyWeight_apply_of_pos f (2 * m + 1 / 2) hx0]
  simp only [Complex.real_smul]
  have hmin : min x x⁻¹ = x⁻¹ := by
    apply min_eq_right
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hx0).2 (by nlinarith [hx])
  rw [hmin]
  rw [show ((1 / 2 : ℂ) - 1) = ((-1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hx0.le]
  rw [← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le,
    ← Real.rpow_add hx0]
  rw [show (-1 / 2 : ℝ) + -(2 * (m : ℝ) + 1 / 2) =
      -(2 * m + 1 : ℝ) by ring]
  exact real_rpow_atom_eq_inv_pow m x

private theorem mellin_bombieriCauchyWeight_eq_weightedAtomIntegral
    (f : BombieriTest) (m : ℕ) :
    mellin (bombieriCauchyWeight f (2 * m + 1 / 2)) (1 / 2 : ℝ) =
      ∫ x : ℝ in Ioi 0, weightedAtomIntegrand f m x := by
  unfold mellin weightedAtomIntegrand
  simp only [smul_eq_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
  congr 2
  norm_num

private theorem weightedAtomIntegrand_integrableOn_Ioi_zero
    (f : BombieriTest) (m : ℕ) :
    IntegrableOn (weightedAtomIntegrand f m) (Ioi 0) := by
  have hconv := bombieriCauchyWeight_mellinConvergent
    f (2 * m + 1 / 2) (1 / 2 : ℝ)
  change IntegrableOn (fun x : ℝ ↦
    (x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ)) - 1) *
      bombieriCauchyWeight f (2 * m + 1 / 2) x) (Ioi 0) at hconv
  refine hconv.congr_fun ?_ measurableSet_Ioi
  intro x _
  unfold weightedAtomIntegrand
  norm_num

private theorem integral_Ioc_zero_one_eq_integral_Ioi_one_inv
    (H : ℝ → ℂ) :
    (∫ y : ℝ in Ioc 0 1, H y) =
      ∫ x : ℝ in Ioi 1, x ^ (-2 : ℝ) • H x⁻¹ := by
  let g : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator H
  have hchange := MeasureTheory.integral_comp_rpow_Ioi
    g (p := (-1 : ℝ)) (by norm_num)
  have hright : (∫ y : ℝ in Ioi 0, g y) = ∫ y : ℝ in Ioc 0 1, H y := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Ioc (0 : ℝ) 1
    · have hy0 : y ∈ Ioi (0 : ℝ) := hy.1
      simp [g, hy, hy0]
    · simp [g, hy]
  have hleft :
      (∫ x : ℝ in Ioi 0,
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x : ℝ in Ioi 1, x ^ (-2 : ℝ) • H x⁻¹ := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with x hx1
    by_cases hx0 : 0 < x
    · rw [show (-1 : ℝ) - 1 = (-2 : ℝ) by norm_num]
      by_cases hx : 1 < x
      · have hinvpos : 0 < x⁻¹ := inv_pos.mpr hx0
        have hinvle : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx.le
        simp [g, hx0, hx, hinvpos, hinvle, Real.rpow_neg_one]
      · have hxlt : x < 1 := lt_of_le_of_ne (le_of_not_gt hx) hx1
        have hinvgt : 1 < x⁻¹ := (one_lt_inv₀ hx0).2 hxlt
        have hinvnotle : ¬ x⁻¹ ≤ 1 := not_le.mpr hinvgt
        simp [g, hx0, hx, hinvnotle, Real.rpow_neg_one]
    · have hxnot0 : ¬ x ∈ Ioi (0 : ℝ) := hx0
      have hxnot1 : ¬ x ∈ Ioi (1 : ℝ) := by
        intro hx
        exact hx0 (zero_lt_one.trans hx)
      simp [hxnot0, hxnot1]
  rw [← hright, ← hleft]
  exact hchange.symm

private theorem weightedAtomIntegrand_inv_jacobian_eq
    (f : BombieriTest) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    x ^ (-2 : ℝ) • weightedAtomIntegrand f m x⁻¹ =
      ((x : ℂ)⁻¹) ^ (2 * m + 1) * transpose (f : ℝ → ℂ) x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hy1 : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx.le
  rw [weightedAtomIntegrand,
    bombieriCauchyWeight_apply_of_pos f (2 * m + 1 / 2) hy0,
    transpose_apply_of_pos _ hx0]
  simp only [Complex.real_smul]
  have hmin : min x⁻¹ (x⁻¹)⁻¹ = x⁻¹ := by
    apply min_eq_left
    simpa using hy1.trans hx.le
  rw [hmin]
  rw [show ((1 / 2 : ℂ) - 1) = ((-1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hy0.le]
  change ((x ^ (-2 : ℝ) : ℝ) : ℂ) *
      (((x⁻¹ ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (((x⁻¹ ^ (2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * f x⁻¹)) =
    ((x : ℂ)⁻¹) ^ (2 * m + 1) * (f x⁻¹ / (x : ℂ))
  have hreal :
      x ^ (-2 : ℝ) *
          (x⁻¹ ^ (-1 / 2 : ℝ) * x⁻¹ ^ (2 * (m : ℝ) + 1 / 2)) =
        x ^ (-(2 * (m : ℝ) + 2)) := by
    calc
      x ^ (-2 : ℝ) *
          (x⁻¹ ^ (-1 / 2 : ℝ) * x⁻¹ ^ (2 * (m : ℝ) + 1 / 2)) =
          x ^ (-2 : ℝ) * x⁻¹ ^ (2 * (m : ℝ)) := by
        rw [← Real.rpow_add hy0]
        congr 2
        ring
      _ = x ^ (-2 : ℝ) * x ^ (-(2 * (m : ℝ))) := by
        rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
      _ = x ^ (-(2 * (m : ℝ) + 2)) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
  have hcomplex :
      ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) =
        ((x : ℂ)⁻¹) ^ (2 * m + 1) * (x : ℂ)⁻¹ := by
    rw [show -(2 * (m : ℝ) + 2) =
        -(2 * (m : ℝ) + 1) + (-1 : ℝ) by ring]
    rw [Real.rpow_add hx0, Complex.ofReal_mul,
      real_rpow_atom_eq_inv_pow m x,
      Real.rpow_neg_one]
    push_cast
    rfl
  have hscalar :
      ((x ^ (-2 : ℝ) : ℝ) : ℂ) *
          (((x⁻¹ ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
            ((x⁻¹ ^ (2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ)) =
        ((x : ℂ)⁻¹) ^ (2 * m + 1) * (x : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal]
    exact hcomplex
  rw [div_eq_mul_inv]
  calc
    _ = (((x ^ (-2 : ℝ) : ℝ) : ℂ) *
          (((x⁻¹ ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
            ((x⁻¹ ^ (2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ))) * f x⁻¹ := by
      ring_nf
    _ = (((x : ℂ)⁻¹) ^ (2 * m + 1) * (x : ℂ)⁻¹) * f x⁻¹ := by
      rw [hscalar]
    _ = _ := by ring

private theorem complex_cpow_atom_eq_inv_pow
    (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((-(2 * (m : ℝ)) : ℝ) - 1 : ℂ) =
      ((x : ℂ)⁻¹) ^ (2 * m + 1) := by
  rw [show ((-(2 * (m : ℝ)) : ℝ) - 1 : ℂ) =
      (-(2 * (m : ℝ) + 1) : ℝ) by push_cast; ring]
  rw [← Complex.ofReal_cpow hx.le]
  exact real_rpow_atom_eq_inv_pow m x

private theorem weightedAtom_direct_integrableOn
    (f : BombieriTest) (m : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      ((x : ℂ)⁻¹) ^ (2 * m + 1) * f x) (Ioi 1) := by
  have hH := weightedAtomIntegrand_integrableOn_Ioi_zero f m
  refine (hH.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun ?_
    measurableSet_Ioi
  intro x hx
  exact weightedAtomIntegrand_eq_inv_pow_mul f m hx

private theorem weightedAtom_transpose_integrableOn
    (f : BombieriTest) (m : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      ((x : ℂ)⁻¹) ^ (2 * m + 1) * transpose (f : ℝ → ℂ) x) (Ioi 1) := by
  have hconv := (transposeLinearMap f).mellinConvergent
    ((-(2 * (m : ℝ)) : ℝ) : ℂ)
  have ht : IntegrableOn (fun x : ℝ ↦
      (x : ℂ) ^ (((-(2 * (m : ℝ)) : ℝ) : ℂ) - 1) *
        transposeLinearMap f x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hconv
  refine (ht.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun ?_
    measurableSet_Ioi
  intro x hx
  change (x : ℂ) ^ (((-(2 * (m : ℝ)) : ℝ) : ℂ) - 1) *
      transposeLinearMap f x =
    ((x : ℂ)⁻¹) ^ (2 * m + 1) * transpose (f : ℝ → ℂ) x
  rw [transposeLinearMap_apply, complex_cpow_atom_eq_inv_pow m
    (zero_lt_one.trans hx)]

/-- The inverse-power real-space atom is genuinely integrable on `(1, ∞)`. -/
theorem bombieriWeightedMellinAtom_realSpace_integrableOn
    (f : BombieriTest) (m : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      ((x : ℂ)⁻¹) ^ (2 * m + 1) *
        (f x + transpose (f : ℝ → ℂ) x)) (Ioi 1) := by
  have hd := weightedAtom_direct_integrableOn f m
  have ht := weightedAtom_transpose_integrableOn f m
  refine (hd.add ht).congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [Pi.add_apply]
  ring

/-- A weighted critical-line Mellin atom equals its direct-plus-transpose
real-space integral, in the ordinary inverse-power form used in Bombieri's
geometric summation. -/
theorem bombieriWeightedMellinAtom_eq_realSpace
    (f : BombieriTest) (m : ℕ) :
    mellin (bombieriCauchyWeight f (2 * m + 1 / 2)) (1 / 2 : ℝ) =
      ∫ x : ℝ in Ioi 1,
        ((x : ℂ)⁻¹) ^ (2 * m + 1) *
          (f x + transpose (f : ℝ → ℂ) x) := by
  have hH := weightedAtomIntegrand_integrableOn_Ioi_zero f m
  have hlow : IntegrableOn (weightedAtomIntegrand f m) (Ioc (0 : ℝ) 1) :=
    hH.mono_set Ioc_subset_Ioi_self
  have hhigh : IntegrableOn (weightedAtomIntegrand f m) (Ioi 1) :=
    hH.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  rw [mellin_bombieriCauchyWeight_eq_weightedAtomIntegral]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlow hhigh]
  rw [integral_Ioc_zero_one_eq_integral_Ioi_one_inv]
  have hinv :
      (∫ x : ℝ in Ioi 1,
          x ^ (-2 : ℝ) • weightedAtomIntegrand f m x⁻¹) =
        ∫ x : ℝ in Ioi 1,
          ((x : ℂ)⁻¹) ^ (2 * m + 1) *
            transpose (f : ℝ → ℂ) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact weightedAtomIntegrand_inv_jacobian_eq f m hx
  have hdir :
      (∫ x : ℝ in Ioi 1, weightedAtomIntegrand f m x) =
        ∫ x : ℝ in Ioi 1,
          ((x : ℂ)⁻¹) ^ (2 * m + 1) * f x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact weightedAtomIntegrand_eq_inv_pow_mul f m hx
  rw [hinv, hdir]
  rw [← MeasureTheory.integral_add
    (weightedAtom_transpose_integrableOn f m)
    (weightedAtom_direct_integrableOn f m)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  ring

private def weightedAtomCorrection
    (f : BombieriTest) (m : ℕ) (x : ℝ) : ℂ :=
  ((x : ℂ)⁻¹) ^ (2 * m + 1) * ((2 / (x : ℂ)) * f 1)

private theorem weightedAtomCorrection_eq_rpow
    (f : BombieriTest) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    weightedAtomCorrection f m x =
      ((2 : ℂ) * f 1) * ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) := by
  have hcomplex :
      ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) =
        ((x : ℂ)⁻¹) ^ (2 * m + 1) * (x : ℂ)⁻¹ := by
    rw [show -(2 * (m : ℝ) + 2) =
        -(2 * (m : ℝ) + 1) + (-1 : ℝ) by ring]
    rw [Real.rpow_add hx, Complex.ofReal_mul,
      real_rpow_atom_eq_inv_pow m x, Real.rpow_neg_one]
    push_cast
    rfl
  rw [weightedAtomCorrection, div_eq_mul_inv, hcomplex]
  ring

private theorem weightedAtomCorrection_integrableOn
    (f : BombieriTest) (m : ℕ) :
    IntegrableOn (weightedAtomCorrection f m) (Ioi 1) := by
  have ha : -(2 * (m : ℝ) + 2) < -1 := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hbase := integrableOn_Ioi_rpow_of_lt ha (by norm_num : (0 : ℝ) < 1)
  have hcomplex : IntegrableOn (fun x : ℝ ↦
      ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ)) (Ioi 1) :=
    hbase.ofReal
  refine (hcomplex.const_mul ((2 : ℂ) * f 1)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (weightedAtomCorrection_eq_rpow f m (zero_lt_one.trans hx)).symm

private theorem weightedAtomCorrection_integral
    (f : BombieriTest) (m : ℕ) :
    (∫ x : ℝ in Ioi 1, weightedAtomCorrection f m x) =
      ((2 : ℂ) / (((2 * m + 1 : ℕ) : ℝ) : ℂ)) * f 1 := by
  have ha : -(2 * (m : ℝ) + 2) < -1 := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  calc
    (∫ x : ℝ in Ioi 1, weightedAtomCorrection f m x) =
        ∫ x : ℝ in Ioi 1,
          ((2 : ℂ) * f 1) *
            ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact weightedAtomCorrection_eq_rpow f m (zero_lt_one.trans hx)
    _ = ((2 : ℂ) * f 1) *
          ∫ x : ℝ in Ioi 1,
            ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Ioi 1)) ((2 : ℂ) * f 1) _
    _ = ((2 : ℂ) * f 1) *
          ((∫ x : ℝ in Ioi 1, x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) := by
      rw [show (∫ x : ℝ in Ioi 1,
            ((x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ)) =
          ((∫ x : ℝ in Ioi 1, x ^ (-(2 * (m : ℝ) + 2)) : ℝ) : ℂ) by
        exact integral_complex_ofReal]
    _ = ((2 : ℂ) * f 1) *
          ((-((1 : ℝ) ^ (-(2 * (m : ℝ) + 2) + 1)) /
            (-(2 * (m : ℝ) + 2) + 1) : ℝ) : ℂ) := by
      rw [integral_Ioi_rpow_of_lt ha (by norm_num : (0 : ℝ) < 1)]
    _ = ((2 : ℂ) / (((2 * m + 1 : ℕ) : ℝ) : ℂ)) * f 1 := by
      simp only [Real.one_rpow]
      have hdenR : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
      have hscalarR :
          (-1 : ℝ) / (-(2 * (m : ℝ) + 2) + 1) =
            (2 * (m : ℝ) + 1)⁻¹ := by
        rw [show -(2 * (m : ℝ) + 2) + 1 =
            (-1 : ℝ) + -(2 * (m : ℝ)) by ring]
        rw [show (-1 : ℝ) + -(2 * (m : ℝ)) =
            -(2 * (m : ℝ) + 1) by ring]
        field_simp [hdenR]
      rw [hscalarR]
      push_cast
      ring

/-- Subtracting the normalized value at `1` moves inside the integral as
Bombieri's bracket `f(x) + f*(x) - 2f(1)/x`. -/
theorem bombieriWeightedMellinAtom_sub_eq_realSpace
    (f : BombieriTest) (m : ℕ) :
    mellin (bombieriCauchyWeight f (2 * m + 1 / 2)) (1 / 2 : ℝ) -
        ((2 : ℂ) / (((2 * m + 1 : ℕ) : ℝ) : ℂ)) * f 1 =
      ∫ x : ℝ in Ioi 1,
        ((x : ℂ)⁻¹) ^ (2 * m + 1) *
          (f x + transpose (f : ℝ → ℂ) x - (2 / (x : ℂ)) * f 1) := by
  rw [bombieriWeightedMellinAtom_eq_realSpace,
    ← weightedAtomCorrection_integral f m]
  rw [← MeasureTheory.integral_sub
    (bombieriWeightedMellinAtom_realSpace_integrableOn f m)
    (weightedAtomCorrection_integrableOn f m)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  unfold weightedAtomCorrection
  ring


end

end ArithmeticHodge.Analysis.MultiplicativeWeil

