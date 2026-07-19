import ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRawParityFoldStructural

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold
open YoshidaEndpointTriangleFoldLipschitz

noncomputable section

/-!
# Positive-half parity fold of the raw logarithmic energy

The centered square splits into two same-sign quadrants and two reflected
quadrants.  Reflection parity identifies the former pair and turns the latter
pair into a nonsingular `1 / (x + y)` form on `[0,1]^2`.  Lipschitz regularity
supplies the genuine product integrability needed for the decomposition.
-/

/-- Raw same-sign logarithmic energy on the positive half square. -/
def fourCellPositiveHalfRawSameSignEnergy (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
    (w x - w y) ^ 2 / |x - y|

/-- Reflected raw energy on the positive half square.  Reflection sign `1`
is the even channel and reflection sign `-1` is the odd channel. -/
def fourCellPositiveHalfRawReflectedEnergy
    (w : ℝ → ℝ) (reflectionSign : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
    (w x - reflectionSign * w y) ^ 2 / (x + y)

private theorem intervalIntegral_integral_zero_one_eq_setIntegral
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F p := by
  calc
    (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, F (x, y)) =
        ∫ x : ℝ in Icc (0 : ℝ) 1,
          ∫ y : ℝ in Icc (0 : ℝ) 1, F (x, y) := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in 0..1, F (x, y)) =
        ∫ y : ℝ in Icc (0 : ℝ) 1, F (x, y)
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          F p := by
      exact (setIntegral_prod F hF).symm

private theorem centeredRawLogEnergy_eq_setIntegral
    (w : ℝ → ℝ)
    (henergy : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    centeredRawLogEnergy w =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        centeredLogDifferenceKernel w p.1 p.2 := by
  unfold centeredRawLogEnergy centeredLogDifferenceKernel
  calc
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
        (w x - w y) ^ 2 / |x - y|) =
        ∫ x : ℝ in Icc (-1 : ℝ) 1,
          ∫ y : ℝ in Icc (-1 : ℝ) 1,
            (w x - w y) ^ 2 / |x - y| := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in -1..1, (w x - w y) ^ 2 / |x - y|) =
        ∫ y : ℝ in Icc (-1 : ℝ) 1,
          (w x - w y) ^ 2 / |x - y|
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
          (w p.1 - w p.2) ^ 2 / |p.1 - p.2| := by
      exact (setIntegral_prod _ henergy).symm

private theorem setIntegral_centeredSquare_eq_quadrants
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, F p) =
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 0, F p) +
      (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 0 ×ˢ Ioc (0 : ℝ) 1, F p) +
      (∫ p : ℝ × ℝ in Ioc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0, F p) +
      (∫ p : ℝ × ℝ in Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1, F p) := by
  let S : Set ℝ := Icc (-1 : ℝ) 1
  let L : Set ℝ := Icc (-1 : ℝ) 0
  let R : Set ℝ := Ioc (0 : ℝ) 1
  have hS : S = L ∪ R := by
    ext x
    simp only [S, L, R, mem_Icc, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases hx0 : x ≤ 0
      · exact Or.inl ⟨hx.1, hx0⟩
      · exact Or.inr ⟨lt_of_not_ge hx0, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans (by norm_num)⟩
      · exact ⟨(by linarith [hx.1]), hx.2⟩
  have hLmeas : MeasurableSet L := measurableSet_Icc
  have hRmeas : MeasurableSet R := measurableSet_Ioc
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hLR : Disjoint L R := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    exact (not_lt_of_ge hxL.2) hxR.1
  have hLsub : L ⊆ S := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hRsub : R ⊆ S := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hLS : IntegrableOn F (L ×ˢ S)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hLsub (Subset.rfl))
  have hRS : IntegrableOn F (R ×ˢ S)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hRsub (Subset.rfl))
  have hLL : IntegrableOn F (L ×ˢ L)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hLsub hLsub)
  have hLRint : IntegrableOn F (L ×ˢ R)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hLsub hRsub)
  have hRLint : IntegrableOn F (R ×ˢ L)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hRsub hLsub)
  have hRR : IntegrableOn F (R ×ˢ R)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hRsub hRsub)
  have houter :
      (∫ p : ℝ × ℝ in S ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in L ×ˢ S, F p) +
          ∫ p : ℝ × ℝ in R ×ˢ S, F p := by
    rw [show S ×ˢ S = (L ×ˢ S) ∪ (R ×ˢ S) by
      rw [hS, union_prod]]
    exact setIntegral_union (hLR.set_prod_left S S)
      (hRmeas.prod hSmeas) hLS hRS
  have hleft :
      (∫ p : ℝ × ℝ in L ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in L ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in L ×ˢ R, F p := by
    rw [show L ×ˢ S = (L ×ˢ L) ∪ (L ×ˢ R) by
      rw [hS, prod_union]]
    exact setIntegral_union (hLR.set_prod_right L L)
      (hLmeas.prod hRmeas) hLL hLRint
  have hright :
      (∫ p : ℝ × ℝ in R ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in R ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in R ×ˢ R, F p := by
    rw [show R ×ˢ S = (R ×ˢ L) ∪ (R ×ˢ R) by
      rw [hS, prod_union]]
    exact setIntegral_union (hLR.set_prod_right R R)
      (hRmeas.prod hRmeas) hRLint hRR
  calc
    (∫ p : ℝ × ℝ in S ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in L ×ˢ S, F p) +
          ∫ p : ℝ × ℝ in R ×ˢ S, F p := houter
    _ = ((∫ p : ℝ × ℝ in L ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in L ×ˢ R, F p) +
        ((∫ p : ℝ × ℝ in R ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in R ×ˢ R, F p) := by
      rw [hleft, hright]
    _ = _ := by ring

private theorem centeredLogDifferenceKernel_swap
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    centeredLogDifferenceKernel w p.swap.1 p.swap.2 =
      centeredLogDifferenceKernel w p.1 p.2 := by
  rcases p with ⟨x, y⟩
  unfold centeredLogDifferenceKernel
  simp only [Prod.swap_prod_mk]
  rw [abs_sub_comm]
  ring

private theorem centeredRawLogEnergy_parityFold
    (w : ℝ → ℝ) (reflectionSign : ℝ)
    (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hreflect : ∀ x : ℝ, w (-x) = reflectionSign * w x)
    (hsign : reflectionSign ^ 2 = 1) :
    centeredRawLogEnergy w / 4 =
      (1 / 2 : ℝ) *
        (fourCellPositiveHalfRawSameSignEnergy w +
          fourCellPositiveHalfRawReflectedEnergy w reflectionSign) := by
  obtain ⟨C, hC⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 - reflectionSign * w p.2) ^ 2 / (p.1 + p.2)
  let S : Set ℝ := Icc (-1 : ℝ) 1
  let L : Set ℝ := Icc (-1 : ℝ) 0
  let R : Set ℝ := Ioc (0 : ℝ) 1
  let P : Set ℝ := Icc (0 : ℝ) 1
  let negNeg : ℝ × ℝ → ℝ × ℝ := fun p ↦ (-p.1, -p.2)
  let negFst : ℝ × ℝ → ℝ × ℝ := fun p ↦ (-p.1, p.2)
  have henergy : IntegrableOn K (S ×ˢ S)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K, S] using
      integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hLsub : L ⊆ S := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hPsub : P ⊆ S := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hLP : IntegrableOn K (L ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    henergy.mono_set (Set.prod_mono hLsub hPsub)
  have hPP : IntegrableOn K (P ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    henergy.mono_set (Set.prod_mono hPsub hPsub)
  have hnegNegMP : MeasurePreserving negNeg
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [negNeg, Prod.map_apply] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hnegNegEmb : MeasurableEmbedding negNeg := by
    simpa only [negNeg, Prod.map_apply] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ)
        (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hnegFstMP : MeasurePreserving negFst
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [negFst, Prod.map_apply, id_eq] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
  have hnegFstEmb : MeasurableEmbedding negFst := by
    simpa only [negFst, Prod.map_apply, id_eq] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ)
        (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have hnegNegPre : negNeg ⁻¹' (P ×ˢ P) = L ×ˢ L := by
    ext p
    simp only [negNeg, preimage, mem_prod]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hy0, hy1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨hx1, hx0⟩, hy1, hy0⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hnegFstPre : negFst ⁻¹' (P ×ˢ P) = L ×ˢ P := by
    ext p
    simp only [negFst, preimage, mem_prod]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · rintro ⟨⟨hx1, hx0⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
  have hKnegNeg (p : ℝ × ℝ) : K (negNeg p) = K p := by
    dsimp only [K, negNeg]
    unfold centeredLogDifferenceKernel
    rw [hreflect, hreflect]
    rw [show -p.1 - -p.2 = -(p.1 - p.2) by ring, abs_neg]
    rw [show (reflectionSign * w p.1 - reflectionSign * w p.2) ^ 2 =
        reflectionSign ^ 2 * (w p.1 - w p.2) ^ 2 by ring,
      hsign, one_mul]
  have hLL_eq_PP :
      (∫ p : ℝ × ℝ in L ×ˢ L, K p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, K p := by
    calc
      (∫ p : ℝ × ℝ in L ×ˢ L, K p) =
          ∫ p : ℝ × ℝ in L ×ˢ L, K (negNeg p) := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p _hp
        exact (hKnegNeg p).symm
      _ = ∫ p : ℝ × ℝ in P ×ˢ P, K p := by
        rw [← hnegNegPre]
        exact hnegNegMP.setIntegral_preimage_emb hnegNegEmb K (P ×ˢ P)
  have hJcomp_eq_K : Set.EqOn (fun p ↦ J (negFst p)) K (L ×ˢ P) := by
    intro p hp
    dsimp only [J, K, negFst]
    unfold centeredLogDifferenceKernel
    rw [hreflect]
    have hden : |p.1 - p.2| = -p.1 + p.2 := by
      rw [abs_of_nonpos (by linarith [hp.1.2, hp.2.1])]
      ring
    rw [hden]
    rw [show (reflectionSign * w p.1 - reflectionSign * w p.2) ^ 2 =
        reflectionSign ^ 2 * (w p.1 - w p.2) ^ 2 by ring,
      hsign, one_mul]
  have hJcompInt : IntegrableOn (fun p ↦ J (negFst p)) (L ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    hLP.congr_fun hJcomp_eq_K.symm
      (measurableSet_Icc.prod measurableSet_Icc)
  have hJPP : IntegrableOn J (P ×ˢ P)
      ((volume : Measure ℝ).prod volume) := by
    rw [← hnegFstMP.integrableOn_comp_preimage hnegFstEmb, hnegFstPre]
    exact hJcompInt
  have hLRae : L ×ˢ R =ᵐ[((volume : Measure ℝ).prod volume)] L ×ˢ P := by
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl)
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hRRae : R ×ˢ R =ᵐ[((volume : Measure ℝ).prod volume)] P ×ˢ P := by
    exact Measure.set_prod_ae_eq
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hLR_eq_J :
      (∫ p : ℝ × ℝ in L ×ˢ R, K p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
    calc
      (∫ p : ℝ × ℝ in L ×ˢ R, K p) =
          ∫ p : ℝ × ℝ in L ×ˢ P, K p :=
        setIntegral_congr_set hLRae
      _ = ∫ p : ℝ × ℝ in L ×ˢ P, J (negFst p) := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p hp
        exact (hJcomp_eq_K hp).symm
      _ = ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
        rw [← hnegFstPre]
        exact hnegFstMP.setIntegral_preimage_emb hnegFstEmb J (P ×ˢ P)
  have hRL_eq_LR :
      (∫ p : ℝ × ℝ in R ×ˢ L, K p) =
        ∫ p : ℝ × ℝ in L ×ˢ R, K p := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) L R K
    calc
      (∫ p : ℝ × ℝ in R ×ˢ L, K p) =
          ∫ p : ℝ × ℝ in R ×ˢ L, K p.swap := by
        apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Icc)
        intro p _hp
        exact (centeredLogDifferenceKernel_swap w p).symm
      _ = ∫ p : ℝ × ℝ in L ×ˢ R, K p := hswap
  have hRR_eq_PP :
      (∫ p : ℝ × ℝ in R ×ˢ R, K p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, K p :=
    setIntegral_congr_set hRRae
  have hquadrants := setIntegral_centeredSquare_eq_quadrants K henergy
  have hraw := centeredRawLogEnergy_eq_setIntegral w henergy
  have hsame : fourCellPositiveHalfRawSameSignEnergy w =
      ∫ p : ℝ × ℝ in P ×ˢ P, K p := by
    unfold fourCellPositiveHalfRawSameSignEnergy
    simpa only [P, K, centeredLogDifferenceKernel] using
      intervalIntegral_integral_zero_one_eq_setIntegral K hPP
  have hreflected : fourCellPositiveHalfRawReflectedEnergy w reflectionSign =
      ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
    unfold fourCellPositiveHalfRawReflectedEnergy
    simpa only [P, J] using
      intervalIntegral_integral_zero_one_eq_setIntegral J hJPP
  rw [hraw, hquadrants, hLL_eq_PP, hRL_eq_LR, hLR_eq_J, hRR_eq_PP,
    hsame, hreflected]
  ring

/-- For an even Lipschitz profile, one quarter of the centered raw energy is
one half of the positive-half same-sign energy plus the reflected difference
energy with denominator `x + y`. -/
theorem centeredRawLogEnergy_div_four_eq_positiveHalf_even
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    centeredRawLogEnergy w / 4 =
      (1 / 2 : ℝ) *
        (fourCellPositiveHalfRawSameSignEnergy w +
          fourCellPositiveHalfRawReflectedEnergy w 1) := by
  apply centeredRawLogEnergy_parityFold w 1 hw
  · intro x
    simpa using heven x
  · norm_num

/-- For an odd Lipschitz profile, one quarter of the centered raw energy is
one half of the positive-half same-sign energy plus the reflected sum energy
with denominator `x + y`. -/
theorem centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w) :
    centeredRawLogEnergy w / 4 =
      (1 / 2 : ℝ) *
        (fourCellPositiveHalfRawSameSignEnergy w +
          fourCellPositiveHalfRawReflectedEnergy w (-1)) := by
  apply centeredRawLogEnergy_parityFold w (-1) hw
  · intro x
    rw [hodd]
    ring
  · norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellRawParityFoldStructural
