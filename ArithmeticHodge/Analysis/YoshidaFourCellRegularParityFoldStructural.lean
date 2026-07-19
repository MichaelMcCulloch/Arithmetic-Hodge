import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelSquareStructural
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRegularParityFoldStructural

open CenteredEndpointCorrelation
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaRegularKernelBound

noncomputable section

/-!
# Positive-half parity completion of the regular kernel

The full centered regular-kernel product first folds by reflection parity.
On the positive half-square it then admits an exact square completion.  The
mass term below is written symmetrically in the two variables; this is the
exact row-potential mass because the half-square kernel is swap invariant.
-/

/-- Same-sign regular-kernel square on the positive half-square. -/
def fourCellPositiveHalfRegularSameSignSquare
    (w : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    yoshidaRegularKernel (a * |p.1 - p.2|) * (w p.1 - w p.2) ^ 2

/-- Reflected regular-kernel square on the positive half-square.  Reflection
sign `1` gives the even difference square and sign `-1` the odd sum square. -/
def fourCellPositiveHalfRegularReflectedSquare
    (w : ℝ → ℝ) (a reflectionSign : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    yoshidaRegularKernel (a * (p.1 + p.2)) *
      (w p.1 - reflectionSign * w p.2) ^ 2

/-- Exact positive-half regular-kernel row-potential mass.  The symmetric
presentation is pointwise suited to square completion and equals either
one-sided row presentation by swap invariance. -/
def fourCellPositiveHalfRegularRowMass
    (w : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    (yoshidaRegularKernel (a * |p.1 - p.2|) +
        yoshidaRegularKernel (a * (p.1 + p.2))) *
      ((w p.1 ^ 2 + w p.2 ^ 2) / 2)

/-- The positive-half product before square completion. -/
private def fourCellPositiveHalfRegularProduct
    (w : ℝ → ℝ) (a reflectionSign : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    (yoshidaRegularKernel (a * |p.1 - p.2|) +
        reflectionSign * yoshidaRegularKernel (a * (p.1 + p.2))) *
      w p.1 * w p.2

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
      · exact ⟨by linarith [hx.1], hx.2⟩
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
    rw [show S ×ˢ S = (L ×ˢ S) ∪ (R ×ˢ S) by rw [hS, union_prod]]
    exact setIntegral_union (hLR.set_prod_left S S)
      (hRmeas.prod hSmeas) hLS hRS
  have hleft :
      (∫ p : ℝ × ℝ in L ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in L ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in L ×ˢ R, F p := by
    rw [show L ×ˢ S = (L ×ˢ L) ∪ (L ×ˢ R) by rw [hS, prod_union]]
    exact setIntegral_union (hLR.set_prod_right L L)
      (hLmeas.prod hRmeas) hLL hLRint
  have hright :
      (∫ p : ℝ × ℝ in R ×ˢ S, F p) =
        (∫ p : ℝ × ℝ in R ×ˢ L, F p) +
          ∫ p : ℝ × ℝ in R ×ˢ R, F p := by
    rw [show R ×ˢ S = (R ×ˢ L) ∪ (R ×ˢ R) by rw [hS, prod_union]]
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

private theorem setIntegral_centeredSquare_eq_iterated_of_integrable
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, F p) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, F (y, x) := by
  symm
  calc
    (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, F (y, x)) =
        ∫ y : ℝ in Icc (-1) 1,
          ∫ x : ℝ in Icc (-1) 1, F (y, x) := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _hy
      change (∫ x : ℝ in -1..1, F (y, x)) =
        ∫ x : ℝ in Icc (-1) 1, F (y, x)
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, F p :=
      (setIntegral_prod F hF).symm

private theorem centeredRegularProduct_parityFold
    (w : ℝ → ℝ) (hw : Continuous w) (a reflectionSign : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2)
    (hreflect : ∀ x : ℝ, w (-x) = reflectionSign * w x)
    (hsign : reflectionSign ^ 2 = 1) :
    (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
        yoshidaRegularKernel (a * |y - x|) * w y * w x) =
      2 * fourCellPositiveHalfRegularProduct w a reflectionSign := by
  let F : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel (a * |p.1 - p.2|) * w p.1 * w p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    reflectionSign * yoshidaRegularKernel (a * (p.1 + p.2)) *
      w p.1 * w p.2
  let S : Set ℝ := Icc (-1 : ℝ) 1
  let L : Set ℝ := Icc (-1 : ℝ) 0
  let R : Set ℝ := Ioc (0 : ℝ) 1
  let P : Set ℝ := Icc (0 : ℝ) 1
  let negNeg : ℝ × ℝ → ℝ × ℝ := fun p ↦ (-p.1, -p.2)
  let negFst : ℝ × ℝ → ℝ × ℝ := fun p ↦ (-p.1, p.2)
  have hregularMeas : Measurable yoshidaRegularKernel :=
    measurable_yoshidaRegularKernel
  have hFMeas : Measurable F := by
    dsimp only [F]
    exact ((hregularMeas.comp
      (measurable_const.mul ((measurable_fst.sub measurable_snd).abs))).mul
        (hw.measurable.comp measurable_fst)).mul
          (hw.measurable.comp measurable_snd)
  let g : ℝ × ℝ → ℝ := fun p ↦
    (1 / 4 : ℝ) * |w p.1| * |w p.2|
  have hgSquare : IntegrableOn g (S ×ˢ S)
      ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact ((continuous_const.mul (hw.comp continuous_fst).abs).mul
      (hw.comp continuous_snd).abs).continuousOn
  have hF : IntegrableOn F (S ×ˢ S)
      ((volume : Measure ℝ).prod volume) := by
    apply hgSquare.mono'
    · exact hFMeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem
          (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      have hdiff : |p.1 - p.2| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      have harg0 : 0 ≤ a * |p.1 - p.2| :=
        mul_nonneg ha0 (abs_nonneg _)
      have harg3 : a * |p.1 - p.2| ≤ Real.log 3 := by
        have hat := mul_le_mul_of_nonneg_left hdiff ha0
        linarith
      have hnonneg :=
        yoshidaRegularKernel_nonneg_of_le_log_three harg0 harg3
      have hupper := yoshidaRegularKernel_le_quarter harg0
      dsimp only [F, g]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hupper (abs_nonneg (w p.1)))
        (abs_nonneg (w p.2))
  have hLsub : L ⊆ S := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hPsub : P ⊆ S := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hLP : IntegrableOn F (L ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hLsub hPsub)
  have hPP : IntegrableOn F (P ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    hF.mono_set (Set.prod_mono hPsub hPsub)
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
  have hFnegNeg (p : ℝ × ℝ) : F (negNeg p) = F p := by
    dsimp only [F, negNeg]
    rw [hreflect, hreflect]
    rw [show -p.1 - -p.2 = -(p.1 - p.2) by ring, abs_neg]
    calc
      yoshidaRegularKernel (a * |p.1 - p.2|) *
          (reflectionSign * w p.1) * (reflectionSign * w p.2) =
          reflectionSign ^ 2 *
            (yoshidaRegularKernel (a * |p.1 - p.2|) * w p.1 * w p.2) := by
        ring
      _ = _ := by rw [hsign, one_mul]
  have hLL_eq_PP :
      (∫ p : ℝ × ℝ in L ×ˢ L, F p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, F p := by
    calc
      (∫ p : ℝ × ℝ in L ×ˢ L, F p) =
          ∫ p : ℝ × ℝ in L ×ˢ L, F (negNeg p) := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p _hp
        exact (hFnegNeg p).symm
      _ = ∫ p : ℝ × ℝ in P ×ˢ P, F p := by
        rw [← hnegNegPre]
        exact hnegNegMP.setIntegral_preimage_emb hnegNegEmb F (P ×ˢ P)
  have hJcomp_eq_F : Set.EqOn (fun p ↦ J (negFst p)) F (L ×ˢ P) := by
    intro p hp
    dsimp only [J, F, negFst]
    rw [hreflect]
    have hdist : |p.1 - p.2| = -p.1 + p.2 := by
      rw [abs_of_nonpos (by linarith [hp.1.2, hp.2.1])]
      ring
    rw [hdist]
    rw [show reflectionSign *
          yoshidaRegularKernel (a * (-p.1 + p.2)) *
            (reflectionSign * w p.1) * w p.2 =
        reflectionSign ^ 2 *
          (yoshidaRegularKernel (a * (-p.1 + p.2)) * w p.1 * w p.2) by ring,
      hsign, one_mul]
  have hJcompInt : IntegrableOn (fun p ↦ J (negFst p)) (L ×ˢ P)
      ((volume : Measure ℝ).prod volume) :=
    hLP.congr_fun hJcomp_eq_F.symm
      (measurableSet_Icc.prod measurableSet_Icc)
  have hJPP : IntegrableOn J (P ×ˢ P)
      ((volume : Measure ℝ).prod volume) := by
    rw [← hnegFstMP.integrableOn_comp_preimage hnegFstEmb, hnegFstPre]
    exact hJcompInt
  have hLRae : L ×ˢ R =ᵐ[((volume : Measure ℝ).prod volume)] L ×ˢ P :=
    Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl)
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hRRae : R ×ˢ R =ᵐ[((volume : Measure ℝ).prod volume)] P ×ˢ P :=
    Measure.set_prod_ae_eq
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hLR_eq_J :
      (∫ p : ℝ × ℝ in L ×ˢ R, F p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
    calc
      (∫ p : ℝ × ℝ in L ×ˢ R, F p) =
          ∫ p : ℝ × ℝ in L ×ˢ P, F p :=
        setIntegral_congr_set hLRae
      _ = ∫ p : ℝ × ℝ in L ×ˢ P, J (negFst p) := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p hp
        exact (hJcomp_eq_F hp).symm
      _ = ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
        rw [← hnegFstPre]
        exact hnegFstMP.setIntegral_preimage_emb hnegFstEmb J (P ×ˢ P)
  have hFswap (p : ℝ × ℝ) : F p.swap = F p := by
    rcases p with ⟨x, y⟩
    dsimp only [F, Prod.swap_prod_mk]
    rw [abs_sub_comm]
    ring
  have hRL_eq_LR :
      (∫ p : ℝ × ℝ in R ×ˢ L, F p) =
        ∫ p : ℝ × ℝ in L ×ˢ R, F p := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) L R F
    calc
      (∫ p : ℝ × ℝ in R ×ˢ L, F p) =
          ∫ p : ℝ × ℝ in R ×ˢ L, F p.swap := by
        apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Icc)
        intro p _hp
        exact (hFswap p).symm
      _ = ∫ p : ℝ × ℝ in L ×ˢ R, F p := hswap
  have hRR_eq_PP :
      (∫ p : ℝ × ℝ in R ×ˢ R, F p) =
        ∫ p : ℝ × ℝ in P ×ˢ P, F p :=
    setIntegral_congr_set hRRae
  have hquadrants := setIntegral_centeredSquare_eq_quadrants F
    (by simpa only [S] using hF)
  have hiter := setIntegral_centeredSquare_eq_iterated_of_integrable F
    (by simpa only [S] using hF)
  have hadd :
      (∫ p : ℝ × ℝ in P ×ˢ P, F p + J p) =
        (∫ p : ℝ × ℝ in P ×ˢ P, F p) +
          ∫ p : ℝ × ℝ in P ×ˢ P, J p := by
    exact integral_add hPP hJPP
  rw [← hiter, hquadrants, hLL_eq_PP, hRL_eq_LR, hLR_eq_J, hRR_eq_PP]
  unfold fourCellPositiveHalfRegularProduct
  change _ = 2 * ∫ p : ℝ × ℝ in P ×ˢ P, _
  rw [show (fun p : ℝ × ℝ ↦
      (yoshidaRegularKernel (a * |p.1 - p.2|) +
          reflectionSign * yoshidaRegularKernel (a * (p.1 + p.2))) *
        w p.1 * w p.2) = fun p ↦ F p + J p by
    funext p
    dsimp only [F, J]
    ring,
    hadd]
  ring

private theorem integrableOn_positiveHalf_regularKernel_mul_continuous
    (distance phi : ℝ × ℝ → ℝ) (hphi : Continuous phi)
    (hdistance : Measurable distance)
    (hdistanceRange : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      0 ≤ distance p ∧ distance p ≤ 2)
    (a : ℝ) (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2) :
    IntegrableOn
      (fun p ↦ yoshidaRegularKernel (a * distance p) * phi p)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel (a * distance p) * phi p
  let g : ℝ × ℝ → ℝ := fun p ↦ (1 / 4 : ℝ) * |phi p|
  have hKMeas : Measurable K := by
    dsimp only [K]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul hdistance)).mul hphi.measurable
  have hg : IntegrableOn g
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact (continuous_const.mul hphi.abs).continuousOn
  apply hg.mono'
  · exact hKMeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
        (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hd := hdistanceRange p hp
    have harg0 : 0 ≤ a * distance p := mul_nonneg ha0 hd.1
    have harg3 : a * distance p ≤ Real.log 3 := by
      have had := mul_le_mul_of_nonneg_left hd.2 ha0
      linarith
    have hnonneg :=
      yoshidaRegularKernel_nonneg_of_le_log_three harg0 harg3
    have hupper := yoshidaRegularKernel_le_quarter harg0
    dsimp only [K, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right hupper (abs_nonneg (phi p))

private theorem positiveHalfRegular_completion
    (w : ℝ → ℝ) (hw : Continuous w) (a reflectionSign : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2)
    (hsign : reflectionSign ^ 2 = 1) :
    -2 * a * fourCellPositiveHalfRegularProduct w a reflectionSign =
      a * (fourCellPositiveHalfRegularSameSignSquare w a +
        fourCellPositiveHalfRegularReflectedSquare w a reflectionSign) -
      2 * a * fourCellPositiveHalfRegularRowMass w a := by
  let P : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let D : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel (a * |p.1 - p.2|)
  let R : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel (a * (p.1 + p.2))
  let A : ℝ × ℝ → ℝ := fun p ↦
    D p * (w p.1 - w p.2) ^ 2
  let B : ℝ × ℝ → ℝ := fun p ↦
    R p * (w p.1 - reflectionSign * w p.2) ^ 2
  let M : ℝ × ℝ → ℝ := fun p ↦
    (D p + R p) * ((w p.1 ^ 2 + w p.2 ^ 2) / 2)
  let H : ℝ × ℝ → ℝ := fun p ↦
    (D p + reflectionSign * R p) * w p.1 * w p.2
  have hdiffMeas : Measurable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) :=
    (measurable_fst.sub measurable_snd).abs
  have hsumMeas : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have hdiffRange : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      0 ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 := by
    intro p hp
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hsumRange : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 2 := by
    intro p hp
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hA : IntegrableOn A P ((volume : Measure ℝ).prod volume) := by
    simpa only [A, D, P] using
      integrableOn_positiveHalf_regularKernel_mul_continuous
        (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
        (fun p ↦ (w p.1 - w p.2) ^ 2)
        (by fun_prop) hdiffMeas hdiffRange a ha0 ha3
  have hB : IntegrableOn B P ((volume : Measure ℝ).prod volume) := by
    simpa only [B, R, P] using
      integrableOn_positiveHalf_regularKernel_mul_continuous
        (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (fun p ↦ (w p.1 - reflectionSign * w p.2) ^ 2)
        (by fun_prop) hsumMeas hsumRange a ha0 ha3
  have hDmass : IntegrableOn
      (fun p ↦ D p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2)) P
      ((volume : Measure ℝ).prod volume) := by
    simpa only [D, P] using
      integrableOn_positiveHalf_regularKernel_mul_continuous
        (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
        (fun p ↦ (w p.1 ^ 2 + w p.2 ^ 2) / 2)
        (by fun_prop) hdiffMeas hdiffRange a ha0 ha3
  have hRmass : IntegrableOn
      (fun p ↦ R p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2)) P
      ((volume : Measure ℝ).prod volume) := by
    simpa only [R, P] using
      integrableOn_positiveHalf_regularKernel_mul_continuous
        (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (fun p ↦ (w p.1 ^ 2 + w p.2 ^ 2) / 2)
        (by fun_prop) hsumMeas hsumRange a ha0 ha3
  have hM : IntegrableOn M P ((volume : Measure ℝ).prod volume) := by
    have hadd := hDmass.add hRmass
    apply hadd.congr_fun _ (by simpa only [P] using
      (measurableSet_Icc.prod measurableSet_Icc))
    intro p _hp
    change D p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2) +
      R p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2) = M p
    dsimp only [M]
    ring
  have hDprod : IntegrableOn
      (fun p ↦ D p * (w p.1 * w p.2)) P
      ((volume : Measure ℝ).prod volume) := by
    simpa only [D, P] using
      integrableOn_positiveHalf_regularKernel_mul_continuous
        (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
        (fun p ↦ w p.1 * w p.2)
        (by fun_prop) hdiffMeas hdiffRange a ha0 ha3
  have hRprod : IntegrableOn
      (fun p ↦ reflectionSign * R p * (w p.1 * w p.2)) P
      ((volume : Measure ℝ).prod volume) := by
    have hbase : IntegrableOn
        (fun p ↦ R p * (w p.1 * w p.2)) P
        ((volume : Measure ℝ).prod volume) := by
      simpa only [R, P] using
        integrableOn_positiveHalf_regularKernel_mul_continuous
          (fun p : ℝ × ℝ ↦ p.1 + p.2)
          (fun p ↦ w p.1 * w p.2)
          (by fun_prop) hsumMeas hsumRange a ha0 ha3
    simpa only [mul_assoc] using hbase.const_mul reflectionSign
  have hH : IntegrableOn H P ((volume : Measure ℝ).prod volume) := by
    have hadd := hDprod.add hRprod
    apply hadd.congr_fun _ (by simpa only [P] using
      (measurableSet_Icc.prod measurableSet_Icc))
    intro p _hp
    change D p * (w p.1 * w p.2) +
      reflectionSign * R p * (w p.1 * w p.2) = H p
    dsimp only [H]
    ring
  have hpoint (p : ℝ × ℝ) : A p + B p - 2 * M p = -2 * H p := by
    dsimp only [A, B, M, H]
    rw [show (w p.1 - reflectionSign * w p.2) ^ 2 =
        w p.1 ^ 2 + reflectionSign ^ 2 * w p.2 ^ 2 -
          2 * reflectionSign * w p.1 * w p.2 by ring,
      hsign]
    ring
  unfold fourCellPositiveHalfRegularProduct
    fourCellPositiveHalfRegularSameSignSquare
    fourCellPositiveHalfRegularReflectedSquare
    fourCellPositiveHalfRegularRowMass
  change -2 * a * (∫ p : ℝ × ℝ in P, H p) =
    a * ((∫ p : ℝ × ℝ in P, A p) + ∫ p : ℝ × ℝ in P, B p) -
      2 * a * ∫ p : ℝ × ℝ in P, M p
  have hcompletion :
      (∫ p : ℝ × ℝ in P, A p + B p - 2 * M p) =
        ∫ p : ℝ × ℝ in P, -2 * H p := by
    apply setIntegral_congr_fun (by simpa only [P] using
      (measurableSet_Icc.prod measurableSet_Icc))
    intro p _hp
    exact hpoint p
  have hAB : IntegrableOn (fun p ↦ A p + B p) P
      ((volume : Measure ℝ).prod volume) := by
    simpa only [Pi.add_apply] using hA.add hB
  have htwoM : IntegrableOn (fun p ↦ 2 * M p) P
      ((volume : Measure ℝ).prod volume) := hM.const_mul 2
  have hAddInt :
      (∫ p : ℝ × ℝ in P, A p + B p) =
        (∫ p : ℝ × ℝ in P, A p) +
          ∫ p : ℝ × ℝ in P, B p := by
    exact integral_add hA hB
  have hTwoMInt :
      (∫ p : ℝ × ℝ in P, 2 * M p) =
        2 * ∫ p : ℝ × ℝ in P, M p := by
    rw [integral_const_mul]
  have hleftExpand :
      (∫ p : ℝ × ℝ in P, A p + B p - 2 * M p) =
        ((∫ p : ℝ × ℝ in P, A p) +
          ∫ p : ℝ × ℝ in P, B p) -
          2 * ∫ p : ℝ × ℝ in P, M p := by
    calc
      (∫ p : ℝ × ℝ in P, A p + B p - 2 * M p) =
          (∫ p : ℝ × ℝ in P, A p + B p) -
            ∫ p : ℝ × ℝ in P, 2 * M p :=
        integral_sub hAB htwoM
      _ = _ := by
        rw [hAddInt, hTwoMInt]
  have hrightExpand :
      (∫ p : ℝ × ℝ in P, -2 * H p) =
        -2 * ∫ p : ℝ × ℝ in P, H p := by
    rw [integral_const_mul]
  rw [hleftExpand, hrightExpand] at hcompletion
  calc
    -2 * a * (∫ p : ℝ × ℝ in P, H p) =
        a * (-2 * ∫ p : ℝ × ℝ in P, H p) := by ring
    _ = a * (((∫ p : ℝ × ℝ in P, A p) +
          ∫ p : ℝ × ℝ in P, B p) -
          2 * ∫ p : ℝ × ℝ in P, M p) := by
      rw [hcompletion]
    _ = _ := by ring

/-- Exact positive-half completion in a reflection-sign channel. -/
private theorem neg_two_mul_regularCorrelation_eq_positiveHalfCompletion
    (w : ℝ → ℝ) (hw : Continuous w) (a reflectionSign : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2)
    (hreflect : ∀ x : ℝ, w (-x) = reflectionSign * w x)
    (hsign : reflectionSign ^ 2 = 1) :
    -2 * a * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) =
      a * (fourCellPositiveHalfRegularSameSignSquare w a +
        fourCellPositiveHalfRegularReflectedSquare w a reflectionSign) -
      2 * a * fourCellPositiveHalfRegularRowMass w a := by
  have hfull := centeredRegularProduct_parityFold
    w hw a reflectionSign ha0 ha3 hreflect hsign
  have hsquare :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw a ha0 ha3
  have hcorr :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) =
        fourCellPositiveHalfRegularProduct w a reflectionSign := by
    rw [hfull] at hsquare
    linarith
  rw [hcorr]
  exact positiveHalfRegular_completion w hw a reflectionSign ha0 ha3 hsign

/-- In the even channel the regular autocorrelation is an exact sum of the
same-sign and reflected-difference squares, minus twice the row mass. -/
theorem neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) (a : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2) :
    -2 * a * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) =
      a * (fourCellPositiveHalfRegularSameSignSquare w a +
        fourCellPositiveHalfRegularReflectedSquare w a 1) -
      2 * a * fourCellPositiveHalfRegularRowMass w a := by
  apply neg_two_mul_regularCorrelation_eq_positiveHalfCompletion
    w hw a 1 ha0 ha3
  · intro x
    simpa using heven x
  · norm_num

/-- In the odd channel the regular autocorrelation is an exact sum of the
same-sign difference and reflected sum squares, minus twice the row mass. -/
theorem neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) (a : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2) :
    -2 * a * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) =
      a * (fourCellPositiveHalfRegularSameSignSquare w a +
        fourCellPositiveHalfRegularReflectedSquare w a (-1)) -
      2 * a * fourCellPositiveHalfRegularRowMass w a := by
  apply neg_two_mul_regularCorrelation_eq_positiveHalfCompletion
    w hw a (-1) ha0 ha3
  · intro x
    rw [hodd]
    ring
  · norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellRegularParityFoldStructural
