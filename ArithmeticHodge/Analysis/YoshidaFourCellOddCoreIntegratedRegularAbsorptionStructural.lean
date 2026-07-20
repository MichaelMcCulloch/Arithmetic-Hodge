import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeIntegralStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreEndpointBlockRegularAbsorptionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

noncomputable section

open YoshidaFourCellOddCoreBlockPiconeIntegralStructural
open YoshidaFourCellOddCoreBlockPiconeStructural
open YoshidaFourCellOddCoreEndpointBlockRegularAbsorptionStructural
open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellOddCoreOffStripRegularAbsorptionStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaRegularKernelBound
open YoshidaEndpointPositiveDistanceFold
open YoshidaEndpointTriangleFoldLipschitz
open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy

/-! ## Endpoint-square reflection orbit -/

def endpointLowerPhysicalSet : Set ℝ := Icc (3 / 5) (4 / 5)

def endpointUpperPhysicalSet : Set ℝ := Ioc (4 / 5) 1

def endpointUpperClosedSet : Set ℝ := Icc (4 / 5) 1

def endpointStripReflection (x : ℝ) : ℝ := 8 / 5 - x

def endpointReflectFirst (p : ℝ × ℝ) : ℝ × ℝ :=
  (endpointStripReflection p.1, p.2)

def endpointReflectSecond (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, endpointStripReflection p.2)

def endpointReflectBoth (p : ℝ × ℝ) : ℝ × ℝ :=
  (endpointStripReflection p.1, endpointStripReflection p.2)

private theorem endpointRawSet_eq_lower_union_upper :
    endpointRawSet = endpointLowerPhysicalSet ∪ endpointUpperPhysicalSet := by
  ext x
  simp only [endpointRawSet, endpointLowerPhysicalSet,
    endpointUpperPhysicalSet, mem_Icc, mem_Ioc, mem_union]
  constructor
  · intro hx
    by_cases hxc : x ≤ 4 / 5
    · exact Or.inl ⟨hx.1, hxc⟩
    · exact Or.inr ⟨lt_of_not_ge hxc, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.trans (by norm_num)⟩
    · exact ⟨by linarith [hx.1], hx.2⟩

private theorem endpointLowerPhysicalSet_disjoint_upper :
    Disjoint endpointLowerPhysicalSet endpointUpperPhysicalSet := by
  rw [Set.disjoint_left]
  intro x hxL hxU
  exact (not_lt_of_ge hxL.2) hxU.1

private theorem endpointUpperPhysicalSet_ae_eq_closed :
    endpointUpperPhysicalSet =ᵐ[(volume : Measure ℝ)]
      endpointUpperClosedSet := by
  exact Ioc_ae_eq_Icc (μ := (volume : Measure ℝ))

private theorem endpointReflection_preimage_lower :
    endpointStripReflection ⁻¹' endpointLowerPhysicalSet =
      endpointUpperClosedSet := by
  ext x
  simp only [endpointStripReflection, endpointLowerPhysicalSet,
    endpointUpperClosedSet, preimage, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem endpointReflectFirst_preimage_lower_closed :
    endpointReflectFirst ⁻¹'
        (endpointLowerPhysicalSet ×ˢ endpointUpperClosedSet) =
      endpointUpperClosedSet ×ˢ endpointUpperClosedSet := by
  ext p
  simp only [endpointReflectFirst, endpointStripReflection,
    endpointLowerPhysicalSet, endpointUpperClosedSet, preimage, mem_prod,
    mem_Icc]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, h₃, h₄⟩

private theorem endpointReflectSecond_preimage_closed_lower :
    endpointReflectSecond ⁻¹'
        (endpointUpperClosedSet ×ˢ endpointLowerPhysicalSet) =
      endpointUpperClosedSet ×ˢ endpointUpperClosedSet := by
  ext p
  simp only [endpointReflectSecond, endpointStripReflection,
    endpointLowerPhysicalSet, endpointUpperClosedSet, preimage, mem_prod,
    mem_Icc]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;>
    exact ⟨⟨h₁, h₂⟩, by linarith, by linarith⟩

private theorem endpointReflectBoth_preimage_lower_lower :
    endpointReflectBoth ⁻¹'
        (endpointLowerPhysicalSet ×ˢ endpointLowerPhysicalSet) =
      endpointUpperClosedSet ×ˢ endpointUpperClosedSet := by
  ext p
  simp only [endpointReflectBoth, endpointStripReflection,
    endpointLowerPhysicalSet, endpointUpperClosedSet, preimage, mem_prod,
    mem_Icc]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Pair the four reflection quadrants of the physical endpoint square over
the closed upper quarter.  This is purely measure-theoretic and applies to
both the raw and folded-regular densities. -/
theorem setIntegral_endpointSquare_eq_reflectionOrbit
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (endpointRawSet ×ˢ endpointRawSet)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, F p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in endpointUpperClosedSet ×ˢ endpointUpperClosedSet,
        (F p + F (endpointReflectFirst p) +
          F (endpointReflectSecond p) + F (endpointReflectBoth p))
          ∂((volume : Measure ℝ).prod volume) := by
  let L : Set ℝ := endpointLowerPhysicalSet
  let U : Set ℝ := endpointUpperPhysicalSet
  let P : Set ℝ := endpointUpperClosedSet
  have hLsub : L ⊆ endpointRawSet := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hUsub : U ⊆ endpointRawSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hLL := hF.mono_set (Set.prod_mono hLsub hLsub)
  have hLU := hF.mono_set (Set.prod_mono hLsub hUsub)
  have hUL := hF.mono_set (Set.prod_mono hUsub hLsub)
  have hUU := hF.mono_set (Set.prod_mono hUsub hUsub)
  have hLmeas : MeasurableSet L := measurableSet_Icc
  have hUmeas : MeasurableSet U := measurableSet_Ioc
  have hBmeas : MeasurableSet endpointRawSet := measurableSet_Icc
  have hquadrants :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume)) =
        (∫ p : ℝ × ℝ in L ×ˢ L, F p
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in L ×ˢ U, F p
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in U ×ˢ L, F p
          ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in U ×ˢ U, F p
          ∂((volume : Measure ℝ).prod volume) := by
    have houter :
        (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume)) =
        (∫ p : ℝ × ℝ in L ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in U ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume) := by
      rw [show endpointRawSet ×ˢ endpointRawSet =
          (L ×ˢ endpointRawSet) ∪ (U ×ˢ endpointRawSet) by
        rw [endpointRawSet_eq_lower_union_upper, union_prod]]
      exact setIntegral_union
        (endpointLowerPhysicalSet_disjoint_upper.set_prod_left
          endpointRawSet endpointRawSet)
        (hUmeas.prod hBmeas)
        (hF.mono_set (Set.prod_mono hLsub (Subset.rfl)))
        (hF.mono_set (Set.prod_mono hUsub (Subset.rfl)))
    have hleft :
        (∫ p : ℝ × ℝ in L ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume)) =
        (∫ p : ℝ × ℝ in L ×ˢ L, F p
          ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in L ×ˢ U, F p
          ∂((volume : Measure ℝ).prod volume) := by
      rw [show L ×ˢ endpointRawSet = (L ×ˢ L) ∪ (L ×ˢ U) by
        rw [endpointRawSet_eq_lower_union_upper, prod_union]]
      exact setIntegral_union
        (endpointLowerPhysicalSet_disjoint_upper.set_prod_right L L)
        (hLmeas.prod hUmeas) hLL hLU
    have hright :
        (∫ p : ℝ × ℝ in U ×ˢ endpointRawSet, F p
          ∂((volume : Measure ℝ).prod volume)) =
        (∫ p : ℝ × ℝ in U ×ˢ L, F p
          ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in U ×ˢ U, F p
          ∂((volume : Measure ℝ).prod volume) := by
      rw [show U ×ˢ endpointRawSet = (U ×ˢ L) ∪ (U ×ˢ U) by
        rw [endpointRawSet_eq_lower_union_upper, prod_union]]
      exact setIntegral_union
        (endpointLowerPhysicalSet_disjoint_upper.set_prod_right U U)
        (hUmeas.prod hUmeas) hUL hUU
    rw [houter, hleft, hright]
    ring
  have hUP := endpointUpperPhysicalSet_ae_eq_closed
  have hLPae : L ×ˢ U =ᵐ[((volume : Measure ℝ).prod volume)] L ×ˢ P :=
    Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl) hUP
  have hPLae : U ×ˢ L =ᵐ[((volume : Measure ℝ).prod volume)] P ×ˢ L :=
    Measure.set_prod_ae_eq hUP (Filter.EventuallyEq.rfl)
  have hPPae : U ×ˢ U =ᵐ[((volume : Measure ℝ).prod volume)] P ×ˢ P :=
    Measure.set_prod_ae_eq hUP hUP
  have hreflect : MeasurePreserving endpointStripReflection
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    simpa only [endpointStripReflection] using
      (volume : Measure ℝ).measurePreserving_sub_left (8 / 5 : ℝ)
  have hfirst : MeasurePreserving endpointReflectFirst
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectFirst, Prod.map_apply, id_eq] using
      hreflect.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hsecond : MeasurePreserving endpointReflectSecond
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectSecond, Prod.map_apply, id_eq] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod hreflect
  have hboth : MeasurePreserving endpointReflectBoth
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectBoth, Prod.map_apply] using
      hreflect.prod hreflect
  have hfirstEmb : MeasurableEmbedding endpointReflectFirst := by
    simpa only [endpointReflectFirst, endpointStripReflection,
      Prod.map_apply, id_eq] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (8 / 5 : ℝ))
        (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have hsecondEmb : MeasurableEmbedding endpointReflectSecond := by
    simpa only [endpointReflectSecond, endpointStripReflection,
      Prod.map_apply, id_eq] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.subLeft (8 / 5 : ℝ))).measurableEmbedding
  have hbothEmb : MeasurableEmbedding endpointReflectBoth := by
    simpa only [endpointReflectBoth, endpointStripReflection,
      Prod.map_apply] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (8 / 5 : ℝ))
        (MeasurableEquiv.subLeft (8 / 5 : ℝ))).measurableEmbedding
  have hLLtransform :
      (∫ p : ℝ × ℝ in L ×ˢ L, F p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectBoth p)
        ∂((volume : Measure ℝ).prod volume) := by
    rw [← endpointReflectBoth_preimage_lower_lower]
    exact (hboth.setIntegral_preimage_emb hbothEmb F (L ×ˢ L)).symm
  have hLPtransform :
      (∫ p : ℝ × ℝ in L ×ˢ P, F p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectFirst p)
        ∂((volume : Measure ℝ).prod volume) := by
    rw [← endpointReflectFirst_preimage_lower_closed]
    exact (hfirst.setIntegral_preimage_emb hfirstEmb F (L ×ˢ P)).symm
  have hPLtransform :
      (∫ p : ℝ × ℝ in P ×ˢ L, F p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectSecond p)
        ∂((volume : Measure ℝ).prod volume) := by
    rw [← endpointReflectSecond_preimage_closed_lower]
    exact (hsecond.setIntegral_preimage_emb hsecondEmb F (P ×ˢ L)).symm
  have hPsub : P ⊆ endpointRawSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hPP := hF.mono_set (Set.prod_mono hPsub hPsub)
  have hfirstInt : IntegrableOn (fun p ↦ F (endpointReflectFirst p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hfirst.integrableOn_comp_preimage hfirstEmb
      (f := F) (s := L ×ˢ P)).2
        (hF.mono_set (Set.prod_mono hLsub hPsub))
    rw [endpointReflectFirst_preimage_lower_closed] at h
    simpa only [Function.comp_apply] using h
  have hsecondInt : IntegrableOn (fun p ↦ F (endpointReflectSecond p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hsecond.integrableOn_comp_preimage hsecondEmb
      (f := F) (s := P ×ˢ L)).2
        (hF.mono_set (Set.prod_mono hPsub hLsub))
    rw [endpointReflectSecond_preimage_closed_lower] at h
    simpa only [Function.comp_apply] using h
  have hbothInt : IntegrableOn (fun p ↦ F (endpointReflectBoth p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hboth.integrableOn_comp_preimage hbothEmb
      (f := F) (s := L ×ˢ L)).2 hLL
    rw [endpointReflectBoth_preimage_lower_lower] at h
    simpa only [Function.comp_apply] using h
  have hsum :
      (∫ p : ℝ × ℝ in P ×ˢ P,
          (F p + F (endpointReflectFirst p) +
            F (endpointReflectSecond p) + F (endpointReflectBoth p))
            ∂((volume : Measure ℝ).prod volume)) =
        (∫ p : ℝ × ℝ in P ×ˢ P, F p
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectFirst p)
          ∂((volume : Measure ℝ).prod volume)) +
        (∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectSecond p)
          ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in P ×ˢ P, F (endpointReflectBoth p)
          ∂((volume : Measure ℝ).prod volume) := by
    change (∫ p : ℝ × ℝ in P ×ˢ P,
        (((F + fun q ↦ F (endpointReflectFirst q)) +
          fun q ↦ F (endpointReflectSecond q)) +
          fun q ↦ F (endpointReflectBoth q)) p
          ∂((volume : Measure ℝ).prod volume)) = _
    have h₁ := integral_add ((hPP.add hfirstInt).add hsecondInt) hbothInt
    have h₂ := integral_add (hPP.add hfirstInt) hsecondInt
    have h₃ := integral_add hPP hfirstInt
    simpa only [Pi.add_apply] using h₁.trans
      (congrArg₂ (fun a b : ℝ ↦ a + b)
        (h₂.trans (congrArg₂ (fun a b : ℝ ↦ a + b) h₃ rfl)) rfl)
  rw [hquadrants, setIntegral_congr_set hLPae,
    setIntegral_congr_set hPLae, setIntegral_congr_set hPPae,
    hLLtransform, hLPtransform, hPLtransform, hsum]
  ring

def endpointNormalizedPositiveSet : Set ℝ := Icc 0 1

/-- The affine endpoint pullback contributes exactly the product Jacobian
`1 / 25`.  Both integrability hypotheses are explicit so the lemma remains
usable for measurable bounded kernels as well as continuous densities. -/
theorem setIntegral_normalizedEndpointSquare_eq_twentyFive_mul_upperSquare
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F
      (endpointUpperClosedSet ×ˢ endpointUpperClosedSet)
      ((volume : Measure ℝ).prod volume))
    (hcomp : IntegrableOn
      (fun p : ℝ × ℝ ↦ F
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      F (endpointStripPhysicalPlusPoint p.1,
        endpointStripPhysicalPlusPoint p.2)
        ∂((volume : Measure ℝ).prod volume)) =
      25 * (∫ p : ℝ × ℝ in
        endpointUpperClosedSet ×ˢ endpointUpperClosedSet, F p
          ∂((volume : Measure ℝ).prod volume)) := by
  let H : ℝ → ℝ := fun x ↦ ∫ y : ℝ in 4 / 5..1, F (x, y)
  have hinner (z : ℝ) :
      (∫ s : ℝ in 0..1,
        F (endpointStripPhysicalPlusPoint z,
          endpointStripPhysicalPlusPoint s)) =
        5 * H (endpointStripPhysicalPlusPoint z) := by
    have h := intervalIntegral.integral_comp_add_mul
      (a := (0 : ℝ)) (b := 1) (c := (1 / 5 : ℝ))
      (fun y : ℝ ↦ F (endpointStripPhysicalPlusPoint z, y))
      (by norm_num) (4 / 5)
    dsimp only [H]
    convert h using 1
    all_goals norm_num [endpointStripPhysicalPlusPoint, div_eq_mul_inv,
      mul_comm]
  have houter :
      (∫ z : ℝ in 0..1, H (endpointStripPhysicalPlusPoint z)) =
        5 * ∫ x : ℝ in 4 / 5..1, H x := by
    have h := intervalIntegral.integral_comp_add_mul
      (a := (0 : ℝ)) (b := 1) (c := (1 / 5 : ℝ)) H
      (by norm_num) (4 / 5)
    convert h using 1
    all_goals norm_num [endpointStripPhysicalPlusPoint]
  have hnormalized := intervalIntegral_integral_eq_setIntegral_square
    (fun p : ℝ × ℝ ↦ F
      (endpointStripPhysicalPlusPoint p.1,
        endpointStripPhysicalPlusPoint p.2))
    0 1 (by norm_num) (by
      simpa only [endpointNormalizedPositiveSet] using hcomp)
  have hphysical := intervalIntegral_integral_eq_setIntegral_square
    F (4 / 5) 1 (by norm_num) (by
      simpa only [endpointUpperClosedSet] using hF)
  have hnormalized' :
      (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        F (endpointStripPhysicalPlusPoint x,
          endpointStripPhysicalPlusPoint y)) =
      ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        F (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2)
          ∂((volume : Measure ℝ).prod volume) := by
    simpa only [] using hnormalized
  have hphysical' :
      (∫ x : ℝ in 4 / 5..1, ∫ y : ℝ in 4 / 5..1, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc (4 / 5 : ℝ) 1 ×ˢ Icc (4 / 5 : ℝ) 1,
        F p ∂((volume : Measure ℝ).prod volume) := hphysical
  simp only [endpointNormalizedPositiveSet, endpointUpperClosedSet]
  rw [← hnormalized', ← hphysical']
  calc
    (∫ z : ℝ in 0..1, ∫ s : ℝ in 0..1,
        F (endpointStripPhysicalPlusPoint z,
          endpointStripPhysicalPlusPoint s)) =
      ∫ z : ℝ in 0..1, 5 * H (endpointStripPhysicalPlusPoint z) := by
        apply intervalIntegral.integral_congr
        intro z _hz
        exact hinner z
    _ = 5 * ∫ z : ℝ in 0..1,
        H (endpointStripPhysicalPlusPoint z) := by
      rw [← intervalIntegral.integral_const_mul]
    _ = 25 * ∫ x : ℝ in 4 / 5..1, H x := by rw [houter]; ring
    _ = 25 * (∫ x : ℝ in 4 / 5..1, ∫ y : ℝ in 4 / 5..1,
        F (x, y)) := by rfl

/-! ## Integrable global densities -/

def positiveHalfRawReserveIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  positiveHalfRawReservePair p.1 p.2 (w p.1) (w p.2)

def positiveHalfReflectedReserveIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  positiveHalfReflectedReserveWeight p.1 p.2 * (w p.1 + w p.2) ^ 2

theorem positiveHalfRawReserveIntegrand_eq_half_coupled
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    positiveHalfRawReserveIntegrand w p =
      (1 / 2 : ℝ) * fourCellOddCoupledRawPair w p := by
  unfold positiveHalfRawReserveIntegrand positiveHalfRawReservePair
    positiveHalfSameReserveWeight positiveHalfReflectedReserveWeight
    fourCellOddCoupledRawPair
  by_cases hdiff : |p.1 - p.2| = 0 <;>
    by_cases hsum : p.1 + p.2 = 0
  all_goals simp only [hdiff, hsum, inv_zero, zero_mul,
    mul_zero, div_eq_mul_inv]
  all_goals field_simp [hdiff, hsum]
  all_goals ring

theorem integrableOn_positiveHalfRawReserveIntegrand
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    IntegrableOn (positiveHalfRawReserveIntegrand w)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  have h : IntegrableOn
      (fun p ↦ (1 / 2 : ℝ) * fourCellOddCoupledRawPair w p)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    (integrableOn_fourCellOddCoupledRawPair w hw hodd).const_mul
      (1 / 2 : ℝ)
  apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  exact (positiveHalfRawReserveIntegrand_eq_half_coupled w p).symm

theorem integrableOn_foldedRegularOriginalIntegrand
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntegrableOn (foldedRegularOriginalIntegrand w)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let A : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * |p.1 - p.2|) * (w p.1 * w p.2)
  let B : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * (p.1 + p.2)) * (w p.1 * w p.2)
  have hdiffMeas : Measurable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) :=
    (measurable_fst.sub measurable_snd).abs
  have hsumMeas : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have hdiffRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 := by
    intro p hp
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hsumRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 2 := by
    intro p hp
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hA : IntegrableOn A (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [A] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
      (fun p ↦ w p.1 * w p.2) (by fun_prop)
      hdiffMeas hdiffRange
  have hB : IntegrableOn B (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [B] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (fun p ↦ w p.1 * w p.2) (by fun_prop)
      hsumMeas hsumRange
  have h : IntegrableOn
      (fun p ↦ (-2 * fourCellOperatorHalfWidth) * (A p - B p))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    (hA.sub hB).const_mul (-2 * fourCellOperatorHalfWidth)
  apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  dsimp only [A, B]
  unfold foldedRegularOriginalIntegrand
    fourCellOddFoldedRegularDifferenceKernel
  ring

theorem positiveHalfRawReserveIntegrand_symmetric
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    positiveHalfRawReserveIntegrand w p.swap =
      positiveHalfRawReserveIntegrand w p := by
  rcases p with ⟨x, y⟩
  unfold positiveHalfRawReserveIntegrand positiveHalfRawReservePair
    positiveHalfSameReserveWeight positiveHalfReflectedReserveWeight
  simp only [Prod.swap_prod_mk]
  rw [abs_sub_comm]
  ring

theorem foldedRegularOriginalIntegrand_symmetric
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    foldedRegularOriginalIntegrand w p.swap =
      foldedRegularOriginalIntegrand w p := by
  rcases p with ⟨x, y⟩
  unfold foldedRegularOriginalIntegrand
    fourCellOddFoldedRegularDifferenceKernel
  simp only [Prod.swap_prod_mk]
  rw [abs_sub_comm]
  ring

def endpointReflectionOrbit
    (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  F p + F (endpointReflectFirst p) +
    F (endpointReflectSecond p) + F (endpointReflectBoth p)

theorem integrableOn_endpointReflectionOrbit
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (endpointRawSet ×ˢ endpointRawSet)
      ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (endpointReflectionOrbit F)
      (endpointUpperClosedSet ×ˢ endpointUpperClosedSet)
      ((volume : Measure ℝ).prod volume) := by
  let L : Set ℝ := endpointLowerPhysicalSet
  let P : Set ℝ := endpointUpperClosedSet
  have hLsub : L ⊆ endpointRawSet := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hPsub : P ⊆ endpointRawSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hreflect : MeasurePreserving endpointStripReflection
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    simpa only [endpointStripReflection] using
      (volume : Measure ℝ).measurePreserving_sub_left (8 / 5 : ℝ)
  have hfirst : MeasurePreserving endpointReflectFirst
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectFirst, Prod.map_apply, id_eq] using
      hreflect.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hsecond : MeasurePreserving endpointReflectSecond
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectSecond, Prod.map_apply, id_eq] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod hreflect
  have hboth : MeasurePreserving endpointReflectBoth
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [endpointReflectBoth, Prod.map_apply] using
      hreflect.prod hreflect
  have hfirstEmb : MeasurableEmbedding endpointReflectFirst := by
    simpa only [endpointReflectFirst, endpointStripReflection,
      Prod.map_apply, id_eq] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (8 / 5 : ℝ))
        (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have hsecondEmb : MeasurableEmbedding endpointReflectSecond := by
    simpa only [endpointReflectSecond, endpointStripReflection,
      Prod.map_apply, id_eq] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.subLeft (8 / 5 : ℝ))).measurableEmbedding
  have hbothEmb : MeasurableEmbedding endpointReflectBoth := by
    simpa only [endpointReflectBoth, endpointStripReflection,
      Prod.map_apply] using
      (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft (8 / 5 : ℝ))
        (MeasurableEquiv.subLeft (8 / 5 : ℝ))).measurableEmbedding
  have hPP := hF.mono_set (Set.prod_mono hPsub hPsub)
  have hfirstInt : IntegrableOn (fun p ↦ F (endpointReflectFirst p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hfirst.integrableOn_comp_preimage hfirstEmb
      (f := F) (s := L ×ˢ P)).2
        (hF.mono_set (Set.prod_mono hLsub hPsub))
    rw [endpointReflectFirst_preimage_lower_closed] at h
    simpa only [Function.comp_apply] using h
  have hsecondInt : IntegrableOn (fun p ↦ F (endpointReflectSecond p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hsecond.integrableOn_comp_preimage hsecondEmb
      (f := F) (s := P ×ˢ L)).2
        (hF.mono_set (Set.prod_mono hPsub hLsub))
    rw [endpointReflectSecond_preimage_closed_lower] at h
    simpa only [Function.comp_apply] using h
  have hbothInt : IntegrableOn (fun p ↦ F (endpointReflectBoth p))
      (P ×ˢ P) ((volume : Measure ℝ).prod volume) := by
    have h := (hboth.integrableOn_comp_preimage hbothEmb
      (f := F) (s := L ×ˢ L)).2
        (hF.mono_set (Set.prod_mono hLsub hLsub))
    rw [endpointReflectBoth_preimage_lower_lower] at h
    simpa only [Function.comp_apply] using h
  exact ((hPP.add hfirstInt).add hsecondInt).add hbothInt

theorem integrableOn_foldedRegularOriginalIntegrand_comp_coordinates
    (w u v : ℝ → ℝ) (hw : Continuous w)
    (hu : Continuous u) (hv : Continuous v)
    (huRange : ∀ x ∈ positiveHalfSet, 0 ≤ u x ∧ u x ≤ 1)
    (hvRange : ∀ x ∈ positiveHalfSet, 0 ≤ v x ∧ v x ≤ 1) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ foldedRegularOriginalIntegrand w (u p.1, v p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let A : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * |u p.1 - v p.2|) *
        (w (u p.1) * w (v p.2))
  let B : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * (u p.1 + v p.2)) *
        (w (u p.1) * w (v p.2))
  have hdiffMeas : Measurable
      (fun p : ℝ × ℝ ↦ |u p.1 - v p.2|) := by fun_prop
  have hsumMeas : Measurable
      (fun p : ℝ × ℝ ↦ u p.1 + v p.2) := by fun_prop
  have hdiffRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ |u p.1 - v p.2| ∧ |u p.1 - v p.2| ≤ 2 := by
    intro p hp
    have hup := huRange p.1 hp.1
    have hvp := hvRange p.2 hp.2
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith
  have hsumRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ u p.1 + v p.2 ∧ u p.1 + v p.2 ≤ 2 := by
    intro p hp
    have hup := huRange p.1 hp.1
    have hvp := hvRange p.2 hp.2
    constructor <;> linarith
  have hA : IntegrableOn A (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [A] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ |u p.1 - v p.2|)
      (fun p ↦ w (u p.1) * w (v p.2)) (by fun_prop)
      hdiffMeas hdiffRange
  have hB : IntegrableOn B (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [B] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ u p.1 + v p.2)
      (fun p ↦ w (u p.1) * w (v p.2)) (by fun_prop)
      hsumMeas hsumRange
  have h : IntegrableOn
      (fun p ↦ (-2 * fourCellOperatorHalfWidth) * (A p - B p))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    (hA.sub hB).const_mul (-2 * fourCellOperatorHalfWidth)
  apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  dsimp only [A, B]
  unfold foldedRegularOriginalIntegrand
    fourCellOddFoldedRegularDifferenceKernel
  ring

theorem endpointStripPhysicalPoints_mem_positiveHalfSet
    {z : ℝ} (hz : z ∈ positiveHalfSet) :
    endpointStripPhysicalPlusPoint z ∈ positiveHalfSet ∧
      endpointStripPhysicalMinusPoint z ∈ positiveHalfSet := by
  unfold positiveHalfSet endpointStripPhysicalPlusPoint
    endpointStripPhysicalMinusPoint
  constructor <;> constructor <;> linarith [hz.1, hz.2]

def endpointNormalizedRawBlockIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  endpointStripRawReserveBlockPair p.1 p.2
    (fourCellOddEndpointStripEven w p.1)
    (fourCellOddEndpointStripOdd w p.1)
    (fourCellOddEndpointStripEven w p.2)
    (fourCellOddEndpointStripOdd w p.2)

def endpointNormalizedRegularCrossIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  endpointStripFoldedRegularCrossDensity p.1 p.2
    (stripParityValue (fourCellOddEndpointStripEven w p.1)
      (fourCellOddEndpointStripOdd w p.1) 1)
    (stripParityValue (fourCellOddEndpointStripEven w p.1)
      (fourCellOddEndpointStripOdd w p.1) (-1))
    (stripParityValue (fourCellOddEndpointStripEven w p.2)
      (fourCellOddEndpointStripOdd w p.2) 1)
    (stripParityValue (fourCellOddEndpointStripEven w p.2)
      (fourCellOddEndpointStripOdd w p.2) (-1))

theorem endpointStripParityValue_one
    (w : ℝ → ℝ) (z : ℝ) :
    stripParityValue (fourCellOddEndpointStripEven w z)
        (fourCellOddEndpointStripOdd w z) 1 =
      w (endpointStripPhysicalPlusPoint z) := by
  unfold stripParityValue fourCellOddEndpointStripEven
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    endpointStripPhysicalPlusPoint
  ring

theorem endpointStripParityValue_neg_one
    (w : ℝ → ℝ) (z : ℝ) :
    stripParityValue (fourCellOddEndpointStripEven w z)
        (fourCellOddEndpointStripOdd w z) (-1) =
      w (endpointStripPhysicalMinusPoint z) := by
  unfold stripParityValue fourCellOddEndpointStripEven
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    endpointStripPhysicalMinusPoint
  ring

private theorem endpointStripReflection_plusPoint
    (z : ℝ) :
    endpointStripReflection (endpointStripPhysicalPlusPoint z) =
      endpointStripPhysicalMinusPoint z := by
  unfold endpointStripReflection endpointStripPhysicalPlusPoint
    endpointStripPhysicalMinusPoint
  ring

theorem endpointNormalizedRegularCrossIntegrand_eq_scaled_reflectionOrbit
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    endpointNormalizedRegularCrossIntegrand w p =
      (1 / 25 : ℝ) * endpointReflectionOrbit
        (foldedRegularOriginalIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2) := by
  unfold endpointNormalizedRegularCrossIntegrand
  rw [endpointStripParityValue_one, endpointStripParityValue_neg_one,
    endpointStripParityValue_one, endpointStripParityValue_neg_one]
  unfold endpointReflectionOrbit endpointReflectFirst endpointReflectSecond
    endpointReflectBoth
  simp only [endpointStripReflection_plusPoint]
  unfold endpointStripFoldedRegularCrossDensity
    endpointStripFoldedRegularPPCoefficient
    endpointStripFoldedRegularMMCoefficient
    endpointStripFoldedRegularPMCoefficient
    endpointStripFoldedRegularMPCoefficient
    endpointStripPulledBackFoldedRegularCoefficient
    foldedRegularOriginalIntegrand
  ring

theorem integrableOn_endpointNormalizedRegularCrossIntegrand
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntegrableOn (endpointNormalizedRegularCrossIntegrand w)
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
  have hplus : Continuous endpointStripPhysicalPlusPoint := by
    unfold endpointStripPhysicalPlusPoint
    fun_prop
  have hminus : Continuous endpointStripPhysicalMinusPoint := by
    unfold endpointStripPhysicalMinusPoint
    fun_prop
  have hplusRange : ∀ x ∈ positiveHalfSet,
      0 ≤ endpointStripPhysicalPlusPoint x ∧
        endpointStripPhysicalPlusPoint x ≤ 1 := by
    intro x hx
    exact (endpointStripPhysicalPoints_mem_positiveHalfSet hx).1
  have hminusRange : ∀ x ∈ positiveHalfSet,
      0 ≤ endpointStripPhysicalMinusPoint x ∧
        endpointStripPhysicalMinusPoint x ≤ 1 := by
    intro x hx
    exact (endpointStripPhysicalPoints_mem_positiveHalfSet hx).2
  have hPP := integrableOn_foldedRegularOriginalIntegrand_comp_coordinates
    w endpointStripPhysicalPlusPoint endpointStripPhysicalPlusPoint
    hw hplus hplus hplusRange hplusRange
  have hMP := integrableOn_foldedRegularOriginalIntegrand_comp_coordinates
    w endpointStripPhysicalMinusPoint endpointStripPhysicalPlusPoint
    hw hminus hplus hminusRange hplusRange
  have hPM := integrableOn_foldedRegularOriginalIntegrand_comp_coordinates
    w endpointStripPhysicalPlusPoint endpointStripPhysicalMinusPoint
    hw hplus hminus hplusRange hminusRange
  have hMM := integrableOn_foldedRegularOriginalIntegrand_comp_coordinates
    w endpointStripPhysicalMinusPoint endpointStripPhysicalMinusPoint
    hw hminus hminus hminusRange hminusRange
  have horbit : IntegrableOn
      (fun p : ℝ × ℝ ↦ endpointReflectionOrbit
        (foldedRegularOriginalIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    have h := ((hPP.add hMP).add hPM).add hMM
    apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
    intro p _hp
    unfold endpointReflectionOrbit endpointReflectFirst endpointReflectSecond
      endpointReflectBoth
    simp only [Pi.add_apply, endpointStripReflection_plusPoint]
  have hscaled : IntegrableOn
      (fun p : ℝ × ℝ ↦ (1 / 25 : ℝ) * endpointReflectionOrbit
        (foldedRegularOriginalIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := horbit.const_mul (1 / 25 : ℝ)
  apply hscaled.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  exact (endpointNormalizedRegularCrossIntegrand_eq_scaled_reflectionOrbit
    w p).symm

theorem endpointNormalizedRegularCrossIntegral_eq_endpointSquare
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedRegularCrossIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  let F : ℝ × ℝ → ℝ := foldedRegularOriginalIntegrand w
  let O : ℝ × ℝ → ℝ := endpointReflectionOrbit F
  let C : ℝ × ℝ → ℝ := fun p ↦ O
    (endpointStripPhysicalPlusPoint p.1,
      endpointStripPhysicalPlusPoint p.2)
  have hfull := integrableOn_foldedRegularOriginalIntegrand w hw
  have hBsub : endpointRawSet ⊆ positiveHalfSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hBB : IntegrableOn F (endpointRawSet ×ˢ endpointRawSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using hfull.mono_set (Set.prod_mono hBsub hBsub)
  have hO : IntegrableOn O
      (endpointUpperClosedSet ×ˢ endpointUpperClosedSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [O] using integrableOn_endpointReflectionOrbit F hBB
  have hcross := integrableOn_endpointNormalizedRegularCrossIntegrand w hw
  have hC : IntegrableOn C
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
    have hscaled : IntegrableOn
        (fun p ↦ (25 : ℝ) * endpointNormalizedRegularCrossIntegrand w p)
        (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
        ((volume : Measure ℝ).prod volume) := hcross.const_mul 25
    apply hscaled.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
    intro p _hp
    dsimp only [C, O, F]
    rw [endpointNormalizedRegularCrossIntegrand_eq_scaled_reflectionOrbit]
    ring
  have haffine :=
    setIntegral_normalizedEndpointSquare_eq_twentyFive_mul_upperSquare
      O hO hC
  have hreflect := setIntegral_endpointSquare_eq_reflectionOrbit F hBB
  calc
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedRegularCrossIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 25 : ℝ) *
        (∫ p : ℝ × ℝ in
          endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
          C p ∂((volume : Measure ℝ).prod volume)) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun
          (measurableSet_Icc.prod measurableSet_Icc)
        intro p _hp
        dsimp only [C, O, F]
        exact endpointNormalizedRegularCrossIntegrand_eq_scaled_reflectionOrbit
          w p
    _ = ∫ p : ℝ × ℝ in
        endpointUpperClosedSet ×ˢ endpointUpperClosedSet,
        O p ∂((volume : Measure ℝ).prod volume) := by
      rw [haffine]
      ring
    _ = ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        F p ∂((volume : Measure ℝ).prod volume) := by
      rw [hreflect]
      rfl

/-! ## Endpoint raw block -/

theorem integrableOn_reflectedDifferenceKernel_of_lipschitzOnWith
    {C : NNReal} (f : ℝ → ℝ) (hf : Continuous f)
    (hC : LipschitzOnWith C f (Icc (-1 : ℝ) 1)) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ (f p.1 - f p.2) ^ 2 / (p.1 + p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let P : Set (ℝ × ℝ) := positiveHalfSet ×ˢ positiveHalfSet
  let J : ℝ × ℝ → ℝ := fun p ↦
    (f p.1 - f p.2) ^ 2 / (p.1 + p.2)
  let D : ℝ × ℝ → ℝ := fun p ↦
    (C : ℝ) ^ 2 * (p.1 + p.2)
  have hD : IntegrableOn D P ((volume : Measure ℝ).prod volume) := by
    exact (by fun_prop : Continuous D).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hJmeas : AEStronglyMeasurable J
      (((volume : Measure ℝ).prod volume).restrict P) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [J]
    exact (((hf.measurable.comp measurable_fst).sub
      (hf.measurable.comp measurable_snd)).pow_const 2).div
        (measurable_fst.add measurable_snd)
  have hdom : ∀ᵐ p ∂(((volume : Measure ℝ).prod volume).restrict P),
      ‖J p‖ ≤ D p := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hxmem : p.1 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hp.1.1], hp.1.2⟩
    have hymem : p.2 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hp.2.1], hp.2.2⟩
    have hbound : |f p.1 - f p.2| ≤ (C : ℝ) * |p.1 - p.2| := by
      simpa only [Real.dist_eq] using hC.dist_le_mul p.1 hxmem p.2 hymem
    have hsum0 : 0 ≤ p.1 + p.2 := add_nonneg hp.1.1 hp.2.1
    have hdiffsum : |p.1 - p.2| ≤ p.1 + p.2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.2.1]
    have hbound' : |f p.1 - f p.2| ≤ (C : ℝ) * (p.1 + p.2) :=
      hbound.trans (mul_le_mul_of_nonneg_left hdiffsum C.property)
    dsimp only [J, D]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) hsum0)]
    by_cases hsum : p.1 + p.2 = 0
    · simp [hsum]
    · have hsumPos : 0 < p.1 + p.2 :=
        lt_of_le_of_ne hsum0 (Ne.symm hsum)
      rw [div_le_iff₀ hsumPos]
      have hright0 : 0 ≤ (C : ℝ) * (p.1 + p.2) :=
        mul_nonneg C.property hsum0
      have hsq :=
        (sq_le_sq₀ (abs_nonneg (f p.1 - f p.2)) hright0).2 hbound'
      rw [sq_abs, mul_pow] at hsq
      nlinarith
  simpa only [P, J] using hD.mono' hJmeas hdom

def endpointNormalizedEvenRawIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (stripSameDifferenceReserveWeight p.1 p.2 +
      stripSameCrossReserveWeight p.1 p.2) *
    (fourCellOddEndpointStripEven w p.1 -
      fourCellOddEndpointStripEven w p.2) ^ 2

def endpointNormalizedReflectedRawIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  stripReflectedRawBlockPair
    (stripReflectedPPReserveWeight p.1 p.2)
    (stripReflectedMMReserveWeight p.1 p.2)
    (stripReflectedPMReserveWeight p.1 p.2)
    (stripReflectedMPReserveWeight p.1 p.2)
    (stripParityValue (fourCellOddEndpointStripEven w p.1)
      (fourCellOddEndpointStripOdd w p.1) 1)
    (stripParityValue (fourCellOddEndpointStripEven w p.1)
      (fourCellOddEndpointStripOdd w p.1) (-1))
    (stripParityValue (fourCellOddEndpointStripEven w p.2)
      (fourCellOddEndpointStripOdd w p.2) 1)
    (stripParityValue (fourCellOddEndpointStripEven w p.2)
      (fourCellOddEndpointStripOdd w p.2) (-1))

theorem endpointNormalizedRawBlockIntegrand_eq_even_add_reflected
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    endpointNormalizedRawBlockIntegrand w p =
      endpointNormalizedEvenRawIntegrand w p +
        endpointNormalizedReflectedRawIntegrand w p := by
  unfold endpointNormalizedRawBlockIntegrand
    endpointNormalizedEvenRawIntegrand
    endpointNormalizedReflectedRawIntegrand
  rw [endpointStripRawReserveBlockPair_eq_survivingSquares]
  unfold stripReflectedRawBlockPair
  ring

theorem endpointNormalizedEvenRawIntegrand_eq_scaled_coupled
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    endpointNormalizedEvenRawIntegrand w p =
      (1 / 5 : ℝ) *
        (centeredLogDifferenceKernel
            (fourCellOddEndpointStripEven w) p.1 p.2 +
          (fourCellOddEndpointStripEven w p.1 -
            fourCellOddEndpointStripEven w p.2) ^ 2 / (p.1 + p.2)) := by
  unfold endpointNormalizedEvenRawIntegrand
    stripSameDifferenceReserveWeight stripSameCrossReserveWeight
    centeredLogDifferenceKernel
  by_cases hdiff : |p.1 - p.2| = 0 <;>
    by_cases hsum : p.1 + p.2 = 0
  all_goals simp only [hdiff, hsum, inv_zero, mul_zero,
    div_eq_mul_inv]
  all_goals field_simp [hdiff, hsum]
  all_goals ring

theorem integrableOn_endpointNormalizedEvenRawIntegrand
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    IntegrableOn (endpointNormalizedEvenRawIntegrand w)
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
  let e : ℝ → ℝ := fourCellOddEndpointStripEven w
  have he : ContDiff ℝ 1 e := by
    dsimp only [e]
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fun_prop
  have helocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e :=
    he.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ :=
    helocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hsameFull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith e hC
  have hsub : positiveHalfSet ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hsame : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel e p.1 p.2)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    hsameFull.mono_set (Set.prod_mono hsub hsub)
  have hreflected :=
    integrableOn_reflectedDifferenceKernel_of_lipschitzOnWith
      e he.continuous hC
  have h : IntegrableOn
      (fun p : ℝ × ℝ ↦ (1 / 5 : ℝ) *
        (centeredLogDifferenceKernel e p.1 p.2 +
          (e p.1 - e p.2) ^ 2 / (p.1 + p.2)))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    (hsame.add hreflected).const_mul (1 / 5 : ℝ)
  apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  dsimp only [e]
  exact (endpointNormalizedEvenRawIntegrand_eq_scaled_coupled w p).symm

theorem endpointNormalizedReflectedRawIntegrand_eq_scaled_reflectionOrbit
    (w : ℝ → ℝ) (p : ℝ × ℝ) :
    endpointNormalizedReflectedRawIntegrand w p =
      (1 / 25 : ℝ) * endpointReflectionOrbit
        (positiveHalfReflectedReserveIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2) := by
  unfold endpointNormalizedReflectedRawIntegrand
  rw [endpointStripParityValue_one, endpointStripParityValue_neg_one,
    endpointStripParityValue_one, endpointStripParityValue_neg_one]
  unfold stripReflectedRawBlockPair
  rw [stripReflectedPPReserveWeight_eq_pulledBack,
    stripReflectedMMReserveWeight_eq_pulledBack,
    stripReflectedPMReserveWeight_eq_pulledBack,
    stripReflectedMPReserveWeight_eq_pulledBack]
  unfold endpointReflectionOrbit endpointReflectFirst endpointReflectSecond
    endpointReflectBoth positiveHalfReflectedReserveIntegrand
  simp only [endpointStripReflection_plusPoint]
  ring

theorem integrableOn_positiveHalfReflectedReserveIntegrand_comp_coordinates
    (w u v : ℝ → ℝ) (hw : Continuous w)
    (hu : Continuous u) (hv : Continuous v)
    (huPos : ∀ x ∈ positiveHalfSet, 0 < u x)
    (hvPos : ∀ x ∈ positiveHalfSet, 0 < v x) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ positiveHalfReflectedReserveIntegrand w
        (u p.1, v p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let Q : ℝ × ℝ → ℝ := fun p ↦
    (w (u p.1) + w (v p.2)) ^ 2 / (2 * (u p.1 + v p.2))
  have hQcont : ContinuousOn Q (positiveHalfSet ×ˢ positiveHalfSet) := by
    apply ContinuousOn.div (by fun_prop : Continuous
      (fun p : ℝ × ℝ ↦ (w (u p.1) + w (v p.2)) ^ 2)).continuousOn
      (by fun_prop : Continuous
        (fun p : ℝ × ℝ ↦ 2 * (u p.1 + v p.2))).continuousOn
    intro p hp
    have hup := huPos p.1 hp.1
    have hvp := hvPos p.2 hp.2
    positivity
  have hQ : IntegrableOn Q (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    hQcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply hQ.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p hp
  have hsum : u p.1 + v p.2 ≠ 0 := by
    have hup := huPos p.1 hp.1
    have hvp := hvPos p.2 hp.2
    positivity
  unfold positiveHalfReflectedReserveIntegrand
    positiveHalfReflectedReserveWeight
  dsimp only [Q]
  field_simp [hsum]

theorem integrableOn_endpointNormalizedReflectedRawIntegrand
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntegrableOn (endpointNormalizedReflectedRawIntegrand w)
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
  have hplus : Continuous endpointStripPhysicalPlusPoint := by
    unfold endpointStripPhysicalPlusPoint
    fun_prop
  have hminus : Continuous endpointStripPhysicalMinusPoint := by
    unfold endpointStripPhysicalMinusPoint
    fun_prop
  have hplusPos : ∀ x ∈ positiveHalfSet,
      0 < endpointStripPhysicalPlusPoint x := by
    intro x hx
    unfold endpointStripPhysicalPlusPoint
    linarith [hx.1, hx.2]
  have hminusPos : ∀ x ∈ positiveHalfSet,
      0 < endpointStripPhysicalMinusPoint x := by
    intro x hx
    unfold endpointStripPhysicalMinusPoint
    linarith [hx.1, hx.2]
  have hPP :=
    integrableOn_positiveHalfReflectedReserveIntegrand_comp_coordinates
      w endpointStripPhysicalPlusPoint endpointStripPhysicalPlusPoint
      hw hplus hplus hplusPos hplusPos
  have hMP :=
    integrableOn_positiveHalfReflectedReserveIntegrand_comp_coordinates
      w endpointStripPhysicalMinusPoint endpointStripPhysicalPlusPoint
      hw hminus hplus hminusPos hplusPos
  have hPM :=
    integrableOn_positiveHalfReflectedReserveIntegrand_comp_coordinates
      w endpointStripPhysicalPlusPoint endpointStripPhysicalMinusPoint
      hw hplus hminus hplusPos hminusPos
  have hMM :=
    integrableOn_positiveHalfReflectedReserveIntegrand_comp_coordinates
      w endpointStripPhysicalMinusPoint endpointStripPhysicalMinusPoint
      hw hminus hminus hminusPos hminusPos
  have horbit : IntegrableOn
      (fun p : ℝ × ℝ ↦ endpointReflectionOrbit
        (positiveHalfReflectedReserveIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    have h := ((hPP.add hMP).add hPM).add hMM
    apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
    intro p _hp
    unfold endpointReflectionOrbit endpointReflectFirst endpointReflectSecond
      endpointReflectBoth
    simp only [Pi.add_apply, endpointStripReflection_plusPoint]
  have hscaled : IntegrableOn
      (fun p : ℝ × ℝ ↦ (1 / 25 : ℝ) * endpointReflectionOrbit
        (positiveHalfReflectedReserveIntegrand w)
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := horbit.const_mul (1 / 25 : ℝ)
  apply hscaled.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  exact
    (endpointNormalizedReflectedRawIntegrand_eq_scaled_reflectionOrbit w p).symm

theorem integrableOn_endpointNormalizedRawBlockIntegrand
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    IntegrableOn (endpointNormalizedRawBlockIntegrand w)
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
  have heven := integrableOn_endpointNormalizedEvenRawIntegrand w hw
  have hreflected :=
    integrableOn_endpointNormalizedReflectedRawIntegrand w hw.continuous
  apply (heven.add hreflected).congr_fun _
    (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  exact (endpointNormalizedRawBlockIntegrand_eq_even_add_reflected w p).symm

theorem setIntegral_scaled_normalizedReflectionOrbit_eq_endpointSquare
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (endpointRawSet ×ˢ endpointRawSet)
      ((volume : Measure ℝ).prod volume))
    (hcomp : IntegrableOn
      (fun p : ℝ × ℝ ↦ endpointReflectionOrbit F
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2))
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      (1 / 25 : ℝ) * endpointReflectionOrbit F
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2)
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        F p ∂((volume : Measure ℝ).prod volume) := by
  let O : ℝ × ℝ → ℝ := endpointReflectionOrbit F
  have hO : IntegrableOn O
      (endpointUpperClosedSet ×ˢ endpointUpperClosedSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [O] using integrableOn_endpointReflectionOrbit F hF
  have haffine :=
    setIntegral_normalizedEndpointSquare_eq_twentyFive_mul_upperSquare
      O hO (by simpa only [O] using hcomp)
  have hreflect := setIntegral_endpointSquare_eq_reflectionOrbit F hF
  calc
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      (1 / 25 : ℝ) * endpointReflectionOrbit F
        (endpointStripPhysicalPlusPoint p.1,
          endpointStripPhysicalPlusPoint p.2)
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 25 : ℝ) *
        (∫ p : ℝ × ℝ in
          endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
          O (endpointStripPhysicalPlusPoint p.1,
            endpointStripPhysicalPlusPoint p.2)
            ∂((volume : Measure ℝ).prod volume)) := by
      rw [integral_const_mul]
    _ = ∫ p : ℝ × ℝ in
        endpointUpperClosedSet ×ˢ endpointUpperClosedSet,
        O p ∂((volume : Measure ℝ).prod volume) := by
      rw [haffine]
      ring
    _ = ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        F p ∂((volume : Measure ℝ).prod volume) := by
      rw [hreflect]
      rfl

theorem endpointNormalizedEvenRawIntegral_eq_half_evenRawEnergy
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedEvenRawIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w := by
  let e : ℝ → ℝ := fourCellOddEndpointStripEven w
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel e p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (e p.1 - e p.2) ^ 2 / (p.1 + p.2)
  have he : ContDiff ℝ 1 e := by
    dsimp only [e]
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fun_prop
  have helocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e :=
    he.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ :=
    helocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hfull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith e hC
  have hsub : positiveHalfSet ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hK : IntegrableOn K (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K] using hfull.mono_set (Set.prod_mono hsub hsub)
  have hJ : IntegrableOn J (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [J] using
      integrableOn_reflectedDifferenceKernel_of_lipschitzOnWith
        e he.continuous hC
  have hKiter := intervalIntegral_integral_eq_setIntegral_square
    K 0 1 (by norm_num) hK
  have hJiter := intervalIntegral_integral_eq_setIntegral_square
    J 0 1 (by norm_num) hJ
  have hparity := centeredRawLogEnergy_div_four_eq_positiveHalf_even
    e helocal (fourCellOddEndpointStripEven_even w)
  unfold fourCellPositiveHalfRawSameSignEnergy
    fourCellPositiveHalfRawReflectedEnergy at hparity
  simp only [one_mul] at hparity
  have hsum :
      (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        (K p + J p) ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        K p ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        J p ∂((volume : Measure ℝ).prod volume) := integral_add hK hJ
  calc
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedEvenRawIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 5 : ℝ) *
        ((∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
          K p ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
          J p ∂((volume : Measure ℝ).prod volume)) := by
      rw [← hsum, ← integral_const_mul]
      apply setIntegral_congr_fun
        (measurableSet_Icc.prod measurableSet_Icc)
      intro p _hp
      dsimp only [K, J, e]
      exact endpointNormalizedEvenRawIntegrand_eq_scaled_coupled w p
    _ = (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w := by
      have hsumEq :
          (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
            K p ∂((volume : Measure ℝ).prod volume)) +
            (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
              J p ∂((volume : Measure ℝ).prod volume)) =
          (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, K (x, y)) +
            ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, J (x, y) := by
        simpa only [positiveHalfSet] using congrArg₂
          (fun a b : ℝ ↦ a + b) hKiter.symm hJiter.symm
      rw [hsumEq]
      dsimp only [K, J]
      unfold centeredLogDifferenceKernel
      unfold fourCellOddEndpointStripEvenRawEnergy
      dsimp only [e] at hparity
      linarith

theorem integrableOn_positiveHalfReflectedReserveIntegrand
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    IntegrableOn (positiveHalfReflectedReserveIntegrand w)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ :=
    hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hreflected :=
    integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
      w hw.continuous hC hodd
  have h : IntegrableOn
      (fun p : ℝ × ℝ ↦ (1 / 2 : ℝ) *
        ((w p.1 + w p.2) ^ 2 / (p.1 + p.2)))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    hreflected.const_mul (1 / 2 : ℝ)
  apply h.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  unfold positiveHalfReflectedReserveIntegrand
    positiveHalfReflectedReserveWeight
  by_cases hsum : p.1 + p.2 = 0
  · simp [hsum]
  · field_simp [hsum]

theorem endpointNormalizedReflectedRawIntegral_eq_half_reflectedRaw
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedReflectedRawIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w := by
  let F : ℝ × ℝ → ℝ := positiveHalfReflectedReserveIntegrand w
  let C : ℝ × ℝ → ℝ := fun p ↦ endpointReflectionOrbit F
    (endpointStripPhysicalPlusPoint p.1,
      endpointStripPhysicalPlusPoint p.2)
  have hfull := integrableOn_positiveHalfReflectedReserveIntegrand
    w hw hodd
  have hBsub : endpointRawSet ⊆ positiveHalfSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hBB : IntegrableOn F (endpointRawSet ×ˢ endpointRawSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using hfull.mono_set (Set.prod_mono hBsub hBsub)
  have hreflectedNorm :=
    integrableOn_endpointNormalizedReflectedRawIntegrand w hw.continuous
  have hC : IntegrableOn C
      (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
      ((volume : Measure ℝ).prod volume) := by
    have hscaled : IntegrableOn
        (fun p ↦ (25 : ℝ) * endpointNormalizedReflectedRawIntegrand w p)
        (endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet)
        ((volume : Measure ℝ).prod volume) := hreflectedNorm.const_mul 25
    apply hscaled.congr_fun _ (measurableSet_Icc.prod measurableSet_Icc)
    intro p _hp
    dsimp only [C, F]
    rw [endpointNormalizedReflectedRawIntegrand_eq_scaled_reflectionOrbit]
    ring
  have htransport :=
    setIntegral_scaled_normalizedReflectionOrbit_eq_endpointSquare
      F hBB hC
  calc
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedReflectedRawIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
        (1 / 25 : ℝ) * C p
          ∂((volume : Measure ℝ).prod volume) := by
      apply setIntegral_congr_fun
        (measurableSet_Icc.prod measurableSet_Icc)
      intro p _hp
      dsimp only [C, F]
      exact endpointNormalizedReflectedRawIntegrand_eq_scaled_reflectionOrbit
        w p
    _ = ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        F p ∂((volume : Measure ℝ).prod volume) := by
      simpa only [C] using htransport
    _ = (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w := by
      unfold endpointReflectedRawSetIntegral F
        positiveHalfReflectedReserveIntegrand
        positiveHalfReflectedReserveWeight
      rw [← integral_const_mul]
      apply setIntegral_congr_fun
        (measurableSet_Icc.prod measurableSet_Icc)
      intro p hp
      have hsum : p.1 + p.2 ≠ 0 := by
        have hx : 0 < p.1 := by linarith [hp.1.1]
        have hy : 0 < p.2 := by linarith [hp.2.1]
        positivity
      field_simp [hsum]

theorem endpointNormalizedRawBlockIntegral_eq_endpointContribution
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedRawBlockIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w := by
  have heven := integrableOn_endpointNormalizedEvenRawIntegrand w hw
  have hreflected :=
    integrableOn_endpointNormalizedReflectedRawIntegrand w hw.continuous
  calc
    (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
      endpointNormalizedRawBlockIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
        (endpointNormalizedEvenRawIntegrand w p +
          endpointNormalizedReflectedRawIntegrand w p)
          ∂((volume : Measure ℝ).prod volume) := by
      apply setIntegral_congr_fun
        (measurableSet_Icc.prod measurableSet_Icc)
      intro p _hp
      exact endpointNormalizedRawBlockIntegrand_eq_even_add_reflected w p
    _ = (∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
        endpointNormalizedEvenRawIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in
        endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet,
        endpointNormalizedReflectedRawIntegrand w p
          ∂((volume : Measure ℝ).prod volume) :=
      integral_add heven hreflected
    _ = (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w := by
      rw [endpointNormalizedEvenRawIntegral_eq_half_evenRawEnergy w hw,
        endpointNormalizedReflectedRawIntegral_eq_half_reflectedRaw
          w hw hodd]
      ring

/-- Integrated endpoint-square retention.  The zero coordinate axes are
null, so the strict pointwise hypotheses are discharged on `Ioc 0 1` and
then transported back to the closed square. -/
theorem nineteenTwentieths_mul_endpointContribution_le_add_regularSquare
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (19 / 20 : ℝ) *
        ((1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
          (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w) ≤
      ((1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  let S : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
  let P : Set (ℝ × ℝ) :=
    endpointNormalizedPositiveSet ×ˢ endpointNormalizedPositiveSet
  let R : ℝ × ℝ → ℝ := endpointNormalizedRawBlockIntegrand w
  let G : ℝ × ℝ → ℝ := endpointNormalizedRegularCrossIntegrand w
  have hR : IntegrableOn R P ((volume : Measure ℝ).prod volume) := by
    simpa only [R, P] using
      integrableOn_endpointNormalizedRawBlockIntegrand w hw
  have hG : IntegrableOn G P ((volume : Measure ℝ).prod volume) := by
    simpa only [G, P] using
      integrableOn_endpointNormalizedRegularCrossIntegrand w hw.continuous
  have hSsub : S ⊆ P := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2.1.le, hp.2.2⟩
  have hRS := hR.mono_set hSsub
  have hGS := hG.mono_set hSsub
  have hmono :
      (∫ p : ℝ × ℝ in S, (19 / 20 : ℝ) * R p
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ p : ℝ × ℝ in S, (R p + G p)
        ∂((volume : Measure ℝ).prod volume) := by
    apply setIntegral_mono_on (hRS.const_mul (19 / 20 : ℝ))
      (hRS.add hGS) (measurableSet_Ioc.prod measurableSet_Ioc)
    intro p hp
    have hpoint :=
      nineteenTwentieths_mul_endpointStripRawReserveBlockPair_le_add_regularCross
        (z := p.1) (s := p.2)
        (eZ := fourCellOddEndpointStripEven w p.1)
        (oZ := fourCellOddEndpointStripOdd w p.1)
        (eS := fourCellOddEndpointStripEven w p.2)
        (oS := fourCellOddEndpointStripOdd w p.2)
        hp.1.1 hp.1.2 hp.2.1 hp.2.2
    simpa only [R, G, endpointNormalizedRawBlockIntegrand,
      endpointNormalizedRegularCrossIntegrand] using hpoint
  have hSP : S =ᵐ[((volume : Measure ℝ).prod volume)] P := by
    dsimp only [S, P, endpointNormalizedPositiveSet]
    exact Measure.set_prod_ae_eq
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hleftEq :
      (∫ p : ℝ × ℝ in S, (19 / 20 : ℝ) * R p
        ∂((volume : Measure ℝ).prod volume)) =
      (19 / 20 : ℝ) *
        ∫ p : ℝ × ℝ in P, R p
          ∂((volume : Measure ℝ).prod volume) := by
    rw [setIntegral_congr_set hSP, integral_const_mul]
  have hrightEq :
      (∫ p : ℝ × ℝ in S, (R p + G p)
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in P, R p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in P, G p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [setIntegral_congr_set hSP, integral_add hR hG]
  rw [hleftEq, hrightEq] at hmono
  have hraw := endpointNormalizedRawBlockIntegral_eq_endpointContribution
    w hw hodd
  have hregular := endpointNormalizedRegularCrossIntegral_eq_endpointSquare
    w hw.continuous
  dsimp only [R, G, P] at hmono
  rw [hraw, hregular] at hmono
  exact hmono

/-! ## Off-strip integration and global assembly -/

theorem rawStripCancellationReserve_eq_halfRaw_partition
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddRawStripCancellationReserve w =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      ((1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
        (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w) := by
  have hpartition := rawStripCancellationReserve_eq_partition w hw hodd
  have hAA :
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) =
      (1 / 2 : ℝ) *
        ∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ico)
    intro p _hp
    exact positiveHalfRawReserveIntegrand_eq_half_coupled w p
  have hBA :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) =
      (1 / 2 : ℝ) *
        ∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ico)
    intro p _hp
    exact positiveHalfRawReserveIntegrand_eq_half_coupled w p
  rw [hAA, hBA]
  linarith

theorem foldedRegularIntegral_eq_partition
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
      foldedRegularOriginalIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  exact setIntegral_positiveHalfSquare_eq_lower_cross_endpoint
    (foldedRegularOriginalIntegrand w)
    (integrableOn_foldedRegularOriginalIntegrand w hw)
    (foldedRegularOriginalIntegrand_symmetric w)

theorem nineteenTwentieths_mul_rawIntegral_le_add_regularIntegral_of_region
    (w : ℝ → ℝ) (S : Set (ℝ × ℝ))
    (hSmeas : MeasurableSet S)
    (hSrange : ∀ p ∈ S,
      0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (hraw : IntegrableOn (positiveHalfRawReserveIntegrand w) S
      ((volume : Measure ℝ).prod volume))
    (hregular : IntegrableOn (foldedRegularOriginalIntegrand w) S
      ((volume : Measure ℝ).prod volume)) :
    (19 / 20 : ℝ) *
        (∫ p : ℝ × ℝ in S, positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) ≤
      (∫ p : ℝ × ℝ in S, positiveHalfRawReserveIntegrand w p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in S, foldedRegularOriginalIntegrand w p
        ∂((volume : Measure ℝ).prod volume) := by
  rw [← integral_const_mul, ← integral_add hraw hregular]
  apply setIntegral_mono_on (hraw.const_mul (19 / 20 : ℝ))
    (hraw.add hregular) hSmeas
  intro p hp
  rcases hSrange p hp with ⟨hx, hx1, hy, hy1⟩
  have hpoint :=
    nineteenTwentieths_mul_positiveHalfRawReservePair_le_sub_foldedRegularCross
      (x := p.1) (y := p.2) (wX := w p.1) (wY := w p.2)
      hx hx1 hy hy1
  simp only [Pi.add_apply]
  simp only [positiveHalfRawReserveIntegrand,
    foldedRegularOriginalIntegrand, sub_eq_add_neg, mul_assoc] at hpoint ⊢
  nlinarith

theorem nineteenTwentieths_mul_lowerLowerRawIntegral_le_add_regular
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (19 / 20 : ℝ) *
        (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
          positiveHalfRawReserveIntegrand w p
            ∂((volume : Measure ℝ).prod volume)) ≤
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  let S : Set (ℝ × ℝ) := Ioc (0 : ℝ) (3 / 5) ×ˢ Ioc (0 : ℝ) (3 / 5)
  let T : Set (ℝ × ℝ) := lowerRawSet ×ˢ lowerRawSet
  have hrawFull := integrableOn_positiveHalfRawReserveIntegrand w hw hodd
  have hregularFull :=
    integrableOn_foldedRegularOriginalIntegrand w hw.continuous
  have hTsub : T ⊆ positiveHalfSet ×ˢ positiveHalfSet := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.le.trans (by norm_num)⟩,
      hp.2.1, hp.2.2.le.trans (by norm_num)⟩
  have hSsub : S ⊆ positiveHalfSet ×ˢ positiveHalfSet := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.trans (by norm_num)⟩,
      hp.2.1.le, hp.2.2.trans (by norm_num)⟩
  have hmono :=
    nineteenTwentieths_mul_rawIntegral_le_add_regularIntegral_of_region
      w S (measurableSet_Ioc.prod measurableSet_Ioc) (by
        intro p hp
        exact ⟨hp.1.1, hp.1.2.trans (by norm_num),
          hp.2.1, hp.2.2.trans (by norm_num)⟩)
      (hrawFull.mono_set hSsub) (hregularFull.mono_set hSsub)
  have hST : S =ᵐ[((volume : Measure ℝ).prod volume)] T := by
    dsimp only [S, T, lowerRawSet]
    exact Measure.set_prod_ae_eq
      (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm
      (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm
  have hrawEq := setIntegral_congr_set
    (f := positiveHalfRawReserveIntegrand w) hST
  have hregularEq := setIntegral_congr_set
    (f := foldedRegularOriginalIntegrand w) hST
  rw [hrawEq, hregularEq] at hmono
  exact hmono

theorem nineteenTwentieths_mul_endpointLowerRawIntegral_le_add_regular
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (19 / 20 : ℝ) *
        (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
          positiveHalfRawReserveIntegrand w p
            ∂((volume : Measure ℝ).prod volume)) ≤
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        positiveHalfRawReserveIntegrand w p
          ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  let S : Set (ℝ × ℝ) := endpointRawSet ×ˢ Ioc (0 : ℝ) (3 / 5)
  let T : Set (ℝ × ℝ) := endpointRawSet ×ˢ lowerRawSet
  have hrawFull := integrableOn_positiveHalfRawReserveIntegrand w hw hodd
  have hregularFull :=
    integrableOn_foldedRegularOriginalIntegrand w hw.continuous
  have hSsub : S ⊆ positiveHalfSet ×ˢ positiveHalfSet := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩,
      hp.2.1.le, hp.2.2.trans (by norm_num)⟩
  have hmono :=
    nineteenTwentieths_mul_rawIntegral_le_add_regularIntegral_of_region
      w S (measurableSet_Icc.prod measurableSet_Ioc) (by
        intro p hp
        exact ⟨by linarith [hp.1.1], hp.1.2,
          hp.2.1, hp.2.2.trans (by norm_num)⟩)
      (hrawFull.mono_set hSsub) (hregularFull.mono_set hSsub)
  have hST : S =ᵐ[((volume : Measure ℝ).prod volume)] T := by
    dsimp only [S, T, lowerRawSet]
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl)
      (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm
  have hrawEq := setIntegral_congr_set
    (f := positiveHalfRawReserveIntegrand w) hST
  have hregularEq := setIntegral_congr_set
    (f := foldedRegularOriginalIntegrand w) hST
  rw [hrawEq, hregularEq] at hmono
  exact hmono

/-- The complete folded regular correlation consumes at most one twentieth
of the exact raw strip-cancellation reserve.  Every term is integrated with
its original sign; no absolute-value regular-kernel estimate is inserted. -/
theorem nineteenTwentieths_mul_rawStripCancellationReserve_le_add_foldedRegular
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve w ≤
      fourCellOddRawStripCancellationReserve w +
      ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  have hraw := rawStripCancellationReserve_eq_halfRaw_partition w hw hodd
  have hregular := foldedRegularIntegral_eq_partition w hw.continuous
  have hAA :=
    nineteenTwentieths_mul_lowerLowerRawIntegral_le_add_regular
      w hw hodd
  have hBA :=
    nineteenTwentieths_mul_endpointLowerRawIntegral_le_add_regular
      w hw hodd
  have hE := nineteenTwentieths_mul_endpointContribution_le_add_regularSquare
    w hw hodd
  rw [hraw, hregular]
  nlinarith

/-- Production normalization of the integrated retention theorem, expressed
directly with the one-dimensional regular correlation occurring in the odd
four-cell core. -/
theorem nineteenTwentieths_mul_fourCellOddRawStripCancellationReserve_le_sub_regularCorrelation
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve w ≤
      fourCellOddRawStripCancellationReserve w -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  have hretain :=
    nineteenTwentieths_mul_rawStripCancellationReserve_le_add_foldedRegular
      w hw hodd
  have hregular := neg_regularCorrelation_eq_foldedRegularSetIntegral
    w hw.continuous hodd
  linarith

/-! ## Production payoff: coercivity of the actual odd core -/

/-- The retained diagonal from the nineteen-twentieths scalar analysis is a
genuine lower bound for the actual odd four-cell core. -/
theorem fourCellOddNineteenTwentiethsRetainedQuadratic_le_coreLocalQuadratic
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddNineteenTwentiethsRetainedQuadratic w ≤
      fourCellOddCoreLocalQuadratic w := by
  have hretain :=
    nineteenTwentieths_mul_fourCellOddRawStripCancellationReserve_le_sub_regularCorrelation
      w hw hodd
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddNineteenTwentiethsRetainedQuadratic
    fourCellOddLocalScalarMassCoefficient
    fourCellOddRetainedEndpointQuadratic
    fourCellOddSignedMassRegularQuadratic
  linarith

/-- Exact scalar coercivity of the actual odd core on the production
`P₁`-orthogonal sector. -/
theorem coercivityConstant_mul_positiveHalfMass_le_coreLocalQuadratic_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    fourCellOddNineteenTwentiethsCoercivityConstant *
        (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddCoreLocalQuadratic w :=
  (coercivityConstant_mul_positiveHalfMass_le_retainedQuadratic_of_P1
    w hw hodd hone).trans
      (fourCellOddNineteenTwentiethsRetainedQuadratic_le_coreLocalQuadratic
        w hw hodd)

/-- Purely rational coercivity of the actual odd core, ready for exact Riesz
and Galerkin quotient estimates. -/
theorem threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_coreLocalQuadratic_of_P1
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    (343 / 12500 : ℝ) * (∫ x : ℝ in 0..1, w x ^ 2) ≤
      fourCellOddCoreLocalQuadratic w :=
  (threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_retainedQuadratic_of_P1
    w hw hodd hone).trans
      (fourCellOddNineteenTwentiethsRetainedQuadratic_le_coreLocalQuadratic
        w hw hodd)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
