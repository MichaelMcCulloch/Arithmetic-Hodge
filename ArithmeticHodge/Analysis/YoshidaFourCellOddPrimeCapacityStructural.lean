import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddPrimeCapacityStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialBound
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellEvenCapacityStructural

/-!
# Structural endpoint capacity in the odd four-cell channel

The determinant used in the even channel is insensitive to the sign of the
second endpoint value.  Applying it with that value negated gives the lower
bound required when the odd dyadic translation is adverse.  A favorable odd
prime contribution must instead be retained; the theorem below is therefore
an adverse-sector tool, not an unconditional replacement of the prime atom.
-/

/-- The odd prime atom is bounded below by minus `99 / 100` of the two
reflected endpoint potentials.  Equivalently, one percent of the strip
potential survives regardless of the sign of the reflected product. -/
theorem neg_endpointStripPotential_le_neg_dyadicPairing
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(99 / 50 : ℝ) *
        (∫ x : ℝ in 3 / 5..1,
          yoshidaEndpointPotential x * w x ^ 2) ≤
      -(Real.sqrt 2 * Real.log 2) * fourCellEndpointPairing w := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  let reflectedProduct : ℝ → ℝ := fun x ↦ w x * w (8 / 5 - x)
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq w hw
  have hsubset : uIcc (3 / 5 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith
  have hpotential : IntervalIntegrable g volume (3 / 5) 1 := by
    dsimp only [g]
    exact IntervalIntegrable.mono_set hpotentialFull hsubset
  have hreflectedPotential : IntervalIntegrable (fun x ↦ g (8 / 5 - x))
      volume (3 / 5) 1 := by
    convert (hpotential.comp_sub_left (8 / 5)).symm using 1 <;> norm_num
  have hleft : IntervalIntegrable
      (fun x ↦ -(99 / 100 : ℝ) * (g x + g (8 / 5 - x)))
      volume (3 / 5) 1 :=
    (hpotential.add hreflectedPotential).const_mul (-(99 / 100))
  have hright : IntervalIntegrable
      (fun x ↦ Real.sqrt 2 * Real.log 2 * reflectedProduct x)
      volume (3 / 5) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [reflectedProduct]
    fun_prop
  have hmono :
      (∫ x : ℝ in 3 / 5..1,
          -(99 / 100 : ℝ) * (g x + g (8 / 5 - x))) ≤
        ∫ x : ℝ in 3 / 5..1,
          Real.sqrt 2 * Real.log 2 * reflectedProduct x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hright
    intro x hx
    have hpoint :=
      fourCell_dyadic_product_le_reflected_endpointPotentials
        hx.1 hx.2 (w x) (-w (8 / 5 - x))
    dsimp only [g, reflectedProduct]
    simp only [neg_sq] at hpoint
    nlinarith
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := g) (a := (3 / 5 : ℝ)) (b := 1) (8 / 5)
  have hreflectEq :
      (∫ x : ℝ in 3 / 5..1, g (8 / 5 - x)) =
        ∫ x : ℝ in 3 / 5..1, g x := by
    convert hreflect using 1
    all_goals norm_num
  have hmono' :
      -(99 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, g x) ≤
        Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in 3 / 5..1, reflectedProduct x) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hpotential hreflectedPotential,
      hreflectEq,
      intervalIntegral.integral_const_mul] at hmono
    linarith
  have hpair : fourCellEndpointPairing w =
      -(∫ x : ℝ in 3 / 5..1, reflectedProduct x) := by
    unfold fourCellEndpointPairing
    rw [show (fun x : ℝ ↦ w x * w (x - 8 / 5)) =
        fun x ↦ -(w x * w (8 / 5 - x)) by
      funext x
      rw [show x - 8 / 5 = -(8 / 5 - x) by ring, hodd]
      ring,
      intervalIntegral.integral_neg]
  rw [hpair]
  dsimp only [g] at hmono' ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddPrimeCapacityStructural
