import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# The complete Bombieri cross as a Hermitian sesquilinear form

The local critical cross and the polarized prime cross must remain coupled.
Their difference is nevertheless a genuine Hermitian sesquilinear form on
the full Bombieri test space.  We prove the scalar laws directly from the
two real polarization coordinates and bundle the result for later operator
and lattice arguments.
-/

private theorem bombieriPolarizedPrimeCross_re
    (f g : BombieriTest) :
    (bombieriPolarizedPrimeCross f g).re =
      (primeSum (bombieriQuadraticCrossTest f g)).re / 2 := by
  unfold bombieriPolarizedPrimeCross
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    mul_zero, sub_zero]

private theorem bombieriPolarizedPrimeCross_im
    (f g : BombieriTest) :
    (bombieriPolarizedPrimeCross f g).im =
      -(primeSum
        (bombieriQuadraticCrossTest f (Complex.I • g))).re / 2 := by
  unfold bombieriPolarizedPrimeCross
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero]
  ring

/-- Complex polarization of the prime contribution is linear in its second
seed. -/
theorem bombieriPolarizedPrimeCross_smul_right
    (f g : BombieriTest) (c : ℂ) :
    bombieriPolarizedPrimeCross f (c • g) =
      c * bombieriPolarizedPrimeCross f g := by
  have hreal :=
    primeSum_bombieriQuadraticCrossTest_smul_re_eq_polarized f g c
  have himag :=
    primeSum_bombieriQuadraticCrossTest_smul_re_eq_polarized
      f g (Complex.I * c)
  have hscale :
      Complex.I • (c • g) = (Complex.I * c) • g := by
    ext x
    simp only [TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  apply Complex.ext
  · rw [bombieriPolarizedPrimeCross_re]
    linarith
  · rw [bombieriPolarizedPrimeCross_im]
    rw [hscale]
    have hrotate :
        (Complex.I * c * bombieriPolarizedPrimeCross f g).re =
          -(c * bombieriPolarizedPrimeCross f g).im := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, zero_sub]
      ring
    linarith

/-- The full local-minus-prime symbol is complex-linear in its second seed. -/
theorem bombieriTwoBlockGlobalCrossSymbol_smul_right
    (f g : BombieriTest) (c : ℂ) :
    bombieriTwoBlockGlobalCrossSymbol f (c • g) =
      c * bombieriTwoBlockGlobalCrossSymbol f g := by
  unfold bombieriTwoBlockGlobalCrossSymbol
  rw [map_smul, bombieriPolarizedPrimeCross_smul_right]
  simp only [smul_eq_mul]
  ring

/-- The full symbol is conjugate-linear in its first seed. -/
theorem bombieriTwoBlockGlobalCrossSymbol_smul_left
    (c : ℂ) (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol (c • f) g =
      starRingEnd ℂ c * bombieriTwoBlockGlobalCrossSymbol f g := by
  calc
    bombieriTwoBlockGlobalCrossSymbol (c • f) g =
        starRingEnd ℂ
          (bombieriTwoBlockGlobalCrossSymbol g (c • f)) := by
      simpa only [starRingEnd_apply] using
        (bombieriTwoBlockGlobalCrossSymbol_conj_swap (c • f) g).symm
    _ = starRingEnd ℂ
        (c * bombieriTwoBlockGlobalCrossSymbol g f) := by
      rw [bombieriTwoBlockGlobalCrossSymbol_smul_right]
    _ = starRingEnd ℂ c *
        starRingEnd ℂ (bombieriTwoBlockGlobalCrossSymbol g f) := by
      rw [map_mul]
    _ = starRingEnd ℂ c *
        bombieriTwoBlockGlobalCrossSymbol f g := by
      rw [show starRingEnd ℂ
          (bombieriTwoBlockGlobalCrossSymbol g f) =
            bombieriTwoBlockGlobalCrossSymbol f g by
        simpa only [starRingEnd_apply] using
          bombieriTwoBlockGlobalCrossSymbol_conj_swap f g]

/-- The complete global Bombieri cross, bundled as a Hermitian sesquilinear
form.  Its value is definitionally the cancellation-preserving symbol used
by the finite lattice Gram expansion. -/
def bombieriTwoBlockGlobalCrossForm :
    BombieriTest →ₗ⋆[ℂ] BombieriTest →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := bombieriTwoBlockGlobalCrossSymbol f
      map_add' := bombieriTwoBlockGlobalCrossSymbol_add_right f
      map_smul' := fun c g ↦ by
        simpa only [smul_eq_mul] using
          bombieriTwoBlockGlobalCrossSymbol_smul_right f g c }
  map_add' f g := by
    ext h
    exact bombieriTwoBlockGlobalCrossSymbol_add_left f g h
  map_smul' c f := by
    ext g
    simpa only [smul_eq_mul] using
      bombieriTwoBlockGlobalCrossSymbol_smul_left c f g

@[simp]
theorem bombieriTwoBlockGlobalCrossForm_apply
    (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossForm f g =
      bombieriTwoBlockGlobalCrossSymbol f g := rfl

/-- The bundled form is Hermitian. -/
theorem bombieriTwoBlockGlobalCrossForm_conj_apply
    (f g : BombieriTest) :
    star (bombieriTwoBlockGlobalCrossForm g f) =
      bombieriTwoBlockGlobalCrossForm f g := by
  exact bombieriTwoBlockGlobalCrossSymbol_conj_swap f g

/-- Its diagonal is exactly the full Bombieri quadratic functional. -/
theorem bombieriTwoBlockGlobalCrossForm_self
    (g : BombieriTest) :
    bombieriTwoBlockGlobalCrossForm g g =
      bombieriFunctional (bombieriQuadraticTest g) := by
  exact bombieriTwoBlockGlobalCrossSymbol_self g

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
