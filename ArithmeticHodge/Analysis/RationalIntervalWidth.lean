import ArithmeticHodge.Analysis.RationalInterval
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.RatInterval

/-! Width and magnitude estimates for exact rational intervals. -/

/-- Endpoint width of a rational interval. -/
def width (I : RatInterval) : ℚ := I.upper - I.lower

/-- A symmetric endpoint magnitude bound. -/
def AbsBound (I : RatInterval) (B : ℚ) : Prop :=
  -B ≤ I.lower ∧ I.upper ≤ B

theorem width_nonneg {I : RatInterval} (hI : I.Valid) :
    0 ≤ width I := by
  exact sub_nonneg.mpr hI

theorem width_pure (q : ℚ) : width (pure q) = 0 := by
  change q - q = 0
  ring

theorem width_add (I J : RatInterval) :
    width (I + J) = width I + width J := by
  change
    (I.upper + J.upper) - (I.lower + J.lower) =
      (I.upper - I.lower) + (J.upper - J.lower)
  ring

theorem width_sub (I J : RatInterval) :
    width (I - J) = width I + width J := by
  change
    (I.upper - J.lower) - (I.lower - J.upper) =
      (I.upper - I.lower) + (J.upper - J.lower)
  ring

theorem valid_pure (q : ℚ) : (pure q).Valid := by
  exact le_rfl

theorem valid_add {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I + J).Valid := by
  change I.lower + J.lower ≤ I.upper + J.upper
  exact add_le_add hI hJ

theorem valid_sub {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I - J).Valid := by
  change I.lower - J.upper ≤ I.upper - J.lower
  exact sub_le_sub hI hJ

theorem valid_mul {I J : RatInterval} (_hI : I.Valid) (_hJ : J.Valid) :
    (I * J).Valid := by
  change
    min (min (I.lower * J.lower) (I.lower * J.upper))
        (min (I.upper * J.lower) (I.upper * J.upper)) ≤
      max (max (I.lower * J.lower) (I.lower * J.upper))
        (max (I.upper * J.lower) (I.upper * J.upper))
  exact (min_le_left _ _).trans ((min_le_left _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _)))

theorem absBound_pure {q B : ℚ} (hq : |q| ≤ B) :
    (pure q).AbsBound B := by
  rw [abs_le] at hq
  exact hq

theorem absBound_add
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.AbsBound BI) (hJ : J.AbsBound BJ) :
    (I + J).AbsBound (BI + BJ) := by
  unfold AbsBound at hI hJ ⊢
  constructor
  · change -(BI + BJ) ≤ I.lower + J.lower
    linarith [hI.1, hJ.1]
  · change I.upper + J.upper ≤ BI + BJ
    linarith [hI.2, hJ.2]

theorem absBound_sub
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.AbsBound BI) (hJ : J.AbsBound BJ) :
    (I - J).AbsBound (BI + BJ) := by
  unfold AbsBound at hI hJ ⊢
  constructor
  · change -(BI + BJ) ≤ I.lower - J.upper
    linarith [hI.1, hJ.2]
  · change I.upper - J.lower ≤ BI + BJ
    linarith [hI.2, hJ.1]

private theorem endpoint_abs_le_of_absBound
    {I : RatInterval} {B : ℚ} (hI : I.Valid) (hB : I.AbsBound B) :
    |I.lower| ≤ B ∧ |I.upper| ≤ B := by
  rw [abs_le, abs_le]
  exact ⟨⟨hB.1, hI.trans hB.2⟩, ⟨hB.1.trans hI, hB.2⟩⟩

private theorem center_abs_le_of_absBound
    {I : RatInterval} {B : ℚ} (hI : I.Valid) (hB : I.AbsBound B) :
    |(I.lower + I.upper) / 2| ≤ B := by
  unfold Valid at hI
  unfold AbsBound at hB
  rw [abs_le]
  constructor <;> linarith [hB.1, hB.2, hI]

theorem absBound_mul
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.Valid) (hJ : J.Valid)
    (hBI : I.AbsBound BI) (hBJ : J.AbsBound BJ)
    (hBI0 : 0 ≤ BI) (_hBJ0 : 0 ≤ BJ) :
    (I * J).AbsBound (BI * BJ) := by
  have hIends := endpoint_abs_le_of_absBound hI hBI
  have hJends := endpoint_abs_le_of_absBound hJ hBJ
  have corner_abs (x y : ℚ) (hx : |x| ≤ BI) (hy : |y| ≤ BJ) :
      |x * y| ≤ BI * BJ := by
    rw [abs_mul]
    gcongr
  have hll := corner_abs I.lower J.lower hIends.1 hJends.1
  have hlu := corner_abs I.lower J.upper hIends.1 hJends.2
  have hul := corner_abs I.upper J.lower hIends.2 hJends.1
  have huu := corner_abs I.upper J.upper hIends.2 hJends.2
  rw [abs_le] at hll hlu hul huu
  constructor
  · change
      -(BI * BJ) ≤
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper))
    exact le_min (le_min hll.1 hlu.1) (le_min hul.1 huu.1)
  · change
      max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) ≤ BI * BJ
    exact max_le (max_le hll.2 hlu.2) (max_le hul.2 huu.2)

private theorem lower_sub_center_abs
    {I : RatInterval} (hI : I.Valid) :
    |I.lower - (I.lower + I.upper) / 2| = width I / 2 := by
  unfold Valid at hI
  rw [abs_of_nonpos]
  · unfold width
    ring
  · linarith [hI]

private theorem upper_sub_center_abs
    {I : RatInterval} (hI : I.Valid) :
    |I.upper - (I.lower + I.upper) / 2| = width I / 2 := by
  unfold Valid at hI
  rw [abs_of_nonneg]
  · unfold width
    ring
  · linarith [hI]

/-- Multiplication is Lipschitz in interval width under symmetric endpoint
magnitude bounds.  This estimate avoids unfolding the four-corner hull in
downstream certificate proofs. -/
theorem width_mul_le
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.Valid) (hJ : J.Valid)
    (hBI : I.AbsBound BI) (hBJ : J.AbsBound BJ)
    (hBI0 : 0 ≤ BI) (hBJ0 : 0 ≤ BJ) :
    width (I * J) ≤ BJ * width I + BI * width J := by
  let cI : ℚ := (I.lower + I.upper) / 2
  let cJ : ℚ := (J.lower + J.upper) / 2
  let rI : ℚ := width I / 2
  let rJ : ℚ := width J / 2
  let R : ℚ := rI * BJ + BI * rJ
  have hrI : 0 ≤ rI := by
    dsimp only [rI]
    exact div_nonneg (width_nonneg hI) (by norm_num)
  have hrJ : 0 ≤ rJ := by
    dsimp only [rJ]
    exact div_nonneg (width_nonneg hJ) (by norm_num)
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hIends := endpoint_abs_le_of_absBound hI hBI
  have hJends := endpoint_abs_le_of_absBound hJ hBJ
  have hcI : |cI| ≤ BI := by
    simpa only [cI] using center_abs_le_of_absBound hI hBI
  have hIl : |I.lower - cI| = rI := by
    simpa only [cI, rI] using lower_sub_center_abs hI
  have hIu : |I.upper - cI| = rI := by
    simpa only [cI, rI] using upper_sub_center_abs hI
  have hJl : |J.lower - cJ| = rJ := by
    simpa only [cJ, rJ] using lower_sub_center_abs hJ
  have hJu : |J.upper - cJ| = rJ := by
    simpa only [cJ, rJ] using upper_sub_center_abs hJ
  have corner_abs (x y : ℚ)
      (hx : |x - cI| ≤ rI) (hy : |y| ≤ BJ)
      (hyc : |y - cJ| ≤ rJ) :
      |x * y - cI * cJ| ≤ R := by
    calc
      |x * y - cI * cJ| =
          |(x - cI) * y + cI * (y - cJ)| := by
        congr 1
        ring
      _ ≤ |(x - cI) * y| + |cI * (y - cJ)| := abs_add_le _ _
      _ = |x - cI| * |y| + |cI| * |y - cJ| := by
        rw [abs_mul, abs_mul]
      _ ≤ rI * BJ + BI * rJ := by gcongr
      _ = R := by rfl
  have hll := corner_abs I.lower J.lower hIl.le hJends.1 hJl.le
  have hlu := corner_abs I.lower J.upper hIl.le hJends.2 hJu.le
  have hul := corner_abs I.upper J.lower hIu.le hJends.1 hJl.le
  have huu := corner_abs I.upper J.upper hIu.le hJends.2 hJu.le
  rw [abs_le] at hll hlu hul huu
  have hlower :
      cI * cJ - R ≤
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper)) := by
    apply le_min
    · exact le_min (by linarith [hll.1]) (by linarith [hlu.1])
    · exact le_min (by linarith [hul.1]) (by linarith [huu.1])
  have hupper :
      max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) ≤
        cI * cJ + R := by
    apply max_le
    · exact max_le (by linarith [hll.2]) (by linarith [hlu.2])
    · exact max_le (by linarith [hul.2]) (by linarith [huu.2])
  change
    max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) -
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper)) ≤
      BJ * width I + BI * width J
  have htwoR : 2 * R = BJ * width I + BI * width J := by
    dsimp only [R, rI, rJ]
    ring
  rw [← htwoR]
  linarith

end ArithmeticHodge.Analysis.RatInterval
