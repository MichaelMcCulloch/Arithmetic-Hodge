import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets

set_option autoImplicit false
set_option maxHeartbeats 5000000

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

open RatInterval
open RationalIntervalSchur
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets

/-!
# Checkpointed full even pivot certificate

Direct reduction of the exact rational Schur recurrence makes the rational
denominators grow prohibitively.  This module instead rounds every Schur
stage outward to a fixed rational grid.  Interval arithmetic is inclusion
isotone, so positivity of the deliberately wider rounded pivots certifies
positivity of the exact pivots.
-/

/-- `I` is the narrower interval and `J` is the wider interval. -/
def Refines (I J : RatInterval) : Prop :=
  J.lower ≤ I.lower ∧ I.upper ≤ J.upper

instance (I J : RatInterval) : Decidable (Refines I J) :=
  inferInstanceAs (Decidable (J.lower ≤ I.lower ∧ I.upper ≤ J.upper))

instance ratIntervalValidDecidable (I : RatInterval) : Decidable I.Valid :=
  inferInstanceAs (Decidable (I.lower ≤ I.upper))

/-- Round an interval outward to the grid with spacing `scale⁻¹`. -/
def roundOut (scale : ℚ) (I : RatInterval) : RatInterval :=
  ⟨((I.lower * scale).floor : ℚ) / scale,
    ((I.upper * scale).ceil : ℚ) / scale⟩

theorem refines_roundOut {scale : ℚ} (hscale : 0 < scale)
    (I : RatInterval) : Refines I (roundOut scale I) := by
  constructor
  · change ((I.lower * scale).floor : ℚ) / scale ≤ I.lower
    exact (div_le_iff₀ hscale).2 (Rat.floor_le (I.lower * scale))
  · change I.upper ≤ ((I.upper * scale).ceil : ℚ) / scale
    exact (le_div_iff₀ hscale).2 Rat.le_ceil

theorem contains_lower {I : RatInterval} (hI : I.Valid) :
    I.Contains (I.lower : ℝ) := by
  exact ⟨le_rfl, (Rat.cast_le (K := ℝ)).2 hI⟩

theorem contains_upper {I : RatInterval} (hI : I.Valid) :
    I.Contains (I.upper : ℝ) := by
  exact ⟨(Rat.cast_le (K := ℝ)).2 hI, le_rfl⟩

theorem contains_of_refines {I J : RatInterval}
    (hIJ : Refines I J) {x : ℝ} (hx : I.Contains x) : J.Contains x := by
  exact ⟨(Rat.cast_le (K := ℝ)).2 hIJ.1 |>.trans hx.1,
    hx.2.trans ((Rat.cast_le (K := ℝ)).2 hIJ.2)⟩

theorem valid_add {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I + J).Valid :=
  valid_of_contains (contains_add (contains_lower hI) (contains_lower hJ))

theorem valid_pure (q : ℚ) : (pure q).Valid := by
  exact le_rfl

theorem valid_sub {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I - J).Valid :=
  valid_of_contains (contains_sub (contains_lower hI) (contains_lower hJ))

theorem valid_mul {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I * J).Valid :=
  valid_of_contains (contains_mul (contains_lower hI) (contains_lower hJ))

theorem valid_inv_of_pos {I : RatInterval} (hpos : 0 < I.lower)
    (hI : I.Valid) : I⁻¹.Valid :=
  valid_of_contains (contains_inv_of_pos hpos (contains_lower hI))

theorem valid_div_of_pos {I J : RatInterval} (hpos : 0 < J.lower)
    (hI : I.Valid) (hJ : J.Valid) : (I / J).Valid :=
  valid_mul hI (valid_inv_of_pos hpos hJ)

theorem valid_roundOut {scale : ℚ} (hscale : 0 < scale)
    {I : RatInterval} (hI : I.Valid) : (roundOut scale I).Valid := by
  have h := refines_roundOut hscale I
  exact h.1.trans (hI.trans h.2)

theorem refines_of_contains_endpoints {I J : RatInterval}
    (hl : J.Contains (I.lower : ℝ)) (hu : J.Contains (I.upper : ℝ)) :
    Refines I J := by
  exact ⟨(Rat.cast_le (K := ℝ)).1 hl.1, (Rat.cast_le (K := ℝ)).1 hu.2⟩

theorem refines_sub {I I' J J' : RatInterval}
    (hI : I.Valid) (hJ : J.Valid)
    (hII' : Refines I I') (hJJ' : Refines J J') :
    Refines (I - J) (I' - J') := by
  apply refines_of_contains_endpoints
  · change (I' - J').Contains ((I.lower - J.upper : ℚ) : ℝ)
    norm_num
    exact contains_sub
      (contains_of_refines hII' (contains_lower hI))
      (contains_of_refines hJJ' (contains_upper hJ))
  · change (I' - J').Contains ((I.upper - J.lower : ℚ) : ℝ)
    norm_num
    exact contains_sub
      (contains_of_refines hII' (contains_upper hI))
      (contains_of_refines hJJ' (contains_lower hJ))

theorem refines_mul {I I' J J' : RatInterval}
    (hI : I.Valid) (hJ : J.Valid)
    (hII' : Refines I I') (hJJ' : Refines J J') :
    Refines (I * J) (I' * J') := by
  have hll := contains_mul
    (contains_of_refines hII' (contains_lower hI))
    (contains_of_refines hJJ' (contains_lower hJ))
  have hlu := contains_mul
    (contains_of_refines hII' (contains_lower hI))
    (contains_of_refines hJJ' (contains_upper hJ))
  have hul := contains_mul
    (contains_of_refines hII' (contains_upper hI))
    (contains_of_refines hJJ' (contains_lower hJ))
  have huu := contains_mul
    (contains_of_refines hII' (contains_upper hI))
    (contains_of_refines hJJ' (contains_upper hJ))
  have hllL : (I' * J').lower ≤ I.lower * J.lower := by
    exact_mod_cast hll.1
  have hluL : (I' * J').lower ≤ I.lower * J.upper := by
    exact_mod_cast hlu.1
  have hulL : (I' * J').lower ≤ I.upper * J.lower := by
    exact_mod_cast hul.1
  have huuL : (I' * J').lower ≤ I.upper * J.upper := by
    exact_mod_cast huu.1
  have hllU : I.lower * J.lower ≤ (I' * J').upper := by
    exact_mod_cast hll.2
  have hluU : I.lower * J.upper ≤ (I' * J').upper := by
    exact_mod_cast hlu.2
  have hulU : I.upper * J.lower ≤ (I' * J').upper := by
    exact_mod_cast hul.2
  have huuU : I.upper * J.upper ≤ (I' * J').upper := by
    exact_mod_cast huu.2
  constructor
  · change (I' * J').lower ≤
      min (min (I.lower * J.lower) (I.lower * J.upper))
        (min (I.upper * J.lower) (I.upper * J.upper))
    exact le_min (le_min hllL hluL) (le_min hulL huuL)
  · change max (max (I.lower * J.lower) (I.lower * J.upper))
        (max (I.upper * J.lower) (I.upper * J.upper)) ≤
      (I' * J').upper
    exact max_le (max_le hllU hluU) (max_le hulU huuU)

theorem refines_inv_of_pos {I I' : RatInterval}
    (hI : I.Valid) (hII' : Refines I I') (hpos : 0 < I'.lower) :
    Refines I⁻¹ I'⁻¹ := by
  have hIlpos : 0 < I.lower := hpos.trans_le hII'.1
  have hIupos : 0 < I.upper := hIlpos.trans_le hI
  change I'.upper⁻¹ ≤ I.upper⁻¹ ∧ I.lower⁻¹ ≤ I'.lower⁻¹
  constructor
  · have hI'upos : 0 < I'.upper := hIupos.trans_le hII'.2
    exact (inv_le_inv₀ hI'upos hIupos).2 hII'.2
  · exact (inv_le_inv₀ hIlpos hpos).2 hII'.1

theorem refines_div_of_pos {I I' J J' : RatInterval}
    (hI : I.Valid) (hJ : J.Valid)
    (hII' : Refines I I') (hJJ' : Refines J J') (hpos : 0 < J'.lower) :
    Refines (I / J) (I' / J') := by
  exact refines_mul hI (valid_inv_of_pos (hpos.trans_le hJJ'.1) hJ)
    hII' (refines_inv_of_pos hJ hJJ' hpos)

theorem refines_trans {I J K : RatInterval}
    (hIJ : Refines I J) (hJK : Refines J K) : Refines I K := by
  exact ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩

theorem intervalSchurStep_entry_valid {n : Type*}
    (p i j : n) (M : Matrix n n RatInterval)
    (hij : (M i j).Valid) (hip : (M i p).Valid)
    (hpj : (M p j).Valid) (hpp : (M p p).Valid)
    (hpos : 0 < (M p p).lower) :
    (intervalSchurStep p M i j).Valid := by
  exact valid_sub hij (valid_div_of_pos hpos (valid_mul hip hpj) hpp)

theorem intervalSchurStep_entry_refines {n m : Type*}
    (p i j : n) (q a b : m)
    (M : Matrix n n RatInterval) (W : Matrix m m RatInterval)
    (hMij : (M i j).Valid) (hMip : (M i p).Valid)
    (hMpj : (M p j).Valid) (hMpp : (M p p).Valid)
    (hij : Refines (M i j) (W a b))
    (hip : Refines (M i p) (W a q))
    (hpj : Refines (M p j) (W q b))
    (hpp : Refines (M p p) (W q q))
    (hpos : 0 < (W q q).lower) :
    Refines (intervalSchurStep p M i j) (intervalSchurStep q W a b) := by
  apply refines_sub hMij (valid_div_of_pos (hpos.trans_le hpp.1)
    (valid_mul hMip hMpj) hMpp) hij
  exact refines_div_of_pos (valid_mul hMip hMpj) hMpp
    (refines_mul hMip hMpj hip hpj) hpp hpos

def roundedIntervalSchurStep {n : Type*} (scale : ℚ) (p : n)
    (M : Matrix n n RatInterval) : Matrix n n RatInterval :=
  fun i j ↦ roundOut scale (intervalSchurStep p M i j)

def RoundedPositivePivots {n : Type*} (scale : ℚ) :
    List n → Matrix n n RatInterval → Prop
  | [], _ => True
  | p :: ps, M =>
      0 < (M p p).lower ∧
        RoundedPositivePivots scale ps (roundedIntervalSchurStep scale p M)

instance roundedPositivePivotsDecidable {n : Type*}
    (scale : ℚ) (ps : List n) (M : Matrix n n RatInterval) :
    Decidable (RoundedPositivePivots scale ps M) := by
  induction ps generalizing M with
  | nil => exact isTrue trivial
  | cons p ps ih =>
      rw [RoundedPositivePivots]
      letI : Decidable
          (RoundedPositivePivots scale ps (roundedIntervalSchurStep scale p M)) :=
        ih (roundedIntervalSchurStep scale p M)
      infer_instance

/-- Four decimal places are sufficient for the full 200-stage rounded replay.
The deliberately coarse grid also keeps the kernel certificate compact. -/
def evenPivotRoundScale : ℚ := 10000

/-- Dense, array-backed matrices prevent recomputation of earlier Schur
stages during the kernel decision procedure. -/
abbrev DenseIntervalMatrix (n : ℕ) :=
  Vector (Vector RatInterval n) n

def denseOfMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) RatInterval) :
    DenseIntervalMatrix n :=
  Vector.ofFn fun i ↦ Vector.ofFn fun j ↦ M i j

def matrixOfDense {n : ℕ} (M : DenseIntervalMatrix n) :
    Matrix (Fin n) (Fin n) RatInterval :=
  fun i j ↦ M[i.1][j.1]

@[simp] theorem matrixOfDense_denseOfMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) RatInterval) :
    matrixOfDense (denseOfMatrix M) = M := by
  ext i j
  simp [matrixOfDense, denseOfMatrix]

def denseLeadingRoundedIntervalSchurStep {n : ℕ} (scale : ℚ)
    (M : DenseIntervalMatrix (n + 1)) : DenseIntervalMatrix n :=
  Vector.ofFn fun i ↦ Vector.ofFn fun j ↦
    roundOut scale
      (M[i.succ.1][j.succ.1] -
        M[i.succ.1][0] * M[0][j.succ.1] / M[0][0])

@[simp] theorem matrixOfDense_denseLeadingRoundedIntervalSchurStep
    {n : ℕ} (scale : ℚ) (M : DenseIntervalMatrix (n + 1))
    (i j : Fin n) :
    matrixOfDense (denseLeadingRoundedIntervalSchurStep scale M) i j =
      roundOut scale
        (intervalSchurStep 0 (matrixOfDense M) i.succ j.succ) := by
  simp [matrixOfDense, denseLeadingRoundedIntervalSchurStep,
    intervalSchurStep]

/-- Rounded elimination in the natural order, dropping the completed row and
column at every stage.  The shrinking dense arrays are the computational
checkpoint representation. -/
def DenseLeadingRoundedPositivePivots (scale : ℚ) :
    {n : ℕ} → DenseIntervalMatrix n → Prop
  | 0, _ => True
  | n + 1, M =>
      0 < (M[0][0]).lower ∧
        DenseLeadingRoundedPositivePivots scale
          (denseLeadingRoundedIntervalSchurStep scale M)

instance denseLeadingRoundedPositivePivotsDecidable (scale : ℚ)
    {n : ℕ} (M : DenseIntervalMatrix n) :
    Decidable (DenseLeadingRoundedPositivePivots scale M) := by
  induction n with
  | zero => exact isTrue trivial
  | succ n ih =>
      rw [DenseLeadingRoundedPositivePivots]
      letI : Decidable (DenseLeadingRoundedPositivePivots scale
          (denseLeadingRoundedIntervalSchurStep scale M)) :=
        ih (denseLeadingRoundedIntervalSchurStep scale M)
      infer_instance

/-- Run exactly `steps` shrinking rounded-elimination stages, leaving a
matrix whose dimension is `tail`.  The dimension equation is carried in the
type, so a checkpoint cannot accidentally be attached at the wrong stage. -/
def denseLeadingRoundedAdvance (scale : ℚ) :
    (steps tail : ℕ) → DenseIntervalMatrix (tail + steps) →
      DenseIntervalMatrix tail
  | 0, _, M => M
  | steps + 1, tail, M =>
      denseLeadingRoundedAdvance scale steps tail
        (denseLeadingRoundedIntervalSchurStep scale M)

/-- Positivity of only the next `steps` leading pivots.  Unlike
`DenseLeadingRoundedPositivePivots`, this proposition deliberately stops at
a typed checkpoint boundary. -/
def DenseLeadingRoundedPositivePrefix (scale : ℚ) :
    (steps tail : ℕ) → DenseIntervalMatrix (tail + steps) → Prop
  | 0, _, _ => True
  | steps + 1, tail, M =>
      0 < (M[0][0]).lower ∧
        DenseLeadingRoundedPositivePrefix scale steps tail
          (denseLeadingRoundedIntervalSchurStep scale M)

instance denseLeadingRoundedPositivePrefixDecidable (scale : ℚ)
    (steps tail : ℕ) (M : DenseIntervalMatrix (tail + steps)) :
    Decidable (DenseLeadingRoundedPositivePrefix scale steps tail M) := by
  induction steps with
  | zero => exact isTrue trivial
  | succ steps ih =>
      rw [DenseLeadingRoundedPositivePrefix]
      letI : Decidable
          (DenseLeadingRoundedPositivePrefix scale steps tail
            (denseLeadingRoundedIntervalSchurStep scale M)) :=
        ih (denseLeadingRoundedIntervalSchurStep scale M)
      infer_instance

/-- Compare dense matrices one row at a time.  A single nested-vector
`DecidableEq` proof has depth proportional to the number of entries and can
overflow the process stack.  This rowwise proposition has maximum proof depth
proportional only to the matrix side length. -/
def DenseRowsEqual {n : ℕ} (rows : List (Fin n))
    (M N : DenseIntervalMatrix n) : Prop :=
  match rows with
  | [] => True
  | i :: rows => M[i.1] = N[i.1] ∧ DenseRowsEqual rows M N

instance denseRowsEqualDecidable {n : ℕ} (rows : List (Fin n))
    (M N : DenseIntervalMatrix n) : Decidable (DenseRowsEqual rows M N) := by
  induction rows with
  | nil => exact isTrue trivial
  | cons i rows ih =>
      rw [DenseRowsEqual]
      letI : Decidable (DenseRowsEqual rows M N) := ih
      infer_instance

def allDenseRows (n : ℕ) : List (Fin n) :=
  List.ofFn fun i : Fin n ↦ i

theorem denseRowsEqual_get {n : ℕ} {rows : List (Fin n)}
    {M N : DenseIntervalMatrix n} (h : DenseRowsEqual rows M N)
    {i : Fin n} (hi : i ∈ rows) : M[i.1] = N[i.1] := by
  induction rows with
  | nil => simp at hi
  | cons j rows ih =>
      rw [DenseRowsEqual] at h
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact h.1
      · exact ih h.2 hi

theorem dense_eq_of_rows {n : ℕ} {M N : DenseIntervalMatrix n}
    (h : DenseRowsEqual (allDenseRows n) M N) : M = N := by
  apply Vector.ext
  intro i hi
  exact denseRowsEqual_get h
    (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩)

/-- A bounded checkpoint certificate combines positivity of a short prefix
with exact rowwise agreement of the resulting rounded matrix and a literal
next checkpoint.  Each theorem proving this proposition can remain opaque,
so kernel checking never has to retain the proof term for all 200 stages at
once. -/
def DenseLeadingRoundedChunk (scale : ℚ) :
    (steps tail : ℕ) → DenseIntervalMatrix (tail + steps) →
      DenseIntervalMatrix tail → Prop
  | 0, tail, M, checkpoint =>
      DenseRowsEqual (allDenseRows tail) M checkpoint
  | steps + 1, tail, M, checkpoint =>
      0 < (M[0][0]).lower ∧
        DenseLeadingRoundedChunk scale steps tail
          (denseLeadingRoundedIntervalSchurStep scale M) checkpoint

instance denseLeadingRoundedChunkDecidable (scale : ℚ)
    (steps tail : ℕ) (M : DenseIntervalMatrix (tail + steps))
    (checkpoint : DenseIntervalMatrix tail) :
    Decidable (DenseLeadingRoundedChunk scale steps tail M checkpoint) := by
  induction steps with
  | zero =>
      rw [DenseLeadingRoundedChunk]
      infer_instance
  | succ steps ih =>
      rw [DenseLeadingRoundedChunk]
      letI : Decidable
          (DenseLeadingRoundedChunk scale steps tail
            (denseLeadingRoundedIntervalSchurStep scale M) checkpoint) :=
        ih (denseLeadingRoundedIntervalSchurStep scale M)
      infer_instance

/-- Assemble one opaque bounded chunk with a certificate for the remaining
checkpoint. -/
theorem denseLeadingRoundedPositivePivots_of_chunk (scale : ℚ) :
    ∀ (steps tail : ℕ) (M : DenseIntervalMatrix (tail + steps))
      (checkpoint : DenseIntervalMatrix tail),
      DenseLeadingRoundedChunk scale steps tail M checkpoint →
      DenseLeadingRoundedPositivePivots scale checkpoint →
      DenseLeadingRoundedPositivePivots scale M := by
  intro steps
  induction steps with
  | zero =>
      intro tail M checkpoint hchunk htail
      rw [DenseLeadingRoundedChunk] at hchunk
      exact dense_eq_of_rows hchunk ▸ htail
  | succ steps ih =>
      intro tail M checkpoint hchunk htail
      rw [DenseLeadingRoundedChunk] at hchunk
      rw [DenseLeadingRoundedPositivePivots]
      exact ⟨hchunk.1,
        ih tail (denseLeadingRoundedIntervalSchurStep scale M)
          checkpoint hchunk.2 htail⟩

set_option maxHeartbeats 5000000 in
/-- A checked dense rounded elimination soundly certifies exact interval
pivots in the corresponding natural order.  At every stage, strict
positivity of the wider rounded denominator makes interval division
inclusion-isotone; `List.ofFn_succ` identifies the dropped dense index with
the next pivot in the original matrix. -/
theorem positivePivots_of_denseLeadingRounded {α : Type*}
    (scale : ℚ) (hscale : 0 < scale) :
    ∀ {n : ℕ} (M : Matrix α α RatInterval) (e : Fin n → α)
      (D : DenseIntervalMatrix n),
      DenseLeadingRoundedPositivePivots scale D →
      (∀ i j, (M (e i) (e j)).Valid) →
      (∀ i j, (matrixOfDense D i j).Valid) →
      (∀ i j, Refines (M (e i) (e j)) (matrixOfDense D i j)) →
      PositivePivots (List.ofFn e) M := by
  intro n
  induction n with
  | zero =>
      intro M e D _hcert _hMvalid _hDvalid _href
      rw [List.ofFn_zero]
      trivial
  | succ n ih =>
      intro M e D hcert hMvalid hDvalid href
      rw [List.ofFn_succ, PositivePivots]
      rw [DenseLeadingRoundedPositivePivots] at hcert
      constructor
      · exact hcert.1.trans_le (href 0 0).1
      · apply ih (intervalSchurStep (e 0) M) (fun i ↦ e i.succ)
          (denseLeadingRoundedIntervalSchurStep scale D) hcert.2
        · intro i j
          exact intervalSchurStep_entry_valid (e 0) (e i.succ) (e j.succ) M
            (hMvalid i.succ j.succ) (hMvalid i.succ 0)
            (hMvalid 0 j.succ) (hMvalid 0 0)
            (hcert.1.trans_le (href 0 0).1)
        · intro i j
          rw [matrixOfDense_denseLeadingRoundedIntervalSchurStep]
          apply valid_roundOut hscale
          exact intervalSchurStep_entry_valid 0 i.succ j.succ
            (matrixOfDense D)
            (hDvalid i.succ j.succ) (hDvalid i.succ 0)
            (hDvalid 0 j.succ) (hDvalid 0 0) hcert.1
        · intro i j
          rw [matrixOfDense_denseLeadingRoundedIntervalSchurStep]
          apply refines_trans
            (intervalSchurStep_entry_refines (e 0) (e i.succ) (e j.succ)
              0 i.succ j.succ M (matrixOfDense D)
              (hMvalid i.succ j.succ) (hMvalid i.succ 0)
              (hMvalid 0 j.succ) (hMvalid 0 0)
              (href i.succ j.succ) (href i.succ 0)
              (href 0 j.succ) (href 0 0) hcert.1)
          exact refines_roundOut hscale _

/- Checkpoints are represented by one packed natural per grid interval.  A
fixed per-checkpoint offset (`4096` at stage five and `2048` thereafter)
makes both signed endpoints nonnegative; packing them in base `65536` keeps
the auditable source payload substantially smaller without changing the
kernel computation.  The canonical sequence of 513500 packed entries has
SHA-256 `f4a44552e69771e665f75acda1f67ae6bbc30e32809367a4f359750bffcfe718`.
Its framing iterates `k = 5, 10, …, 195`, sets `n = 200 - k`, and visits rows
`i = 0, …, n - 1`; each row hashes `k`, `i`, and `n` as big-endian unsigned
16-bit integers, followed by every packed code as a big-endian unsigned
64-bit integer.  This hash is provenance only: the downstream chunk theorems
kernel-check every entry against the rounded recurrence. -/
abbrev DenseGridCodes (n : ℕ) := Vector (Vector ℕ n) n

def gridIntervalOfCode (offset code : ℕ) : RatInterval :=
  let lower : ℤ := ((code / 65536 : ℕ) : ℤ) - offset
  let upper : ℤ := ((code % 65536 : ℕ) : ℤ) - offset
  ⟨(lower : ℚ) / 10000, (upper : ℚ) / 10000⟩

def denseOfGridCodes {n : ℕ} (offset : ℕ) (codes : DenseGridCodes n) :
    DenseIntervalMatrix n :=
  codes.map fun row ↦ row.map (gridIntervalOfCode offset)

def evenTargetInitialDense : DenseIntervalMatrix 200 :=
  denseOfMatrix
    (inflatedEvenMomentIntervalGram evenCorrectionRadius
      yoshidaEvenSineTargets yoshidaEvenDiagonalTargets)

/- Exercise the bounded API directly on one tiny stage. -/
example : DenseLeadingRoundedPositivePrefix 1 1 0
    (denseOfMatrix (fun _ _ : Fin 1 => RatInterval.pure 1)) := by
  decide +kernel

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
