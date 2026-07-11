import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct

set_option autoImplicit false

open Complex Filter Topology Finset BigOperators Metric

namespace ArithmeticHodge.Analysis.EntireFunction

/-- Scratch companion to `weierstraß_factorization` exposing the construction's
    canonical genus, zero coverage, and analytic multiplicities. Zero padding is
    retained, so entries are asserted to be zeros only when nonzero. -/
theorem weierstraß_factorization_canonical_scratch (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) :
    ∃ (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ),
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      (∀ z, f z = z ^ m * Complex.exp (g z) *
        ∏' n, weierstraßElementary p (z / a n)) ∧
      p = Nat.floor (entireOrder f).toReal ∧
      (∀ z, f z = 0 → z ≠ 0 → ∃ n, z = a n) ∧
      ∀ z, f z = 0 → z ≠ 0 →
        analyticOrderAt f z =
          analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / a n)) z := by
  -- Split into zero-free and has-zeros cases
  by_cases hzf : ∀ z, f z ≠ 0
  · -- f is zero-free: use entire logarithm theorem.
    -- Take m = 0, canonical p, and a = const 0, so every product factor is 1.
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm f hf hzf
    set p₀ := Nat.floor (entireOrder f).toReal
    refine ⟨0, g, fun _ => 0, p₀, hg_diff,
      fun n h => absurd rfl h, ?_, ?_, rfl, ?_, ?_⟩
    · -- Summability: the padded sequence contributes only zero terms.
      exact summable_of_ne_finset_zero (s := ∅) (fun n _ => by
        simp [norm_zero, inv_zero,
          Real.zero_rpow (by positivity : (p₀ : ℝ) + 1 ≠ 0)])
    · intro z
      simp [hg_eq z, weierstraßElementary_zero]
    · intro z hfz _
      exact (hzf z hfz).elim
    · intro z hfz _
      exact (hzf z hfz).elim
  · -- f has zeros: Weierstraß product construction for finite-order functions.
    -- analyticOrderAt_tprod_weierstraß is now proved; remaining issues are
    -- stutteredEnum_pair_lt alignment and Encodable.decode₂ API mismatches.
    push_neg at hzf
    -- ═══════════════════════════════════════════════════════════
    -- Step 1: Factor out the zero at the origin
    -- f(z) = z^m · f₁(z) with f₁(0) ≠ 0, using analytic order at 0
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨m, f₁, hf₁_diff, hf₁_nz, hf_eq⟩ :
        ∃ (m : ℕ) (f₁ : ℂ → ℂ), Differentiable ℂ f₁ ∧ f₁ 0 ≠ 0 ∧
          ∀ z, f z = z ^ m * f₁ z := by
      by_cases hf0 : f 0 ≠ 0
      · exact ⟨0, f, hf, hf0, fun z => by simp⟩
      · push_neg at hf0
        have hf_an : AnalyticAt ℂ f 0 := hf.analyticAt 0
        have hord_ne_top : analyticOrderAt f 0 ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0
            (fun z => hf.analyticAt z)).not.mpr hf_ne
        set m' := analyticOrderNatAt f 0
        obtain ⟨g, hg_an, hg_nz, hg_eq⟩ := hf_an.analyticOrderAt_ne_top.mp hord_ne_top
        have hg_eq' : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ m' * g z :=
          hg_eq.mono fun z hz => by simp only [sub_zero, smul_eq_mul] at hz; exact hz
        refine ⟨m', Function.update (fun z => f z / z ^ m') 0 (g 0), ?_, ?_, ?_⟩
        · -- f₁ is entire
          intro z₀
          by_cases hz₀ : z₀ = 0
          · subst hz₀
            refine (hg_an.congr ?_).differentiableAt
            apply hg_eq'.mono
            intro z hz
            by_cases hz0 : z = 0
            · subst hz0; simp [Function.update_self]
            · rw [Function.update_of_ne hz0, hz,
                mul_div_cancel_left₀ _ (pow_ne_zero m' hz0)]
          · exact (hf.differentiableAt.div ((differentiable_pow m').differentiableAt)
              (pow_ne_zero m' hz₀)).congr_of_eventuallyEq
              ((isOpen_ne.eventually_mem hz₀).mono fun z hz =>
                Function.update_of_ne hz _ _)
        · simp [Function.update_self, hg_nz]
        · intro z
          by_cases hz : z = 0
          · subst hz; rw [Function.update_self]; exact hg_eq'.self_of_nhds
          · simp only [Function.update_of_ne hz]
            exact (mul_div_cancel₀ (f z) (pow_ne_zero m' hz)).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 2: Enumerate zeros with summability
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨a, p, ha_zeros, hconv, ha_covers, ha_ord_eq, hp⟩ :
        ∃ (a : ℕ → ℂ) (p : ℕ),
          (∀ n, a n ≠ 0 → f₁ (a n) = 0) ∧
          Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
          (∀ z, f₁ z = 0 → ∃ n, z = a n) ∧
          (∀ z, f₁ z = 0 → z ≠ 0 →
            analyticOrderAt f₁ z =
              analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / a n)) z) ∧
          p = Nat.floor (entireOrder f).toReal := by
      -- Step 2a: Zeros of f₁ are discrete and countable
      have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (by rw [h]; simp)
      have hf₁_an : AnalyticOnNhd ℂ f₁ Set.univ := fun z _ => hf₁_diff.analyticAt z
      have hcodisc : f₁ ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
        hf₁_an.preimage_zero_mem_codiscrete hf₁_nz
      have hdisc : IsDiscrete (f₁ ⁻¹' {0}) := by
        have := (mem_codiscrete'.mp hcodisc).2
        rwa [Set.preimage_compl, compl_compl] at this
      have hcount : (f₁ ⁻¹' {0}).Countable :=
        (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
      letI : Encodable (f₁ ⁻¹' {0}) := hcount.toEncodable
      -- Step 2b: Enumerate distinct zeros
      set a₀ : ℕ → ℂ := fun n =>
        match @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n with
        | some y => y | none => 0
      have ha₀_surj : ∀ z, f₁ z = 0 → ∃ k, z = a₀ k := by
        intro z hz
        refine ⟨@Encodable.encode _ hcount.toEncodable ⟨z, Set.mem_preimage.mpr
          (Set.mem_singleton_iff.mpr hz)⟩, ?_⟩
        simp only [a₀, Encodable.decode₂_encode]
      have ha₀_zeros : ∀ k, a₀ k ≠ 0 → f₁ (a₀ k) = 0 := by
        intro k hk
        simp only [a₀] at hk ⊢
        cases h : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
        | none => simp [h] at hk
        | some val => simp; exact val.2
      have ha₀_inj : Set.InjOn a₀ {k | a₀ k ≠ 0} := by
        intro i hi j hj hij
        simp only [a₀] at hi hj hij
        cases hi_decode : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable i with
        | none => simp [hi_decode] at hi
        | some vi =>
          cases hj_decode : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable j with
          | none => simp [hj_decode] at hj
          | some vj =>
            have hv : vi = vj := by
              apply Subtype.ext
              simpa [hi_decode, hj_decode] using hij
            rw [Encodable.decode₂_eq_some] at hi_decode hj_decode
            rw [← hi_decode, ← hj_decode, hv]
      -- Step 2c: Define multiplicities and stuttered enumeration
      set mult' : ℕ → ℕ := fun k =>
        if a₀ k = 0 then 0 else analyticOrderNatAt f₁ (a₀ k)
      have hmult_pos : ∀ k, a₀ k ≠ 0 → 0 < mult' k := by
        intro k hk
        simp only [mult', hk, ite_false]
        rw [Nat.pos_iff_ne_zero, Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
        exact ⟨analyticOrderAt_ne_zero.mpr ⟨hf₁_diff.analyticAt _, ha₀_zeros k hk⟩,
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne⟩
      have hmult_zero : ∀ k, a₀ k = 0 → mult' k = 0 :=
        fun k hk => by simp [mult', hk]
      have hmult_le : ∀ k, a₀ k ≠ 0 →
          mult' k ≤ analyticOrderNatAt f (a₀ k) := by
        intro k hk
        simp only [mult', hk, ite_false]
        apply le_of_eq
        have hfun : f = (fun w : ℂ => w ^ m) * f₁ := by
          funext w
          exact hf_eq w
        have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) (a₀ k) :=
          (differentiable_pow m).analyticAt (a₀ k)
        have hpow_order_enat : analyticOrderAt (fun w : ℂ => w ^ m) (a₀ k) = 0 :=
          hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hk)
        have hpow_ne_top : analyticOrderAt (fun w : ℂ => w ^ m) (a₀ k) ≠ ⊤ := by
          rw [hpow_order_enat]
          exact ENat.zero_ne_top
        have hf₁_ne_top : analyticOrderAt f₁ (a₀ k) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
            (fun w => hf₁_diff.analyticAt w)).not.mpr hf₁_ne
        rw [hfun, analyticOrderNatAt_mul hpow_an (hf₁_diff.analyticAt (a₀ k))
          hpow_ne_top hf₁_ne_top]
        have hpow_order : analyticOrderNatAt (fun w : ℂ => w ^ m) (a₀ k) = 0 := by
          rw [analyticOrderNatAt, hpow_order_enat]
          rfl
        rw [hpow_order, zero_add]
      set a' := stutteredEnum a₀ mult'
      set p' := Nat.floor (entireOrder f).toReal
      -- Step 2d: Verify properties
      have ha_zeros' : ∀ n, a' n ≠ 0 → f₁ (a' n) = 0 :=
        fun n hn => stutteredEnum_maps_zeros ha₀_zeros hn
      have ha_covers' : ∀ z, f₁ z = 0 → ∃ n, z = a' n := by
        intro z hz
        obtain ⟨k, rfl⟩ := ha₀_surj z hz
        have hk : a₀ k ≠ 0 := fun h0 => hf₁_nz (h0 ▸ hz)
        obtain ⟨n, hn⟩ := stutteredEnum_covers (hmult_pos k hk)
        exact ⟨n, hn.symm⟩
      have hconv' : Summable (fun n => (‖a' n‖⁻¹) ^ ((p' : ℝ) + 1)) :=
        summable_stutteredEnum_of_weighted (Nat.cast_add_one_pos p')
          (finite_order_zero_summable_weighted f hf hf_ne hfin a₀
            (fun k hk => by have := ha₀_zeros k hk; rw [hf_eq]; simp [this])
            ha₀_inj mult' hmult_zero hmult_le)
      refine ⟨a', p', ha_zeros', hconv', ha_covers', ?_, rfl⟩
      -- Order equality: analytic order of Weierstraß product at each zero
      -- equals analyticOrderAt f₁ there.
      intro z hz hne
      obtain ⟨k, rfl⟩ := ha₀_surj z hz
      have hk : a₀ k ≠ 0 := hne
      -- The multiplicity m = analyticOrderNatAt f₁ (a₀ k)
      set m := mult' k with hm_def
      have hm_pos : 0 < m := hmult_pos k hk
      -- analyticOrderAt f₁ (a₀ k) = ↑m
      have hord_ne_top : analyticOrderAt f₁ (a₀ k) ≠ ⊤ :=
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
          (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
      have hord_f₁ : analyticOrderAt f₁ (a₀ k) = ↑m := by
        simp only [m, mult', hk, ite_false]
        exact (Nat.cast_analyticOrderNatAt hord_ne_top).symm
      rw [hord_f₁]
      -- Use the standalone tprod order lemma
      set S : Finset ℕ := (Finset.range m).image (Nat.pair k)
      have hS_val : ∀ n ∈ S, a' n = a₀ k := by
        intro n hn; simp only [S, Finset.mem_image, Finset.mem_range] at hn
        obtain ⟨j, hj, rfl⟩ := hn; exact stutteredEnum_pair_lt hj
      have hS_compl : ∀ n, n ∉ S → a' n ≠ a₀ k := by
        intro n hn ha'n_eq
        have ha'n_ne : a' n ≠ 0 := ha'n_eq ▸ hk
        have ⟨hlt, ha₀_ne⟩ := stutteredEnum_ne_zero_imp ha'n_ne
        have ha'_simp : a' n = a₀ n.unpair.1 := by
          simp only [a', stutteredEnum_apply, hlt, if_true]
        have heq_a₀ : a₀ n.unpair.1 = a₀ k := ha'_simp ▸ ha'n_eq
        -- enumerateCountable injectivity: a₀ n.unpair.1 = a₀ k → n.unpair.1 = k
        have hfst_eq : n.unpair.1 = k := by
          simp only [a₀] at ha₀_ne heq_a₀
          revert ha₀_ne heq_a₀
          cases h1 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n.unpair.1 with
          | none => simp
          | some v1 =>
            cases h2 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
            | none => simp_all
            | some v2 =>
              intro _ heq
              have hv_eq : v1 = v2 := Subtype.val_injective heq
              rw [Encodable.decode₂_eq_some] at h1 h2
              rw [← h1, ← h2, hv_eq]
        have hlt' : n.unpair.2 < m := by
          simpa only [hm_def, hfst_eq] using hlt
        exact hn (by
          rw [show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm, hfst_eq]
          exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hlt'))
      have hS_card : S.card = m := by
        simp only [S]
        exact (Finset.card_image_of_injective _
          (fun j₁ j₂ h => (Nat.pair_eq_pair.mp h).2)).trans (Finset.card_range m)
      rw [← hS_card]
      exact (analyticOrderAt_tprod_weierstraß a' p' hconv' (a₀ k) hk S hS_val hS_compl).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 3–4: Quotient f₁/P is entire and zero-free
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨h, hh_diff, hh_ne, hh_eq⟩ :
        ∃ (h : ℂ → ℂ), Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧
          (∀ z, f₁ z = h z * ∏' n, weierstraßElementary p (z / a n)) := by
      set P : ℂ → ℂ := fun z => ∏' n, weierstraßElementary p (z / a n)
      have hP_diff : Differentiable ℂ P := tprod_weierstraßElementary_differentiable a p hconv
      have hq_diff : ∀ z, P z ≠ 0 → DifferentiableAt ℂ (fun w => f₁ w / P w) z :=
        fun z hz => hf₁_diff.differentiableAt.div hP_diff.differentiableAt hz
      set h₀ : ℂ → ℂ := fun z =>
        if P z ≠ 0 then f₁ z / P z
        else limUnder (𝓝[≠] z) (fun w => f₁ w / P w)
      have hh₀_eq : ∀ z, f₁ z = h₀ z * P z := by
        intro z
        by_cases hPz : P z ≠ 0
        · rw [show h₀ z = f₁ z / P z from if_pos hPz, div_mul_cancel₀ (f₁ z) hPz]
        · push_neg at hPz
          have hf₁z : f₁ z = 0 := by
            by_contra hf₁z_ne
            have hne : ∀ n, z / a n ≠ 1 := by
              intro n heq
              by_cases han : a n = 0
              · simp [han] at heq
              · exact hf₁z_ne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han)
            exact absurd hPz (tprod_weierstraßElementary_ne_zero a p hconv z hne)
          rw [hf₁z, hPz, mul_zero]
      have hh₀_diff : Differentiable ℂ h₀ := by
        intro z₀
        by_cases hPz₀ : P z₀ ≠ 0
        · have heq : h₀ =ᶠ[𝓝 z₀] fun w => f₁ w / P w := by
            have : ∀ᶠ w in 𝓝 z₀, P w ≠ 0 :=
              hP_diff.continuous.continuousAt.eventually_ne hPz₀
            exact this.mono fun w hw => by simp [h₀, hw]
          exact (hq_diff z₀ hPz₀).congr_of_eventuallyEq heq
        · push_neg at hPz₀
          have hP_an : AnalyticAt ℂ P z₀ := hP_diff.analyticAt z₀
          have hP_not_ev_zero : ¬ ∀ᶠ w in 𝓝 z₀, P w = 0 := by
            intro hev
            have hf₁_ev : ∀ᶠ w in 𝓝 z₀, f₁ w = 0 :=
              hev.mono fun w hw => by rw [hh₀_eq w, hw, mul_zero]
            have hf₁_eq : f₁ = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
              (fun z => hf₁_diff.analyticAt z)).mp (analyticOrderAt_eq_top.mpr hf₁_ev)
            exact hf₁_nz (congr_fun hf₁_eq 0)
          have hP_ev_ne : ∀ᶠ w in 𝓝[≠] z₀, P w ≠ 0 :=
            hP_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left hP_not_ev_zero
          have hh₀_diff_punct : ∀ᶠ w in 𝓝[≠] z₀, DifferentiableAt ℂ h₀ w := by
            apply hP_ev_ne.mono
            intro w hw
            have heq : h₀ =ᶠ[𝓝 w] fun v => f₁ v / P v :=
              (hP_diff.continuous.continuousAt.eventually_ne hw).mono
                fun v hv => by simp [h₀, hv]
            exact (hf₁_diff.differentiableAt.div hP_diff.differentiableAt hw).congr_of_eventuallyEq
              heq
          -- ContinuousAt h₀ z₀: factor f₁ and P by their equal analytic orders,
          -- cancel (z-z₀)^k to get h₀ = u/v, then use continuity of u/v.
          have hcont : ContinuousAt h₀ z₀ := by
            -- f₁ vanishes at z₀
            have hf₁z₀ : f₁ z₀ = 0 := by
              by_contra hne
              exact absurd hPz₀ (tprod_weierstraßElementary_ne_zero a p hconv z₀
                fun n heq => by
                  by_cases han : a n = 0
                  · simp [han] at heq
                  · exact hne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han))
            -- z₀ ≠ 0
            have hz₀_ne : z₀ ≠ 0 := by
              intro heq; rw [heq] at hPz₀
              have : P 0 = ∏' n, weierstraßElementary p (0 / a n) := rfl
              simp only [zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero (this ▸ hPz₀)
            have hord := ha_ord_eq z₀ hf₁z₀ hz₀_ne
            -- Neither function is identically zero
            have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
            have hP_ne : ¬ P = 0 := by
              intro heq
              have : P 0 = 0 := congr_fun heq 0
              simp only [P, zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero this
            have hf₁_top : analyticOrderAt f₁ z₀ ≠ ⊤ :=
              (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
                (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
            have hP_top : analyticOrderAt P z₀ ≠ ⊤ := hord ▸ hf₁_top
            -- Factor: f₁(z) =ᶠ (z-z₀)^k • u(z), P(z) =ᶠ (z-z₀)^k • v(z)
            set k := analyticOrderNatAt f₁ z₀ with hk_def
            obtain ⟨u, hu_an, hu_ne, hu_eq⟩ :=
              (hf₁_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hf₁_top
            obtain ⟨v, hv_an, hv_ne, hv_eq⟩ :=
              (hP_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hP_top
            have hP_ord : analyticOrderNatAt P z₀ = k := by
              simp only [analyticOrderNatAt]; congr 1; exact hord.symm
            rw [hP_ord] at hv_eq
            -- u/v is continuous at z₀
            have huv_cont : ContinuousAt (fun w => u w / v w) z₀ :=
              hu_an.continuousAt.div hv_an.continuousAt hv_ne
            -- h₀ = u/v on 𝓝[≠] z₀ (cancel (z-z₀)^k via smul = mul in ℂ)
            have heq_uv : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = u w / v w := by
              apply (hP_ev_ne.and ((hu_eq.and hv_eq).filter_mono nhdsWithin_le_nhds)).mono
              rintro w ⟨hwP, hwu, hwv⟩
              -- h₀ w = f₁ w / P w (since P w ≠ 0)
              change (if P w ≠ 0 then f₁ w / P w else _) = u w / v w
              rw [if_pos hwP]
              -- f₁ w = (w-z₀)^k • u w, P w = (w-z₀)^k • v w
              have hwne : (w - z₀) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.mpr (by
                intro heq; rw [heq] at hwP; exact hwP hPz₀))
              simp only [hwu, hwv, smul_eq_mul]
              exact mul_div_mul_left (u w) (v w) hwne
            -- Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀))
            have htend : Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) :=
              (huv_cont.tendsto.mono_left nhdsWithin_le_nhds).congr'
                (heq_uv.mono fun w hw => hw.symm)
            -- h₀ z₀ = u z₀ / v z₀ (limUnder uniqueness in T2)
            have hval : h₀ z₀ = u z₀ / v z₀ := by
              -- h₀ z₀ = limUnder (𝓝[≠] z₀) h₀ by definition (P z₀ = 0 branch)
              -- limUnder h₀ = u z₀ / v z₀ by htend (T2 uniqueness)
              have hlim_eq : (𝓝[≠] z₀).limUnder h₀ = u z₀ / v z₀ := htend.limUnder_eq
              -- h₀ z₀ = limUnder (f₁/P) on 𝓝[≠] z₀
              -- limUnder (f₁/P) = limUnder h₀ since they agree eventually
              -- h₀ z₀ = limUnder h₀ on 𝓝[≠] z₀
              -- First: h₀ z₀ = limUnder (f₁/P)
              have h₀_val : h₀ z₀ = (𝓝[≠] z₀).limUnder (fun w => f₁ w / P w) := by
                simp only [h₀, show ¬(P z₀ ≠ 0) from not_not.mpr hPz₀, ↓reduceIte]
              -- Second: the Tendsto of f₁/P toward u z₀/v z₀ gives its limUnder
              have htend_fg : Tendsto (fun w => f₁ w / P w) (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) := by
                apply htend.congr'
                have : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = f₁ w / P w :=
                  hP_ev_ne.mono fun w hw => (if_pos hw : h₀ w = f₁ w / P w)
                exact this.mono fun w (hw : h₀ w = f₁ w / P w) =>
                  show h₀ w = (fun w => f₁ w / P w) w from hw
              rw [h₀_val, htend_fg.limUnder_eq]
            -- ContinuousAt via nhds = nhdsWithin ⊔ pure
            rw [ContinuousAt, hval, ← nhdsNE_sup_pure z₀]
            exact htend.sup (Filter.tendsto_pure_left.mpr fun _s hs =>
              hval ▸ mem_of_mem_nhds hs)
          exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
            hh₀_diff_punct hcont).differentiableAt
      have hh₀_ne : ∀ z, h₀ z ≠ 0 := by
        intro z hz
        have hf₁z : f₁ z = 0 := by rw [hh₀_eq z, hz, zero_mul]
        obtain ⟨n, rfl⟩ := ha_covers z hf₁z
        have han : a n ≠ 0 := fun h => hf₁_nz (h ▸ hf₁z)
        -- All functions are entire and not identically zero
        have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
        have hh₀_ne_fun : ¬ h₀ = 0 := by
          intro h; apply hf₁_ne; ext z; simp [hh₀_eq z, show h₀ z = 0 from congr_fun h z]
        have hP_ne_fun : ¬ P = 0 := by
          intro hP_eq
          have hP0 : P 0 = 0 := congr_fun hP_eq 0
          have : (fun n => weierstraßElementary p (0 / a n)) = fun _ => (1 : ℂ) :=
            funext fun n => by rw [zero_div, weierstraßElementary_zero]
          simp only [P, this, tprod_one] at hP0 -- hP0 : 1 = 0
          exact one_ne_zero hP0
        -- Orders are finite (not ⊤) since functions are analytic and not identically zero
        have hf₁_top : analyticOrderAt f₁ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
        have hh₀_top : analyticOrderAt h₀ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hh₀_diff.analyticAt z)).not.mpr hh₀_ne_fun
        have hP_top : analyticOrderAt P (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hP_diff.analyticAt z)).not.mpr hP_ne_fun
        -- f₁ = h₀ * P ⟹ order(f₁) = order(h₀) + order(P) in ℕ
        have hord_eq : analyticOrderNatAt f₁ (a n) =
            analyticOrderNatAt h₀ (a n) + analyticOrderNatAt P (a n) := by
          have hfun_eq : f₁ = h₀ * P :=
            funext fun z => by rw [hh₀_eq z, Pi.mul_apply]
          conv_lhs => rw [hfun_eq]
          exact analyticOrderNatAt_mul (hh₀_diff.analyticAt _) (hP_diff.analyticAt _)
            hh₀_top hP_top
        -- h₀(a n) = 0 ⟹ order(h₀, a n) ≥ 1
        have hh₀_pos : 1 ≤ analyticOrderNatAt h₀ (a n) := by
          rw [Nat.one_le_iff_ne_zero, Ne, analyticOrderNatAt,
            ENat.toNat_eq_zero, not_or]
          exact ⟨analyticOrderAt_ne_zero.mpr ⟨hh₀_diff.analyticAt _, hz⟩, hh₀_top⟩
        -- From multiplicity-aware enumeration: order(P, a n) = order(f₁, a n)
        have hP_ge : analyticOrderNatAt f₁ (a n) ≤ analyticOrderNatAt P (a n) := by
          have h := ha_ord_eq (a n) hf₁z han
          -- h : analyticOrderAt f₁ (a n) = analyticOrderAt P (a n)
          simp only [analyticOrderNatAt]
          exact ENat.toNat_le_toNat h.le hP_top
        -- Contradiction: f₁_ord = h₀_ord + P_ord ≥ 1 + f₁_ord, impossible in ℕ
        omega
      exact ⟨h₀, hh₀_diff, hh₀_ne, hh₀_eq⟩
    -- ═══════════════════════════════════════════════════════════
    -- Step 5: entire_logarithm + assembly
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm h hh_diff hh_ne
    refine ⟨m, g, a, p, hg_diff,
      fun n hn => by rw [hf_eq (a n), ha_zeros n hn, mul_zero],
      hconv, ?_, hp, ?_, ?_⟩
    · intro z
      rw [hf_eq z, hh_eq z, hg_eq z, ← mul_assoc]
    · intro z hfz hz
      have hf₁z : f₁ z = 0 := by
        have hmul : z ^ m * f₁ z = 0 := by rw [← hf_eq z, hfz]
        exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero m hz)
      exact ha_covers z hf₁z
    · intro z hfz hz
      have hf₁z : f₁ z = 0 := by
        have hmul : z ^ m * f₁ z = 0 := by rw [← hf_eq z, hfz]
        exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero m hz)
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) z :=
        (differentiable_pow m).analyticAt z
      have hpow_order : analyticOrderAt (fun w : ℂ => w ^ m) z = 0 :=
        hpow_an.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hz)
      have hfun : f = (fun w : ℂ => w ^ m) * f₁ := by
        funext w
        exact hf_eq w
      calc
        analyticOrderAt f z =
            analyticOrderAt ((fun w : ℂ => w ^ m) * f₁) z := by rw [hfun]
        _ = analyticOrderAt (fun w : ℂ => w ^ m) z + analyticOrderAt f₁ z :=
          analyticOrderAt_mul hpow_an (hf₁_diff.analyticAt z)
        _ = analyticOrderAt f₁ z := by rw [hpow_order, zero_add]
        _ = analyticOrderAt
            (fun w => ∏' n, weierstraßElementary p (w / a n)) z :=
          ha_ord_eq z hf₁z hz

/-- The existing public API is a direct projection of the stronger companion,
    so downstream positional destructuring can remain unchanged. -/
theorem weierstraß_factorization_legacy_projection_scratch (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) :
    ∃ (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ),
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (g z) *
        ∏' n, weierstraßElementary p (z / a n) := by
  obtain ⟨m, g, a, p, hg, ha, hs, hfac, _, _, _⟩ :=
    weierstraß_factorization_canonical_scratch f hf hf_ne hfin
  exact ⟨m, g, a, p, hg, ha, hs, hfac⟩

#print axioms weierstraß_factorization_canonical_scratch
#print axioms weierstraß_factorization_legacy_projection_scratch

end ArithmeticHodge.Analysis.EntireFunction
