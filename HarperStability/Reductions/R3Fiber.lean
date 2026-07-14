import HarperStability.Reductions.Basic

namespace HarperStability

/-!
R3 fiber expected-log worker.

This file is split out of `Reductions.Basic` so the remaining
`r3_fiber_log_lower` proof can be attacked independently from the R2 HBL
assembly.
-/

lemma r3_fiber_transfer {m : ℕ} (A : Finset (Cube m)) (I : Finset (Fin m))
    (theta_m : ℕ) :
    (∑ z ∈ A.image (proj Iᶜ),
      (((neighborhood theta_m (A.filter (fun x => proj Iᶜ x = z))).filter
        (fun y => proj Iᶜ y = z)).card : ℝ)) ≤
    ((neighborhood theta_m A).card : ℝ) := by
  classical
  let slice : Cube m → Finset (Cube m) := fun z =>
    (neighborhood theta_m (A.filter (fun x => proj Iᶜ x = z))).filter
      (fun y => proj Iᶜ y = z)
  have hpair :
      ((A.image (proj Iᶜ) : Finset (Cube m)) : Set (Cube m)).PairwiseDisjoint slice := by
    intro z _hz z' _hz' hne
    change Disjoint (slice z) (slice z')
    rw [Finset.disjoint_left]
    intro y hy hy'
    have hyz : proj Iᶜ y = z := (Finset.mem_filter.mp hy).2
    have hyz' : proj Iᶜ y = z' := (Finset.mem_filter.mp hy').2
    exact hne (hyz.symm.trans hyz')
  have hsubset : (A.image (proj Iᶜ)).biUnion slice ⊆ neighborhood theta_m A := by
    intro y hy
    rw [Finset.mem_biUnion] at hy
    rcases hy with ⟨z, _hz, hyz⟩
    have hy_neigh : y ∈ neighborhood theta_m (A.filter (fun x => proj Iᶜ x = z)) :=
      (Finset.mem_filter.mp hyz).1
    rw [mem_neighborhood_iff] at hy_neigh ⊢
    rcases hy_neigh with ⟨x, hx, hdist⟩
    exact ⟨x, (Finset.mem_filter.mp hx).1, hdist⟩
  have hnat :
      ∑ z ∈ A.image (proj Iᶜ), (slice z).card ≤ (neighborhood theta_m A).card := by
    rw [← Finset.card_biUnion hpair]
    exact Finset.card_le_card hsubset
  have hreal :
      ((∑ z ∈ A.image (proj Iᶜ), (slice z).card : ℕ) : ℝ) ≤
        ((neighborhood theta_m A).card : ℝ) := by
    exact_mod_cast hnat
  simpa [slice, Nat.cast_sum] using hreal

private lemma r3_uH_proj_pair_compl_eq_univ {m : ℕ} (A : Finset (Cube m))
    (I : Finset (Fin m)) :
    uH A (fun x => (proj I x, proj Iᶜ x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) := by
  classical
  apply le_antisymm
  · have hfun :
        (fun x : Cube m =>
          (proj I (proj (Finset.univ : Finset (Fin m)) x),
            proj Iᶜ (proj (Finset.univ : Finset (Fin m)) x))) =
          (fun x : Cube m => (proj I x, proj Iᶜ x)) := by
      funext x
      simp [proj]
    have hle := uH_comp_le A (proj (Finset.univ : Finset (Fin m)))
      (fun y : Cube m => (proj I y, proj Iᶜ y))
    simpa [hfun] using hle
  · have hfun :
        (fun x : Cube m => (proj I x, proj Iᶜ x).1 ∪ (proj I x, proj Iᶜ x).2) =
          (proj (Finset.univ : Finset (Fin m))) := by
      funext x
      ext t
      simp only [proj, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        Finset.mem_univ, and_true]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
        · exact hx
        · exact hx
      · intro hx
        by_cases ht : t ∈ I
        · exact Or.inl ⟨hx, ht⟩
        · exact Or.inr ⟨hx, ht⟩
    have hle := uH_comp_le A (fun x => (proj I x, proj Iᶜ x))
      (fun p : Cube m × Cube m => p.1 ∪ p.2)
    simpa [hfun] using hle

/-- Entropy of an injective-on-`A` statistic is the full `log |A|`. -/
private lemma uH_of_injOn_eq_log_card {m : ℕ} {B : Type*}
    (A : Finset (Cube m)) (hA : A.Nonempty) (f : Cube m → B)
    (hinj : Set.InjOn f A) : uH A f = Real.log (A.card : ℝ) := by
  classical
  have hApos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hpOn : ∀ b ∈ A.image f, pOn A f b = 1 / (A.card : ℝ) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
    unfold pOn
    congr 1
    norm_cast
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, hyf⟩
      exact hinj hyA hx hyf
    · rintro rfl
      exact ⟨hx, rfl⟩
  have hcard_img : (A.image f).card = A.card := Finset.card_image_of_injOn hinj
  have hnegMulLog : Real.negMulLog (1 / (A.card : ℝ)) =
      (1 / (A.card : ℝ)) * Real.log (A.card : ℝ) := by
    unfold Real.negMulLog
    rw [Real.log_div one_ne_zero hApos.ne', Real.log_one]
    ring
  unfold uH
  calc (∑ b ∈ A.image f, Real.negMulLog (pOn A f b))
      = ∑ _b ∈ A.image f, (1 / (A.card : ℝ)) * Real.log (A.card : ℝ) := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [hpOn b hb, hnegMulLog]
    _ = ((A.image f).card : ℝ) * ((1 / (A.card : ℝ)) * Real.log (A.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Real.log (A.card : ℝ) := by
        rw [hcard_img]
        field_simp

/-- On a fiber of `proj Iᶜ`, the window projection `proj I` is injective. -/
private lemma projI_injOn_fiber {m : ℕ} (A : Finset (Cube m))
    (I : Finset (Fin m)) (z : Cube m) :
    Set.InjOn (proj I) (A.filter fun x => proj Iᶜ x = z) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_filter] at hx hy
  ext t
  by_cases ht : t ∈ I
  · have h := congrArg (fun w => t ∈ w) hxy
    simpa [proj, ht] using h
  · have ht' : t ∈ Iᶜ := Finset.mem_compl.mpr ht
    have h := congrArg (fun w => t ∈ w) (hx.2.trans hy.2.symm)
    simpa [proj, ht'] using h

/-- The conditional entropy of a window given its complement is exactly the
expected log fiber size (all fibers of the uniform law are uniform). -/
private lemma uCondH_eq_expected_log_fiber {m : ℕ} (A : Finset (Cube m))
    (hA : A.Nonempty) (I : Finset (Fin m)) :
    uCondH A (proj I) (proj Iᶜ) =
      ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
        Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  classical
  unfold uCondH
  rw [uH_prod_sub_eq_sum A hA (proj I) (proj Iᶜ)]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  congr 1
  have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hinner :
      (∑ b ∈ A.image (proj I),
        Real.negMulLog (pOn (A.filter fun y => proj Iᶜ y = z) (proj I) b)) =
      uH (A.filter fun y => proj Iᶜ y = z) (proj I) := by
    unfold uH
    refine (Finset.sum_subset ?_ ?_).symm
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_filter] at hy ⊢
      obtain ⟨x, ⟨hxA, _⟩, hxy⟩ := hy
      exact ⟨x, hxA, hxy⟩
    · intro b _hb hb'
      have hzero : pOn (A.filter fun y => proj Iᶜ y = z) (proj I) b = 0 := by
        unfold pOn
        rw [div_eq_zero_iff]
        left
        simp only [Nat.cast_eq_zero, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro y hy hyb
        refine hb' ?_
        simp only [Finset.mem_image]
        exact ⟨y, hy, hyb⟩
      rw [hzero, Real.negMulLog_zero]
  rw [hinner,
    uH_of_injOn_eq_log_card _ hfib_ne _ (projI_injOn_fiber A I z)]

lemma r3_fiber_harper {m : ℕ} (A : Finset (Cube m)) (I : Finset (Fin m))
    (z : Cube m) (θ : ℕ) :
    V I.card ((A.filter (fun x => proj Iᶜ x = z)).card) θ ≤ (((neighborhood θ (A.filter (fun x => proj Iᶜ x = z))).filter (fun y => proj Iᶜ y = z)).card) := by
  by_cases hF : (A.filter fun x => proj Iᶜ x = z).Nonempty <;> simp_all +decide [ V ];
  · split_ifs <;> simp_all +decide [ Finset.min' ];
    obtain ⟨x0, hx0⟩ : ∃ x0 ∈ Finset.filter (fun x => proj Iᶜ x = z) A, True := by
      exact ⟨ hF.choose, hF.choose_spec, trivial ⟩
    have hz_subset : z ⊆ Iᶜ := by
      unfold proj at hx0; aesop;
    have hz_disjoint_I : Disjoint z I := by
      exact Finset.disjoint_left.mpr fun x hxz hxI => Finset.mem_compl.mp ( hz_subset hxz ) hxI
    generalize_proofs at *;
    -- Define the bijection `lift : Cube I.card → Cube m` by `lift w = (w.map e.toEmbedding) ∪ z`.
    obtain ⟨e, he⟩ : ∃ e : Fin I.card ↪o Fin m, Finset.univ.map e.toEmbedding = I := by
      use I.orderEmbOfFin rfl
      generalize_proofs at *;
      ext; simp
    generalize_proofs at *;
    set lift : Cube I.card → Cube m := fun w => (w.map e.toEmbedding) ∪ z;
    have hlift_inj : Function.Injective lift := by
      intro w1 w2 h_eq
      have h_eq_map : w1.map e.toEmbedding = w2.map e.toEmbedding := by
        ext x; replace h_eq := Finset.ext_iff.mp h_eq x; simp_all +decide [ Finset.disjoint_left ] ;
        replace he := Finset.ext_iff.mp he x; aesop;
      generalize_proofs at *;
      exact Finset.map_injective e.toEmbedding h_eq_map |> fun h => by simpa using h;;
    have hlift_proj : ∀ w : Cube I.card, proj Iᶜ (lift w) = z := by
      intro w; ext x; simp [lift, proj] ;
      by_cases hx : x ∈ z <;> simp_all +decide [ Finset.disjoint_left ];
      intro y hy hxy; replace he := Finset.ext_iff.mp he x; aesop;;
    have hlift_dist : ∀ w1 w2 : Cube I.card, hDist (lift w1) (lift w2) = hDist w1 w2 := by
      intros w1 w2
      have h_symmDiff : symmDiff (lift w1) (lift w2) = symmDiff (w1.map e.toEmbedding) (w2.map e.toEmbedding) := by
        simp +decide [ symmDiff, Finset.ext_iff ];
        intro a; by_cases ha : a ∈ z <;> simp +decide [ ha, lift ] ;
        exact ⟨ fun x hx hx' => False.elim <| Finset.disjoint_left.mp hz_disjoint_I ha <| hx'.symm ▸ Finset.mem_map_of_mem _ ( Finset.mem_univ _ ) |> fun h => he ▸ h, fun x hx hx' => False.elim <| Finset.disjoint_left.mp hz_disjoint_I ha <| hx'.symm ▸ Finset.mem_map_of_mem _ ( Finset.mem_univ _ ) |> fun h => he ▸ h ⟩
      generalize_proofs at *;
      unfold hDist; simp +decide [ h_symmDiff ] ;
      rw [ show symmDiff ( Finset.map e.toEmbedding w1 ) ( Finset.map e.toEmbedding w2 ) = Finset.map e.toEmbedding ( symmDiff w1 w2 ) from ?_, Finset.card_map ];
      unfold symmDiff; simp +decide [ Finset.map_sdiff, Finset.map_union ] ;;
    have hlift_surj : ∀ y : Cube m, proj Iᶜ y = z → ∃ w : Cube I.card, lift w = y := by
      intro y hy
      use Finset.univ.filter (fun j => e j ∈ y);
      ext x; simp [lift];
      by_cases hx : x ∈ I <;> simp_all +decide [ Finset.ext_iff, proj ]; all_goals grind +splitImp;
    generalize_proofs at *;
    refine' ⟨ Finset.filter ( fun w => lift w ∈ Finset.filter ( fun x => proj Iᶜ x = z ) A ) Finset.univ, _, _ ⟩
    all_goals generalize_proofs at *;
    · refine' Finset.card_bij ( fun w hw => lift w ) _ _ _ <;> simp_all +decide [ Function.Injective.eq_iff hlift_inj ];
      exact fun y hy hy' => by obtain ⟨ w, rfl ⟩ := hlift_surj y hy'; exact ⟨ w, by aesop ⟩ ;
    · refine' le_of_eq ( Finset.card_bij ( fun w hw => lift w ) _ _ _ ) <;> simp_all +decide [ Finset.mem_filter ];
      · exact fun a x hx hx' => ⟨ lift x, ⟨ hx, hlift_proj x ⟩, by simpa only [ hlift_dist ] using hx' ⟩;
      · exact fun a₁ x hx₁ hx₂ a₂ y hy₁ hy₂ h => hlift_inj h;
      · grind +qlia;
  · simp_all +decide [ Finset.filter_eq_empty_iff.mpr ];
    unfold neighborhood; aesop;

/-- Core analytic inequality for the geometric growth of sparse fibers.
Shows that the entropy chord for a sparse fiber (density `a ≤ q - ζ`)
grows strictly faster than the dense chord at `q`, yielding a quadratic gain. -/
private lemma r3_entropy_growth_core {q ζ p t a : ℝ}
    (hq_max : q ≤ 1 / 2)
    (hζ_pos : 0 < ζ) (hζ_le : ζ ≤ q / 2)
    (hp_pos : 0 < p) (hp_le : p ≤ 1)
    (ht_pos : 0 ≤ t) (ht_le : t ≤ p * ζ / 2)
    (ha_pos : 0 ≤ a) (ha_le : a ≤ q - ζ) :
    p * (H (a + t / p) - H a) - (H (q + t) - H q) ≥ 2 * t * ζ := by
  by_cases ht0 : t = 0
  · rw [ht0]
    norm_num
  have ht_pos' : 0 < t := lt_of_le_of_ne ht_pos (Ne.symm ht0)
  set h : ℝ := t / p with hh_def
  have hh_pos : 0 < h := by
    rw [hh_def]
    exact div_pos ht_pos' hp_pos
  have hh_nonneg : 0 ≤ h := hh_pos.le
  have hh_le_zeta_half : h ≤ ζ / 2 := by
    rw [hh_def]
    rw [div_le_iff₀ hp_pos]
    linarith
  have ht_le_zeta_half : t ≤ ζ / 2 := by
    nlinarith [ht_le, hp_le, hζ_pos]
  have hq_pos : 0 < q := by nlinarith [hζ_pos, hζ_le]
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have ha_h_le : a + h ≤ q - ζ / 2 := by nlinarith
  have ha_h_lt_q : a + h < q := by nlinarith
  have ha_lt_ah : a < a + h := by linarith
  have hq_lt_qt : q < q + t := by linarith
  have ha_le_one : a ≤ 1 := by nlinarith [ha_le, hq_max, hζ_pos]
  have hah_le_one : a + h ≤ 1 := by nlinarith [ha_h_le, hq_max]
  have hqt_le_one : q + t ≤ 1 := by nlinarith [hq_max, ht_le_zeta_half, hζ_le]
  let F : ℝ → ℝ := fun x => H x + 2 * x ^ 2
  have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) F := by
    simpa [F, H] using concaveOn_binEntropy_add_two_sq
  have hslope1 := hconc.slope_anti_adjacent (x := a) (y := a + h) (z := q)
    ⟨ha_pos, ha_le_one⟩ ⟨hq_nonneg, by linarith⟩ ha_lt_ah ha_h_lt_q
  have hslope2 := hconc.slope_anti_adjacent (x := a + h) (y := q) (z := q + t)
    ⟨by nlinarith [ha_pos, hh_nonneg], hah_le_one⟩
    ⟨by nlinarith [hq_nonneg, ht_pos], hqt_le_one⟩ ha_h_lt_q hq_lt_qt
  have hslopeF : (F (q + t) - F q) / t ≤ (F (a + h) - F a) / h := by
    have htrans := le_trans hslope2 hslope1
    simpa [F, hh_pos.ne', ht_pos'.ne'] using htrans
  have hslopeH : 2 * ζ ≤ (H (a + h) - H a) / h - (H (q + t) - H q) / t := by
    have h_alg :
        (H (q + t) - H q) / t + 2 * (2 * q + t) ≤
          (H (a + h) - H a) / h + 2 * (2 * a + h) := by
      have h := hslopeF
      dsimp [F] at h
      field_simp [ht_pos'.ne', hh_pos.ne'] at h ⊢
      nlinarith
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hslopeH ht_pos
  have hrewrite :
      t * ((H (a + h) - H a) / h - (H (q + t) - H q) / t) =
        p * (H (a + t / p) - H a) - (H (q + t) - H q) := by
    rw [hh_def]
    field_simp [hp_pos.ne', ht_pos'.ne']
  rw [hrewrite] at hmul
  nlinarith

/-
Concavity shift bound: `H (a+δ) - H a ≤ H δ` for `a ≥ 0`, `δ > 0`, `a+δ ≤ 1`.
Proved from concavity of `H` (via `concaveOn_binEntropy_add_two_sq`): the slope
of `H` over `[a, a+δ]` is at most the slope over `[0, δ]`, whose value is
`H δ / δ`.
-/
lemma r3_H_shift_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hle : a + δ ≤ 1) :
    H (a + δ) - H a ≤ H δ := by
  have h_concave : ConcaveOn ℝ (Set.Icc 0 1) (fun x => Real.binEntropy x + 2 * x^2) := by
    convert concaveOn_binEntropy_add_two_sq using 1;
  by_cases ha0 : a = 0;
  · unfold H; aesop;
  · have := h_concave.2 ( show 0 ∈ Set.Icc 0 1 by norm_num ) ( show a + δ ∈ Set.Icc 0 1 by constructor <;> linarith );
    have := @this ( δ / ( a + δ ) ) ( a / ( a + δ ) ) ( by positivity ) ( by positivity ) ( by rw [ ← add_div, div_eq_iff ] <;> linarith ) ; simp_all +decide [ mul_comm ] ;
    simp_all +decide [ mul_div_cancel₀ _ ( by positivity : ( a + δ ) ≠ 0 ) ];
    rename_i h; have := @h ( a / ( a + δ ) ) ( δ / ( a + δ ) ) ( by positivity ) ( by positivity ) ( by rw [ ← add_div, div_eq_iff ] <;> linarith ) ; simp_all +decide ;
    simp_all +decide [ H, div_mul_cancel₀ _ ( by positivity : ( a + δ ) ≠ 0 ) ];
    rw [ div_mul_eq_mul_div, div_le_iff₀ ] at * <;> nlinarith [ mul_self_pos.mpr ha0 ]

/-
`n · H(1/n)` is sublinear (it is `Θ(log n)`).
-/
private lemma r3_nH_inv_sublinear :
    Sublinear (fun n : ℕ => (n : ℝ) * H (1 / (n : ℝ))) := by
  refine' ⟨ fun n => _, _ ⟩;
  · by_cases hn : n = 0 <;> simp +decide [ hn, H ];
    exact mul_nonneg ( Nat.cast_nonneg _ ) ( Real.binEntropy_nonneg ( by positivity ) ( inv_le_one_of_one_le₀ ( mod_cast Nat.one_le_iff_ne_zero.mpr hn ) ) );
  · intro ε hε
    have h_lim : Filter.Tendsto (fun n : ℕ => H (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.comp ( show Filter.Tendsto H ( nhds 0 ) ( nhds 0 ) from ?_ ) ( tendsto_one_div_atTop_nhds_zero_nat ) using 2;
      convert ContinuousAt.tendsto _ using 2 <;> norm_num [ H ];
      refine' ContinuousAt.add _ _;
      · simpa using Real.continuous_mul_log.neg.continuousAt;
      · exact ContinuousAt.mul ( continuousAt_const.sub continuousAt_id ) ( ContinuousAt.log ( ContinuousAt.inv₀ ( continuousAt_const.sub continuousAt_id ) ( by norm_num ) ) ( by norm_num ) );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( ge_mem_nhds hε ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by simpa [ mul_comm ] using mul_le_mul_of_nonneg_left ( hN n hn ) ( Nat.cast_nonneg n ) ⟩

/-- Running maximum of a function over the prefix `{0, …, m}`. -/
noncomputable def r3_runMax (s : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩ s

lemma r3_runMax_ge {s : ℕ → ℝ} {j m : ℕ} (h : j ≤ m) :
    s j ≤ r3_runMax s m := by
  -- Since j is in the range up to m+1, the supremum must be at least s j. This follows directly from the definition of the supremum.
  apply Finset.le_sup' s (Finset.mem_range.mpr (by linarith))

private lemma r3_runMax_sublinear {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (r3_runMax s) := by
  refine' ⟨ fun n => _, fun ε hε => _ ⟩;
  · exact le_trans ( hs.1 0 ) ( r3_runMax_ge ( Nat.zero_le _ ) );
  · obtain ⟨ N, hN ⟩ := hs.2 ( ε / 2 ) ( half_pos hε );
    -- Let $C = \max_{0 \leq j \leq N} s j$.
    obtain ⟨C, hC⟩ : ∃ C, ∀ j ≤ N, s j ≤ C := by
      exact ⟨ ∑ j ∈ Finset.range ( N + 1 ), |s j|, fun j hj => le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun i _ => abs_nonneg ( s i ) ) ( Finset.mem_range_succ_iff.mpr hj ) ) ⟩;
    refine' ⟨ N + ⌈2 * C / ε⌉₊ + 1, fun n hn => _ ⟩;
    refine' Finset.sup'_le _ _ _;
    intro j hj; by_cases hj' : j ≤ N <;> simp_all +decide ;
    · nlinarith [ Nat.le_ceil ( 2 * C / ε ), mul_div_cancel₀ ( 2 * C ) hε.ne', show ( n : ℝ ) ≥ N + ⌈2 * C / ε⌉₊ + 1 by exact_mod_cast hn, hC j hj' ];
    · nlinarith [ hN j hj'.le, show ( j : ℝ ) ≤ n by norm_cast ]

/-
Robust entropy growth: the sparse density `a` is allowed to exceed the
target `q - ζ` by a nonnegative slack `δ`, at the cost of an `O(δ)` loss in the
quadratic gain.  Derived from `r3_entropy_growth_core` applied at
`a' = min a (q - ζ)` together with the chord bound `binEntropy_chord_upper`.
-/
private lemma r3_entropy_growth_robust {q ζ p t a δ : ℝ}
    (hq_max : q ≤ 1 / 2) (hζ_pos : 0 < ζ) (hζ_le : ζ ≤ q / 2)
    (hp_pos : 0 < p) (hp_le : p ≤ 1)
    (ht_pos : 0 ≤ t) (ht_le : t ≤ p * ζ / 2)
    (ha_pos : 0 ≤ a) (ha_half : a ≤ 1 / 2)
    (hat_half : a + t / p ≤ 1 / 2) (hδ : 0 ≤ δ)
    (ha_le : a ≤ q - ζ + δ) :
    p * (H (a + t / p) - H a) - (H (q + t) - H q) ≥
      2 * t * ζ - δ * Real.log ((1 - q / 2) / (q / 2)) := by
  by_cases ha_le' : a ≤ q - ζ;
  · have := r3_entropy_growth_core (hq_max := hq_max) (hζ_pos := hζ_pos) (hζ_le := hζ_le) (hp_pos := hp_pos) (hp_le := hp_le) (ht_pos := ht_pos) (ht_le := ht_le) (ha_pos := ha_pos) (ha_le := ha_le');
    exact le_trans ( sub_le_self _ <| mul_nonneg hδ <| Real.log_nonneg <| by rw [ le_div_iff₀ ] <;> linarith ) this;
  · have h_term1 : H (a + t / p) - H (q - ζ + t / p) ≥ 0 := by
      unfold H;
      unfold Real.binEntropy;
      have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 (1 / 2), deriv (fun x => x * Real.log (1 / x) + (1 - x) * Real.log (1 / (1 - x))) x ≥ 0 := by
        intro x hx; norm_num [ show x ≠ 0 from hx.1.ne', show 1 - x ≠ 0 from by linarith [ hx.2 ], Real.log_div, Real.log_mul, sub_ne_zero ] ; ring_nf;
        have h_deriv_nonneg : deriv (fun x => -(x * Real.log x) + (x * Real.log (1 - x) - Real.log (1 - x))) x = -Real.log x - 1 + Real.log (1 - x) + x * (-1 / (1 - x)) - (-1 / (1 - x)) := by
          convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_id x ) ( Real.hasDerivAt_log hx.1.ne' ) ) ) ( HasDerivAt.sub ( HasDerivAt.mul ( hasDerivAt_id x ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ) ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ) ) ) using 1 ; ring_nf;
          norm_num [ hx.1.ne' ] ; ring;
        nlinarith [ hx.1, hx.2, Real.log_le_sub_one_of_pos hx.1, Real.log_le_log ( by linarith [ hx.1, hx.2 ] ) ( by linarith [ hx.1, hx.2 ] : 1 - x ≥ x ), mul_div_cancel₀ ( -1 ) ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ];
      have := exists_deriv_eq_slope ( f := fun x => x * Real.log ( 1 / x ) + ( 1 - x ) * Real.log ( 1 / ( 1 - x ) ) ) ( show q - ζ + t / p < a + t / p by linarith ) ; norm_num at *;
      contrapose! this;
      refine' ⟨ _, _, _ ⟩;
      · fun_prop;
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.neg ( differentiableAt_id.mul ( Real.differentiableAt_log ( by linarith [ hx.1, show 0 < q - ζ + t / p by exact add_pos_of_pos_of_nonneg ( by linarith ) ( div_nonneg ht_pos hp_pos.le ) ] ) ) ) ) ( DifferentiableAt.neg ( DifferentiableAt.mul ( differentiableAt_id.const_sub _ ) ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith [ hx.2, show a + t / p ≤ 1 / 2 by linarith ] ) ) ) ) );
      · intro c hc; rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonneg c ( by linarith [ show 0 ≤ t / p by positivity ] ) ( by linarith [ show 0 ≤ t / p by positivity ] ) ] ;
    have h_term2 : H a - H (q - ζ) ≤ (a - (q - ζ)) * Real.log ((1 - (q - ζ)) / (q - ζ)) := by
      apply_rules [ binEntropy_chord_upper ]; all_goals linarith;
    have h_log_ratio : Real.log ((1 - (q - ζ)) / (q - ζ)) ≤ Real.log ((1 - q / 2) / (q / 2)) := by
      exact Real.log_le_log ( div_pos ( by linarith ) ( by linarith ) ) ( by rw [ div_le_div_iff₀ ] <;> nlinarith );
    have h_core : p * (H (q - ζ + t / p) - H (q - ζ)) - (H (q + t) - H q) ≥ 2 * t * ζ := by
      apply r3_entropy_growth_core;
      all_goals linarith;
    have h_final : p * (H (a + t / p) - H a) - (H (q + t) - H q) ≥ p * (H (q - ζ + t / p) - H (q - ζ)) - (H (q + t) - H q) - (a - (q - ζ)) * Real.log ((1 - q / 2) / (q / 2)) := by
      nlinarith [ show 0 ≤ ( a - ( q - ζ ) ) * Real.log ( ( 1 - ( q - ζ ) ) / ( q - ζ ) ) by exact mul_nonneg ( by linarith ) ( Real.log_nonneg ( by rw [ le_div_iff₀ ] <;> linarith ) ) ];
    nlinarith [ show 0 ≤ Real.log ( ( 1 - q / 2 ) / ( q / 2 ) ) by exact Real.log_nonneg ( by rw [ le_div_iff₀ ] <;> linarith ) ]

lemma r3_theta_floor_bounds (Q : QData) (pLow : ℝ) (hlow : 0 < pLow)
    (m : ℕ) (ζ : ℝ) (hζ_pos : 0 < ζ) (hζscale : ζ ≤ 2 * Q.s0 / pLow)
    (Icard : ℕ) (hIlow : pLow * (m : ℝ) ≤ (Icard : ℝ)) :
    let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
    θ = ⌊pLow * ζ * (m : ℝ) / 2⌋₊ ∧
    (θ : ℝ) / (m : ℝ) ≤ pLow * ζ / 2 ∧
    (1 ≤ m → pLow * ζ / 2 - 1 / (m : ℝ) ≤ (θ : ℝ) / (m : ℝ)) ∧
    (θ : ℝ) / (Icard : ℝ) ≤ ζ / 2 ∧
    θ ≤ Nat.ceil (Q.s0 * (m : ℝ)) := by
  have hmin_left :
      ⌊pLow * ζ * (m : ℝ) / 2⌋₊ ≤ Nat.ceil (Q.s0 * (m : ℝ)) := by
    apply Nat.floor_le_of_le
    have hscale' : pLow * ζ / 2 ≤ Q.s0 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hmul : pLow * ζ ≤ pLow * (2 * Q.s0 / pLow) :=
        mul_le_mul_of_nonneg_left hζscale hlow.le
      have hcancel : pLow * (2 * Q.s0 / pLow) = 2 * Q.s0 := by
        rw [mul_div_cancel₀ _ hlow.ne']
      linarith
    have hmul :
        (pLow * ζ / 2) * (m : ℝ) ≤ Q.s0 * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hscale' (Nat.cast_nonneg m)
    have hrewrite : pLow * ζ * (m : ℝ) / 2 = (pLow * ζ / 2) * (m : ℝ) := by
      ring
    exact le_trans (by rwa [hrewrite]) (Nat.le_ceil _)
  have hmin_eq :
      min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ))) =
        ⌊pLow * ζ * (m : ℝ) / 2⌋₊ := min_eq_left hmin_left
  have hθceil :
      min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ))) ≤
        Nat.ceil (Q.s0 * (m : ℝ)) := min_le_right _ _
  refine ⟨hmin_eq, ?_, ?_, ?_, hθceil⟩
  · rw [hmin_eq]
    have hfloor :
        (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) ≤ pLow * ζ * (m : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    by_cases hm : m = 0
    · simp [hm]
      positivity
    · have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      rw [div_le_iff₀ hmpos]
      nlinarith
  · intro hm
    rw [hmin_eq]
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hlt :
        pLow * ζ * (m : ℝ) / 2 <
          (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one (pLow * ζ * (m : ℝ) / 2)
    have hfloor_lower :
        pLow * ζ * (m : ℝ) / 2 - 1 ≤
          (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) := by
      linarith
    have hdiv :
        (pLow * ζ * (m : ℝ) / 2 - 1) / (m : ℝ) ≤
          (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) / (m : ℝ) :=
      div_le_div_of_nonneg_right hfloor_lower hmpos.le
    have hrewrite :
        (pLow * ζ * (m : ℝ) / 2 - 1) / (m : ℝ) =
          pLow * ζ / 2 - 1 / (m : ℝ) := by
      field_simp [hmpos.ne']
    rwa [hrewrite] at hdiv
  · rw [hmin_eq]
    by_cases hm : m = 0
    · simp [hm]
      positivity
    · have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hIpos : 0 < (Icard : ℝ) :=
        lt_of_lt_of_le (mul_pos hlow hmpos) hIlow
      have hfloor :
          (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) ≤ pLow * ζ * (m : ℝ) / 2 :=
        Nat.floor_le (by positivity)
      have hscaled :
          pLow * (m : ℝ) * (ζ / 2) ≤ (Icard : ℝ) * (ζ / 2) :=
        mul_le_mul_of_nonneg_right hIlow (by positivity)
      rw [div_le_iff₀ hIpos]
      nlinarith

lemma r3_vplus_witness_succ_card (n k : ℕ) (t : ℕ)
    (ht_max : ∀ t', t' ≤ n → (ball (∅ : Cube n) t').card ≤ k → t' ≤ t)
    (ht_lt : t < n) :
    k < (ball (∅ : Cube n) (t + 1)).card := by
  by_contra hnot
  have hsucc_le : t + 1 ≤ n := Nat.succ_le_of_lt ht_lt
  have hcard_le : (ball (∅ : Cube n) (t + 1)).card ≤ k := Nat.le_of_not_gt hnot
  have hle := ht_max (t + 1) hsucc_le hcard_le
  omega

private lemma r3_vplus_volume_ratio_lower (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (n k θ : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ 2 ^ n) :
    ∃ t : ℕ,
      t ≤ n ∧
      (ball (∅ : Cube n) t).card ≤ k ∧
      (t + θ ≤ n / 2 → t + 1 ≤ n / 2 →
        let vSlack := Classical.choose hBV
        Real.exp (H ((t + θ : ℝ) / (n : ℝ)) * (n : ℝ) -
          H ((t + 1 : ℝ) / (n : ℝ)) * (n : ℝ) -
          2 * vSlack n) * (k : ℝ) ≤ (V n k θ : ℝ)) := by
  classical
  obtain ⟨t, ht_le, ht_card, ht_max, htV⟩ := hVPlus n k θ hk1 hkn
  refine ⟨t, ht_le, ht_card, ?_⟩
  intro htθ_safe ht1_safe
  let vSlack := Classical.choose hBV
  have hvol := (Classical.choose_spec hBV).2
  have hlow := (hvol n (t + θ) htθ_safe).1
  have hupper := (hvol n (t + 1) ht1_safe).2
  have ht_lt : t < n := by omega
  have hk_succ :
      (k : ℝ) ≤ ((ball (∅ : Cube n) (t + 1)).card : ℝ) := by
    exact_mod_cast (r3_vplus_witness_succ_card n k t ht_max ht_lt).le
  calc
    Real.exp (H ((t + θ : ℝ) / (n : ℝ)) * (n : ℝ) -
          H ((t + 1 : ℝ) / (n : ℝ)) * (n : ℝ) -
          2 * vSlack n) * (k : ℝ)
        ≤ Real.exp (H ((t + θ : ℝ) / (n : ℝ)) * (n : ℝ) -
          H ((t + 1 : ℝ) / (n : ℝ)) * (n : ℝ) -
          2 * vSlack n) *
            ((ball (∅ : Cube n) (t + 1)).card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hk_succ (Real.exp_pos _).le
    _ ≤ Real.exp (H ((t + θ : ℝ) / (n : ℝ)) * (n : ℝ) -
          H ((t + 1 : ℝ) / (n : ℝ)) * (n : ℝ) -
          2 * vSlack n) *
            Real.exp (H ((t + 1 : ℝ) / (n : ℝ)) * (n : ℝ) + vSlack n) := by
          exact mul_le_mul_of_nonneg_left (by simpa [vSlack, Nat.cast_add] using hupper)
            (Real.exp_pos _).le
    _ = Real.exp (H ((t + θ : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ ((ball (∅ : Cube n) (t + θ)).card : ℝ) := by
          simpa [vSlack, Nat.cast_add] using hlow
    _ ≤ (V n k θ : ℝ) := htV

/-- Lower chord bound for binary entropy on the increasing branch. -/
private lemma r3_binEntropy_chord_lower_local {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    (b - a) * Real.log ((1 - b) / b) ≤ H b - H a := by
  by_cases h_eq : a = b
  · subst b
    simp
  obtain ⟨c, hc⟩ :
      ∃ c ∈ Set.Ioo a b,
        deriv H c = (H b - H a) / (b - a) := by
    apply_rules [exists_deriv_eq_slope]
    · exact lt_of_le_of_ne hab h_eq
    · refine' ContinuousOn.congr _ _
      use fun x => -x * Real.log x - (1 - x) * Real.log (1 - x)
      · exact ContinuousOn.sub
          (ContinuousOn.mul (continuousOn_id.neg)
            (Real.continuousOn_log.mono
              (by intro x hx; exact ne_of_gt (by linarith [hx.1]))))
          (ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
            (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
              (by intro x hx; exact ne_of_gt (by linarith [hx.2, hb]))))
      · intro x hx
        unfold H
        norm_num [Real.binEntropy]
        ring
    · intro x hx
      exact DifferentiableAt.differentiableWithinAt
        ((Real.hasDerivAt_binEntropy (by linarith [hx.1])
          (by linarith [hx.2, hb])).differentiableAt)
  have h_deriv : deriv H c = Real.log (1 - c) - Real.log c := by
    convert Real.deriv_binEntropy c using 1
  have h_log_div :
      Real.log ((1 - b) / b) ≤ Real.log (1 - c) - Real.log c := by
    rw [← Real.log_div (by linarith [hc.1.1, hc.1.2, hb])
      (by linarith [ha, hc.1.1])]
    exact Real.log_le_log
      (div_pos (by linarith [hc.1.1, hc.1.2, hb]) (by linarith [ha, hc.1.1]))
      (by
        rw [div_le_div_iff₀] <;> nlinarith [ha, hc.1.1, hc.1.2, hb])
  rw [h_deriv, eq_div_iff] at hc
  · nlinarith [hc.1.1, hc.1.2, h_log_div]
  · linarith [hc.1.1, hc.1.2]

lemma r3_entropy_compact_inverse_chord (Q : QData) (hvalid : validQData Q) :
    ∃ L > 0, ∀ a x : ℝ,
      Q.qMin / 2 ≤ a → a ≤ x → x ≤ Q.qMax + Q.s0 →
      L * (x - a) ≤ H x - H a := by
  let hi : ℝ := Q.qMax + Q.s0
  refine ⟨Real.log ((1 - hi) / hi), ?_, ?_⟩
  · have hhi_pos : 0 < hi := by
      dsimp [hi]
      nlinarith [hvalid.1, hvalid.2.1, hvalid.2.2.2.1]
    have hhi_lt_half : hi < 1 / 2 := by
      dsimp [hi]
      nlinarith [hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1]
    exact Real.log_pos (by
      rw [one_lt_div hhi_pos]
      linarith)
  · intro a x ha hax hxhi
    have hhi_pos : 0 < hi := by
      dsimp [hi]
      nlinarith [hvalid.1, hvalid.2.1, hvalid.2.2.2.1]
    have hhi_lt_half : hi < 1 / 2 := by
      dsimp [hi]
      nlinarith [hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1]
    have ha_pos : 0 < a := by nlinarith [hvalid.1, ha]
    have hx_half : x ≤ 1 / 2 := by linarith [hxhi, hhi_lt_half]
    have hchord := r3_binEntropy_chord_lower_local ha_pos hax hx_half
    have hlog_le :
        Real.log ((1 - hi) / hi) ≤ Real.log ((1 - x) / x) := by
      apply Real.log_le_log
      · exact div_pos (by linarith) (by linarith)
      · rw [div_le_div_iff₀] <;> nlinarith [hhi_pos, hhi_lt_half, hxhi, ha_pos, hax]
    have hdiff_nonneg : 0 ≤ x - a := by linarith
    calc
      Real.log ((1 - hi) / hi) * (x - a)
          = (x - a) * Real.log ((1 - hi) / hi) := by ring
      _ ≤ (x - a) * Real.log ((1 - x) / x) :=
          mul_le_mul_of_nonneg_left hlog_le hdiff_nonneg
      _ ≤ H x - H a := hchord

private lemma r3_radius_entropy_upper_from_k (hBV : BallVolumeTwoSidedStatement)
    (n t : ℕ) (k : ℕ) (q ζ L : ℝ)
    (ht_safe : t ≤ n / 2)
    (h_ball : (ball (∅ : Cube n) t).card ≤ k)
    (hk : (k : ℝ) ≤ Real.exp (H (q - ζ) * (n : ℝ)))
    (_ha_pos : 0 < q - ζ)
    (_ha_half : q - ζ ≤ 1 / 2)
    (hL_pos : 0 < L)
    (h_inv : ∀ x : ℝ, q - ζ ≤ x → x ≤ 1 / 2 →
      L * (x - (q - ζ)) ≤ H x - H (q - ζ))
    (hn : 0 < n) :
    let vSlack := Classical.choose hBV
    (t : ℝ) / (n : ℝ) ≤ q - ζ + (vSlack n / (n : ℝ)) / L := by
  classical
  let vSlack := Classical.choose hBV
  have hvol := (Classical.choose_spec hBV).2
  have hslack_nonneg : 0 ≤ vSlack n := (Classical.choose_spec hBV).1.1 n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlow := (hvol n t ht_safe).1
  have hball_real : ((ball (∅ : Cube n) t).card : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast h_ball
  have hexp_chain :
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) ≤
        Real.exp (H (q - ζ) * (n : ℝ)) :=
    le_trans hlow (le_trans hball_real hk)
  have hlog_chain :
      H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n ≤
        H (q - ζ) * (n : ℝ) :=
    Real.exp_le_exp.mp hexp_chain
  have hH_le :
      H ((t : ℝ) / (n : ℝ)) - H (q - ζ) ≤ vSlack n / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    nlinarith
  have ht_half_real : (t : ℝ) ≤ (n : ℝ) / 2 := by
    have ht2 : 2 * t ≤ n := by omega
    have ht2r : ((2 * t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht2
    norm_num at ht2r ⊢
    linarith
  have hx_half : (t : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnpos]
    linarith
  have hδ_nonneg : 0 ≤ (vSlack n / (n : ℝ)) / L :=
    div_nonneg (div_nonneg hslack_nonneg hnpos.le) hL_pos.le
  by_cases hx : (t : ℝ) / (n : ℝ) ≤ q - ζ
  · linarith
  · have hax : q - ζ ≤ (t : ℝ) / (n : ℝ) := le_of_not_ge hx
    have h_inv_applied := h_inv ((t : ℝ) / (n : ℝ)) hax hx_half
    have hdiff_le : ((t : ℝ) / (n : ℝ)) - (q - ζ) ≤
        (vSlack n / (n : ℝ)) / L := by
      rw [le_div_iff₀ hL_pos]
      exact le_trans (by simpa [mul_comm] using h_inv_applied) hH_le
    linarith

/-- Multiplying a sublinear envelope by a nonnegative constant keeps it sublinear. -/
private lemma r3_sublinear_const_mul {s : ℕ → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hs : Sublinear s) : Sublinear (fun n => c * s n) := by
  refine ⟨fun n => mul_nonneg hc (hs.1 n), fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hs.2 (ε / (c + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : c * s n ≤ c * (ε / (c + 1) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hc
  have h3 : c * (ε / (c + 1) * (n : ℝ)) ≤ ε * (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_mul_eq_mul_div, mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0:ℝ) < c + 1)]
    nlinarith
  linarith

/-
A constant nonnegative function is sublinear.
-/
private lemma r3_sublinear_const (c : ℝ) (hc : 0 ≤ c) : Sublinear (fun _ : ℕ => c) := by
  exact ⟨ fun _ => hc, fun ε hε => ⟨ ⌈c / ε⌉₊ + 1, fun n hn => by nlinarith [ Nat.le_ceil ( c / ε ), mul_div_cancel₀ c ( ne_of_gt hε ), ( by norm_cast : ( ⌈c / ε⌉₊ : ℝ ) + 1 ≤ n ) ] ⟩ ⟩

/-- `V n k r ≥ k` whenever the family of `k`-sets is nonempty (`k ≤ 2^n`). -/
private lemma r3_k_le_V (n k r : ℕ) (hk : k ≤ 2 ^ n) : k ≤ V n k r := by
  classical
  have hcard_univ : (Finset.univ : Finset (Cube n)).card = 2 ^ n := by
    simp +decide [Finset.card_univ]
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Cube n))) (n := k)
      (by rw [hcard_univ]; exact hk)
  have hsubA : A ⊆ neighborhood r A := by
    intro x hx
    rw [mem_neighborhood_iff]
    exact ⟨x, hx, by simp [hDist]⟩
  unfold V
  have hmem :
      (neighborhood r A).card ∈
        ((Finset.univ : Finset (Cube n)).powerset.filter
          (fun B : Finset (Cube n) => B.card = k)).image
          (fun B => (neighborhood r B).card) := by
    refine Finset.mem_image.mpr ⟨A, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hAsub, hAcard⟩
  rw [dif_pos ⟨_, hmem⟩]
  apply Finset.le_min'
  intro v hv
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hv
  rw [Finset.mem_filter] at hB
  have hsubB : B ⊆ neighborhood r B := by
    intro x hx
    rw [mem_neighborhood_iff]
    exact ⟨x, hx, by simp [hDist]⟩
  calc k = B.card := hB.2.symm
    _ ≤ (neighborhood r B).card := Finset.card_le_card hsubB

/-
Hamming balls around a fixed center are monotone in radius (cardinality).
-/
private lemma r3_ball_card_mono {n : ℕ} {a b : ℕ} (hab : a ≤ b) :
    (ball (∅ : Cube n) a).card ≤ (ball (∅ : Cube n) b).card := by
  refine Finset.card_mono ?_;
  exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, le_trans ( Finset.mem_filter.mp hx |>.2 ) hab ⟩

/-
The VPlus max-witness eventually stays inside the safe (below-equator) zone,
and its radius is entropy-controlled.  For `Icard ≥ N`, the maximal `t` with
`ball(t) ≤ k` satisfies both the safety bounds `t + θ ≤ Icard/2`, `t + 1 ≤ Icard/2`
and the radius bound `t/Icard ≤ q - ζ + vSlack Icard/(Icard·L)`.
-/
set_option maxHeartbeats 1000000 in
lemma r3_fiber_growth_witness_safe (vSlack : ℕ → ℝ) (hvsub : Sublinear vSlack)
    (hvol : ∀ (n t : ℕ), t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + vSlack n))
    (Q : QData) (hvalid : validQData Q)
    (L : ℝ) (hLpos : 0 < L)
    (h_inv : ∀ a x : ℝ, Q.qMin / 2 ≤ a → a ≤ x → x ≤ Q.qMax + Q.s0 →
        L * (x - a) ≤ H x - H a) :
    ∃ N : ℕ, ∀ (Icard : ℕ), N ≤ Icard →
      ∀ (q ζ : ℝ), Q.qMin ≤ q → q ≤ Q.qMax → 0 < ζ → ζ ≤ q / 2 →
      ∀ (θ : ℕ), (θ : ℝ) / (Icard : ℝ) ≤ ζ / 2 →
      ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.exp (H (q - ζ) * (Icard : ℝ)) →
      ∀ (t : ℕ), t ≤ Icard → (ball (∅ : Cube Icard) t).card ≤ k →
        (∀ t', t' ≤ Icard → (ball (∅ : Cube Icard) t').card ≤ k → t' ≤ t) →
        t + θ ≤ Icard / 2 ∧ t + 1 ≤ Icard / 2 ∧
          (t : ℝ) / (Icard : ℝ) ≤ q - ζ + (vSlack Icard) / ((Icard : ℝ) * L) := by
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ Icard ≥ N1, vSlack Icard ≤ (L * (Q.s0 / 4) / 2) * Icard := by
    convert hvsub.2 ( L * Q.s0 / 8 ) ( by nlinarith [ hvalid.2.2.2.1 ] ) using 1 ; ring_nf!;
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ Icard ≥ N2, vSlack Icard ≤ (L * (1 / 2 - Q.qMax) / 2) * Icard := by
    have := hvsub;
    exact this.2 ( L * ( 1 / 2 - Q.qMax ) / 2 ) ( by nlinarith [ hvalid.2.2.1 ] ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun Icard hIcard => hN Icard hIcard ⟩;
  use max (max N1 N2) (Nat.ceil (4 / Q.s0) + 1) + 1;
  intro Icard hIcard q ζ hq hq' hζ hζ' θ hθ k hk hk' t ht ht' ht''; specialize hN1 Icard ( by linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ) ; specialize hN2 Icard ( by linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ) ;
  -- Let $w = \lfloor hi * Icard \rfloor$.
  set w := Nat.floor ((Q.qMax + Q.s0 / 2) * Icard) with hw_def
  have hw_le : w ≤ Icard / 2 := by
    have hw_le : (w : ℝ) ≤ (Q.qMax + Q.s0 / 2) * Icard := by
      exact Nat.floor_le ( mul_nonneg ( add_nonneg ( le_trans ( by linarith [ hvalid.1 ] ) hvalid.2.1 ) ( div_nonneg ( by linarith [ hvalid.2.2.2.1 ] ) zero_le_two ) ) ( Nat.cast_nonneg _ ) );
    have hw_le_half : (Q.qMax + Q.s0 / 2) * Icard < (1 / 2) * Icard := by
      exact mul_lt_mul_of_pos_right ( by linarith [ hvalid.2.2.2.2.2.1, hvalid.2.2.2.1, hvalid.2.2.2.2.1 ] ) ( Nat.cast_pos.mpr ( by linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ) );
    exact Nat.le_div_iff_mul_le zero_lt_two |>.2 ( by rw [ ← @Nat.cast_le ℝ ] ; push_cast; linarith )
  have hw_ge : Q.qMax + Q.s0 / 4 ≤ (w : ℝ) / Icard := by
    rw [ le_div_iff₀ ] <;> norm_num at *;
    · have := Nat.lt_of_ceil_lt ( by linarith : ⌈4 / Q.s0⌉₊ < Icard ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ hvalid.2.2.2.1, hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1, hvalid.2.2.2.2.2.2.1, Nat.lt_floor_add_one ( ( Q.qMax + Q.s0 / 2 ) * Icard ) ] ;
    · grind
  have hw_ball : (ball (∅ : Cube Icard) w).card > k := by
    have hw_ball : (ball (∅ : Cube Icard) w).card ≥ Real.exp (H (w / Icard) * Icard - vSlack Icard) := by
      grind;
    have hw_ball : H (w / Icard) - H (q - ζ) ≥ L * (Q.s0 / 4) := by
      have := h_inv ( q - ζ ) ( w / Icard ) ?_ ?_ ?_ <;> try linarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ];
      · nlinarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ];
      · rw [ div_le_iff₀ ] <;> norm_num;
        · exact Nat.floor_le ( mul_nonneg ( by linarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ] ) ( Nat.cast_nonneg _ ) ) |> le_trans <| mul_le_mul_of_nonneg_right ( by linarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ] ) ( Nat.cast_nonneg _ );
        · linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ];
    have hw_ball : Real.exp (H (w / Icard) * Icard - vSlack Icard) > Real.exp (H (q - ζ) * Icard) := by
      exact Real.exp_lt_exp.mpr ( by nlinarith [ show ( Icard : ℝ ) ≥ 1 by norm_cast; linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ], show ( 0 : ℝ ) < L * ( Q.s0 / 4 ) by exact mul_pos hLpos ( div_pos ( show ( 0 : ℝ ) < Q.s0 by linarith [ hvalid.2.2.2.1 ] ) zero_lt_four ) ] );
    exact_mod_cast hk'.trans_lt hw_ball |> lt_of_lt_of_le <| ‹ ( ball ∅ w |> Finset.card : ℝ ) ≥ Real.exp ( H ( w / Icard ) * Icard - vSlack Icard ) ›.trans' <| by norm_num;
  have ht_lt_w : t < w := by
    exact lt_of_not_ge fun h => hw_ball.not_ge <| le_trans ( r3_ball_card_mono h ) ht'
  have ht_le_Icard_div_2 : t ≤ Icard / 2 := by
    linarith
  have ht_plus_1_le_Icard_div_2 : t + 1 ≤ Icard / 2 := by
    grind
  have h_radius_bound : (t : ℝ) / Icard ≤ q - ζ + (vSlack Icard) / (Icard * L) := by
    have h_radius_bound : H ((t : ℝ) / Icard) - H (q - ζ) ≤ (vSlack Icard) / Icard := by
      have h_radius_bound : (ball (∅ : Cube Icard) t).card ≥ Real.exp (H ((t : ℝ) / Icard) * Icard - vSlack Icard) := by
        have := hvol Icard t ht_le_Icard_div_2; aesop;
      have h_radius_bound : Real.exp (H ((t : ℝ) / Icard) * Icard - vSlack Icard) ≤ Real.exp (H (q - ζ) * Icard) := by
        exact h_radius_bound.trans ( mod_cast hk'.trans' <| mod_cast ht' );
      rw [ Real.exp_le_exp ] at h_radius_bound;
      rw [ le_div_iff₀ ] <;> linarith [ show ( Icard : ℝ ) > 0 by norm_cast; linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ];
    by_cases h_case : (t : ℝ) / Icard ≤ q - ζ;
    · exact le_add_of_le_of_nonneg h_case ( div_nonneg ( hvsub.1 _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) hLpos.le ) );
    · have := h_inv ( q - ζ ) ( t / Icard ) ?_ ?_ ?_ <;> try linarith [ hvalid.1, hvalid.2.1 ];
      · rw [ ← div_div ];
        rw [ add_div', le_div_iff₀ ] <;> linarith;
      · refine' le_trans ( div_le_div_of_nonneg_right ( Nat.cast_le.mpr ht_lt_w.le ) ( Nat.cast_nonneg _ ) ) _;
        rw [ div_le_iff₀ ] <;> norm_num;
        · exact le_trans ( Nat.floor_le ( by nlinarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ] ) ) ( mul_le_mul_of_nonneg_right ( by linarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1 ] ) ( Nat.cast_nonneg _ ) );
        · linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ]
  exact ⟨by
  have h_theta_le : (t + θ : ℝ) / Icard ≤ Q.qMax + (1 / 2 - Q.qMax) / 2 := by
    have h_theta_le : (vSlack Icard) / (Icard * L) ≤ (1 / 2 - Q.qMax) / 2 := by
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( Icard : ℝ ) > 0 by norm_cast; linarith [ Nat.le_max_left ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_right ( max N1 N2 ) ( ⌈4 / Q.s0⌉₊ + 1 ), Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ];
    ring_nf at *; linarith;
  rw [ div_le_iff₀ ] at h_theta_le <;> norm_num at *;
  · rw [ Nat.le_div_iff_mul_le ] <;> norm_num at *;
    exact_mod_cast ( by nlinarith [ show ( Q.qMax : ℝ ) ≤ 1 / 2 by linarith [ hvalid.2.2.1, hvalid.2.2.2.2.2.1 ] ] : ( t + θ : ℝ ) * 2 ≤ Icard );
  · grind, by
    exact ht_plus_1_le_Icard_div_2, by
    exact h_radius_bound⟩

/-
Safe-branch fiber growth bound: assembles the VPlus/BV volume ratio and the
robust entropy-growth inequality into the per-`m` exponent bound, given the
safety bounds, the radius bound and a dominating error term `err`.
-/
set_option maxHeartbeats 1000000 in
lemma r3_fiber_growth_safe_bound (vSlack : ℕ → ℝ) (hvsub : Sublinear vSlack)
    (hvol : ∀ (n t : ℕ), t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + vSlack n))
    (Q : QData) (hvalid : validQData Q)
    (pLow : ℝ) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2)
    (m : ℕ) (hm : 1 ≤ m) (q : ℝ) (hqmax : q ≤ Q.qMax)
    (Icard : ℕ) (hIlow : pLow * (m : ℝ) ≤ (Icard : ℝ))
    (hIhigh : (Icard : ℝ) ≤ (1 - pLow) * (m : ℝ))
    (ζ : ℝ) (hζpos : 0 < ζ) (hζle : ζ ≤ q / 2) (hζscale : ζ ≤ 2 * Q.s0 / pLow)
    (L : ℝ) (hLpos : 0 < L)
    (k : ℕ)
    (θ : ℕ) (hθdef : θ = min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ))))
    (t : ℕ)
    (hsafe1 : t + θ ≤ Icard / 2) (hsafe2 : t + 1 ≤ Icard / 2)
    (harad : (t : ℝ) / (Icard : ℝ) ≤ q - ζ + (vSlack Icard) / ((Icard : ℝ) * L))
    (hk_succ : (k : ℝ) ≤ ((ball (∅ : Cube Icard) (t + 1)).card : ℝ))
    (htV : ((ball (∅ : Cube Icard) (t + θ)).card : ℝ) ≤ (V Icard k θ : ℝ))
    (err : ℝ)
    (herr : 2 * ζ
        + (m : ℝ) * ((vSlack Icard) / ((Icard : ℝ) * L))
            * Real.log ((1 - q / 2) / (q / 2))
        + (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ)))
        + 2 * (vSlack Icard) ≤ err) :
    Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)
        + (pLow / 2) * ζ ^ 2 * (m : ℝ) - err) * (k : ℝ)
      ≤ (V Icard k θ : ℝ) := by
  refine le_trans ?_ htV;
  refine' le_trans ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr _ ) ( Nat.cast_nonneg _ ) ) _;
  exact H ( ( t + θ : ℝ ) / Icard ) * Icard - H ( ( t + 1 : ℝ ) / Icard ) * Icard - 2 * vSlack Icard;
  · have h_growth : (Icard : ℝ) * (H ((t + θ : ℝ) / Icard) - H ((t : ℝ) / Icard)) - (m : ℝ) * (H (q + (θ : ℝ) / m) - H q) ≥ 2 * (θ : ℝ) * ζ - (m : ℝ) * (vSlack Icard / ((Icard : ℝ) * L)) * Real.log ((1 - q / 2) / (q / 2)) := by
      have h_robust : q ≤ 1 / 2 ∧ 0 < ζ ∧ ζ ≤ q / 2 ∧ 0 < (Icard : ℝ) / m ∧ (Icard : ℝ) / m ≤ 1 ∧ 0 ≤ (θ : ℝ) / m ∧ (θ : ℝ) / m ≤ (Icard : ℝ) / m * ζ / 2 ∧ 0 ≤ (t : ℝ) / Icard ∧ (t : ℝ) / Icard ≤ 1 / 2 ∧ (t : ℝ) / Icard + (θ : ℝ) / m / ((Icard : ℝ) / m) ≤ 1 / 2 ∧ 0 ≤ vSlack Icard / ((Icard : ℝ) * L) ∧ (t : ℝ) / Icard ≤ q - ζ + vSlack Icard / ((Icard : ℝ) * L) := by
        refine' ⟨ _, _, _, _, _, _, _, _ ⟩ <;> try linarith [ hvalid.1, hvalid.2.1, hvalid.2.2.1 ];
        · exact div_pos ( lt_of_lt_of_le ( by positivity ) hIlow ) ( by positivity );
        · exact div_le_one_of_le₀ ( by nlinarith ) ( by positivity );
        · positivity;
        · have := r3_theta_floor_bounds Q pLow hlow m ζ hζpos hζscale Icard hIlow;
          convert this.2.1.trans _ using 1;
          · rw [ hθdef ];
          · gcongr;
            rw [ le_div_iff₀ ] <;> first | positivity | linarith;
        · refine' ⟨ by positivity, _, _, _, harad ⟩;
          · rw [ div_le_div_iff₀ ] <;> norm_cast;
            · lia;
            · grind;
          · field_simp;
            rw [ div_le_iff₀ ] <;> norm_cast;
            · linarith [ Nat.div_mul_le_self Icard 2 ];
            · grind;
          · exact div_nonneg ( hvsub.1 _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) hLpos.le );
      have := r3_entropy_growth_robust h_robust.1 h_robust.2.1 h_robust.2.2.1 ( show 0 < ( Icard : ℝ ) / m by exact h_robust.2.2.2.1 ) h_robust.2.2.2.2.1 h_robust.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.2.2.2.2.1 h_robust.2.2.2.2.2.2.2.2.2.2.2;
      field_simp at this ⊢;
      exact this;
    have h_theta_lower : (θ : ℝ) ≥ pLow * ζ * (m : ℝ) / 2 - 1 := by
      cases min_cases ⌊pLow * ζ * m / 2⌋₊ ⌈Q.s0 * m⌉₊ <;> simp +decide [ * ];
      · exact le_of_lt ( Nat.lt_floor_add_one _ );
      · rw [ le_div_iff₀ ] at hζscale <;> nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast, show ( Icard : ℝ ) ≥ pLow * m by exact_mod_cast hIlow, show ( Icard : ℝ ) ≤ ( 1 - pLow ) * m by exact_mod_cast hIhigh, Nat.le_ceil ( Q.s0 * m ), Nat.lt_of_ceil_lt ( by linarith : ⌈Q.s0 * m⌉₊ < ⌊pLow * ζ * m / 2⌋₊ ), Nat.floor_le ( show 0 ≤ pLow * ζ * m / 2 by positivity ) ];
    nlinarith [ mul_pos hζpos hζpos, mul_pos hζpos hlow, mul_pos hζpos ( show 0 < ( m : ℝ ) by positivity ), mul_pos hlow ( show 0 < ( m : ℝ ) by positivity ) ];
  · have hvol_bound : (k : ℝ) ≤ Real.exp (H ((t + 1 : ℝ) / Icard) * Icard + vSlack Icard) := by
      grind;
    refine' le_trans _ ( show ( ball ∅ ( t + θ ) |> Finset.card : ℝ ) ≥ Real.exp ( H ( ( t + θ : ℝ ) / Icard ) * Icard - vSlack Icard ) from _ );
    · convert mul_le_mul_of_nonneg_left hvol_bound ( Real.exp_nonneg _ ) using 1 ; rw [ ← Real.exp_add ] ; ring_nf;
    · grind

set_option maxHeartbeats 1000000 in
private lemma r3_fiber_growth_V_bound (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ c > 0, ∃ sV : ℕ → ℝ, Sublinear sV ∧
    ∀ (m : ℕ) (q : ℝ), Q.qMin ≤ q → q ≤ Q.qMax →
      ∀ Icard : ℕ, pLow * (m : ℝ) ≤ (Icard : ℝ) →
        (Icard : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * Q.s0 / pLow →
      let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
      ∀ k : ℕ, (k : ℝ) ≤ Real.exp (H (q - ζ) * (Icard : ℝ)) →
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m) * (k : ℝ) ≤
        (V Icard k θ : ℝ) := by
  refine (fun _ : InteriorVolumeCalculusStatement => ?_) hVC
  classical
  obtain ⟨L, hLpos, hchord⟩ := r3_entropy_compact_inverse_chord Q hvalid
  set vSlack := Classical.choose hBV with hvSlack_def
  have hvsub : Sublinear vSlack := (Classical.choose_spec hBV).1
  have hvnn : ∀ n, 0 ≤ vSlack n := (Classical.choose_spec hBV).1.1
  have hvol : ∀ (n t : ℕ), t ≤ n / 2 → Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧ ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + vSlack n) := (Classical.choose_spec hBV).2
  obtain ⟨N, hN⟩ := r3_fiber_growth_witness_safe vSlack hvsub hvol Q hvalid L hLpos hchord
  set Nm := Nat.ceil ((N : ℝ) / pLow) + 1 with hNm_def
  set Λ := Real.log ((1 - Q.qMin / 2) / (Q.qMin / 2)) with hΛ_def
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ_def]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith [hvalid.1])]
    nlinarith [hvalid.1, hvalid.2.1, hvalid.2.2.1]
  set B := (Nm : ℝ) * (Real.log 2 + 1) + 1 with hB_def
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hBnn : 0 ≤ B := by
    rw [hB_def]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by norm_num)
  set coefV := Λ / (pLow * L) + 2 with hcoefV_def
  have hcoefVnn : 0 ≤ coefV := by
    rw [hcoefV_def]
    exact add_nonneg (div_nonneg hΛnn (by positivity)) (by norm_num)
  set sV := fun mm : ℕ =>
      B + coefV * r3_runMax vSlack mm
        + r3_runMax (fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) mm with hsV_def
  refine ⟨pLow / 2, by positivity, sV, ?_, ?_⟩
  · refine reductions_sublinear_add (reductions_sublinear_add ?_ ?_) ?_
    · exact r3_sublinear_const B hBnn
    · exact r3_sublinear_const_mul coefV hcoefVnn (r3_runMax_sublinear hvsub)
    · exact r3_runMax_sublinear r3_nH_inv_sublinear
  · intro m q hqmin hqmax Icard hIlow hIhigh ζ hζpos hζle hζscale θ k hk
    have hqpos : 0 < q := lt_of_lt_of_le hvalid.1 hqmin
    have hqle_half : q ≤ 1 / 2 := le_of_lt (lt_of_le_of_lt hqmax hvalid.2.2.1)
    have hkn : k ≤ 2 ^ Icard := by
      have h2 : (k : ℝ) ≤ (2 : ℝ) ^ Icard := by
        calc (k : ℝ) ≤ Real.exp (H (q - ζ) * (Icard : ℝ)) := hk
          _ ≤ Real.exp (Real.log ((2 : ℝ) ^ Icard)) := by
              apply Real.exp_le_exp.mpr
              rw [Real.log_pow]
              have hb : H (q - ζ) ≤ Real.log 2 := Real.binEntropy_le_log_two
              nlinarith [hb, Nat.cast_nonneg (α := ℝ) Icard]
          _ = (2 : ℝ) ^ Icard := Real.exp_log (by positivity)
      exact_mod_cast h2
    by_cases hmge : Nm ≤ m
    · -- Safe branch: `m` large enough that the witness stays below the equator.
      have hmpos : 1 ≤ m := le_trans (by rw [hNm_def]; omega) hmge
      have hmpos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have hIpos : (0 : ℝ) < (Icard : ℝ) := lt_of_lt_of_le (mul_pos hlow hmpos_r) hIlow
      have hIle : (Icard : ℝ) ≤ (m : ℝ) := le_trans hIhigh (by nlinarith [hlow.le])
      have hIm : Icard ≤ m := by exact_mod_cast hIle
      have hIN : N ≤ Icard := by
        have hceil : (N : ℝ) / pLow ≤ (Nm : ℝ) := by
          rw [hNm_def]; push_cast; linarith [Nat.le_ceil ((N : ℝ) / pLow)]
        have h1 : (N : ℝ) ≤ pLow * (Nm : ℝ) := by
          have hh := (div_le_iff₀ hlow).mp hceil
          rw [mul_comm]; exact hh
        have h2 : pLow * (Nm : ℝ) ≤ pLow * (m : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hmge) hlow.le
        have hstep : (N : ℝ) ≤ (Icard : ℝ) := le_trans h1 (le_trans h2 hIlow)
        exact_mod_cast hstep
      obtain ⟨hθeq, hθm_le, hθm_lo, hθI, hθceil⟩ :=
        r3_theta_floor_bounds Q pLow hlow m ζ hζpos hζscale Icard hIlow
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        obtain ⟨t, ht_le, ht_card, ht_max, htV⟩ := hVPlus Icard k θ hk1 hkn
        obtain ⟨hsafe1, hsafe2, harad⟩ :=
          hN Icard hIN q ζ hqmin hqmax hζpos hζle θ hθI k hk1 hk t ht_le ht_card ht_max
        have ht_lt : t < Icard := by
          have := Nat.div_le_self Icard 2
          omega
        have hk_succ : (k : ℝ) ≤ ((ball (∅ : Cube Icard) (t + 1)).card : ℝ) := by
          exact_mod_cast (r3_vplus_witness_succ_card Icard k t ht_max ht_lt).le
        refine r3_fiber_growth_safe_bound vSlack hvsub hvol Q hvalid pLow hlow hhigh m hmpos q hqmax
          Icard hIlow hIhigh ζ hζpos hζle hζscale L hLpos k θ rfl t hsafe1 hsafe2 harad
          hk_succ htV (sV m) ?_
        -- discharge `herr`
        have hδnn : 0 ≤ vSlack Icard / ((Icard : ℝ) * L) :=
          div_nonneg (hvnn Icard) (by positivity)
        have hrunV : vSlack Icard ≤ r3_runMax vSlack m := r3_runMax_ge hIm
        have hLog_le : Real.log ((1 - q / 2) / (q / 2)) ≤ Λ := by
          rw [hΛ_def]
          apply Real.log_le_log (div_pos (by linarith [hqle_half]) (by linarith [hqpos]))
          rw [div_le_div_iff₀ (by linarith [hqpos]) (by nlinarith [hvalid.1])]
          nlinarith [hvalid.1, hqmin]
        have hLog_nn : 0 ≤ Real.log ((1 - q / 2) / (q / 2)) :=
          Real.log_nonneg (by
            rw [le_div_iff₀ (by linarith [hqpos] : (0 : ℝ) < q / 2)]; nlinarith [hqle_half])
        -- Bound1: the +1 vs t entropy gap
        have hshift : H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ))
            ≤ H (1 / (Icard : ℝ)) := by
          have hle1 : (t : ℝ) / (Icard : ℝ) + 1 / (Icard : ℝ) ≤ 1 := by
            rw [← add_div, div_le_one hIpos]
            have : t + 1 ≤ Icard := by
              have := Nat.div_le_self Icard 2; omega
            exact_mod_cast this
          have := r3_H_shift_le (a := (t : ℝ) / (Icard : ℝ)) (δ := 1 / (Icard : ℝ))
            (by positivity) (by positivity) hle1
          rwa [← add_div] at this
        have hBound1 : (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ)))
            ≤ r3_runMax (fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) m := by
          have hstep : (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ)))
              ≤ (Icard : ℝ) * H (1 / (Icard : ℝ)) :=
            mul_le_mul_of_nonneg_left hshift hIpos.le
          exact le_trans hstep (r3_runMax_ge (s := fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) hIm)
        -- Bound2: the slack term
        have hmIcard : (m : ℝ) / (Icard : ℝ) ≤ 1 / pLow := by
          rw [div_le_div_iff₀ hIpos hlow]
          nlinarith [hIlow]
        have hBound2 : (m : ℝ) * (vSlack Icard / ((Icard : ℝ) * L))
              * Real.log ((1 - q / 2) / (q / 2)) + 2 * vSlack Icard
            ≤ coefV * r3_runMax vSlack m := by
          have hA : (m : ℝ) * (vSlack Icard / ((Icard : ℝ) * L))
                * Real.log ((1 - q / 2) / (q / 2))
              ≤ (Λ / (pLow * L)) * vSlack Icard := by
            have hlhs : (m : ℝ) * (vSlack Icard / ((Icard : ℝ) * L))
                  * Real.log ((1 - q / 2) / (q / 2))
                = ((m : ℝ) / (Icard : ℝ)) * (vSlack Icard / L)
                    * Real.log ((1 - q / 2) / (q / 2)) := by
              ring
            rw [hlhs]
            have hstep1 : ((m : ℝ) / (Icard : ℝ)) * (vSlack Icard / L)
                  * Real.log ((1 - q / 2) / (q / 2))
                ≤ (1 / pLow) * (vSlack Icard / L) * Λ := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_right hmIcard (div_nonneg (hvnn Icard) hLpos.le)
              · exact hLog_le
              · exact hLog_nn
              · exact mul_nonneg (div_nonneg zero_le_one hlow.le) (div_nonneg (hvnn Icard) hLpos.le)
            calc ((m : ℝ) / (Icard : ℝ)) * (vSlack Icard / L)
                    * Real.log ((1 - q / 2) / (q / 2))
                ≤ (1 / pLow) * (vSlack Icard / L) * Λ := hstep1
              _ = (Λ / (pLow * L)) * vSlack Icard := by ring
          have hB2 : (Λ / (pLow * L)) * vSlack Icard ≤ (Λ / (pLow * L)) * r3_runMax vSlack m :=
            mul_le_mul_of_nonneg_left hrunV (div_nonneg hΛnn (mul_pos hlow hLpos).le)
          have h2v : 2 * vSlack Icard ≤ 2 * r3_runMax vSlack m := by linarith
          have : coefV * r3_runMax vSlack m
              = (Λ / (pLow * L)) * r3_runMax vSlack m + 2 * r3_runMax vSlack m := by
            rw [hcoefV_def]; ring
          rw [this]; linarith
        -- Bound3: the constant 2ζ
        have hBound3 : 2 * ζ ≤ B := by
          have h1 : 2 * ζ ≤ 1 := by nlinarith [hvalid.2.2.1, hqmax, hζle]
          have hB1 : (1 : ℝ) ≤ B := by
            rw [hB_def]
            have : 0 ≤ (Nm : ℝ) * (Real.log 2 + 1) :=
              mul_nonneg (Nat.cast_nonneg _) (by linarith)
            linarith
          linarith
        have hrunNH_nn : 0 ≤ r3_runMax (fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) m :=
          le_trans (r3_nH_inv_sublinear.1 0)
            (r3_runMax_ge (s := fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) (Nat.zero_le m))
        simp only [hsV_def]
        linarith
    · -- Unsafe branch: `m < Nm`, absorb everything into the constant part of `sV`.
      have hm_le : (m : ℝ) ≤ (Nm : ℝ) := by
        have : m ≤ Nm := le_of_lt (lt_of_not_ge hmge)
        exact_mod_cast this
      have hrun_nn : 0 ≤ r3_runMax vSlack m := le_trans (hvnn 0) (r3_runMax_ge (Nat.zero_le m))
      have hrunNH_nn : 0 ≤ r3_runMax (fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) m :=
        le_trans (r3_nH_inv_sublinear.1 0)
          (r3_runMax_ge (s := fun nn => (nn : ℝ) * H (1 / (nn : ℝ))) (Nat.zero_le m))
      have hsV_ge : B ≤ sV m := by
        simp only [hsV_def]
        have := mul_nonneg hcoefVnn hrun_nn
        linarith
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hHq_nn : 0 ≤ H q := Real.binEntropy_nonneg (le_of_lt hqpos) (by linarith [hqle_half])
      have hexp_nonpos : H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)
          + pLow / 2 * ζ ^ 2 * (m : ℝ) - sV m ≤ 0 := by
        have hHub : H (q + (θ : ℝ) / (m : ℝ)) ≤ Real.log 2 := Real.binEntropy_le_log_two
        have hζsmall : pLow / 2 * ζ ^ 2 ≤ 1 := by nlinarith [hvalid.2.2.1, hqmax, hζpos, hζle]
        have hpart : H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)
            + pLow / 2 * ζ ^ 2 * (m : ℝ) ≤ (m : ℝ) * (Real.log 2 + 1) := by
          nlinarith [mul_le_mul_of_nonneg_right hHub hmnn,
            mul_nonneg hHq_nn hmnn, mul_le_mul_of_nonneg_right hζsmall hmnn]
        have hmNm : (m : ℝ) * (Real.log 2 + 1) ≤ (Nm : ℝ) * (Real.log 2 + 1) :=
          mul_le_mul_of_nonneg_right hm_le (by linarith)
        have : (Nm : ℝ) * (Real.log 2 + 1) ≤ B := by rw [hB_def]; linarith
        linarith
      have hexp_le_one : Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)
          + pLow / 2 * ζ ^ 2 * (m : ℝ) - sV m) ≤ 1 :=
        Real.exp_le_one_iff.mpr hexp_nonpos
      calc Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)
              + pLow / 2 * ζ ^ 2 * (m : ℝ) - sV m) * (k : ℝ)
          ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hexp_le_one (Nat.cast_nonneg _)
        _ = (k : ℝ) := one_mul _
        _ ≤ (V Icard k θ : ℝ) := by exact_mod_cast r3_k_le_V Icard k θ hkn

private lemma r3_sparse_fiber_growth_ratio (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ c > 0, ∃ sGrow : ℕ → ℝ, Sublinear sGrow ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * Q.s0 / pLow →
      let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
      ∀ k : ℕ, (k : ℝ) ≤ Real.exp (H (q - ζ) * (I.card : ℝ)) →
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) +
          c * ζ^2 * (m : ℝ) - sGrow m) * (k : ℝ) / (A.card : ℝ) ≤
        (V I.card k θ : ℝ) := by
  obtain ⟨c, hc, sV, hsV, hVbound⟩ := r3_fiber_growth_V_bound hBV hVPlus hVC Q pLow hvalid hlow hhigh
  refine ⟨c, hc, fun m => sV m + Q.sigma m,
    reductions_sublinear_add hsV hvalid.2.2.2.2.2.2.1, ?_⟩
  intro m A q hA hfat hpinned I hIlow hIhigh ζ hζpos hζle hζscale θ k hk
  have h_Vbound :=
    hVbound m q hfat.2.2.1 hfat.2.2.2.1 I.card hIlow hIhigh ζ hζpos hζle hζscale k hk
  have h_log_le : H q * (m : ℝ) - Q.sigma m ≤ Real.log (A.card : ℝ) := by
    have h_fat := hfat.2.2.2.2
    rw [abs_le] at h_fat
    linarith
  have h_A_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have h_A_card : Real.exp (H q * (m : ℝ) - Q.sigma m) ≤ (A.card : ℝ) :=
    (Real.le_log_iff_exp_le h_A_card_pos).mp h_log_le
  have h_div_le : Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) + c * ζ^2 * (m : ℝ) - (sV m + Q.sigma m)) * (k : ℝ) / (A.card : ℝ) ≤
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m) * (k : ℝ) := by
    rw [div_le_iff₀ h_A_card_pos]
    calc
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) + c * ζ^2 * (m : ℝ) - (sV m + Q.sigma m)) * (k : ℝ)
          = Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m + (H q * (m : ℝ) - Q.sigma m)) * (k : ℝ) := by
            congr 2; ring
        _ = Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m) * Real.exp (H q * (m : ℝ) - Q.sigma m) * (k : ℝ) := by
            rw [Real.exp_add]
        _ = Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m) * (k : ℝ) * Real.exp (H q * (m : ℝ) - Q.sigma m) := by
            ring
        _ ≤ Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + c * ζ^2 * (m : ℝ) - sV m) * (k : ℝ) * (A.card : ℝ) := by
            refine mul_le_mul_of_nonneg_left h_A_card (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg k))
  exact le_trans h_div_le h_Vbound

/-- Local Harper growth lower bound for the sparse fibers.

This is the remaining geometric leaf. It no longer contains the pinned-budget
or Markov algebra: it says that the total grown size of entropy-sparse fibers
dominates their original mass by an exponential factor. The radius is capped
at the available pinned scale. -/
private lemma r3_sparse_fibers_growth_lower (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ c > 0, ∃ sGrow : ℕ → ℝ, Sublinear sGrow ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * Q.s0 / pLow →
      let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) +
          c * ζ^2 * (m : ℝ) - sGrow m) *
        (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
            (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
              Real.exp (H (q - ζ) * (I.card : ℝ))),
          pOn A (proj Iᶜ) z) ≤
        (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
            (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
              Real.exp (H (q - ζ) * (I.card : ℝ))),
          (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter
            (fun y => proj Iᶜ y = z)).card : ℝ)) := by
  classical
  obtain ⟨c, hc, sGrow, hsGrow, hratio⟩ := r3_sparse_fiber_growth_ratio hBV hVPlus hVC Q pLow hvalid hlow hhigh
  refine ⟨c, hc, sGrow, hsGrow, ?_⟩
  intro m A q hA hfat hpinned I hI_low hI_high ζ hζ_pos hζ_le hζscale
  let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
  let P : Cube m → Prop := fun z => (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤ Real.exp (H (q - ζ) * (I.card : ℝ))
  let filterSet := (A.image (proj Iᶜ)).filter P
  let LHS_factor := Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) + c * ζ^2 * (m : ℝ) - sGrow m)
  have h_bound : ∀ z ∈ filterSet,
      LHS_factor * pOn A (proj Iᶜ) z ≤
      (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter (fun y => proj Iᶜ y = z)).card : ℝ) := by
    intro z hz
    have hP : P z := (Finset.mem_filter.mp hz).2
    have hk_le : ((A.filter fun x => proj Iᶜ x = z).card : ℝ) ≤ Real.exp (H (q - ζ) * (I.card : ℝ)) := hP
    have h_ratio_bound :=
      hratio m A q hA hfat hpinned I hI_low hI_high ζ hζ_pos hζ_le hζscale
        ((A.filter fun x => proj Iᶜ x = z).card) hk_le
    have h_harper := r3_fiber_harper A I z θ
    have h_harper_real : (V I.card ((A.filter fun x => proj Iᶜ x = z).card) θ : ℝ) ≤ (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter (fun y => proj Iᶜ y = z)).card : ℝ) := by
      exact_mod_cast h_harper
    have h_eq : LHS_factor * pOn A (proj Iᶜ) z = LHS_factor * ((A.filter fun x => proj Iᶜ x = z).card : ℝ) / (A.card : ℝ) := by
      unfold pOn
      rw [mul_div_assoc']
      congr 2
      congr 1
      congr 1
      ext x
      simp
    rw [h_eq]
    exact le_trans h_ratio_bound h_harper_real
  have h_sum : (∑ z ∈ filterSet, LHS_factor * pOn A (proj Iᶜ) z) ≤
      (∑ z ∈ filterSet, (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter (fun y => proj Iᶜ y = z)).card : ℝ)) := by
    apply Finset.sum_le_sum h_bound
  rw [← Finset.mul_sum] at h_sum
  exact h_sum

lemma r3_sparse_neighborhood_budget {m : ℕ} (Q : QData)
    (A : Finset (Cube m)) (q : ℝ) (hpinned : pinned Q m A q)
    (I : Finset (Fin m)) (θ : ℕ)
    (hθ : θ ≤ Nat.ceil (Q.s0 * (m : ℝ))) (P : Cube m → Prop)
    [DecidablePred P] :
    (∑ z ∈ (A.image (proj Iᶜ)).filter P,
      (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter
        (fun y => proj Iᶜ y = z)).card : ℝ)) ≤
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) + Q.sigma m) := by
  classical
  let slice : Cube m → Finset (Cube m) := fun z =>
    (neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter
      (fun y => proj Iᶜ y = z)
  have hsubset_sum :
      (∑ z ∈ (A.image (proj Iᶜ)).filter P, ((slice z).card : ℝ)) ≤
        ∑ z ∈ A.image (proj Iᶜ), ((slice z).card : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro z _hz _hznot
    positivity
  have htransfer :
      (∑ z ∈ A.image (proj Iᶜ), ((slice z).card : ℝ)) ≤
        ((neighborhood θ A).card : ℝ) := by
    simpa [slice] using r3_fiber_transfer A I θ
  exact le_trans hsubset_sum (le_trans htransfer (hpinned θ hθ))

/-- Sparse fibers have exponentially small total mass. -/
private lemma r3_sparse_fibers_mass (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ c > 0, ∃ sMass : ℕ → ℝ, Sublinear sMass ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * Q.s0 / pLow →
      (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
          (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
            Real.exp (H (q - ζ) * (I.card : ℝ))),
        pOn A (proj Iᶜ) z) ≤ Real.exp (- c * ζ^2 * (m : ℝ) + sMass m) := by
  classical
  obtain ⟨c, hc, sGrow, hsGrow, hgrowth⟩ :=
    r3_sparse_fibers_growth_lower hBV hVPlus hVC Q pLow hvalid hlow hhigh
  refine ⟨c, hc, fun m => sGrow m + Q.sigma m,
    reductions_sublinear_add hsGrow hvalid.2.2.2.2.2.2.1, ?_⟩
  intro m A q hA hfat hpinned I hIlow hIhigh ζ hζpos hζle hζscale
  let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (Q.s0 * (m : ℝ)))
  let P : Cube m → Prop := fun z =>
    (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
      Real.exp (H (q - ζ) * (I.card : ℝ))
  let mass : ℝ := ∑ z ∈ (A.image (proj Iᶜ)).filter P, pOn A (proj Iᶜ) z
  let grown : ℝ := ∑ z ∈ (A.image (proj Iᶜ)).filter P,
    (((neighborhood θ (A.filter fun x => proj Iᶜ x = z)).filter
      (fun y => proj Iᶜ y = z)).card : ℝ)
  let base : ℝ := H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ)
  have hθ : θ ≤ Nat.ceil (Q.s0 * (m : ℝ)) := by
    dsimp [θ]
    exact min_le_right _ _
  have hgrowth' :
      Real.exp (base + c * ζ^2 * (m : ℝ) - sGrow m) * mass ≤ grown := by
    simpa [θ, P, mass, grown, base] using
      hgrowth m A q hA hfat hpinned I hIlow hIhigh ζ hζpos hζle hζscale
  have hbudget : grown ≤ Real.exp (base + Q.sigma m) := by
    simpa [θ, P, grown, base] using
      r3_sparse_neighborhood_budget Q A q hpinned I θ hθ P
  have hfactor_pos : 0 < Real.exp (base + c * ζ^2 * (m : ℝ) - sGrow m) :=
    Real.exp_pos _
  have hmass_le_div :
      mass ≤ Real.exp (base + Q.sigma m) /
          Real.exp (base + c * ζ^2 * (m : ℝ) - sGrow m) := by
    rw [le_div_iff₀ hfactor_pos]
    rw [mul_comm]
    exact le_trans hgrowth' hbudget
  have hdiv :
      Real.exp (base + Q.sigma m) /
          Real.exp (base + c * ζ^2 * (m : ℝ) - sGrow m) =
        Real.exp (-c * ζ^2 * (m : ℝ) + (sGrow m + Q.sigma m)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  simpa [P, mass, hdiv] using hmass_le_div

/-- One fixed-threshold algebra step: if fibers below
`exp(H(q - ζ)|I|)` have total mass at most `μ`, then the expected log fiber
size is at least the dense threshold times the dense mass. -/
lemma r3_expected_log_from_sparse_mass_once {m : ℕ}
    (A : Finset (Cube m)) (hA : A.Nonempty) (I : Finset (Fin m))
    (q ζ μ : ℝ) (hT0 : 0 ≤ H (q - ζ) * (I.card : ℝ))
    (hSparse :
      (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
        (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
          Real.exp (H (q - ζ) * (I.card : ℝ))),
        pOn A (proj Iᶜ) z) ≤ μ) :
    H (q - ζ) * (I.card : ℝ) * (1 - μ) ≤
      ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
        Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  classical
  let img : Finset (Cube m) := A.image (proj Iᶜ)
  let P : Cube m → Prop := fun z =>
    (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
      Real.exp (H (q - ζ) * (I.card : ℝ))
  let T : ℝ := H (q - ζ) * (I.card : ℝ)
  have hsum_all : (∑ z ∈ img, pOn A (proj Iᶜ) z) = 1 := by
    let imgC := @Finset.image (Cube m) (Cube m)
      (fun a b => Classical.propDecidable (a = b)) (proj Iᶜ) A
    have himg : imgC = img := by
      ext z
      simp [imgC, img]
    rw [← himg]
    exact sum_pOn_image_eq_one A hA (proj Iᶜ)
  have hsplit_p :
      (∑ z ∈ img.filter P, pOn A (proj Iᶜ) z) +
        (∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z) = 1 := by
    simpa [img, P] using
      (Finset.sum_filter_add_sum_filter_not img P (fun z => pOn A (proj Iᶜ) z)).trans
        hsum_all
  have hsparse_nonneg :
      0 ≤ ∑ z ∈ img.filter P,
        pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
    refine Finset.sum_nonneg (fun z hz => ?_)
    have hz_img : z ∈ img := (Finset.mem_filter.mp hz).1
    have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
      rcases Finset.mem_image.mp (by simpa [img] using hz_img) with ⟨x, hx, rfl⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    have hcard1 : (1 : ℝ) ≤ ((A.filter fun x => proj Iᶜ x = z).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hfib_ne
    exact mul_nonneg (pOn_nonneg A (proj Iᶜ) z) (Real.log_nonneg hcard1)
  have hdense_lower :
      T * (∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z) ≤
        ∑ z ∈ img.filter (fun z => ¬ P z),
          pOn A (proj Iᶜ) z *
            Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
    calc
      T * (∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z)
          = ∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z * T := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ∑ z ∈ img.filter (fun z => ¬ P z),
          pOn A (proj Iᶜ) z *
            Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
            refine Finset.sum_le_sum (fun z hz => ?_)
            have hz_img : z ∈ img := (Finset.mem_filter.mp hz).1
            have hnP : ¬ P z := (Finset.mem_filter.mp hz).2
            have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
              rcases Finset.mem_image.mp (by simpa [img] using hz_img) with ⟨x, hx, rfl⟩
              exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
            have hcard_pos : 0 < ((A.filter fun x => proj Iᶜ x = z).card : ℝ) := by
              exact_mod_cast Finset.card_pos.mpr hfib_ne
            have hcard_lt : Real.exp T < ((A.filter fun x => proj Iᶜ x = z).card : ℝ) := by
              exact not_le.mp (by simpa [P, T] using hnP)
            have hlog :
                T ≤ Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
              exact (Real.le_log_iff_exp_le hcard_pos).mpr hcard_lt.le
            exact mul_le_mul_of_nonneg_left hlog (pOn_nonneg A (proj Iᶜ) z)
  have hsum_dense_ge :
      1 - μ ≤ ∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z := by
    have hSparse' : (∑ z ∈ img.filter P, pOn A (proj Iᶜ) z) ≤ μ := by
      simpa [img, P] using hSparse
    linarith
  have htarget_dense : T * (1 - μ) ≤
      T * (∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z) := by
    exact mul_le_mul_of_nonneg_left hsum_dense_ge hT0
  have hsplit_E :
      (∑ z ∈ img, pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ))) =
        (∑ z ∈ img.filter P, pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ))) +
        (∑ z ∈ img.filter (fun z => ¬ P z), pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ))) := by
    simpa [img, P] using
      (Finset.sum_filter_add_sum_filter_not img P
        (fun z => pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)))).symm
  have hgoal_img : T * (1 - μ) ≤
      ∑ z ∈ img, pOn A (proj Iᶜ) z *
        Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
    rw [hsplit_E]
    exact le_trans htarget_dense (le_trans hdense_lower (by linarith [hsparse_nonneg]))
  simpa [img, T] using hgoal_img

/-- Diagonal threshold sequence `ζ(m) → 0` used to trade the sparse-mass
exponential decay against the sublinear `sMass` envelope. -/
noncomputable def r3ZetaSeq (c : ℝ) (sMass : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (2 * (sMass m + Real.sqrt (m : ℝ)) / (c * (m : ℝ)))

/-- The square of the diagonal threshold, cleared of the `sqrt`, for `m ≥ 1`. -/
private lemma r3ZetaSeq_sq_eq (c : ℝ) (hc : 0 < c) (sMass : ℕ → ℝ)
    (hsMass : Sublinear sMass) {m : ℕ} (hm : 1 ≤ m) :
    c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) = 2 * (sMass m + Real.sqrt (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnum_nonneg : 0 ≤ 2 * (sMass m + Real.sqrt (m : ℝ)) :=
    mul_nonneg (by norm_num) (add_nonneg (hsMass.1 m) (Real.sqrt_nonneg _))
  have hrad_nonneg : 0 ≤ 2 * (sMass m + Real.sqrt (m : ℝ)) / (c * (m : ℝ)) :=
    div_nonneg hnum_nonneg (mul_pos hc hmpos).le
  unfold r3ZetaSeq
  rw [Real.sq_sqrt hrad_nonneg]
  field_simp

/-
Core asymptotic estimate: the diagonal threshold tends to `0`.
-/
private lemma r3ZetaSeq_eventually_small (c : ℝ) (hc : 0 < c) (sMass : ℕ → ℝ)
    (hsMass : Sublinear sMass) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → r3ZetaSeq c sMass m ≤ ε := by
  intro ε hε;
  -- By definition of $r3ZetaSeq$, we have $r3ZetaSeq c sMass m = \sqrt{2 * (sMass m + \sqrt{m}) / (c * m)}$.
  unfold r3ZetaSeq;
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ m ≥ N₁, sMass m ≤ (ε^2 * c / 4) * m := by
    exact hsMass.2 ( ε ^ 2 * c / 4 ) ( by positivity );
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ m ≥ N₂, Real.sqrt m ≤ (ε^2 * c / 4) * m := by
    have h_sqrt_le : ∃ N₂ : ℕ, ∀ m ≥ N₂, Real.sqrt m ≤ (ε^2 * c / 4) * m := by
      have h_sqrt_le_aux : Filter.Tendsto (fun m : ℕ => Real.sqrt m / (m : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ Real.sqrt_div_self ] using tendsto_inv_atTop_nhds_zero_nat.sqrt
      exact Filter.eventually_atTop.mp ( h_sqrt_le_aux.eventually ( gt_mem_nhds <| show 0 < ε ^ 2 * c / 4 by positivity ) ) |> fun ⟨ N₂, hN₂ ⟩ ↦ ⟨ N₂ + 1, fun m hm ↦ by have := hN₂ m ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩;
    exact h_sqrt_le;
  refine' ⟨ N₁ + N₂ + 1, fun m hm => Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩ ⟩;
  rw [ div_le_iff₀ ] <;> nlinarith [ hN₁ m ( by linarith ), hN₂ m ( by linarith ), show ( m : ℝ ) ≥ 1 by norm_cast; linarith, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ]

/-
Core asymptotic estimate: the residual mass envelope is `o(m)`.
-/
private lemma r3_residual_eventually_small (c : ℝ) (hc : 0 < c) (sMass : ℕ → ℝ)
    (hsMass : Sublinear sMass) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Real.log 2 * ((m : ℝ) *
        Real.exp (-c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) + sMass m)) ≤ ε * (m : ℝ) := by
  intro ε hε;
  -- We'll use that exponential functions grow faster than polynomial functions to find such an $N$.
  have h_exp_growth : ∃ N : ℕ, ∀ m ≥ N, Real.exp (-2 * Real.sqrt m) ≤ ε / Real.log 2 := by
    have h_exp_growth : Filter.Tendsto (fun m : ℕ => Real.exp (-2 * Real.sqrt m)) Filter.atTop (nhds 0) := by
      norm_num [ Real.sqrt_eq_rpow ];
      exact Filter.Tendsto.const_mul_atTop ( by norm_num ) ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    simpa using h_exp_growth.eventually ( ge_mem_nhds <| by positivity );
  obtain ⟨ N, hN ⟩ := h_exp_growth; use N + 1; intro m hm; specialize hN m ( by linarith ) ; rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ] at hN;
  have h_exp_growth : Real.exp (-c * (r3ZetaSeq c sMass m)^2 * m + sMass m) ≤ Real.exp (-2 * Real.sqrt m) := by
    have h_exp_growth : -c * (r3ZetaSeq c sMass m)^2 * m + sMass m ≤ -2 * Real.sqrt m := by
      have := r3ZetaSeq_sq_eq c hc sMass hsMass ( by linarith : 1 ≤ m ) ; nlinarith [ hsMass.1 m, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] ;
    exact Real.exp_le_exp.mpr h_exp_growth;
  nlinarith [ show ( m : ℝ ) ≥ N + 1 by norm_cast, Real.log_pos one_lt_two, mul_le_mul_of_nonneg_left h_exp_growth <| show ( 0 : ℝ ) ≤ m by positivity ]

/-- The diagonal sequence has the required asymptotics: `ζ(m)·m` is sublinear,
the residual mass envelope `log 2 · m · exp(-c ζ² m + sMass m)` is sublinear,
and eventually `0 < ζ(m) ≤ b`. -/
private lemma r3_diagonal_seq (c : ℝ) (hc : 0 < c) (sMass : ℕ → ℝ)
    (hsMass : Sublinear sMass) (b : ℝ) (hb : 0 < b) :
    Sublinear (fun m => r3ZetaSeq c sMass m * (m : ℝ)) ∧
    Sublinear (fun m => Real.log 2 * ((m : ℝ) *
      Real.exp (-c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) + sMass m))) ∧
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      0 < r3ZetaSeq c sMass m ∧ r3ZetaSeq c sMass m ≤ b := by
  refine ⟨?_, ?_, ?_⟩
  · -- `ζ(m) · m` is sublinear.
    refine ⟨fun m => mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _), fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := r3ZetaSeq_eventually_small c hc sMass hsMass ε hε
    refine ⟨N, fun m hm => ?_⟩
    exact mul_le_mul_of_nonneg_right (hN m hm) (Nat.cast_nonneg _)
  · -- The residual mass envelope is sublinear.
    refine ⟨fun m => mul_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le), fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := r3_residual_eventually_small c hc sMass hsMass ε hε
    exact ⟨N, fun m hm => hN m hm⟩
  · -- Eventually `0 < ζ(m) ≤ b`.
    obtain ⟨Nb, hNb⟩ := r3ZetaSeq_eventually_small c hc sMass hsMass b hb
    refine ⟨max 1 Nb, fun m hm => ?_⟩
    have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
    have hmNb : Nb ≤ m := le_trans (le_max_right _ _) hm
    refine ⟨?_, hNb m hmNb⟩
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    unfold r3ZetaSeq
    apply Real.sqrt_pos.mpr
    apply div_pos
    · exact mul_pos (by norm_num)
        (by nlinarith [hsMass.1 m, Real.sqrt_pos.mpr hmpos])
    · exact mul_pos hc hmpos

/-- A nonnegative function that is eventually zero is sublinear. -/
private lemma r3_sublinear_eventually_zero {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (N : ℕ) (hN : ∀ n, N ≤ n → f n = 0) : Sublinear f := by
  refine ⟨hf0, fun ε hε => ?_⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn]
  positivity

lemma r3_binEntropy_chord_upper {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) :
    H b - H a ≤ (b - a) * Real.log ((1 - a) / a) := by
  by_cases h : a = b <;> simp_all +decide
  obtain ⟨c, hc⟩ :
      ∃ c ∈ Set.Ioo a b,
        deriv Real.binEntropy c = (Real.binEntropy b - Real.binEntropy a) / (b - a) := by
    apply_rules [exists_deriv_eq_slope]
    · exact lt_of_le_of_ne hab h
    · refine' ContinuousOn.add _ _ <;> norm_num at *
      · exact ContinuousOn.neg Real.continuous_mul_log.continuousOn
      · exact ContinuousOn.neg
          (ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
            (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
              fun x hx => by linarith [hx.1, hx.2]))
    · refine' fun x hx => DifferentiableAt.differentiableWithinAt _
      exact Real.hasDerivAt_binEntropy (by linarith [hx.1]) (by linarith [hx.2])
        |>.differentiableAt
  have h_deriv : deriv Real.binEntropy c ≤ Real.log ((1 - a) / a) := by
    rw [Real.deriv_binEntropy]
    rw [Real.log_div] <;> try linarith [hc.1.1, hc.1.2]
    exact sub_le_sub
      (Real.log_le_log (by linarith [hc.1.1, hc.1.2]) (by linarith [hc.1.1, hc.1.2]))
      (Real.log_le_log (by linarith [hc.1.1, hc.1.2]) (by linarith [hc.1.1, hc.1.2]))
  rw [hc.2, div_le_iff₀] at h_deriv <;> linarith! [hc.1.1, hc.1.2]

/-- Compact entropy loss for the repaired density-gap threshold.

For `q` in the fixed compact Q-range and `0 <= ζ <= q/2`, replacing the
old entropy threshold `H q - ζ` by `H (q - ζ)` costs at most a constant
multiple of `ζ`.  This is the only new analytic leaf introduced by the
`H(q-ζ)` repair. -/
lemma r3_entropy_gap_lipschitz (Q : QData) (hvalid : validQData Q) :
    ∃ L ≥ 0, ∀ q ζ : ℝ, Q.qMin ≤ q → q ≤ Q.qMax →
      0 ≤ ζ → ζ ≤ q / 2 → H q - H (q - ζ) ≤ L * ζ := by
  use Real.log ((1 - Q.qMin / 2) / (Q.qMin / 2))
  have hqmin_pos : 0 < Q.qMin := hvalid.1
  have ha_pos : 0 < Q.qMin / 2 := by positivity
  have hL_ge_0 : 0 ≤ Real.log ((1 - Q.qMin / 2) / (Q.qMin / 2)) := by
    apply Real.log_nonneg
    rw [one_le_div ha_pos]
    linarith [hvalid.2.1, hvalid.2.2.1]
  refine ⟨hL_ge_0, ?_⟩
  intro q ζ hq_min hq_max hζ_nonneg hζ_le
  by_cases hζ_zero : ζ = 0
  · simp [hζ_zero]
  have hζ_pos : 0 < ζ := lt_of_le_of_ne hζ_nonneg (Ne.symm hζ_zero)
  have hq_pos : 0 < q := by linarith
  have ha_le_b : q - ζ ≤ q := by linarith
  have hb_le_half : q ≤ 1 / 2 := by linarith [hvalid.2.2.1]
  have ha_pos' : 0 < q - ζ := by linarith
  have h_chord := r3_binEntropy_chord_upper ha_pos' ha_le_b hb_le_half
  have h_diff : q - (q - ζ) = ζ := by ring
  rw [h_diff] at h_chord
  apply le_trans h_chord
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right
  · have h1 : (1 - (q - ζ)) / (q - ζ) ≤ (1 - Q.qMin / 2) / (Q.qMin / 2) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    apply Real.log_le_log
    · exact div_pos (by linarith) (by linarith)
    · exact h1
  · exact hζ_nonneg

/-- The conditional expected log fiber size given the mass bound. -/
private lemma r3_expected_log_from_mass (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (_hhigh : pLow ≤ 1 / 2) :
    (∃ c > 0, ∃ sMass : ℕ → ℝ, Sublinear sMass ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
          (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * Q.s0 / pLow →
        (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
            (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
              Real.exp (H (q - ζ) * (I.card : ℝ))),
          pOn A (proj Iᶜ) z) ≤ Real.exp (- c * ζ^2 * (m : ℝ) + sMass m)) →
    ∃ sSp : ℕ → ℝ, Sublinear sSp ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      H q * (I.card : ℝ) - sSp m ≤
        ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  rintro ⟨c, hc, sMass, hsMass, hmass⟩
  obtain ⟨L, hL0, hLgap⟩ := r3_entropy_gap_lipschitz Q hvalid
  -- Constant thresholds coming from the fixed `Q`-data.
  have hqMin_pos : 0 < Q.qMin := hvalid.1
  have hqMin_lt_half : Q.qMin < 1 / 2 := lt_of_le_of_lt hvalid.2.1 hvalid.2.2.1
  have hHqMin_pos : 0 < H Q.qMin := by
    unfold H; exact Real.binEntropy_pos hqMin_pos (by linarith)
  set b : ℝ := min (min (Q.qMin / 2) (H Q.qMin)) (2 * Q.s0 / pLow) with hb_def
  have hscale_pos : 0 < 2 * Q.s0 / pLow :=
    div_pos (mul_pos (by norm_num) hvalid.2.2.2.1) hlow
  have hb_pos : 0 < b := lt_min (lt_min (by linarith) hHqMin_pos) hscale_pos
  obtain ⟨hζm_sub, hexp_sub, N, hζvalid⟩ := r3_diagonal_seq c hc sMass hsMass b hb_pos
  refine ⟨fun m => L * (r3ZetaSeq c sMass m * (m : ℝ))
      + Real.log 2 * ((m : ℝ) *
          Real.exp (-c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) + sMass m))
      + (if m < N then Real.log 2 * (m : ℝ) else 0), ?_, ?_⟩
  · -- The envelope is a sum of three sublinear pieces.
    have hLζ_sub : Sublinear (fun m => L * (r3ZetaSeq c sMass m * (m : ℝ))) :=
      r3_sublinear_const_mul L hL0 hζm_sub
    refine reductions_sublinear_add (reductions_sublinear_add hLζ_sub hexp_sub) ?_
    refine r3_sublinear_eventually_zero ?_ N ?_
    · intro n; dsimp only; split <;> positivity
    · intro n hn; simp [Nat.not_lt.mpr hn]
  · intro m A q hA hfat hpinned I hIlow hIhigh
    simp only []
    -- Range facts for `q` and `I`.
    have hq_ge : Q.qMin ≤ q := hfat.2.2.1
    have hq_le : q ≤ Q.qMax := hfat.2.2.2.1
    have hq_lt_half : q < 1 / 2 := lt_of_le_of_lt hq_le hvalid.2.2.1
    have hq_nonneg : 0 ≤ q := le_of_lt (lt_of_lt_of_le hqMin_pos hq_ge)
    have hHq_nonneg : 0 ≤ H q := by
      unfold H; exact Real.binEntropy_nonneg hq_nonneg (by linarith)
    have hHq_le : H q ≤ Real.log 2 := by unfold H; exact Real.binEntropy_le_log_two
    have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hIcard_le_m : (I.card : ℝ) ≤ (m : ℝ) := by
      have : I.card ≤ m := by simpa [Fintype.card_fin] using (Finset.card_le_univ I)
      exact_mod_cast this
    have hIcard_nonneg : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
    -- The expected log fiber size is nonnegative (fibers are nonempty).
    have hE_nonneg :
        0 ≤ ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
      refine Finset.sum_nonneg (fun z hz => ?_)
      have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      have hcard1 : (1 : ℝ) ≤ ((A.filter fun x => proj Iᶜ x = z).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hfib_ne
      exact mul_nonneg (pOn_nonneg A (proj Iᶜ) z) (Real.log_nonneg hcard1)
    by_cases hmN : N ≤ m
    · -- Diagonal case: apply the fixed-threshold algebra with `ζ := r3ZetaSeq`.
      obtain ⟨hζpos, hζb⟩ := hζvalid m hmN
      set ζm : ℝ := r3ZetaSeq c sMass m with hζm_def
      have hζ_le_q2 : ζm ≤ q / 2 :=
        le_trans hζb (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by linarith)))
      have hζ_le_HqMin : ζm ≤ H Q.qMin :=
        le_trans hζb (le_trans (min_le_left _ _) (min_le_right _ _))
      have hζ_le_scale : ζm ≤ 2 * Q.s0 / pLow := le_trans hζb (min_le_right _ _)
      have hHqMin_le_Hq : H Q.qMin ≤ H q := by
        apply Real.binEntropy_strictMonoOn.monotoneOn
        · exact ⟨le_of_lt hqMin_pos, by norm_num; linarith⟩
        · exact ⟨hq_nonneg, by norm_num; linarith⟩
        · exact hq_ge
      have hq_minus_nonneg : 0 ≤ q - ζm := by linarith
      have hHq_sub_nonneg : 0 ≤ H (q - ζm) := by
        unfold H; exact Real.binEntropy_nonneg hq_minus_nonneg (by linarith)
      have hT0 : 0 ≤ H (q - ζm) * (I.card : ℝ) :=
        mul_nonneg hHq_sub_nonneg hIcard_nonneg
      have hSparse := hmass m A q hA hfat hpinned I hIlow hIhigh ζm hζpos hζ_le_q2 hζ_le_scale
      set μ : ℝ := Real.exp (-c * ζm ^ 2 * (m : ℝ) + sMass m) with hμ_def
      have hμnn : 0 ≤ μ := (Real.exp_pos _).le
      have hOnce := r3_expected_log_from_sparse_mass_once A hA I q ζm μ hT0 hSparse
      have hif0 : (if m < N then Real.log 2 * (m : ℝ) else 0) = 0 :=
        if_neg (Nat.not_lt.mpr hmN)
      -- Lipschitz loss: H q - H(q-ζm) costs at most L ζm, and the sparse
      -- threshold loses an additional μ-fraction bounded by log 2.
      have hA1 : L * ζm * (I.card : ℝ) ≤ L * ζm * (m : ℝ) := by
        exact mul_le_mul_of_nonneg_left hIcard_le_m (mul_nonneg hL0 hζpos.le)
      have hLip : H q - H (q - ζm) ≤ L * ζm :=
        hLgap q ζm hq_ge hq_le hζpos.le hζ_le_q2
      have hLipI : (H q - H (q - ζm)) * (I.card : ℝ) ≤ L * ζm * (I.card : ℝ) :=
        mul_le_mul_of_nonneg_right hLip hIcard_nonneg
      have hHq_sub_le : H (q - ζm) ≤ Real.log 2 := by
        unfold H; exact Real.binEntropy_le_log_two
      have hA2 : H (q - ζm) * (I.card : ℝ) * μ ≤ Real.log 2 * (m : ℝ) * μ := by
        apply mul_le_mul_of_nonneg_right _ hμnn
        exact mul_le_mul hHq_sub_le hIcard_le_m hIcard_nonneg hlog2_nonneg
      have hkey : H q * (I.card : ℝ)
          - (L * (r3ZetaSeq c sMass m * (m : ℝ))
            + Real.log 2 * ((m : ℝ) *
                Real.exp (-c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) + sMass m))
            + (if m < N then Real.log 2 * (m : ℝ) else 0))
          ≤ H (q - ζm) * (I.card : ℝ) * (1 - μ) := by
        rw [hif0, ← hζm_def, ← hμ_def]
        nlinarith [hA1, hLipI, hA2]
      exact le_trans hkey hOnce
    · -- Small `m`: the envelope dominates `H q · |I|` outright.
      have hif1 : (if m < N then Real.log 2 * (m : ℝ) else 0) = Real.log 2 * (m : ℝ) :=
        if_pos (Nat.lt_of_not_le hmN)
      have hHqI_le : H q * (I.card : ℝ) ≤ Real.log 2 * (m : ℝ) :=
        mul_le_mul hHq_le hIcard_le_m hIcard_nonneg hlog2_nonneg
      have hz_nonneg : 0 ≤ L * (r3ZetaSeq c sMass m * (m : ℝ)) :=
        mul_nonneg hL0 (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
      have hexp_nonneg : 0 ≤ Real.log 2 * ((m : ℝ) *
          Real.exp (-c * (r3ZetaSeq c sMass m) ^ 2 * (m : ℝ) + sMass m)) :=
        mul_nonneg hlog2_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      rw [hif1]
      nlinarith [hE_nonneg, hHqI_le, hz_nonneg, hexp_nonneg]

/-- Sparse fibers are light, in expected-logarithm form: the mean log fiber
size over a middle window `I` is at least `H(q)|I| - o(m)`.

Proof route (prose R3): `r3_fiber_transfer` splits the pinned neighborhood
budget over the `proj Iᶜ` fibers; each fiber of density below `q - ζ`
Harper-grows (`V+` in the `I`-subcube through the fiber embedding, plus the
two-sided ball volume) at the per-step rate `H'(density)`, which exceeds the
global pinned rate `H'(q)` by `≥ 2ζ` (`|H''| ≥ 4`, cf.
`binEntropy_chord_lower`); with `θ := ⌊pLow ζ m / 2⌋` the mass of such fibers
is at most `exp(-pLow ζ² m + o(m))|A|` by Markov.  Choosing the diagonal
`ζ(m) → 0` slowly (e.g. `ζ(m)³ = slack(m)/m`) and bounding light-fiber
contributions by `log ≥ 0`, heavy fibers by `H(q-ζ)|I| ≥ H(q)|I| - ζ·c₁|I|`
(chord bound) gives the stated envelope. -/
lemma r3_fiber_log_lower (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ sSp : ℕ → ℝ, Sublinear sSp ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      H q * (I.card : ℝ) - sSp m ≤
        ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  apply r3_expected_log_from_mass Q pLow hvalid hlow hhigh
  apply r3_sparse_fibers_mass hBV hVPlus hVC Q pLow hvalid hlow hhigh

private lemma r3_cond_entropy_bound (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    ∃ sCond : ℕ → ℝ, Sublinear sCond ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) → (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      |uCondH A (proj I) (proj Iᶜ) - H q * (I.card : ℝ)| ≤ sCond m := by
  classical
  obtain ⟨sSp, hsSp, hlower⟩ := r3_fiber_log_lower hBV hVPlus hVC Q pLow hvalid hlow hhigh
  refine ⟨fun m => Q.sigma m + sSp m,
    reductions_sublinear_add hvalid.2.2.2.2.2.2.1 hsSp, ?_⟩
  intro m A q hA hfat hpinned I hIlow hIhigh
  -- complement window range bookkeeping
  have hIcard_le : I.card ≤ m := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ I)
  have hcard_comp_nat : (Iᶜ).card = m - I.card := by
    simpa [Fintype.card_fin] using (Finset.card_compl I)
  have hcard_comp : ((Iᶜ).card : ℝ) = (m : ℝ) - (I.card : ℝ) := by
    rw [hcard_comp_nat]
    norm_num [Nat.cast_sub hIcard_le]
  have hIc_low : pLow * (m : ℝ) ≤ ((Iᶜ).card : ℝ) := by
    rw [hcard_comp]; nlinarith
  have hIc_high : ((Iᶜ).card : ℝ) ≤ (1 - pLow) * (m : ℝ) := by
    rw [hcard_comp]; nlinarith
  -- lower direction: the expected-log identity on I
  have hid_I := uCondH_eq_expected_log_fiber A hA I
  have hlow_I : H q * (I.card : ℝ) - sSp m ≤ uCondH A (proj I) (proj Iᶜ) := by
    rw [hid_I]
    exact hlower m A q hA hfat hpinned I hIlow hIhigh
  -- upper direction: subadditivity + the identity on the complement window
  have hid_Ic : uCondH A (proj Iᶜ) (proj I) =
      ∑ z ∈ A.image (proj I), pOn A (proj I) z *
        Real.log (((A.filter fun x => proj I x = z).card : ℝ)) := by
    have h := uCondH_eq_expected_log_fiber A hA Iᶜ
    simpa [compl_compl] using h
  have hlow_Ic : H q * ((Iᶜ).card : ℝ) - sSp m ≤ uCondH A (proj Iᶜ) (proj I) := by
    rw [hid_Ic]
    have h := hlower m A q hA hfat hpinned Iᶜ hIc_low hIc_high
    simpa [compl_compl] using h
  have hsubadd : uCondH A (proj Iᶜ) (proj I) ≤ uH A (proj Iᶜ) := by
    have h := uH_prod_le A hA (proj Iᶜ) (proj I)
    unfold uCondH
    linarith
  have hpair : uH A (fun x => (proj I x, proj Iᶜ x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) :=
    r3_uH_proj_pair_compl_eq_univ A I
  have hcond_eq : uCondH A (proj I) (proj Iᶜ) =
      uH A (proj (Finset.univ : Finset (Fin m))) - uH A (proj Iᶜ) := by
    unfold uCondH
    rw [hpair]
  have htotal :
      |uH A (proj (Finset.univ : Finset (Fin m))) - H q * (m : ℝ)| ≤ Q.sigma m := by
    rw [uH_proj_univ A hA]
    exact hfat.2.2.2.2
  have hσ0 : 0 ≤ Q.sigma m := hvalid.2.2.2.2.2.2.1.1 m
  have hsSp0 : 0 ≤ sSp m := hsSp.1 m
  rw [abs_le] at htotal ⊢
  constructor
  · linarith [hlow_I]
  · -- uCondH(I|Iᶜ) = uH(univ) - uH(proj Iᶜ) ≤ (Hq·m + σ) - (Hq·|Iᶜ| - sSp)
    have hup : uCondH A (proj I) (proj Iᶜ) ≤
        (H q * (m : ℝ) + Q.sigma m) - (H q * ((Iᶜ).card : ℝ) - sSp m) := by
      rw [hcond_eq]
      have h1 : uH A (proj Iᶜ) ≥ H q * ((Iᶜ).card : ℝ) - sSp m :=
        le_trans hlow_Ic hsubadd
      linarith [htotal.2]
    have harith : (H q * (m : ℝ) + Q.sigma m) - (H q * ((Iᶜ).card : ℝ) - sSp m) =
        H q * (I.card : ℝ) + (Q.sigma m + sSp m) := by
      rw [hcard_comp]
      ring
    linarith [hup, harith.le]

private lemma r3_sigmaStar_from_cond_entropy (Q : QData) (pLow : ℝ)
    (hvalid : validQData Q) (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2) :
    (∃ sCond : ℕ → ℝ, Sublinear sCond ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) → (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
        |uCondH A (proj I) (proj Iᶜ) - H q * (I.card : ℝ)| ≤ sCond m) →
    ∃ sigmaStar : ℕ → ℝ, Sublinear sigmaStar ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      blockRegular m A q pLow (sigmaStar m) := by
  intro hcondExists
  rcases hcondExists with ⟨sCond, hsCond, hcond⟩
  refine ⟨fun m => sCond m + Q.sigma m,
    reductions_sublinear_add hsCond hvalid.2.2.2.2.2.2.1, ?_⟩
  intro m A q hA hfat hpinned
  refine ⟨hlow, hhigh, ?_⟩
  intro I hI_low hI_high
  classical
  have hIcard_le : I.card ≤ m := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ I)
  have hcard_comp_nat : (Iᶜ).card = m - I.card := by
    simpa [Fintype.card_fin] using (Finset.card_compl I)
  have hcard_comp : ((Iᶜ).card : ℝ) = (m : ℝ) - (I.card : ℝ) := by
    rw [hcard_comp_nat]
    norm_num [Nat.cast_sub hIcard_le]
  have hIc_low : pLow * (m : ℝ) ≤ ((Iᶜ).card : ℝ) := by
    rw [hcard_comp]
    nlinarith
  have hIc_high : ((Iᶜ).card : ℝ) ≤ (1 - pLow) * (m : ℝ) := by
    rw [hcard_comp]
    nlinarith
  have hcondIc := hcond m A q hA hfat hpinned Iᶜ hIc_low hIc_high
  have hcondIc' :
      |uCondH A (proj Iᶜ) (proj I) - H q * ((Iᶜ).card : ℝ)| ≤ sCond m := by
    simpa using hcondIc
  have hpair : uH A (fun x => (proj Iᶜ x, proj I x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) := by
    simpa using (r3_uH_proj_pair_compl_eq_univ A Iᶜ)
  have hcond_eq : uCondH A (proj Iᶜ) (proj I) =
      uH A (proj (Finset.univ : Finset (Fin m))) - uH A (proj I) := by
    unfold uCondH
    rw [hpair]
  have htotal :
      |uH A (proj (Finset.univ : Finset (Fin m))) - H q * (m : ℝ)| ≤ Q.sigma m := by
    rw [uH_proj_univ A hA]
    exact hfat.2.2.2.2
  rw [abs_le] at htotal hcondIc' ⊢
  rw [hcond_eq, hcard_comp] at hcondIc'
  constructor <;> nlinarith

private lemma r3_sigmaStar_of_Q (_hBV : BallVolumeTwoSidedStatement)
    (_hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) (Q : QData) (pLow : ℝ)
    (_hvalid : validQData Q) (_hlow : 0 < pLow) (_hhigh : pLow ≤ 1 / 2) :
    ∃ sigmaStar : ℕ → ℝ, Sublinear sigmaStar ∧
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      blockRegular m A q pLow (sigmaStar m) := by
  apply r3_sigmaStar_from_cond_entropy Q pLow _hvalid _hlow _hhigh
  apply r3_cond_entropy_bound _hBV _hVPlus hVC Q pLow _hvalid _hlow _hhigh

theorem R3_skeleton (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) : R3Statement := by
  -- fiber Harper: V+ and volume bounds inside coordinate fibers
  intro Q pLow hvalid hlow hhigh
  exact r3_sigmaStar_of_Q hBV hVPlus hVC Q pLow hvalid hlow hhigh

end HarperStability
