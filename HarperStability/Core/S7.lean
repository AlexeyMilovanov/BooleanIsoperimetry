import HarperStability.Core.Basic

namespace HarperStability

attribute [local instance] Classical.propDecidable

/-- Pure entropy pigeonhole: if the entropy of `f` is bounded by `c`, there is a fiber
with probability mass at least `exp(-c)`. -/
lemma heavy_fiber_of_uH_le {m : ℕ} {B : Type*} (A : Finset (Cube m)) (f : Cube m → B) (c : ℝ)
    (hc : uH A f ≤ c) (hA : A.Nonempty) :
    ∃ b : B, Real.exp (-c) * (A.card : ℝ) ≤ ((A.filter (fun x => f x = b)).card : ℝ) := by
  classical
  let img : Finset B :=
    @Finset.image (Cube m) B (fun a b => Classical.propDecidable (a = b)) f A
  by_contra hnone
  have hcard_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have himg_nonempty : img.Nonempty := by
    rcases hA with ⟨x, hx⟩
    dsimp [img]
    exact ⟨f x, Finset.mem_image_of_mem f hx⟩
  have hp_pos : ∀ b ∈ img, 0 < pOn A f b := by
    intro b hb
    dsimp [img] at hb
    rcases Finset.mem_image.mp hb with ⟨x, hxA, rfl⟩
    unfold pOn
    exact div_pos
      (by
        exact_mod_cast (Finset.card_pos.mpr
          ⟨x, by simp [hxA]⟩))
      hcard_pos
  have hp_lt : ∀ b ∈ img, pOn A f b < Real.exp (-c) := by
    intro b hb
    have hnot :
        ¬ Real.exp (-c) * (A.card : ℝ) ≤
          ((A.filter fun x => f x = b).card : ℝ) := by
      intro hbnd
      exact hnone ⟨b, hbnd⟩
    have hlt :
        ((A.filter fun x => f x = b).card : ℝ) <
          Real.exp (-c) * (A.card : ℝ) := lt_of_not_ge hnot
    unfold pOn
    rw [div_lt_iff₀ hcard_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have hterm_gt :
      ∀ b ∈ img, c * pOn A f b < Real.negMulLog (pOn A f b) := by
    intro b hb
    have hlog_lt : Real.log (pOn A f b) < -c := by
      simpa [Real.log_exp] using
        (Real.log_lt_log (hp_pos b hb) (hp_lt b hb))
    have hc_lt : c < -Real.log (pOn A f b) := by
      linarith
    have hmul := mul_lt_mul_of_pos_right hc_lt (hp_pos b hb)
    unfold Real.negMulLog
    nlinarith
  have hsum_lt :
      (∑ b ∈ img, c * pOn A f b) <
        ∑ b ∈ img, Real.negMulLog (pOn A f b) := by
    exact Finset.sum_lt_sum_of_nonempty himg_nonempty hterm_gt
  have hsum_prob : (∑ b ∈ img, pOn A f b) = 1 := by
    simpa using sum_pOn_image_eq_one A hA f
  have hc_lt_uH : c < uH A f := by
    calc
      c = ∑ b ∈ img, c * pOn A f b := by
        rw [← Finset.mul_sum, hsum_prob, mul_one]
      _ < ∑ b ∈ img, Real.negMulLog (pOn A f b) := hsum_lt
      _ = uH A f := by
        rfl
  linarith

/-- The core Azuma + pigeonhole step of S7: if the predictable center has low entropy
and the average number of bad steps is sublinear, then there is a heavy ball. -/
lemma s7_good_event_size {m : ℕ} (A : Finset (Cube m))
    (q eps b : ℝ) (hq : 0 ≤ q) (heps : 0 ≤ eps) (hqeps : q + eps ≤ 1 / 2)
    (hA : A.Nonempty) (hPF : averageBadStepsLE A q eps b) :
    let G := A.filter (fun x => (hDist x (predictableCenter A x) : ℝ) ≤ (q + 4 * eps) * m)
    (3 * eps * m - b) * A.card ≤ (q + 4 * eps) * m * G.card := by
  let R : ℝ := (q + 4 * eps) * (m : ℝ)
  let d : Cube m → ℝ := fun x => (hDist x (predictableCenter A x) : ℝ)
  let G : Finset (Cube m) := A.filter (fun x => d x ≤ R)
  change (3 * eps * (m : ℝ) - b) * (A.card : ℝ) ≤ R * (G.card : ℝ)
  have hcard_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hdist_expect :=
    uE_hDist_predictableCenter_le_of_averageBadStepsLE A hA hq heps hqeps hPF
  have hsum_upper :
      (∑ x ∈ A, d x) ≤ ((q + eps) * (m : ℝ) + b) * (A.card : ℝ) := by
    unfold uE at hdist_expect
    rw [div_le_iff₀ hcard_pos] at hdist_expect
    simpa [d, mul_assoc, mul_left_comm, mul_comm] using hdist_expect
  let Bad : Finset (Cube m) := A.filter (fun x => ¬ d x ≤ R)
  have hBad_sub : Bad ⊆ A := Finset.filter_subset _ _
  have hBad_point : ∀ x ∈ Bad, R ≤ d x := by
    intro x hx
    have hx_not : ¬ d x ≤ R := (Finset.mem_filter.mp hx).2
    exact le_of_lt (lt_of_not_ge hx_not)
  have hBad_sum_lower : R * (Bad.card : ℝ) ≤ ∑ x ∈ Bad, d x := by
    calc
      R * (Bad.card : ℝ) = ∑ x ∈ Bad, R := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ Bad, d x := by
        exact Finset.sum_le_sum hBad_point
  have hBad_sum_le_all : (∑ x ∈ Bad, d x) ≤ ∑ x ∈ A, d x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hBad_sub (by
      intro x _ _
      dsimp [d]
      exact_mod_cast Nat.zero_le (hDist x (predictableCenter A x)))
  have hsplit : G.card + Bad.card = A.card := by
    dsimp [G, Bad]
    exact Finset.card_filter_add_card_filter_not (s := A) (p := fun x => d x ≤ R)
  have hBad_card : (Bad.card : ℝ) = (A.card : ℝ) - (G.card : ℝ) := by
    have hsplit_real : (G.card : ℝ) + (Bad.card : ℝ) = (A.card : ℝ) := by
      exact_mod_cast hsplit
    linarith
  have hsum_lower : R * ((A.card : ℝ) - (G.card : ℝ)) ≤ ∑ x ∈ A, d x := by
    rw [← hBad_card]
    exact hBad_sum_lower.trans hBad_sum_le_all
  have hcombined :
      R * ((A.card : ℝ) - (G.card : ℝ)) ≤
        ((q + eps) * (m : ℝ) + b) * (A.card : ℝ) :=
    hsum_lower.trans hsum_upper
  dsimp [R] at hcombined ⊢
  nlinarith [hcombined]

set_option maxHeartbeats 1000000 in
lemma heavy_fiber_in_good_set {m : ℕ} {B : Type*} [DecidableEq B]
    (A G : Finset (Cube m)) (f : Cube m → B) (E c : ℝ)
    (hG_sub : G ⊆ A) (hG_card : c * A.card ≤ G.card)
    (hc : 0 < c) (hE : uH A f ≤ E) (hA : A.Nonempty) :
    ∃ b : B, (c / 2) * Real.exp (- 2 * E / c) * A.card ≤ (G.filter (fun x => f x = b)).card := by
  -- Let T = 2E/c. By Markov, |Atyp| ≤ (c/2)|A|.
  set T := 2 * E / c
  have hAtyp_card : (A.filter (fun x => T < -Real.log (pOn A f (f x)))).card ≤ (c / 2) * A.card := by
    -- Since $uH A f \leq E$, we have $\sum_{x \in A} (-\log(pOn A f (f x))) \leq E \cdot |A|$.
    have h_sum_log : ∑ x ∈ A, -Real.log (pOn A f (f x)) ≤ E * A.card := by
      have h_avg_log : (∑ x ∈ A, -Real.log (pOn A f (f x))) = uH A f * A.card := by
        have hAtyp_card : ∑ x ∈ A, -Real.log (pOn A f (f x)) = ∑ b ∈ A.image f, (A.filter (fun x => f x = b)).card * (-Real.log (pOn A f b)) := by
          rw [ Finset.sum_image' ];
          intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_filter.mp hy |>.2 ] ] ; simp +decide [ mul_comm ] ;
        simp_all +decide [ uH, pOn ];
        simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, Finset.mul_sum _ _ _, Real.negMulLog ];
        simp +decide [ ← mul_assoc, hA.ne_empty ];
        convert rfl;
      exact h_avg_log ▸ mul_le_mul_of_nonneg_right hE ( Nat.cast_nonneg _ );
    have h_markov : ∑ x ∈ A.filter (fun x => T < -Real.log (pOn A f (f x))), T ≤ E * A.card := by
      refine' le_trans _ h_sum_log;
      rw [ Finset.sum_filter ];
      gcongr;
      split_ifs <;> linarith [ show 0 ≤ -Real.log ( pOn A f ( f ‹_› ) ) from neg_nonneg_of_nonpos ( Real.log_nonpos ( by exact HarperStability.pOn_nonneg _ _ _ ) ( by exact HarperStability.pOn_le_one _ _ _ ) ) ];
    by_cases hE : E = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_comm, mul_left_comm ];
    · rw [ show ( { x ∈ A | T < -Real.log ( pOn A f ( f x ) ) } : Finset ( Cube m ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun x hx => ?_ ] <;> norm_num;
      · positivity;
      · simp +zetaDelta at *;
        have h_log_nonpos : ∀ x ∈ A, Real.log (pOn A f (f x)) ≤ 0 := by
          exact fun x hx => Real.log_nonpos ( pOn_nonneg A f ( f x ) ) ( pOn_le_one A f ( f x ) );
        contrapose! h_sum_log;
        rw [ Finset.sum_eq_add_sum_diff_singleton hx.1 ];
        exact add_neg_of_neg_of_nonpos ( lt_of_le_of_ne ( h_log_nonpos x hx.1 ) ( by aesop ) ) ( Finset.sum_nonpos fun y hy => h_log_nonpos y ( Finset.mem_sdiff.mp hy |>.1 ) );
    · rw [ div_mul_eq_mul_div, div_le_iff₀ ] at h_markov <;> cases lt_or_gt_of_ne hE <;> nlinarith [ show 0 < E by exact lt_of_le_of_ne ( by nlinarith [ show 0 ≤ uH A f by exact uH_nonneg A f ] ) ( Ne.symm hE ) ];
  -- Let Gtyp = G.filter (fun x => - Real.log (pOn A f (f x)) ≤ T).
  set Gtyp := G.filter (fun x => -Real.log (pOn A f (f x)) ≤ T) with hGtyp_def
  have hGtyp_card : Gtyp.card ≥ (c / 2) * A.card := by
    have hGtyp_card : Gtyp.card ≥ G.card - (A.filter (fun x => T < -Real.log (pOn A f (f x)))).card := by
      rw [ ge_iff_le, tsub_le_iff_right ];
      rw [ ← Finset.card_union_add_card_inter ];
      exact le_add_right ( Finset.card_le_card fun x hx => by by_cases h : -Real.log ( pOn A f ( f x ) ) ≤ T <;> aesop );
    norm_num +zetaDelta at *;
    nlinarith [ ( by norm_cast : ( G.card : ℝ ) ≤ { x ∈ G | -Real.log ( pOn A f ( f x ) ) ≤ 2 * E / c }.card + { x ∈ A | 2 * E / c < -Real.log ( pOn A f ( f x ) ) }.card ) ];
  -- Let Vtyp = (A.image f).filter (fun b => Real.exp (-T) ≤ pOn A f b), the typical values.
  set Vtyp := (A.image f).filter (fun b => Real.exp (-T) ≤ pOn A f b) with hVtyp_def
  have hVtyp_card : Vtyp.card ≤ Real.exp T := by
    have hVtyp_card : ∑ b ∈ Vtyp, pOn A f b ≤ 1 := by
      refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => _ ) _;
      · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
      · convert sum_pOn_image_eq_one A hA f |> le_of_eq using 1;
        convert rfl;
    have hVtyp_card : ∑ b ∈ Vtyp, pOn A f b ≥ Vtyp.card * Real.exp (-T) := by
      exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => Finset.mem_filter.mp hx |>.2 );
    rw [ Real.exp_neg ] at hVtyp_card;
    nlinarith [ Real.exp_pos T, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos T ) ) ]
  have hGtyp_subset_Vtyp : ∀ x ∈ Gtyp, f x ∈ Vtyp := by
    simp_all +decide [ Finset.subset_iff ];
    intro x hx hT; refine' ⟨ ⟨ x, hG_sub hx, rfl ⟩, _ ⟩ ; rw [ ← Real.log_le_log_iff ( Real.exp_pos _ ) ( _ ), Real.log_exp ] ; linarith;
    exact div_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ x, by aesop ⟩ ) ) ( Nat.cast_pos.mpr hA.card_pos );
  -- By pigeonhole, there exists b ∈ Vtyp with |G.filter (f=b)| ≥ |Gtyp| / |Vtyp|.
  obtain ⟨b, hb⟩ : ∃ b ∈ Vtyp, (G.filter (fun x => f x = b)).card ≥ (Gtyp.card : ℝ) / Vtyp.card := by
    have h_pigeonhole : ∑ b ∈ Vtyp, (G.filter (fun x => f x = b)).card ≥ Gtyp.card := by
      rw [ ← Finset.card_biUnion ];
      · exact Finset.card_le_card fun x hx => by aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    contrapose! h_pigeonhole;
    have := Finset.sum_lt_sum_of_nonempty ( show Vtyp.Nonempty from ?_ ) h_pigeonhole;
    · by_cases h : Vtyp = ∅ <;> simp_all +decide [ div_eq_mul_inv ];
      · rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ Finset.ext_iff ];
        exact Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact mul_pos ( mul_pos hc ( by norm_num ) ) ( Nat.cast_pos.mpr hA.card_pos ) ) hGtyp_card ) );
      · rw [ ← @Nat.cast_lt ℝ ] ; simp_all +decide [ mul_comm, mul_left_comm ];
    · exact ⟨ f ( Classical.choose ( Finset.card_pos.mp ( show 0 < Finset.card Gtyp from Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact mul_pos ( half_pos hc ) ( Nat.cast_pos.mpr hA.card_pos ) ) hGtyp_card ) ) ) ), hGtyp_subset_Vtyp _ ( Classical.choose_spec ( Finset.card_pos.mp ( show 0 < Finset.card Gtyp from Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact mul_pos ( half_pos hc ) ( Nat.cast_pos.mpr hA.card_pos ) ) hGtyp_card ) ) ) ) ⟩;
  refine' ⟨ b, _ ⟩;
  refine' le_trans _ ( hb.2.trans' ( div_le_div_of_nonneg_left _ _ hVtyp_card ) );
  · convert mul_le_mul_of_nonneg_right hGtyp_card ( inv_nonneg.mpr ( Real.exp_nonneg T ) ) using 1 ; ring_nf;
    rw [ ← Real.exp_neg ] ; ring_nf!;
  · positivity;
  · exact Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ _, hb.1 ⟩ )

lemma s7_core_env_sublinear (eps : ℝ) (cEnv : ℕ → ℝ) (heps : 0 < eps) (hcEnv : Sublinear cEnv) :
    let c := 2 * eps / (1 / 2 + 4 * eps)
    let env := fun (m : ℕ) => (2 / c) * cEnv m - Real.log (c / 2)
    Sublinear env := by
  let c : ℝ := 2 * eps / (1 / 2 + 4 * eps)
  change Sublinear (fun m : ℕ => (2 / c) * cEnv m - Real.log (c / 2))
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hcoef_nonneg : 0 ≤ 2 / c := by positivity
  have hc_half_pos : 0 < c / 2 := by positivity
  have hc_half_le_one : c / 2 ≤ 1 := by
    dsimp [c]
    have hden_pos : 0 < (1 / 2 : ℝ) + 4 * eps := by positivity
    field_simp [hden_pos.ne']
    nlinarith [heps]
  have hconst_nonneg : 0 ≤ -Real.log (c / 2) := by
    have hlog_nonpos : Real.log (c / 2) ≤ 0 :=
      Real.log_nonpos (le_of_lt hc_half_pos) hc_half_le_one
    linarith
  have hsub :
      Sublinear (fun m : ℕ => (2 / c) * cEnv m + (-Real.log (c / 2))) :=
    core_Sublinear_add (core_Sublinear_smul hcoef_nonneg hcEnv)
      (core_Sublinear_const hconst_nonneg)
  convert hsub using 1

lemma s7_core_mass_slack_eventually_small (eps : ℝ) (massSlack : ℝ → ℕ → ℝ) (heps : 0 < eps)
    (hmass : Sublinear (massSlack eps)) :
    ∃ m1 : ℕ, ∀ m ≥ m1, massSlack eps m ≤ eps * m := by
  exact sublinear_eventual_le_linear (massSlack eps) hmass eps heps

lemma s7_core (_Q : QData) (eps : ℝ)
    (cEnv : ℕ → ℝ) (massSlack : ℝ → ℕ → ℝ)
    (heps : 0 < eps)
    (hcEnv : Sublinear cEnv)
    (hmass : Sublinear (massSlack eps)) :
    ∃ env : ℕ → ℝ, Sublinear env ∧
      ∃ m1 : ℕ, ∀ m ≥ m1, ∀ (A : Finset (Cube m)) (q : ℝ),
        0 ≤ q →
        q + eps ≤ 1 / 2 →
        A.Nonempty →
        averageBadStepsLE A q eps (massSlack eps m) →
        uH A (predictableCenter A) ≤ cEnv m →
        ∃ a : Cube m,
          Real.exp (-(env m)) * (A.card : ℝ) ≤
            ((A.filter fun x =>
              hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))).card : ℝ) := by
  let c := 2 * eps / (1 / 2 + 4 * eps)
  let env := fun (m : ℕ) => (2 / c) * cEnv m - Real.log (c / 2)
  have henv : Sublinear env := s7_core_env_sublinear eps cEnv heps hcEnv
  refine ⟨env, henv, ?_⟩
  rcases s7_core_mass_slack_eventually_small eps massSlack heps hmass with ⟨m0, hm0⟩
  refine ⟨max m0 1, ?_⟩
  intro m hm A q hq hqeps hA hPF hCenterBound
  let G := A.filter (fun x => (hDist x (predictableCenter A x) : ℝ) ≤ (q + 4 * eps) * m)
  have h_G_size : (3 * eps * m - massSlack eps m) * A.card ≤ (q + 4 * eps) * m * G.card :=
    s7_good_event_size A q eps (massSlack eps m) hq (le_of_lt heps) hqeps hA hPF
  have h_mass : massSlack eps m ≤ eps * m :=
    hm0 m (le_trans (le_max_left m0 1) hm)
  have hm_one : 1 ≤ m := le_trans (le_max_right m0 1) hm
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_one
  have h_c_pos : 0 < c := by
    dsimp [c]; positivity
  have h_G_card : c * A.card ≤ G.card := by
    have h1 : 2 * eps * m * A.card ≤ (3 * eps * m - massSlack eps m) * A.card := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith [h_mass]
    have h2 : (2 * eps * m) * A.card ≤ (q + 4 * eps) * m * G.card := le_trans h1 h_G_size
    have h2' : (2 * eps) * (A.card : ℝ) ≤ (q + 4 * eps) * (G.card : ℝ) := by
      have hdiv := div_le_div_of_nonneg_right h2 (le_of_lt hm_pos)
      field_simp [hm_pos.ne'] at hdiv
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hden_pos : 0 < (1 / 2 : ℝ) + 4 * eps := by positivity
    have hq_den : q + 4 * eps ≤ (1 / 2 : ℝ) + 4 * eps := by
      linarith [hqeps]
    have h3 : (2 * eps) * (A.card : ℝ) ≤ ((1 / 2 : ℝ) + 4 * eps) * (G.card : ℝ) := by
      exact h2'.trans (mul_le_mul_of_nonneg_right hq_den (Nat.cast_nonneg _))
    dsimp [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith [h3]
  have h_G_sub : G ⊆ A := Finset.filter_subset _ _
  rcases heavy_fiber_in_good_set A G (predictableCenter A) (cEnv m) c h_G_sub h_G_card h_c_pos hCenterBound hA with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have h_env_eval : Real.exp (-(env m)) * A.card = (c / 2) * Real.exp (- 2 * cEnv m / c) * A.card := by
    dsimp [env]
    have hc2_pos : 0 < c / 2 := by positivity
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc2_pos]
    ring_nf
  rw [h_env_eval]
  refine le_trans ha ?_
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxG, hxa⟩
  rw [Finset.mem_filter] at hxG
  refine ⟨hxG.1, ?_⟩
  have hd : (hDist x a : ℝ) ≤ (q + 4 * eps) * m := by
    rw [← hxa]
    exact hxG.2
  have hd2 : (hDist x a : ℝ) ≤ Nat.ceil ((q + 4 * eps) * m) :=
    le_trans hd (Nat.le_ceil _)
  exact_mod_cast hd2

theorem S7_skeleton (_hR3 : R3Statement) (_hS1 : S1Statement)
    (_hS2 : S2Statement) (_hS5 : S5Statement) (_hS6 : S6Statement) :
    S7Statement := by
  intro Q hQ eps heps heps_qMin heps_qMax
  rcases hQ with
    ⟨hqMin_pos, hqMin_le_qMax, hqMax_lt, hs0_pos, hmu0_pos, hreg,
      hSigma_sub, hSigma_log⟩
  rcases _hS5 Q
      ⟨hqMin_pos, hqMin_le_qMax, hqMax_lt, hs0_pos, hmu0_pos, hreg,
        hSigma_sub, hSigma_log⟩ with
    ⟨massSlack, hmassSub, hmassPF⟩
  rcases blockRegularFamily_from_R3 Q _hR3
      ⟨hqMin_pos, hqMin_le_qMax, hqMax_lt, hs0_pos, hmu0_pos, hreg,
        hSigma_sub, hSigma_log⟩ with
    ⟨sFam, hsFamSub, hsFam⟩
  rcases varianceFamily_from_R3_S1_S2 Q _hR3 _hS1 _hS2
      ⟨hqMin_pos, hqMin_le_qMax, hqMax_lt, hs0_pos, hmu0_pos, hreg,
        hSigma_sub, hSigma_log⟩ with
    ⟨vFam, hvFamSub, hvFam⟩
  let gap : ℝ := (1 / 2 - Q.qMax - eps) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have hgap_le : Q.qMax + eps ≤ 1 / 2 - gap := by
    dsimp [gap]
    linarith
  rcases _hS6 Q.qMin Q.qMax eps gap
      (le_of_lt hqMin_pos) hqMin_le_qMax hqMax_lt heps hgap_pos hgap_le
      sFam vFam (massSlack eps) hsFamSub hvFamSub (hmassSub eps heps) with
    ⟨cEnv, hcEnv, hCenter⟩
  rcases s7_core Q eps cEnv massSlack heps hcEnv (hmassSub eps heps) with
    ⟨env, henv, m1, hcore⟩
  refine ⟨env, henv, m1, ?_⟩
  intro m hm A q hA hfat hpinned
  have hqMin_le_q : Q.qMin ≤ q := hfat.2.2.1
  have hq_le_qMax : q ≤ Q.qMax := hfat.2.2.2.1
  have hq_nonneg : 0 ≤ q := by
    exact (le_of_lt hqMin_pos).trans hqMin_le_q
  have hq_eps_half : q + eps ≤ 1 / 2 := by
    linarith
  have hPF : averageBadStepsLE A q eps (massSlack eps m) :=
    hmassPF m A q eps hA heps heps_qMin hfat hpinned
  have hBRF : blockRegularFamily m A q sFam :=
    hsFam m A q hA hfat hpinned
  have hVar :
      ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
        varianceBudgetLE A pLow (vFam pLow m) :=
    hvFam m A q hA hfat hpinned
  have hCenterBound : uH A (predictableCenter A) ≤ cEnv m :=
    hCenter m A q hqMin_le_q hq_le_qMax hA hBRF hVar hPF
  exact hcore m hm A q hq_nonneg hq_eps_half hA hPF hCenterBound

end HarperStability