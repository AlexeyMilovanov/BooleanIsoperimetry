import HarperStability.Entropy

namespace HarperStability

/-!
Process layer: S1--S4.
-/

/-- Pure algebraic squeeze underlying the S2 variance budget: given the
observer surplus bound `2V <= U - S`, the block-regularity cap `U <= C + s`,
and a lower bound `C - B <= S` on the step-entropy sum, the variance `V` is
controlled by `(s + B)/2`. -/
theorem variance_budget_algebra
    (V U S C s B : ℝ)
    (hsurplus : 2 * V ≤ U - S)
    (hU : U ≤ C + s)
    (hS : C - B ≤ S) :
    V ≤ (s + B) / 2 := by
  linarith

/-
Deterministic sorted-profile blocks.
-/
set_option maxHeartbeats 1000000 in
theorem exists_sorted_blocks (m : ℕ) (h : Fin m → ℝ) (k : ℕ) (hk : 3 * k ≤ m) :
    ∃ T M Bt : Finset (Fin m),
      T.card = k ∧ M.card = k ∧ Bt.card = k ∧
      Disjoint T M ∧ Disjoint (T ∪ M) Bt ∧
      (∀ t ∈ T, ∀ u ∉ T, h u ≤ h t) ∧
      (∀ t ∈ M, ∀ u, u ∉ T → u ∉ M → h u ≤ h t) ∧
      (∀ t ∈ Bt, ∀ u ∉ Bt, h t ≤ h u) := by
  rcases k with ( _ | k ) <;> simp_all +decide [ Finset.disjoint_left ];
  -- By definition of $T$, $M$, and $Bt$, we know that they are disjoint and their union is the entire set.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin m ≃ Fin m, ∀ i j : Fin m, i ≤ j → h (σ i) ≤ h (σ j) := by
    have h_sorted : ∃ σ : Fin m → Fin m, Function.Injective σ ∧ ∀ i j : Fin m, i < j → h (σ i) ≤ h (σ j) := by
      have h_exists_min : ∀ (S : Finset (Fin m)), S.Nonempty → ∃ x ∈ S, ∀ y ∈ S, h y ≥ h x := by
        exact fun S hS => Finset.exists_min_image _ _ hS
      -- We can construct such a permutation by repeatedly selecting the minimum element from the remaining elements.
      have h_perm : ∀ (n : ℕ) (hn : n ≤ m), ∀ (S : Finset (Fin m)), S.card = n → ∃ σ : Fin n → Fin m, Function.Injective σ ∧ (∀ i, σ i ∈ S) ∧ ∀ i j : Fin n, i < j → h (σ i) ≤ h (σ j) := by
        intro n hn S hS_card
        induction' n with n ih generalizing S;
        · simp +decide [ Function.Injective ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := h_exists_min S ( Finset.card_pos.mp ( by linarith ) );
          obtain ⟨ σ, hσ₁, hσ₂, hσ₃ ⟩ := ih ( Nat.le_of_succ_le hn ) ( S.erase x ) ( by rw [ Finset.card_erase_of_mem hx₁, hS_card ] ; simp +decide );
          use Fin.cons x σ;
          simp_all +decide [ Fin.forall_fin_succ, Function.Injective ];
          exact ⟨ fun i hi => False.elim <| hσ₂ i |>.1 <| hi.symm, fun i j hij => hσ₁ hij ⟩;
      exact Exists.elim ( h_perm m le_rfl Finset.univ ( by simpa ) ) fun σ hσ => ⟨ σ, hσ.1, hσ.2.2 ⟩;
    obtain ⟨ σ, hσ₁, hσ₂ ⟩ := h_sorted; exact ⟨ Equiv.ofBijective σ ⟨ hσ₁, Finite.injective_iff_surjective.mp hσ₁ ⟩, fun i j hij => by cases hij.lt_or_eq <;> aesop ⟩ ;
  refine' ⟨ Finset.image σ ( Finset.Icc ⟨ m - ( k + 1 ), by omega ⟩ ⟨ m - 1, by omega ⟩ ), _, Finset.image σ ( Finset.Icc ⟨ m - 2 * ( k + 1 ), by omega ⟩ ⟨ m - ( k + 1 ) - 1, by omega ⟩ ), _, Finset.image σ ( Finset.Icc ⟨ 0, by omega ⟩ ⟨ k, by omega ⟩ ), _, _, _ ⟩ <;> simp +decide [ Finset.card_image_of_injective _ σ.injective ];
  · omega;
  · grind;
  · rintro a x hx₁ hx₂ rfl y hy₁ hy₂; contrapose! hy₂;
    rw [ ← σ.injective hy₂ ] at hx₁; exact lt_of_lt_of_le ( Nat.sub_lt ( Nat.sub_pos_of_lt ( by linarith ) ) zero_lt_one ) hx₁;
  · refine' ⟨ _, _, _, _ ⟩;
    · rintro a ( ⟨ i, hi, rfl ⟩ | ⟨ i, hi, rfl ⟩ ) x hx₁ hx₂ <;> simp_all +decide [ Fin.ext_iff ];
      · exact ne_of_lt ( lt_of_le_of_lt hx₂ ( lt_of_lt_of_le ( Nat.lt_sub_of_add_lt ( by linarith ) ) hi.1 ) );
      · grind;
    · rintro t x hx₁ hx₂ rfl u hu;
      obtain ⟨ y, hy ⟩ := σ.surjective u;
      grind;
    · intro t x hx₁ hx₂ hx₃ u hu₁ hu₂; subst hx₃;
      obtain ⟨ y, rfl ⟩ := σ.surjective u;
      grind;
    · intro t x hx₁ hx₂ hx₃ u hu; subst hx₃;
      obtain ⟨ y, hy ⟩ := σ.surjective u;
      grind

/-
Deterministic sorted-profile lemma.
-/
set_option maxHeartbeats 1000000 in
theorem sortedProfile (m : ℕ)
    (h : Fin m → ℝ) (κ s ε : ℝ) (k : ℕ)
    (T M Bt : Finset (Fin m))
    (hTcard : T.card = k) (hMcard : M.card = k) (hBtcard : Bt.card = k)
    (hkm : 4 * k ≤ m) (hmk : m ≤ 4 * k + 4) (hk1 : 1 ≤ k)
    (hdTM : Disjoint T M) (hdB : Disjoint (T ∪ M) Bt)
    (hTtop : ∀ t ∈ T, ∀ u ∉ T, h u ≤ h t)
    (hMtop : ∀ t ∈ M, ∀ u, u ∉ T → u ∉ M → h u ≤ h t)
    (hBtbot : ∀ t ∈ Bt, ∀ u ∉ Bt, h t ≤ h u)
    (h0 : ∀ t, 0 ≤ h t)
    (hs : 0 ≤ s) (hε : 0 < ε)
    (hT : ∑ t ∈ T, h t ≤ κ * (k : ℝ) + s)
    (hM : ∑ t ∈ M, h t ≤ κ * (k : ℝ) + s)
    (hU : ∑ t ∈ Btᶜ, h t ≤ κ * ((m - k : ℕ) : ℝ) + s)
    (htot : κ * (m : ℝ) - s ≤ ∑ t, h t) :
    (((Finset.univ : Finset (Fin m)).filter
      (fun t => ε ≤ |h t - κ|)).card : ℝ) ≤
        12 * s / ε + 4 := by
  by_cases h_case : k * ε ≤ 2 * s;
  · rw [ div_add', le_div_iff₀ ] <;> try positivity;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_le_univ _ ) hε.le ) _ ; norm_num ; nlinarith [ ( by norm_cast : ( 4 :ℝ ) * k ≤ m ), ( by norm_cast : ( m :ℝ ) ≤ 4 * k + 4 ), ( by norm_cast : ( 1 :ℝ ) ≤ k ) ];
  · -- In this case, we have $U.card \leq 5*s/(3*ε)$ and $D.card \leq 7*s/(3*ε)$.
    have hU_card : (Finset.univ.filter (fun t => κ + ε ≤ h t)).card ≤ 5 * s / (3 * ε) := by
      have hU_subset_T : Finset.univ.filter (fun t => κ + ε ≤ h t) ⊆ T := by
        intro t ht; contrapose! ht; simp_all +decide [ Finset.subset_iff ] ;
        have := Finset.sum_le_sum fun x ( hx : x ∈ T ) => hTtop x hx t ht; simp_all +decide [ Finset.sum_add_distrib ] ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ] ;
      have hU_card : ∑ t ∈ T, (h t - κ) ≥ (Finset.univ.filter (fun t => κ + ε ≤ h t)).card * ε + (T.card - (Finset.univ.filter (fun t => κ + ε ≤ h t)).card) * (-2 * s / (3 * k)) := by
        have hU_card : ∀ t ∈ T \ Finset.univ.filter (fun t => κ + ε ≤ h t), h t - κ ≥ -2 * s / (3 * k) := by
          intros t ht
          have h_beta : ∀ u ∉ T, h u ≤ h t := by
            exact hTtop t ( Finset.mem_sdiff.mp ht |>.1 );
          have h_beta : ∑ u ∈ Finset.univ \ T, h u ≤ (m - k) * h t := by
            convert Finset.sum_le_sum fun u hu => h_beta u <| Finset.mem_sdiff.mp hu |>.2 using 1 ; norm_num [ Finset.card_sdiff, * ];
            exact Or.inl ( by rw [ Nat.cast_sub ( by linarith ) ] );
          simp_all +decide [ Finset.card_sdiff ];
          rw [ div_le_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( m : ℝ ) ≥ 4 * k by norm_cast ];
        have hU_card : ∑ t ∈ T \ Finset.univ.filter (fun t => κ + ε ≤ h t), (h t - κ) ≥ (T.card - (Finset.univ.filter (fun t => κ + ε ≤ h t)).card) * (-2 * s / (3 * k)) := by
          refine' le_trans _ ( Finset.sum_le_sum hU_card );
          simp +decide [ Finset.card_sdiff, * ];
          rw [ Finset.inter_eq_left.mpr hU_subset_T, Nat.cast_sub ( by exact le_trans ( Finset.card_le_card hU_subset_T ) ( by aesop ) ) ];
        have hU_card : ∑ t ∈ Finset.univ.filter (fun t => κ + ε ≤ h t), (h t - κ) ≥ (Finset.univ.filter (fun t => κ + ε ≤ h t)).card * ε := by
          exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x hx => show h x - κ ≥ ε by linarith [ Finset.mem_filter.mp hx ] );
        rw [ ← Finset.sum_sdiff hU_subset_T ];
        linarith;
      simp_all +decide [ Finset.sum_sub_distrib ];
      rw [ le_div_iff₀ ] <;> nlinarith [ mul_div_cancel₀ ( - ( 2 * s ) ) ( by positivity : ( 3 * k : ℝ ) ≠ 0 ) ]
    have hD_card : (Finset.univ.filter (fun t => h t ≤ κ - ε)).card ≤ 7 * s / (3 * ε) := by
      -- By definition of $D$, we know that $D \subseteq Bt$.
      have hD_subset_Bt : (Finset.univ.filter (fun t => h t ≤ κ - ε)) ⊆ Bt := by
        have h_sum_Bt : ∑ t ∈ Bt, h t ≥ κ * k - 2 * s := by
          simp_all +decide [ Finset.compl_eq_univ_sdiff ];
          rw [ Nat.cast_sub ( by linarith ) ] at * ; nlinarith [ ( by norm_cast : ( 4 : ℝ ) * k ≤ m ), ( by norm_cast : ( m : ℝ ) ≤ 4 * k + 4 ) ];
        intro t ht; contrapose! h_sum_Bt; simp_all +decide [ Finset.sum_le_sum ] ;
        exact lt_of_le_of_lt ( Finset.sum_le_sum fun x hx => hBtbot x hx t h_sum_Bt ) ( by norm_num [ hBtcard ] ; nlinarith );
      -- By definition of $D$, we know that $\sum_{t \in Bt} (\kappa - h t) \leq 2s$.
      have hD_sum : ∑ t ∈ Bt, (κ - h t) ≤ 2 * s := by
        simp_all +decide [ Finset.compl_eq_univ_sdiff ];
        rw [ Nat.cast_sub ( by linarith ) ] at * ; nlinarith [ ( by norm_cast : ( 4 : ℝ ) * k ≤ m ), ( by norm_cast : ( m : ℝ ) ≤ 4 * k + 4 ) ];
      -- By definition of $D$, we know that $\sum_{t \in Bt} (\kappa - h t) \geq D.card * ε - (k - D.card) * s / (3 * k)$.
      have hD_sum_ge : ∑ t ∈ Bt, (κ - h t) ≥ (Finset.univ.filter (fun t => h t ≤ κ - ε)).card * ε - (k - (Finset.univ.filter (fun t => h t ≤ κ - ε)).card) * s / (3 * k) := by
        have hD_sum_ge : ∀ t ∈ Bt, κ - h t ≥ if h t ≤ κ - ε then ε else -s / (3 * k) := by
          intro t ht
          by_cases h_case : h t ≤ κ - ε;
          · rw [ if_pos h_case ] ; linarith;
          · have h_max : ∑ t ∈ Btᶜ, h t ≥ (m - k) * h t := by
              have h_max : ∀ u ∈ Btᶜ, h u ≥ h t := by
                exact fun u hu => hBtbot t ht u ( by simpa using hu );
              refine' le_trans _ ( Finset.sum_le_sum h_max ) ; norm_num [ Finset.card_compl, * ];
              rw [ Nat.cast_sub ( by linarith ) ];
            rw [ Nat.cast_sub ( by linarith ) ] at *;
            rw [ if_neg h_case ];
            rw [ ge_iff_le, div_le_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( m : ℝ ) ≥ 4 * k by norm_cast ];
        refine' le_trans _ ( Finset.sum_le_sum hD_sum_ge );
        norm_num [ Finset.sum_ite ];
        rw [ show ( Finset.filter ( fun t => h t ≤ κ - ε ) Bt ) = Finset.filter ( fun t => h t ≤ κ - ε ) Finset.univ from ?_, show ( Finset.filter ( fun t => κ - ε < h t ) Bt ) = Bt \ Finset.filter ( fun t => h t ≤ κ - ε ) Finset.univ from ?_ ];
        · rw [ Finset.card_sdiff ] ; norm_num [ hBtcard, hD_subset_Bt ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ] ;
          rw [ Nat.cast_sub ] <;> norm_num [ Finset.inter_eq_left.mpr hD_subset_Bt ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ] ;
          exact le_trans ( Finset.card_le_card hD_subset_Bt ) ( by norm_num [ hBtcard ] );
        · grind;
        · grind;
      rw [ le_div_iff₀ ] <;> try linarith;
      nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( ( k - Finset.card ( Finset.filter ( fun t => h t ≤ κ - ε ) Finset.univ ) ) * s ) ( by positivity : ( 3 * k : ℝ ) ≠ 0 ) ];
    have h_bad_card : (Finset.univ.filter (fun t => ε ≤ |h t - κ|)).card ≤ (Finset.univ.filter (fun t => κ + ε ≤ h t)).card + (Finset.univ.filter (fun t => h t ≤ κ - ε)).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      exact le_add_right ( Finset.card_le_card fun x hx => by norm_num at *; cases abs_cases ( h x - κ ) <;> first | left; linarith | right; linarith );
    refine le_trans ( Nat.cast_le.mpr h_bad_card ) ?_;
    norm_num at *; ring_nf at *; linarith;

theorem S1_skeleton : S1Statement := by
  intro m A kappa s eps hA hs heps hWin hTotal
  by_cases hm_small : m < 4
  · have hcard_nat :
        ((Finset.univ : Finset (Fin m)).filter
          (fun t => eps ≤ |hstep A t - kappa|)).card ≤ m := by
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ
          (((Finset.univ : Finset (Fin m)).filter
            (fun t => eps ≤ |hstep A t - kappa|))))
    have hcard_real :
        ((((Finset.univ : Finset (Fin m)).filter
          (fun t => eps ≤ |hstep A t - kappa|)).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hcard_nat
    have hm_real : (m : ℝ) ≤ 4 := by
      have hm_nat : m ≤ 4 := by omega
      exact_mod_cast hm_nat
    have hnonneg : 0 ≤ 12 * s / eps := by positivity
    linarith
  · have hm_ge : 4 ≤ m := by omega
    let k : ℕ := m / 4
    have hk1 : 1 ≤ k := by
      dsimp [k]
      omega
    have h4k : 4 * k ≤ m := by
      dsimp [k]
      omega
    have hm4k : m ≤ 4 * k + 4 := by
      dsimp [k]
      omega
    have h3k : 3 * k ≤ m := by omega
    rcases exists_sorted_blocks m (fun t => hstep A t) k h3k with
      ⟨T, M, Bt, hTcard, hMcard, hBtcard, hdTM, hdB, hTtop, hMtop, hBtbot⟩
    have hk_lower : m / 5 ≤ k := by
      dsimp [k]
      omega
    have hk_upper : k ≤ m - m / 5 := by
      dsimp [k]
      omega
    have hmk_lower : m / 5 ≤ m - k := by
      dsimp [k]
      omega
    have hmk_upper : m - k ≤ m - m / 5 := by
      dsimp [k]
      omega
    have hBandRight :
        (((m - m / 5 : ℕ) : ℝ) = (m : ℝ) - ((m / 5 : ℕ) : ℝ)) := by
      exact Nat.cast_sub (by omega : m / 5 ≤ m)
    have hTsum :
        ∑ t ∈ T, hstep A t ≤ kappa * (k : ℝ) + s := by
      have hTlow : (((m / 5 : ℕ) : ℝ) ≤ (T.card : ℝ)) := by
        exact_mod_cast (by simpa [hTcard] using hk_lower)
      have hThigh : ((T.card : ℝ) ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ)) := by
        rw [← hBandRight, hTcard]
        exact_mod_cast hk_upper
      have hEnt := hWin T hTlow hThigh
      have hChain := sum_hstep_le_uH_proj A hA T
      have hEnt' : uH A (proj T) ≤ kappa * (k : ℝ) + s := by
        simpa [hTcard] using hEnt
      exact hChain.trans hEnt'
    have hMsum :
        ∑ t ∈ M, hstep A t ≤ kappa * (k : ℝ) + s := by
      have hMlow : (((m / 5 : ℕ) : ℝ) ≤ (M.card : ℝ)) := by
        exact_mod_cast (by simpa [hMcard] using hk_lower)
      have hMhigh : ((M.card : ℝ) ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ)) := by
        rw [← hBandRight, hMcard]
        exact_mod_cast hk_upper
      have hEnt := hWin M hMlow hMhigh
      have hChain := sum_hstep_le_uH_proj A hA M
      have hEnt' : uH A (proj M) ≤ kappa * (k : ℝ) + s := by
        simpa [hMcard] using hEnt
      exact hChain.trans hEnt'
    have hBtComplCard : Btᶜ.card = m - k := by
      simpa [Fintype.card_fin, hBtcard] using (Finset.card_compl Bt)
    have hUsum :
        ∑ t ∈ Btᶜ, hstep A t ≤ kappa * (((m - k : ℕ) : ℝ)) + s := by
      have hUlow : (((m / 5 : ℕ) : ℝ) ≤ (Btᶜ.card : ℝ)) := by
        exact_mod_cast (by simpa [hBtComplCard] using hmk_lower)
      have hUhigh : ((Btᶜ.card : ℝ) ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ)) := by
        rw [← hBandRight, hBtComplCard]
        exact_mod_cast hmk_upper
      have hEnt := hWin Btᶜ hUlow hUhigh
      have hChain := sum_hstep_le_uH_proj A hA Btᶜ
      have hEnt' : uH A (proj Btᶜ) ≤ kappa * (((m - k : ℕ) : ℝ)) + s := by
        simpa [hBtComplCard] using hEnt
      exact hChain.trans hEnt'
    have htot : kappa * (m : ℝ) - s ≤ ∑ t, hstep A t := by
      calc
        kappa * (m : ℝ) - s ≤ uH A (proj (Finset.univ : Finset (Fin m))) := hTotal
        _ = ∑ t, hstep A t := by
          simpa [hstep] using
            (uH_proj_chain A hA (Finset.univ : Finset (Fin m)))
    exact sortedProfile m (fun t => hstep A t) kappa s eps k T M Bt
      hTcard hMcard hBtcard h4k hm4k hk1 hdTM hdB hTtop hMtop hBtbot
      (fun t => hstep_nonneg A hA t) hs heps hTsum hMsum hUsum htot

theorem S2_skeleton : S2Statement := by
  intro m A q pLow s eps e hA hpLow_pos hpLow_le hs heps he hBR hFlat
  unfold varianceBudgetLE
  intro W hWlow hWhigh
  rcases hBR with ⟨_, _, hBR_windows⟩
  have hAbs := hBR_windows W hWlow hWhigh
  have hUpper :
      uH A (proj W) ≤ H q * (W.card : ℝ) + s := by
    linarith [(abs_le.mp hAbs).2]

  let bad : Finset (Fin m) :=
    (Finset.univ : Finset (Fin m)).filter
      (fun t => eps ≤ |hstep A t - H q|)
  have hbadCard : ((bad.card : ℕ) : ℝ) ≤ e := by
    simpa [bad] using hFlat
  have hH_le : H q ≤ Real.log 2 := by
    simpa [H] using Real.binEntropy_le_log_two (p := q)
  have hlog_nonneg : 0 ≤ Real.log 2 := by positivity
  have heps_nonneg : 0 ≤ eps := le_of_lt heps

  have hPoint :
      ∀ t : Fin m,
        H q - eps - (if t ∈ bad then Real.log 2 else 0) ≤ hstep A t := by
    intro t
    by_cases ht : t ∈ bad
    · have hnonneg := hstep_nonneg A hA t
      have hleft_nonpos : H q - eps - Real.log 2 ≤ 0 := by linarith
      simpa [ht] using hleft_nonpos.trans hnonneg
    · have ht_not : ¬ eps ≤ |hstep A t - H q| := by
        simpa [bad] using ht
      have hlt : |hstep A t - H q| < eps := lt_of_not_ge ht_not
      have hlow : H q - eps ≤ hstep A t := by
        have hneg : -eps < hstep A t - H q := (abs_lt.mp hlt).1
        linarith
      simpa [ht] using hlow

  have hSumPoint :
      (∑ t ∈ W, (H q - eps - (if t ∈ bad then Real.log 2 else 0)))
        ≤ ∑ t ∈ W, hstep A t := by
    exact Finset.sum_le_sum (fun t _ => hPoint t)

  have hBadInterCard : (((W.filter fun t => t ∈ bad).card : ℕ) : ℝ) ≤ e := by
    have hcard_le : (W.filter fun t => t ∈ bad).card ≤ bad.card := by
      exact Finset.card_le_card (by
        intro t ht
        exact (Finset.mem_filter.mp ht).2)
    have hcard_le_real :
        (((W.filter fun t => t ∈ bad).card : ℕ) : ℝ) ≤ (bad.card : ℝ) := by
      exact_mod_cast hcard_le
    exact hcard_le_real.trans hbadCard

  have hIndicatorSum :
      (∑ t ∈ W, (if t ∈ bad then Real.log 2 else 0)) =
        (((W.filter fun t => t ∈ bad).card : ℕ) : ℝ) * Real.log 2 := by
    rw [← Finset.sum_filter]
    simp

  have hIndicatorBound :
      (∑ t ∈ W, (if t ∈ bad then Real.log 2 else 0)) ≤ e * Real.log 2 := by
    rw [hIndicatorSum]
    exact mul_le_mul_of_nonneg_right hBadInterCard hlog_nonneg

  have hWcard_le_m : (W.card : ℝ) ≤ (m : ℝ) := by
    have hWcard_nat : W.card ≤ m := by
      simpa using (W.card_le_univ : W.card ≤ Fintype.card (Fin m))
    exact_mod_cast hWcard_nat

  have hLowerBase :
      H q * (W.card : ℝ) - eps * (W.card : ℝ) -
          (∑ t ∈ W, (if t ∈ bad then Real.log 2 else 0))
        ≤ ∑ t ∈ W, hstep A t := by
    have hsum_eq :
        (∑ t ∈ W, (H q - eps - (if t ∈ bad then Real.log 2 else 0))) =
          H q * (W.card : ℝ) - eps * (W.card : ℝ) -
            (∑ t ∈ W, (if t ∈ bad then Real.log 2 else 0)) := by
      simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    simpa [hsum_eq] using hSumPoint

  have hLower :
      H q * (W.card : ℝ) - eps * (m : ℝ) - e * Real.log 2
        ≤ ∑ t ∈ W, hstep A t := by
    have h1 :
        H q * (W.card : ℝ) - eps * (m : ℝ) - e * Real.log 2
          ≤ H q * (W.card : ℝ) - eps * (W.card : ℝ) -
            (∑ t ∈ W, (if t ∈ bad then Real.log 2 else 0)) := by
      have heps_card : eps * (W.card : ℝ) ≤ eps * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hWcard_le_m heps_nonneg
      linarith
    exact h1.trans hLowerBase

  have hSurplus := observer_surplus_lemma A hA W
  have hSurplusUpper :
      uH A (proj W) - ∑ t ∈ W, hstep A t
        ≤ s + eps * (m : ℝ) + e * Real.log 2 := by
    linarith
  have hTwo :
      2 * (∑ t ∈ W,
        uCondVar A
          (fun x => rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
          (proj (below W t))) ≤
        s + eps * (m : ℝ) + e * Real.log 2 := by
    linarith
  linarith

/-
Grouping/superadditivity for `Real.negMulLog`: coarsening probabilities
cannot increase the total entropy contribution.
-/
lemma negMulLog_sum_le {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : (∑ i ∈ s, p i) ≤ 1) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  by_contra h_contra;
  -- Apply the definition of `Real.negMulLog` to rewrite the inequality.
  rw [Real.negMulLog_def] at h_contra;
  have h_pointwise : ∀ i ∈ s, p i * (-Real.log (∑ i ∈ s, p i)) ≤ p i * (-Real.log (p i)) := by
    intro i hi; by_cases hi0 : p i = 0 <;> simp_all +decide [ mul_neg ] ;
    exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( lt_of_le_of_ne ( hp i hi ) ( Ne.symm hi0 ) ) ( Finset.single_le_sum ( fun i _ => hp i ‹_› ) hi ) ) ( hp i hi );
  exact h_contra ( by simpa [ mul_neg, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum h_pointwise )

/-
Fiber decomposition of the coarsened distribution: the probability of a
value `c` of `g ∘ f` is the sum of the probabilities of the `f`-values `b`
with `g b = c`.
-/
lemma pOn_comp_eq_sum {m : ℕ} {B C : Type*} [DecidableEq B] [DecidableEq C]
    (A : Finset (Cube m)) (f : Cube m → B) (g : B → C) (c : C) :
    pOn A (fun x => g (f x)) c
      = ∑ b ∈ (A.image f).filter (fun b => g b = c), pOn A f b := by
  norm_num [ pOn ];
  rw [ ← Finset.sum_div _ _ _, eq_comm ];
  rw_mod_cast [ ← Finset.card_biUnion ];
  · congr with x ; aesop;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;


lemma uH_le_of_dependsOnWindow {m : ℕ} {B : Type*}
    (A : Finset (Cube m)) (hA : A.Nonempty)
    (J : Finset (Fin m)) (G : Cube m → B)
    (hG : dependsOnWindow J G) :
    uH A G ≤ uH A (proj J) := by
  classical
  have hEq : G = (fun x => G (proj J x)) := by
    funext x
    apply hG
    show proj J x = proj J (proj J x)
    simp [proj, Finset.inter_assoc]
  calc
    uH A G = uH A (fun x => G (proj J x)) := by rw [← hEq]
    _ ≤ uH A (proj J) := uH_comp_le A (proj J) G

set_option maxHeartbeats 1000000 in
lemma fano_concavity (m : ℕ) (p BSize : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eJ : Finset (Fin m) → ℝ) (heJ0 : ∀ J, 0 ≤ eJ J) :
    (∑ J : Finset (Fin m), windowProb J p *
      ((m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) + eJ J * Real.log BSize))
    ≤ (m : ℝ) * H (min ((∑ J, windowProb J p * eJ J) / (m : ℝ)) (1 / 2)) +
      (∑ J, windowProb J p * eJ J) * Real.log BSize := by
  by_cases hm : m = 0;
  · subst hm; norm_num [ Finset.sum_range_succ', windowProb ] ;
    norm_num [ mul_assoc ];
  · -- Apply Jensen's inequality for the concave function φ with the weights windowProb J p.
    have h_jensen : (∑ J : Finset (Fin m), windowProb J p * (H (min (eJ J / m) (1 / 2)))) ≤ H (min ((∑ J : Finset (Fin m), windowProb J p * eJ J) / m) (1 / 2)) := by
      have h_jensen : ConcaveOn ℝ (Set.Ici 0) (fun e => H (min (e / m) (1 / 2))) := by
        apply_rules [ ConcaveOn.comp, concaveOn_id ];
        · refine' ConcaveOn.subset _ _ _;
          exact Set.Icc 0 ( 1 / 2 );
          · have h_concave : StrictConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy := by
              grind +suggestions;
            exact h_concave.concaveOn.subset ( Set.Icc_subset_Icc_right ( by norm_num ) ) ( convex_Icc _ _ );
          · exact Set.image_subset_iff.mpr fun x hx => ⟨ le_min ( div_nonneg hx.out ( Nat.cast_nonneg _ ) ) ( by norm_num ), min_le_right _ _ ⟩;
          · refine' convex_iff_forall_pos.mpr _;
            simp +zetaDelta at *;
            intro a ha b hb x y hx hy hxy; use ( x * min ( a / m ) ( 1 / 2 ) + y * min ( b / m ) ( 1 / 2 ) ) * m; ring_nf; norm_num [ hm ] ;
            exact ⟨ by positivity, by nlinarith [ show ( m : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ), inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ), min_le_left ( a * ( m : ℝ ) ⁻¹ ) ( 1 / 2 ), min_le_right ( a * ( m : ℝ ) ⁻¹ ) ( 1 / 2 ), min_le_left ( ( m : ℝ ) ⁻¹ * b ) ( 1 / 2 ), min_le_right ( ( m : ℝ ) ⁻¹ * b ) ( 1 / 2 ) ] ⟩;
        · refine' ⟨ convex_Ici _, _ ⟩;
          norm_num +zetaDelta at *;
          intro x hx y hy a b ha hb hab; constructor <;> cases min_cases ( x / m ) ( 1 / 2 ) <;> cases min_cases ( y / m ) ( 1 / 2 ) <;> ring_nf at * <;> nlinarith [ inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ) ] ;
        · refine' fun x hx y hy hxy => _;
          obtain ⟨ x, hx, rfl ⟩ := hx; obtain ⟨ y, hy, rfl ⟩ := hy;
          refine' Real.binEntropy_strictMonoOn.monotoneOn _ _ hxy <;> norm_num at *; all_goals positivity;
      convert h_jensen.le_map_sum _ _ _ <;> norm_num [ windowProb_nonneg, sum_windowProb_eq_one, heJ0 ];
      · exact fun J => windowProb_nonneg J p hp0 hp1;
      · exact sum_windowProb_eq_one p hp0 hp1;
    simp_all +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
    simpa only [ mul_left_comm, Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left h_jensen <| Nat.cast_nonneg m

lemma windowProb_exp_card_sum (m : ℕ) (p c : ℝ) :
    (∑ J : Finset (Fin m), windowProb J p * Real.exp (c * (J.card : ℝ))) =
      (p * Real.exp c + (1 - p)) ^ m := by
  classical
  unfold windowProb
  simpa [Fintype.card_fin, ← Real.exp_nat_mul, mul_pow, mul_assoc, mul_comm, mul_left_comm]
    using
      (Fintype.sum_pow_mul_eq_add_pow (Fin m) (p * Real.exp c) (1 - p) :
        (∑ J : Finset (Fin m),
          (p * Real.exp c) ^ J.card * (1 - p) ^ (Fintype.card (Fin m) - J.card)) =
            (p * Real.exp c + (1 - p)) ^ Fintype.card (Fin m))

lemma exp_neg_half_le_five_eighths : Real.exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have hquad := Real.quadratic_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
  norm_num at hquad
  have h85 : (8 / 5 : ℝ) ≤ Real.exp (1 / 2) := by nlinarith
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  convert one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8 / 5) h85 using 1
  norm_num

lemma exp_one_le_twenty_three_eighths : Real.exp (1 : ℝ) ≤ 23 / 8 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (n := 3)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  nlinarith

lemma windowProb_lower_tail_bound (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
  (∑ J ∈ Finset.univ.filter
    (fun I : Finset (Fin m) => (I.card : ℝ) < p * (m : ℝ) / 2),
    windowProb J p)
  ≤ Real.exp (-p * (m : ℝ) / 8) := by
  classical
  have hp_nonneg : 0 ≤ p := le_of_lt hp0
  have hp_le_one : p ≤ 1 := by linarith
  let E : Finset (Finset (Fin m)) :=
    Finset.univ.filter
      (fun I : Finset (Fin m) => (I.card : ℝ) < p * (m : ℝ) / 2)
  let tilt : ℝ := Real.exp (p * (m : ℝ) / 4)
  let tilted : Finset (Fin m) → ℝ :=
    fun J => windowProb J p * Real.exp (-(1 / 2 : ℝ) * (J.card : ℝ))
  have hpoint : ∀ J ∈ E, windowProb J p ≤ tilt * tilted J := by
    intro J hJ
    have hJlt : (J.card : ℝ) < p * (m : ℝ) / 2 := by
      simpa [E] using (Finset.mem_filter.mp hJ).2
    have hdiff : 0 ≤ (1 / 2 : ℝ) * (p * (m : ℝ) / 2 - (J.card : ℝ)) := by
      nlinarith
    have hone : (1 : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * (p * (m : ℝ) / 2 - (J.card : ℝ))) :=
      Real.one_le_exp hdiff
    have hwp : 0 ≤ windowProb J p := windowProb_nonneg J p hp_nonneg hp_le_one
    calc
      windowProb J p = windowProb J p * 1 := by ring
      _ ≤ windowProb J p *
          Real.exp ((1 / 2 : ℝ) * (p * (m : ℝ) / 2 - (J.card : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hone hwp
      _ = tilt * tilted J := by
            dsimp [tilt, tilted]
            rw [show (1 / 2 : ℝ) * (p * (m : ℝ) / 2 - (J.card : ℝ)) =
                p * (m : ℝ) / 4 + (-(1 / 2 : ℝ) * (J.card : ℝ)) by ring]
            rw [Real.exp_add]
            ring
  have hnonneg_tilted : ∀ J ∈ Finset.univ, 0 ≤ tilted J := by
    intro J _
    exact mul_nonneg (windowProb_nonneg J p hp_nonneg hp_le_one) (Real.exp_pos _).le
  have hsum_subset : (∑ J ∈ E, tilted J) ≤ ∑ J : Finset (Fin m), tilted J := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro J hJ
      simp
    · intro J _ _
      exact hnonneg_tilted J (Finset.mem_univ J)
  have hbase_le :
      p * Real.exp (-(1 / 2 : ℝ)) + (1 - p) ≤ Real.exp (-(3 * p / 8)) := by
    have h1 : p * Real.exp (-(1 / 2 : ℝ)) ≤ p * (5 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left exp_neg_half_le_five_eighths hp_nonneg
    have hexp : 1 - 3 * p / 8 ≤ Real.exp (-(3 * p / 8)) := by
      simpa using Real.one_sub_le_exp_neg (3 * p / 8)
    linarith
  have hbase_nonneg : 0 ≤ p * Real.exp (-(1 / 2 : ℝ)) + (1 - p) := by
    have h1p : 0 ≤ 1 - p := by linarith
    positivity
  have hpow :
      (p * Real.exp (-(1 / 2 : ℝ)) + (1 - p)) ^ m ≤
        Real.exp (-(3 * p / 8) * (m : ℝ)) := by
    calc
      (p * Real.exp (-(1 / 2 : ℝ)) + (1 - p)) ^ m
          ≤ (Real.exp (-(3 * p / 8))) ^ m :=
            pow_le_pow_left₀ hbase_nonneg hbase_le m
      _ = Real.exp ((m : ℝ) * (-(3 * p / 8))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-(3 * p / 8) * (m : ℝ)) := by ring_nf
  calc
    (∑ J ∈ E, windowProb J p)
        ≤ ∑ J ∈ E, tilt * tilted J := Finset.sum_le_sum hpoint
    _ = tilt * (∑ J ∈ E, tilted J) := by rw [Finset.mul_sum]
    _ ≤ tilt * (∑ J : Finset (Fin m), tilted J) := by
          exact mul_le_mul_of_nonneg_left hsum_subset (Real.exp_pos _).le
    _ = Real.exp (p * (m : ℝ) / 4) *
          (p * Real.exp (-(1 / 2 : ℝ)) + (1 - p)) ^ m := by
          dsimp [tilt, tilted]
          rw [windowProb_exp_card_sum m p (-(1 / 2 : ℝ))]
    _ ≤ Real.exp (p * (m : ℝ) / 4) *
          Real.exp (-(3 * p / 8) * (m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-p * (m : ℝ) / 8) := by
          rw [← Real.exp_add]
          congr 1
          ring

lemma windowProb_upper_tail_bound (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
  (∑ J ∈ Finset.univ.filter
    (fun I : Finset (Fin m) => 2 * p * (m : ℝ) < (I.card : ℝ)),
    windowProb J p)
  ≤ Real.exp (-p * (m : ℝ) / 8) := by
  classical
  have hp_nonneg : 0 ≤ p := le_of_lt hp0
  have hp_le_one : p ≤ 1 := by linarith
  let E : Finset (Finset (Fin m)) :=
    Finset.univ.filter
      (fun I : Finset (Fin m) => 2 * p * (m : ℝ) < (I.card : ℝ))
  let tilt : ℝ := Real.exp (-(2 * p * (m : ℝ)))
  let tilted : Finset (Fin m) → ℝ :=
    fun J => windowProb J p * Real.exp ((J.card : ℝ))
  have hpoint : ∀ J ∈ E, windowProb J p ≤ tilt * tilted J := by
    intro J hJ
    have hJlt : 2 * p * (m : ℝ) < (J.card : ℝ) := by
      simpa [E] using (Finset.mem_filter.mp hJ).2
    have hdiff : 0 ≤ (J.card : ℝ) - 2 * p * (m : ℝ) := by linarith
    have hone : (1 : ℝ) ≤ Real.exp ((J.card : ℝ) - 2 * p * (m : ℝ)) :=
      Real.one_le_exp hdiff
    have hwp : 0 ≤ windowProb J p := windowProb_nonneg J p hp_nonneg hp_le_one
    calc
      windowProb J p = windowProb J p * 1 := by ring
      _ ≤ windowProb J p * Real.exp ((J.card : ℝ) - 2 * p * (m : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hone hwp
      _ = tilt * tilted J := by
            dsimp [tilt, tilted]
            rw [show (J.card : ℝ) - 2 * p * (m : ℝ) =
                (-(2 * p * (m : ℝ))) + (J.card : ℝ) by ring]
            rw [Real.exp_add]
            ring
  have hnonneg_tilted : ∀ J ∈ Finset.univ, 0 ≤ tilted J := by
    intro J _
    exact mul_nonneg (windowProb_nonneg J p hp_nonneg hp_le_one) (Real.exp_pos _).le
  have hsum_subset : (∑ J ∈ E, tilted J) ≤ ∑ J : Finset (Fin m), tilted J := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro J hJ
      simp
    · intro J _ _
      exact hnonneg_tilted J (Finset.mem_univ J)
  have hbase_le :
      p * Real.exp (1 : ℝ) + (1 - p) ≤ Real.exp (15 * p / 8) := by
    have h1 : p * Real.exp (1 : ℝ) ≤ p * (23 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left exp_one_le_twenty_three_eighths hp_nonneg
    have hexp : 1 + 15 * p / 8 ≤ Real.exp (15 * p / 8) := by
      simpa [add_comm] using Real.add_one_le_exp (15 * p / 8)
    linarith
  have hbase_nonneg : 0 ≤ p * Real.exp (1 : ℝ) + (1 - p) := by
    have h1p : 0 ≤ 1 - p := by linarith
    positivity
  have hpow :
      (p * Real.exp (1 : ℝ) + (1 - p)) ^ m ≤
        Real.exp ((15 * p / 8) * (m : ℝ)) := by
    calc
      (p * Real.exp (1 : ℝ) + (1 - p)) ^ m
          ≤ (Real.exp (15 * p / 8)) ^ m :=
            pow_le_pow_left₀ hbase_nonneg hbase_le m
      _ = Real.exp ((m : ℝ) * (15 * p / 8)) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp ((15 * p / 8) * (m : ℝ)) := by ring_nf
  calc
    (∑ J ∈ E, windowProb J p)
        ≤ ∑ J ∈ E, tilt * tilted J := Finset.sum_le_sum hpoint
    _ = tilt * (∑ J ∈ E, tilted J) := by rw [Finset.mul_sum]
    _ ≤ tilt * (∑ J : Finset (Fin m), tilted J) := by
          exact mul_le_mul_of_nonneg_left hsum_subset (Real.exp_pos _).le
    _ = Real.exp (-(2 * p * (m : ℝ))) *
          (p * Real.exp (1 : ℝ) + (1 - p)) ^ m := by
          dsimp [tilt, tilted]
          have hmgf := windowProb_exp_card_sum m p (1 : ℝ)
          simpa using congrArg (fun x => Real.exp (-(2 * p * (m : ℝ))) * x) hmgf
    _ ≤ Real.exp (-(2 * p * (m : ℝ))) *
          Real.exp ((15 * p / 8) * (m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-p * (m : ℝ) / 8) := by
          rw [← Real.exp_add]
          congr 1
          ring

lemma windowProb_tail_bound (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    (∑ J ∈ Finset.univ.filter (fun I : Finset (Fin m) => ¬ (p * (m : ℝ) / 2 ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * p * (m : ℝ))), windowProb J p)
    ≤ 2 * Real.exp (-p * (m : ℝ) / 8) := by
  have h1 := windowProb_lower_tail_bound m p hp0 hp1
  have h2 := windowProb_upper_tail_bound m p hp0 hp1
  have h_eq : (Finset.univ.filter (fun I : Finset (Fin m) => ¬ (p * (m : ℝ) / 2 ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * p * (m : ℝ)))) =
    (Finset.univ.filter (fun I : Finset (Fin m) => (I.card : ℝ) < p * (m : ℝ) / 2)) ∪
    (Finset.univ.filter (fun I : Finset (Fin m) => 2 * p * (m : ℝ) < (I.card : ℝ))) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_and_or, not_le]
  rw [h_eq]
  have h_disj : Disjoint (Finset.univ.filter (fun I : Finset (Fin m) => (I.card : ℝ) < p * (m : ℝ) / 2))
                         (Finset.univ.filter (fun I : Finset (Fin m) => 2 * p * (m : ℝ) < (I.card : ℝ))) := by
    rw [Finset.disjoint_left]
    intro I h_in1 h_in2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_in1 h_in2
    linarith
  rw [Finset.sum_union h_disj]
  linarith


lemma uCondH_coord_le_log_two {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (hA : A.Nonempty) (t : Fin m) (g : Cube m → B) :
    uCondH A (coord t) g ≤ Real.log 2 := by
  rw [uCondH_bool_eq_uE_binEntropy A hA (coord t) g]
  unfold uE H
  have hcard_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  rw [div_le_iff₀ hcard_pos]
  calc
    (∑ x ∈ A, Real.binEntropy (pOn (A.filter fun y => g y = g x) (coord t) true))
        ≤ ∑ _x ∈ A, Real.log 2 := by
          exact Finset.sum_le_sum fun x _ => Real.binEntropy_le_log_two
    _ = Real.log 2 * (A.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma uH_proj_le_m (m : ℕ) (A : Finset (Cube m)) (hA : A.Nonempty) (I : Finset (Fin m)) :
    uH A (proj I) ≤ (m : ℝ) := by
  rw [uH_proj_chain A hA I]
  have hsum_log :
      (∑ t ∈ I, uCondH A (coord t) (proj (below I t))) ≤
        ∑ _t ∈ I, Real.log 2 := by
    exact Finset.sum_le_sum fun t _ => uCondH_coord_le_log_two A hA t (proj (below I t))
  have hcard_le : (I.card : ℝ) ≤ (m : ℝ) := by
    have hcard_nat : I.card ≤ m := by
      simpa [Fintype.card_fin] using (I.card_le_univ : I.card ≤ Fintype.card (Fin m))
    exact_mod_cast hcard_nat
  have hlog_two_le_one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  calc
    (∑ t ∈ I, uCondH A (coord t) (proj (below I t)))
        ≤ ∑ _t ∈ I, Real.log 2 := hsum_log
    _ = (I.card : ℝ) * Real.log 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * 1 := by
          exact mul_le_mul hcard_le hlog_two_le_one (by positivity) (by exact_mod_cast Nat.zero_le m)
    _ = (m : ℝ) := by ring

lemma sum_windowProb_eq_one_univ (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    (∑ J : Finset (Fin m), windowProb J p) = 1 := by
  apply sum_windowProb_eq_one p (le_of_lt hp0) (by linarith)

lemma window_entropy_expectation (m : ℕ) (A : Finset (Cube m))
    (kappa s p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hkappa : 0 ≤ kappa) (hs : 0 ≤ s)
    (hBR : ∀ I : Finset (Fin m),
      p * (m : ℝ) / 2 ≤ (I.card : ℝ) →
      (I.card : ℝ) ≤ 2 * p * (m : ℝ) →
      uH A (proj I) ≤ kappa * (I.card : ℝ) + s) :
    (∑ J : Finset (Fin m), windowProb J p * uH A (proj J))
    ≤ 2 * kappa * p * (m : ℝ) + s + 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
  by_cases hA : A.Nonempty
  · let good := Finset.univ.filter (fun I : Finset (Fin m) => p * (m : ℝ) / 2 ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * p * (m : ℝ))
    let bad := Finset.univ.filter (fun I : Finset (Fin m) => ¬ (p * (m : ℝ) / 2 ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * p * (m : ℝ)))
    have h_split : (∑ J : Finset (Fin m), windowProb J p * uH A (proj J)) =
      (∑ J ∈ good, windowProb J p * uH A (proj J)) +
      (∑ J ∈ bad, windowProb J p * uH A (proj J)) := Finset.sum_filter_add_sum_filter_not Finset.univ _ _ |>.symm
    rw [h_split]

    have hp1_le_one : p ≤ 1 := by linarith

    have h_good_bound : ∀ J ∈ good, windowProb J p * uH A (proj J) ≤ windowProb J p * (2 * kappa * p * (m : ℝ) + s) := by
      intro J hJ
      rw [Finset.mem_filter] at hJ
      have huH := hBR J hJ.2.1 hJ.2.2
      have h_card_le : kappa * (J.card : ℝ) ≤ kappa * (2 * p * (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hJ.2.2 hkappa
      have h_uH_le : uH A (proj J) ≤ 2 * kappa * p * (m : ℝ) + s := by
        linarith
      exact mul_le_mul_of_nonneg_left h_uH_le (windowProb_nonneg J p (le_of_lt hp0) hp1_le_one)

    have h_good_sum : (∑ J ∈ good, windowProb J p * uH A (proj J)) ≤ ∑ J ∈ good, windowProb J p * (2 * kappa * p * (m : ℝ) + s) := Finset.sum_le_sum h_good_bound

    have h_good_sum2 : (∑ J ∈ good, windowProb J p * (2 * kappa * p * (m : ℝ) + s)) = (∑ J ∈ good, windowProb J p) * (2 * kappa * p * (m : ℝ) + s) := by
      rw [← Finset.sum_mul]

    have h_good_sum3 : (∑ J ∈ good, windowProb J p) * (2 * kappa * p * (m : ℝ) + s) ≤ 1 * (2 * kappa * p * (m : ℝ) + s) := by
      apply mul_le_mul_of_nonneg_right
      · have h_le_univ : (∑ J ∈ good, windowProb J p) ≤ ∑ J : Finset (Fin m), windowProb J p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro J _ _
          exact windowProb_nonneg J p (le_of_lt hp0) hp1_le_one
        rw [sum_windowProb_eq_one_univ m p hp0 hp1] at h_le_univ
        exact h_le_univ
      · positivity

    have h_good_final : (∑ J ∈ good, windowProb J p * uH A (proj J)) ≤ 2 * kappa * p * (m : ℝ) + s := by
      linarith

    have h_bad_bound : ∀ J ∈ bad, windowProb J p * uH A (proj J) ≤ windowProb J p * (m : ℝ) := by
      intro J _
      have huH := uH_proj_le_m m A hA J
      exact mul_le_mul_of_nonneg_left huH (windowProb_nonneg J p (le_of_lt hp0) hp1_le_one)

    have h_bad_sum : (∑ J ∈ bad, windowProb J p * uH A (proj J)) ≤ ∑ J ∈ bad, windowProb J p * (m : ℝ) := Finset.sum_le_sum h_bad_bound

    have h_bad_sum2 : (∑ J ∈ bad, windowProb J p * (m : ℝ)) = (∑ J ∈ bad, windowProb J p) * (m : ℝ) := by
      rw [← Finset.sum_mul]

    have h_bad_sum3 : (∑ J ∈ bad, windowProb J p) * (m : ℝ) ≤ (2 * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ) := by
      apply mul_le_mul_of_nonneg_right (windowProb_tail_bound m p hp0 hp1)
      positivity

    have h_bad_final : (∑ J ∈ bad, windowProb J p * uH A (proj J)) ≤ 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
      linarith

    linarith
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hLhs :
        (∑ J : Finset (Fin m), windowProb J p * uH A (proj J)) = 0 := by
      simp [hAempty, uH]
    have hRhs_nonneg :
        0 ≤ 2 * kappa * p * (m : ℝ) + s +
          2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
      have hp_nonneg : 0 ≤ p := le_of_lt hp0
      have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      have hmain : 0 ≤ 2 * kappa * p * (m : ℝ) := by positivity
      have htail : 0 ≤ 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by positivity
      linarith
    rw [hLhs]
    exact hRhs_nonneg

lemma fano_mono (m : ℕ) (BSize e1 e2 : ℝ)
    (hBSize : 1 ≤ BSize) (he1 : 0 ≤ e1) (he12 : e1 ≤ e2) :
    (m : ℝ) * H (min (e1 / (m : ℝ)) (1 / 2)) + e1 * Real.log BSize
    ≤ (m : ℝ) * H (min (e2 / (m : ℝ)) (1 / 2)) + e2 * Real.log BSize := by
  have hlog_nonneg : 0 ≤ Real.log BSize := Real.log_nonneg hBSize
  have hlinear : e1 * Real.log BSize ≤ e2 * Real.log BSize :=
    mul_le_mul_of_nonneg_right he12 hlog_nonneg
  by_cases hm : m = 0
  · simp [hm]
    exact hlinear
  · have hmpos_nat : 0 < m := Nat.pos_of_ne_zero hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
    have hmnonneg : 0 ≤ (m : ℝ) := le_of_lt hmpos
    have he2 : 0 ≤ e2 := he1.trans he12
    let x1 : ℝ := min (e1 / (m : ℝ)) (1 / 2)
    let x2 : ℝ := min (e2 / (m : ℝ)) (1 / 2)
    have hx1_nonneg : 0 ≤ x1 := by
      dsimp [x1]
      exact le_min (div_nonneg he1 hmnonneg) (by norm_num)
    have hx1_half : x1 ≤ (2⁻¹ : ℝ) := by
      dsimp [x1]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num]
      exact min_le_right _ _
    have hx2_nonneg : 0 ≤ x2 := by
      dsimp [x2]
      exact le_min (div_nonneg he2 hmnonneg) (by norm_num)
    have hx2_half : x2 ≤ (2⁻¹ : ℝ) := by
      dsimp [x2]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num]
      exact min_le_right _ _
    have hxle : x1 ≤ x2 := by
      dsimp [x1, x2]
      exact min_le_min (div_le_div_of_nonneg_right he12 hmnonneg) le_rfl
    have hHle : H x1 ≤ H x2 := by
      dsimp [H]
      exact (Real.binEntropy_strictMonoOn.le_iff_le
        (by exact ⟨hx1_nonneg, hx1_half⟩)
        (by exact ⟨hx2_nonneg, hx2_half⟩)).2 hxle
    have hEntropy :
        (m : ℝ) * H x1 ≤ (m : ℝ) * H x2 :=
      mul_le_mul_of_nonneg_left hHle hmnonneg
    dsimp [x1, x2] at hEntropy
    linarith

theorem S3_skeleton : S3Statement := by
  classical
  intro m A kappa s B F p e BSize hA hkappa hs hp0 hp_half he hBSize hBR hSize hG
  rcases hG with ⟨G, hG_dep, hG_err⟩
  have hp1 : p ≤ 1 := by linarith

  let eJ : Finset (Fin m) → ℝ := fun J =>
    uE A (fun x =>
      (((Finset.univ : Finset (Fin m)).filter fun t => F x t ≠ G J x t).card : ℝ))

  have heJ0 : ∀ J, 0 ≤ eJ J := by
    intro J
    dsimp [eJ]
    unfold uE
    apply div_nonneg
    · exact Finset.sum_nonneg fun x _ => by exact_mod_cast Nat.zero_le _
    · exact_mod_cast Nat.zero_le _

  have hFanoPoint :
      ∀ J : Finset (Fin m),
        uH A F ≤ uH A (G J) +
          (m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) +
          eJ J * Real.log BSize := by
    intro J
    exact deterministic_field_fano A hA F (G J) (eJ J) BSize
      (heJ0 J) hBSize hSize (by rfl)

  have hWindowDP :
      ∀ J : Finset (Fin m), uH A (G J) ≤ uH A (proj J) := by
    intro J
    exact uH_le_of_dependsOnWindow A hA J (G J) (hG_dep J)

  have hPoint :
      ∀ J : Finset (Fin m),
        uH A F ≤ uH A (proj J) +
          (m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) +
          eJ J * Real.log BSize := by
    intro J
    linarith [hFanoPoint J, hWindowDP J]

  have hWeighted :
      (∑ J : Finset (Fin m), windowProb J p * uH A F) ≤
        ∑ J : Finset (Fin m),
          windowProb J p *
            (uH A (proj J) +
              (m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) +
              eJ J * Real.log BSize) := by
    apply Finset.sum_le_sum
    intro J _
    exact mul_le_mul_of_nonneg_left (hPoint J)
      (windowProb_nonneg J p (le_of_lt hp0) hp1)

  have hSumProb : (∑ J : Finset (Fin m), windowProb J p) = 1 :=
    sum_windowProb_eq_one p (le_of_lt hp0) hp1

  have hLhs :
      (∑ J : Finset (Fin m), windowProb J p * uH A F) = uH A F := by
    rw [← Finset.sum_mul, hSumProb, one_mul]

  have hRhsSplit :
      (∑ J : Finset (Fin m),
          windowProb J p *
            (uH A (proj J) +
              (m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) +
              eJ J * Real.log BSize)) =
        (∑ J : Finset (Fin m), windowProb J p * uH A (proj J)) +
        (∑ J : Finset (Fin m),
          windowProb J p *
            ((m : ℝ) * H (min (eJ J / (m : ℝ)) (1 / 2)) +
              eJ J * Real.log BSize)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring

  rw [hLhs, hRhsSplit] at hWeighted

  have hEntropy := window_entropy_expectation m A kappa s p hp0 hp_half hkappa hs hBR
  have hFanoConcavity := fano_concavity m p BSize (le_of_lt hp0) hp1 eJ heJ0

  have hAvgErr :
      (∑ J : Finset (Fin m), windowProb J p * eJ J) =
        expectedEstimatorError A F G p := by
    dsimp [eJ, expectedEstimatorError]

  have hAvgErrNonneg :
      0 ≤ expectedEstimatorError A F G p := by
    rw [← hAvgErr]
    exact Finset.sum_nonneg fun J _ =>
      mul_nonneg (windowProb_nonneg J p (le_of_lt hp0) hp1) (heJ0 J)

  have hFanoMono :=
    fano_mono m BSize (expectedEstimatorError A F G p) e
      hBSize hAvgErrNonneg hG_err

  rw [hAvgErr] at hFanoConcavity
  linarith [hWeighted, hEntropy, hFanoConcavity, hFanoMono]

/-
Sublinear diagonalization.  Given a per-density family `Sfam` that is
`Sublinear` in `m` for every fixed admissible density `p ∈ (0, 1/2]`, and a
nonnegative slope `c`, there is a single `Sublinear` envelope `env` together
with a density schedule `P : ℕ → ℝ` (valued in `(0, 1/2]`) dominating
`m ↦ Sfam (P m) m + c · P m · m`.  The point is that the linear term
`c · P m · m` is made negligible by letting `P m → 0` while the sublinear
terms `Sfam (P m) m` are tamed by a diagonal choice of thresholds.
-/
lemma sublinear_diagonalize (Sfam : ℝ → ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hS : ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → Sublinear (Sfam p)) :
    ∃ (env : ℕ → ℝ) (P : ℕ → ℝ),
      Sublinear env ∧
      (∀ m : ℕ, 0 < P m ∧ P m ≤ 1 / 2) ∧
      (∀ m : ℕ, Sfam (P m) m + c * P m * (m : ℝ) ≤ env m) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧ ∀ k ≥ 1, ∀ m ≥ N k, Sfam (1 / (k + 2)) m ≤ (1 / (k + 2)) * m := by
    have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ m ≥ N, Sfam (1 / (k + 2)) m ≤ (1 / (k + 2)) * m := by
      intro k;
      convert hS ( 1 / ( k + 2 ) ) ( by positivity ) ( by rw [ div_le_iff₀ ] <;> linarith ) |>.2 ( 1 / ( k + 2 ) ) ( by positivity ) using 1;
    choose N hN using hN;
    refine' ⟨ fun k => Nat.recOn k 0 fun k ih => Max.max ( N ( k + 1 ) ) ( ih + 1 ), strictMono_nat_of_lt_succ fun k => _, _, _ ⟩ <;> norm_num;
    intro k hk m hm; specialize hN k m; induction hk <;> aesop;
  refine' ⟨ fun m => Sfam ( 1 / ( Nat.findGreatest ( fun k => N k ≤ m ) m + 2 ) ) m + c * ( 1 / ( Nat.findGreatest ( fun k => N k ≤ m ) m + 2 ) ) * m, fun m => 1 / ( Nat.findGreatest ( fun k => N k ≤ m ) m + 2 ), _, _, _ ⟩ <;> norm_num;
  · refine' ⟨ fun m => add_nonneg ( _ ) ( mul_nonneg ( mul_nonneg hc ( inv_nonneg.2 ( by positivity ) ) ) ( Nat.cast_nonneg m ) ), _ ⟩;
    · have := hS ( ( Nat.findGreatest ( fun k => N k ≤ m ) m + 2 : ℝ ) ⁻¹ ) ( by positivity ) ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.findGreatest_eq_iff.mp ( rfl : Nat.findGreatest ( fun k => N k ≤ m ) m = _ ) ] ) ; exact this.1 m;
    · intro ε hε
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ (1 + c) / (k + 2 : ℝ) ≤ ε := by
        exact ⟨ ⌊ ( 1 + c ) / ε⌋₊ + 1, by linarith, by rw [ div_le_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( ( 1 + c ) / ε ), mul_div_cancel₀ ( 1 + c ) hε.ne' ] ⟩
      use N k
      intro n hn
      have hidx : Nat.findGreatest (fun k => N k ≤ n) n ≥ k := by
        apply Nat.le_findGreatest;
        · exact le_trans ( hN.1.id_le _ ) hn;
        · linarith
      have hP : (Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹ ≤ (k + 2 : ℝ)⁻¹ := by
        exact inv_anti₀ ( by positivity ) ( by norm_cast; linarith )
      have hSfam : Sfam (1 / (Nat.findGreatest (fun k => N k ≤ n) n + 2)) n ≤ (1 / (k + 2 : ℝ)) * n := by
        have := hN.2.2 ( Nat.findGreatest ( fun k => N k ≤ n ) n ) ( by linarith ) n ?_ <;> norm_num at *;
        · exact this.trans ( mul_le_mul_of_nonneg_right hP <| Nat.cast_nonneg _ );
        · have := Nat.findGreatest_eq_iff.mp ( rfl : Nat.findGreatest ( fun k => N k ≤ n ) n = _ ) ; aesop;
      have henv : Sfam (1 / (Nat.findGreatest (fun k => N k ≤ n) n + 2)) n + c * (1 / (Nat.findGreatest (fun k => N k ≤ n) n + 2)) * n ≤ ε * n := by
        refine le_trans ?_ ( mul_le_mul_of_nonneg_right hk.2 <| Nat.cast_nonneg _ );
        convert add_le_add hSfam ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( show ( 1 / ( Nat.findGreatest ( fun k => N k ≤ n ) n + 2 : ℝ ) ) ≤ ( 1 / ( k + 2 : ℝ ) ) from by simpa using hP ) hc ) ( Nat.cast_nonneg n ) ) using 1 ; ring
      exact henv.trans' (by
      norm_num [ add_comm ]);
  · exact fun m => ⟨ by positivity, by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> linarith ⟩

set_option linter.unusedVariables false in
noncomputable def s4_pUse (p : ℝ) : ℝ :=
  min p (1 / 3)

set_option linter.unusedVariables false in
noncomputable def s4_errorBound (w : ℝ) (vFam : ℝ → ℕ → ℝ) (p : ℝ) (m : ℕ) : ℝ :=
  let pLow := p / 2
  (((vFam pLow m / p +
      2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)) ^
        (1 / 2 : ℝ)) / w

set_option linter.unusedVariables false in
noncomputable def s4_Sfam (w : ℝ) (sFam vFam : ℝ → ℕ → ℝ) (p : ℝ) (m : ℕ) : ℝ :=
  let p0 := s4_pUse p
  let e := s4_errorBound w vFam p0 m
  let BSize := max 1 (1 / w + 2)
  0 + (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) + e * Real.log BSize + 2 * (m : ℝ) * Real.exp (-p0 * (m : ℝ) / 8)

/-- Local copy of additive closure of `Sublinear` (the `Volume` copy is not
in scope for the `Process` layer). -/
lemma s4_Sublinear_add {s t : ℕ → ℝ} (hs : Sublinear s) (ht : Sublinear t) :
    Sublinear (fun n => s n + t n) := by
  refine ⟨fun n => add_nonneg (hs.1 n) (ht.1 n), fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := hs.2 (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := ht.2 (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  simp only
  linarith

/-- Local copy of nonnegative scalar closure of `Sublinear`. -/
lemma s4_Sublinear_smul {c : ℝ} (hc : 0 ≤ c) {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (fun n => c * s n) := by
  refine ⟨fun n => mul_nonneg hc (hs.1 n), fun ε hε => ?_⟩
  rcases eq_or_lt_of_le hc with h | h
  · exact ⟨0, fun n _ => by simp [← h]; positivity⟩
  · obtain ⟨N, hN⟩ := hs.2 (ε / c) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h2 : c * s n ≤ c * (ε / c * (n : ℝ)) := by nlinarith [hN n hn]
    have h3 : c * (ε / c * (n : ℝ)) = ε * n := by field_simp
    show c * s n ≤ ε * n
    rw [← h3]; exact h2

/-- Local copy of pointwise domination closure of `Sublinear`. -/
lemma s4_Sublinear_of_le {s t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (hle : ∀ n, t n ≤ s n) (hs : Sublinear s) : Sublinear t := by
  refine ⟨ht0, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hs.2 ε hε
  exact ⟨N, fun n hn => (hle n).trans (hN n hn)⟩

/-
The sequence `m ↦ m · exp(-c·m/8)` is sublinear (it tends to `0`).
-/
lemma s4_Sublinear_mexp (c : ℝ) (hc : 0 < c) :
    Sublinear (fun m => (m : ℝ) * Real.exp (-c * (m : ℝ) / 8)) := by
  refine' ⟨ fun m => by positivity, fun ε hε => _ ⟩;
  -- Choose $N$ such that for all $n \geq N$, we have $\exp(-c * n / 8) \leq \epsilon$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, Real.exp (-c * (n : ℝ) / 8) ≤ ε := by
    simpa [ neg_div, neg_mul ] using ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| tendsto_natCast_atTop_atTop.const_mul_atTop hc ) |> fun h => h.eventually ( ge_mem_nhds hε );
  exact ⟨ N, fun n hn => by simpa [ mul_comm ] using mul_le_mul_of_nonneg_left ( hN n hn ) ( Nat.cast_nonneg n ) ⟩

/-
If `B` is sublinear then so is `m ↦ (B m · m)^{1/2} / w` for `w > 0`
(the shape of `s4_errorBound`).
-/
lemma s4_Sublinear_rpow_half_mul (w : ℝ) (hw : 0 < w) (B : ℕ → ℝ)
    (hB : Sublinear B) :
    Sublinear (fun m => (B m * (m : ℝ)) ^ (1 / 2 : ℝ) / w) := by
  constructor;
  · exact fun n => div_nonneg ( Real.rpow_nonneg ( mul_nonneg ( hB.1 n ) ( Nat.cast_nonneg n ) ) _ ) hw.le;
  · intro ε hε
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, B n ≤ (ε * w)^2 * n := by
      exact hB.2 _ ( by positivity );
    refine' ⟨ N + 1, fun n hn => _ ⟩ ; rw [ div_le_iff₀ hw ] ; rw [ ← Real.sqrt_eq_rpow ] ; rw [ Real.sqrt_le_left ];
    · nlinarith [ hN n ( by linarith ), show ( n : ℝ ) ≥ N + 1 by norm_cast ];
    · positivity

/-
The `s4_errorBound` sequence is sublinear whenever the variance family
component `vFam (p0/2)` is sublinear.
-/
lemma s4_Sublinear_errorBound (w : ℝ) (hw : 0 < w) (vFam : ℝ → ℕ → ℝ) (p0 : ℝ)
    (hp0 : 0 < p0) (hvF : Sublinear (vFam (p0 / 2))) :
    Sublinear (fun m => s4_errorBound w vFam p0 m) := by
  have hB : Sublinear (fun m => (vFam (p0 / 2) m / p0 + 2 * (m : ℝ) / p0 * Real.exp (-p0 * (m : ℝ) / 8))) := by
    convert s4_Sublinear_add ( s4_Sublinear_smul ( by positivity : 0 ≤ 1 / p0 ) hvF ) ( s4_Sublinear_smul ( by positivity : 0 ≤ 2 / p0 ) ( s4_Sublinear_mexp p0 hp0 ) ) using 2 ; ring;
  convert s4_Sublinear_rpow_half_mul w hw _ hB using 1

/-
Entropy envelope term: if `g` is sublinear then so is
`m ↦ m · H (min (g m / m) (1/2))`, because `g m / m → 0` and `H` is
continuous with `H 0 = 0`.
-/
lemma s4_Sublinear_entropyTerm (g : ℕ → ℝ) (hg : Sublinear g) :
    Sublinear (fun m => (m : ℝ) * H (min (g m / (m : ℝ)) (1 / 2))) := by
  refine' ⟨ fun m => _, fun ε hε => _ ⟩ <;> norm_num [ H ] at *;
  · exact mul_nonneg ( Nat.cast_nonneg _ ) ( Real.binEntropy_nonneg ( by cases min_cases ( g m / m ) ( 1 / 2 ) <;> nlinarith [ hg.1 m, show ( 0 : ℝ ) ≤ g m / m from div_nonneg ( hg.1 m ) ( Nat.cast_nonneg m ) ] ) ( by cases min_cases ( g m / m ) ( 1 / 2 ) <;> linarith ) );
  · -- By the continuity of `Real.binEntropy` at 0, there exists `δ > 0` such that `Real.binEntropy x ≤ ε` for `x ∈ [0, δ]`.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Icc 0 δ, Real.binEntropy x ≤ ε := by
      have := Metric.continuousAt_iff.mp ( show ContinuousAt ( fun x : ℝ => Real.binEntropy x ) 0 by exact Real.binEntropy_continuous.continuousAt ) ε hε; simp_all +decide [ Real.binEntropy ] ;
      obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this; exact ⟨ δ / 2, half_pos hδ₁, fun x hx₁ hx₂ => by linarith [ abs_lt.mp ( hδ₂ ( show |x| < δ by rw [ abs_of_nonneg hx₁ ] ; linarith ) ) ] ⟩ ;
    obtain ⟨ N, hN ⟩ := hg.2 δ hδ_pos;
    refine' ⟨ N + 1, fun n hn => _ ⟩ ; rw [ mul_comm ] ; gcongr;
    exact hδ _ ⟨ by exact le_min ( div_nonneg ( hg.1 _ ) ( Nat.cast_nonneg _ ) ) ( by norm_num ), by exact min_le_of_left_le ( div_le_of_le_mul₀ ( by norm_cast; linarith ) ( by positivity ) ( by linarith [ hN n ( by linarith ) ] ) ) ⟩

lemma s4_Sfam_sublinear (w : ℝ) (hw : 0 < w) (sFam vFam : ℝ → ℕ → ℝ)
    (hsF : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow))
    (hvF : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow))
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    Sublinear (s4_Sfam w sFam vFam p) := by
  have h_sublinear : Sublinear (fun m => s4_errorBound w vFam (min p (1 / 3)) m) := by
    apply s4_Sublinear_errorBound w hw vFam (min p (1 / 3)) (by
    positivity) (hvF (min p (1 / 3) / 2) (by
    positivity) (by
    linarith [ min_le_left p ( 1 / 3 ), min_le_right p ( 1 / 3 ) ]));
  convert s4_Sublinear_add ( s4_Sublinear_add ( s4_Sublinear_entropyTerm _ h_sublinear ) ( s4_Sublinear_smul ( Real.log_nonneg <| show 1 ≤ max 1 ( 1 / w + 2 ) from le_max_left _ _ ) h_sublinear ) ) ( s4_Sublinear_smul ( by norm_num : ( 0 : ℝ ) ≤ 2 ) <| s4_Sublinear_mexp _ ( show 0 < min p ( 1 / 3 ) by positivity ) ) using 1;
  grind +locals

noncomputable def s4_canonicalEstimator (m : ℕ) (A : Finset (Cube m)) (w o : ℝ) (J : Finset (Fin m)) (x : Cube m) (t : Fin m) : ℤ :=
  let Afib := A.filter fun y => proj J y = proj J x
  Int.floor ((fold (uE Afib fun y => rho A t (proj (below Finset.univ t) y)) - o) / w)

lemma s4_canonicalEstimator_dependsOnWindow (m : ℕ) (A : Finset (Cube m)) (w o : ℝ) (J : Finset (Fin m)) :
    dependsOnWindow J (s4_canonicalEstimator m A w o J) := by
  intro x y hxy
  funext t
  simp [s4_canonicalEstimator, hxy]

/-
`fold x = min x (1-x)` is 1-Lipschitz.
-/
lemma fold_sub_abs_le (a b : ℝ) : |fold a - fold b| ≤ |a - b| := by
  unfold fold;
  cases min_cases a ( 1 - a ) <;> cases min_cases b ( 1 - b ) <;> cases abs_cases ( a - b ) <;> cases abs_cases ( min a ( 1 - a ) - min b ( 1 - b ) ) <;> linarith

/-
Cauchy–Schwarz / power-mean: `∑ sqrt cᵢ ≤ sqrt (|s| · ∑ cᵢ)`.
-/
lemma sum_sqrt_le_sqrt_card_mul_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, Real.sqrt (c i)) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, c i) := by
  refine Real.le_sqrt_of_sq_le ?_;
  convert ( Finset.sum_mul_sq_le_sq_mul_sq s ( fun _ => 1 ) ( fun i => Real.sqrt ( c i ) ) ) using 1 <;> norm_num [ hc ];
  exact Or.inl ( Finset.sum_congr rfl fun i hi => by rw [ Real.sq_sqrt ( hc i hi ) ] )

/-
Jensen for the concave `sqrt` with probability weights.
-/
lemma sum_weight_sqrt_le_sqrt_sum_weight {ι : Type*} (s : Finset ι) (wt y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ wt i) (hy : ∀ i ∈ s, 0 ≤ y i) (hsum : ∑ i ∈ s, wt i = 1) :
    (∑ i ∈ s, wt i * Real.sqrt (y i)) ≤ Real.sqrt (∑ i ∈ s, wt i * y i) := by
  have h_jensen : ConcaveOn ℝ (Set.Ici 0) Real.sqrt := by
    exact ( Real.strictConcaveOn_sqrt.concaveOn );
  convert h_jensen.le_map_sum _ _ _ <;> aesop

/-
Conditional variance equals the fiber-averaged squared deviation from the
fiber mean.
-/
lemma uCondVar_eq_uE_fiber_sq {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (f : Cube m → ℝ) (g : Cube m → B) :
    uCondVar A f g = uE A (fun x => (f x - uE (A.filter fun y => g y = g x) f) ^ 2) := by
  by_cases hA : A = ∅ <;> simp_all +decide [ uCondVar, uE ];
  simp +decide [ Finset.sum_div _ _ _, pOn, varOn ];
  simp +decide [ uE, Finset.sum_div _ _ _, Finset.sum_filter ];
  simp +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun x hx => _;
  simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, hx ];
  rw [ if_pos ⟨ x, hx, rfl ⟩ ] ; by_cases h : Finset.card ( Finset.filter ( fun y => g y = g x ) A ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact False.elim ( h hx rfl );
  · convert rfl

/-
`E|f - E[f|g]| ≤ sqrt (Var[f|g])` (conditional Cauchy–Schwarz).
-/
lemma uE_abs_fiber_le_sqrt_uCondVar {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (f : Cube m → ℝ) (g : Cube m → B) :
    uE A (fun x => |f x - uE (A.filter fun y => g y = g x) f|) ≤ Real.sqrt (uCondVar A f g) := by
  -- Let Z x := f x - uE (A.filter fun y => g y = g x) f.
  set Z : Cube m → ℝ := fun x => f x - uE (A.filter fun y => g y = g x) f;
  have h_cauchy_schwarz : (∑ x ∈ A, |Z x|) ^ 2 ≤ A.card * ∑ x ∈ A, Z x ^ 2 := by
    have h_cauchy_schwarz : ∀ (s : Finset (Cube m)) (u v : Cube m → ℝ), (∑ x ∈ s, u x * v x) ^ 2 ≤ (∑ x ∈ s, u x ^ 2) * (∑ x ∈ s, v x ^ 2) :=
      fun s u v => Finset.sum_mul_sq_le_sq_mul_sq s u v;
    simpa using h_cauchy_schwarz A ( fun _ => 1 ) ( fun x => |Z x| );
  refine Real.le_sqrt_of_sq_le ?_;
  by_cases hA : A.Nonempty <;> simp_all +decide [ uE, uCondVar_eq_uE_fiber_sq ];
  rw [ div_pow, div_le_div_iff₀ ] <;> try positivity;
  convert mul_le_mul_of_nonneg_right h_cauchy_schwarz ( Nat.cast_nonneg A.card ) using 1 ; ring!

/-
Law of total variance (monotonicity): conditioning on a finer statistic `g`
(one that refines `h`) can only reduce the conditional variance.
-/
lemma uCondVar_le_of_refines {m : ℕ} {B C : Type*} [DecidableEq B] [DecidableEq C]
    (A : Finset (Cube m)) (f : Cube m → ℝ) (g : Cube m → B) (h : Cube m → C)
    (hA : A.Nonempty) (hgh : ∀ x y, g x = g y → h x = h y) :
    uCondVar A f g ≤ uCondVar A f h := by
  rw [ uCondVar_eq_uE_fiber_sq, uCondVar_eq_uE_fiber_sq ];
  refine' div_le_div_of_nonneg_right ( _ : _ ≤ _ ) ( Nat.cast_nonneg A.card );
  have h_sum_sq_le : ∀ b ∈ A.image g, ∑ x ∈ A.filter (fun y => g y = b), (f x - uE (A.filter (fun y => g y = b)) f) ^ 2 ≤ ∑ x ∈ A.filter (fun y => g y = b), (f x - uE (A.filter (fun y => h y = h x)) f) ^ 2 := by
    intro b hb
    have h_const : ∀ x ∈ A.filter (fun y => g y = b), uE (A.filter (fun y => h y = h x)) f = uE (A.filter (fun y => h y = h (Classical.choose (Finset.mem_image.mp hb))) ) f := by
      intro x hx
      have h_const : h x = h (Classical.choose (Finset.mem_image.mp hb)) := by
        grind
      simp [h_const];
    have h_sum_sq_le : ∀ S : Finset (Cube m), S.Nonempty → ∀ c : ℝ, ∑ x ∈ S, (f x - uE S f) ^ 2 ≤ ∑ x ∈ S, (f x - c) ^ 2 := by
      intro S hS c
      have h_sum_sq_le : ∑ x ∈ S, (f x - uE S f) ^ 2 = ∑ x ∈ S, (f x - c) ^ 2 - S.card * (uE S f - c) ^ 2 := by
        unfold uE; ring;
        simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sq, mul_assoc, mul_comm, mul_left_comm, hS.ne_empty ] ; ring;
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, hS.ne_empty ] ; ring;
      exact h_sum_sq_le ▸ sub_le_self _ ( mul_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) );
    convert h_sum_sq_le ( A.filter ( fun y => g y = b ) ) _ ( uE ( A.filter ( fun y => h y = h ( Classical.choose ( Finset.mem_image.mp hb ) ) ) ) f ) using 1;
    · exact Finset.sum_congr rfl fun x hx => by rw [ h_const x hx ] ;
    · exact Exists.elim ( Finset.mem_image.mp hb ) fun x hx => ⟨ x, Finset.mem_filter.mpr ⟨ hx.1, hx.2 ⟩ ⟩;
  convert Finset.sum_le_sum h_sum_sq_le using 1;
  · rw [ Finset.sum_image' ];
    intro x hx; congr! 2; aesop;
  · rw [ Finset.sum_image' ] ; aesop

/-
Offset averaging for the floor bins: over one period `[0,w)` the measure of
offsets that separate `a` and `b` into different bins is at most `|a-b|`.
-/
set_option maxHeartbeats 4000000 in
lemma offset_floor_bad_integral (a b w : ℝ) (hw : 0 < w) :
    (∫ o in Set.Ico (0:ℝ) w,
      (if Int.floor ((a - o) / w) ≠ Int.floor ((b - o) / w) then (1:ℝ) else 0))
      ≤ |a - b| := by
  -- Set for real c the function o ↦ ⌊(c-o)/w⌋. On o ∈ [0,w), the mismatch indicator `if ⌊(a-o)/w⌋ ≠ ⌊(b-o)/w⌋ then 1 else 0` is ≤ `|⌊(a-o)/w⌋ - ⌊(b-o)/w⌋|` (since distinct integers differ by ≥ 1).
  suffices h_suff : ∀ (a b w : ℝ), 0 < w → a ≥ b → ∫ o in Set.Ico 0 w, (max (⌊(a - o) / w⌋ - ⌊(b - o) / w⌋) 0 : ℝ) ≤ a - b by
    cases le_total a b <;> simp_all +decide [ abs_of_nonneg, abs_of_nonpos ];
    · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) ( h_suff b a w hw ‹_› );
      · exact Filter.Eventually.of_forall fun x => by positivity;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => 1 + |(b - x) / w - (a - x) / w|;
        · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.Ico_subset_Icc_self );
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with x hx;
          rw [ Real.norm_eq_abs, abs_le ];
          constructor <;> cases max_cases ( ⌊ ( b - x ) / w⌋ - ⌊ ( a - x ) / w⌋ : ℝ ) 0 <;> cases abs_cases ( ( b - x ) / w - ( a - x ) / w ) <;> linarith [ Int.floor_le ( ( b - x ) / w ), Int.lt_floor_add_one ( ( b - x ) / w ), Int.floor_le ( ( a - x ) / w ), Int.lt_floor_add_one ( ( a - x ) / w ) ];
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with o ho;
        split_ifs <;> norm_num;
        exact le_tsub_of_add_le_left ( mod_cast lt_of_le_of_ne ( Int.floor_mono <| by rw [ div_le_div_iff_of_pos_right hw ] ; linarith ) ‹_› );
    · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) ( h_suff a b w hw ‹_› );
      · exact Filter.Eventually.of_forall fun x => by positivity;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => ( a - b ) / w + 1;
        · norm_num;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with x hx;
          rw [ Real.norm_of_nonneg ] <;> norm_num;
          constructor <;> nlinarith [ Int.floor_le ( ( a - x ) / w ), Int.lt_floor_add_one ( ( a - x ) / w ), Int.floor_le ( ( b - x ) / w ), Int.lt_floor_add_one ( ( b - x ) / w ), mul_div_cancel₀ ( a - x ) hw.ne', mul_div_cancel₀ ( b - x ) hw.ne', mul_div_cancel₀ ( a - b ) hw.ne', hx.1, hx.2 ];
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with o ho ; split_ifs <;> norm_num;
        exact le_tsub_of_add_le_left ( mod_cast lt_of_le_of_ne ( Int.floor_mono <| by rw [ div_le_div_iff_of_pos_right hw ] ; linarith ) ( Ne.symm ‹_› ) );
  intros a b w hw hab
  have h_suff : ∫ o in Set.Ico 0 w, (max (⌊(a - o) / w⌋ - ⌊(b - o) / w⌋) 0 : ℝ) ≤ ∫ o in Set.Ico 0 w, ((a - o) / w - (b - o) / w) - (Int.fract ((a - o) / w) - Int.fract ((b - o) / w)) := by
    refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
    · exact Filter.Eventually.of_forall fun x => le_max_right _ _;
    · refine' MeasureTheory.Integrable.sub _ _;
      · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.Ico_subset_Icc_self );
      · refine' MeasureTheory.Integrable.sub _ _;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          exacts [ fun _ => 1, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.fract ( by exact Measurable.div_const ( measurable_const.sub measurable_id' ) _ ) ), Filter.Eventually.of_forall fun x => by simpa using abs_le.mpr ⟨ by linarith [ Int.fract_nonneg ( ( a - x ) / w ) ], by linarith [ Int.fract_lt_one ( ( a - x ) / w ) ] ⟩ ];
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          exacts [ fun _ => 1, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.fract ( by exact Measurable.div_const ( measurable_const.sub measurable_id' ) _ ) ), Filter.Eventually.of_forall fun x => by simpa [ abs_of_nonneg ] using Int.fract_lt_one _ |> le_of_lt ];
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with o ho using by rw [ max_eq_left ( sub_nonneg_of_le <| mod_cast Int.floor_mono <| by gcongr ) ] ; linarith [ Int.fract_add_floor ( ( a - o ) / w ), Int.fract_add_floor ( ( b - o ) / w ) ] ;
  -- The integral of the fractional part function over [0, w) is w/2.
  have h_fract_integral : ∀ (c : ℝ), ∫ o in Set.Ico 0 w, Int.fract ((c - o) / w) = w / 2 := by
    intro c
    have h_fract_integral : ∫ o in Set.Ico 0 w, Int.fract ((c - o) / w) = ∫ o in Set.Ico 0 w, Int.fract (o / w) := by
      have h_fract_integral : ∫ o in Set.Ico 0 w, Int.fract ((c - o) / w) = ∫ o in (c / w - 1)..c / w, Int.fract o * w := by
        rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ];
        · rw [ intervalIntegral.integral_comp_sub_left fun x => Int.fract ( x / w ) ] ; norm_num [ hw.ne', mul_comm w ];
          grind;
        · positivity;
      have h_fract_integral : ∫ o in (c / w - 1)..c / w, Int.fract o * w = ∫ o in (0 : ℝ)..1, Int.fract o * w := by
        have h_fract_integral : ∫ o in (c / w - 1)..c / w, Int.fract o * w = (∫ o in (c / w - 1)..0, Int.fract o * w) + (∫ o in (0)..c / w, Int.fract o * w) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => w;
            · exact Continuous.integrableOn_Icc ( by continuity );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fract ) measurable_const );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x ] ;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => w;
            · exact Continuous.integrableOn_Icc ( by continuity );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fract ) measurable_const );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x ] ;
        have h_fract_integral : ∫ o in (c / w - 1)..0, Int.fract o * w = ∫ o in (c / w)..1, Int.fract o * w := by
          convert intervalIntegral.integral_comp_add_right _ 1 using 2 <;> norm_num;
        rw [ ‹∫ o in c / w - 1..c / w, Int.fract o * w = _›, h_fract_integral ];
        rw [ add_comm, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun x => w;
          · exact Continuous.integrableOn_Icc ( by continuity );
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fract ) measurable_const );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x ] ;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun x => w;
          · exact Continuous.integrableOn_Icc ( by continuity );
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fract ) measurable_const );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x ] ;
      convert h_fract_integral using 1;
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hw.le ] ; simp +decide [ div_eq_inv_mul, intervalIntegral.integral_comp_mul_left, hw.ne' ] ; ring;
    -- The integral of the fractional part function over [0, w) is w/2 because it is periodic with period w.
    have h_fract_integral : ∫ o in Set.Ico 0 w, Int.fract (o / w) = ∫ o in Set.Ico 0 1, Int.fract o * w := by
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, ← MeasureTheory.integral_Icc_eq_integral_Ico ] ; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc ] ; rw [ ← intervalIntegral.integral_of_le ( by linarith ), ← intervalIntegral.integral_of_le ( by linarith ) ] ; simp +decide [ div_eq_inv_mul, intervalIntegral.integral_comp_mul_left, hw.ne' ] ; ring;
    rw [ ‹∫ o in Set.Ico 0 w, Int.fract ( ( c - o ) / w ) = ∫ o in Set.Ico 0 w, Int.fract ( o / w ) ›, h_fract_integral ];
    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ico fun x hx => by rw [ Int.fract ] ];
    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ico fun x hx => by rw [ show ⌊x⌋ = 0 from Int.floor_eq_iff.mpr ⟨ by norm_num; linarith [ hx.1 ], by norm_num; linarith [ hx.2 ] ⟩ ] ] ; norm_num [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] ; ring;
  rw [ MeasureTheory.integral_sub, MeasureTheory.integral_sub ] at h_suff;
  · rw [ MeasureTheory.integral_sub ] at h_suff;
    · simp_all +decide [ sub_div ];
      convert h_suff using 1 ; norm_num [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hw.le ] ; ring;
      norm_num [ hw.ne' ];
    · exact ( by have := h_fract_integral a; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; linarith ) );
    · exact ( by have := h_fract_integral b; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; linarith ) );
  · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.Ico_subset_Icc_self );
  · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.Ico_subset_Icc_self );
  · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ico_subset_Icc_self;
  · refine' MeasureTheory.Integrable.sub _ _;
    · exact ( by have := h_fract_integral a; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; linarith ) );
    · exact ( by have := h_fract_integral b; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; linarith ) )

/-
Reindexing `J ↔ insert t J` produces the `1/p` factor: the full-coordinate
sum is bounded by `1/p` times the in-window sum.
-/
lemma windowProb_reindex_le (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (φ : Finset (Fin m) → Fin m → ℝ)
    (hφ : ∀ (J : Finset (Fin m)) (t : Fin m), t ∉ J → φ J t = φ (insert t J) t)
    (hφnn : ∀ J t, 0 ≤ φ J t) :
    (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, φ J t)
      ≤ (1 / p) * ∑ J : Finset (Fin m), windowProb J p * ∑ t ∈ J, φ J t := by
  -- Apply the reindexing step to the sum over $J$ where $t \notin J$.
  have h_reindex_step : ∀ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * φ J t = ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * ((1 - p) / p) * φ J t := by
    intro t
    apply Finset.sum_bij (fun J _ => insert t J);
    · grind;
    · simp +contextual [ Finset.ext_iff ];
      grind;
    · exact fun J hJ => ⟨ J.erase t, by aesop ⟩;
    · intro J hJ; rw [ hφ J t ( by simpa using hJ ) ] ; simp +decide [ windowProb, Finset.card_insert_of_notMem ( by simpa using hJ ) ] ; ring;
      field_simp;
      exact Or.inl ( by rw [ ← pow_succ', show m - J.card = m - ( 1 + J.card ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 + J.card ≤ m from by linarith [ show J.card < m from lt_of_lt_of_le ( Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ J, by aesop_cat ⟩ ) ( by simpa ) ] ] ] );
  -- Apply the reindexing step to each term in the sum over $t$.
  have h_sum_reindex : ∑ J, windowProb J p * ∑ t, φ J t = ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * φ J t + ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * φ J t := by
    simp +decide only [Finset.mul_sum _ _ _, ← Finset.sum_add_distrib];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_filter_add_sum_filter_not ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, ne_of_gt hp0 ];
  simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_comm, h_reindex_step ];
  rw [ show ( ∑ x : Finset ( Fin m ), ( ∑ t ∈ x, φ x t ) * windowProb x p ) = ∑ t : Fin m, ∑ x with t ∈ x, φ x t * windowProb x p from ?_ ];
  · field_simp;
    norm_num;
  · simp +decide only [Finset.sum_mul _ _ _, Finset.sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-
Averaging: if the integral of `f` over `[0,w)` is at most `w·C`, some point of
`[0,w)` has value at most `C`.
-/
lemma exists_offset_le_of_setIntegral_le (w C : ℝ) (hw : 0 < w) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f (Set.Ico 0 w))
    (hle : (∫ o in Set.Ico (0:ℝ) w, f o) ≤ w * C) :
    ∃ o : ℝ, 0 ≤ o ∧ o < w ∧ f o ≤ C := by
  by_contra h_contra
  push_neg at h_contra
  have h_int_pos : 0 < ∫ o in Set.Ico 0 w, (f o - C) := by
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp +zetaDelta at *;
      exact lt_of_lt_of_le ( by simpa [ hw ] ) ( MeasureTheory.measure_mono ( show Set.Ico 0 w ⊆ ( Function.support fun o => f o - C ) ∩ Set.Ico 0 w from fun x hx => ⟨ ne_of_gt ( sub_pos.mpr ( h_contra x hx.1 hx.2 ) ), hx ⟩ ) );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with o ho using sub_nonneg_of_le <| le_of_lt <| h_contra o ho.1 ho.2;
    · exact hf.sub ( MeasureTheory.integrable_const C );
  rw [ MeasureTheory.integral_sub hf ] at h_int_pos <;> norm_num at *;
  rw [ max_eq_left hw.le ] at h_int_pos ; linarith

/-
The offset-averaged variance sum is controlled by the variance budget with a
`1/p` overhead plus an exponentially small tail.
-/
lemma s4_avg_variance_bound (m : ℕ) (A : Finset (Cube m)) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) (hA : A.Nonempty)
    (V : ℝ) (hV : 0 ≤ V) (hvar : varianceBudgetLE A (p / 2) V) :
    (∑ J : Finset (Fin m), windowProb J p *
        ∑ t : Fin m,
          uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj J))
      ≤ V / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8) := by
  refine' le_trans ( Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun t _ => _ ) ( _ ) ) _;
  use fun J t => uCondVar A ( fun x => rho A t ( proj ( below Finset.univ t ) x ) ) ( proj ( below J t ) );
  · apply_rules [ uCondVar_le_of_refines ];
    intro x y hxy; ext i; simp_all +decide [ Finset.ext_iff, proj ] ;
    exact fun hi => hxy i ( Finset.mem_of_mem_filter _ hi );
  · exact windowProb_nonneg J p ( by linarith ) ( by linarith );
  · refine' le_trans ( windowProb_reindex_le m p hp0 ( by linarith ) _ _ _ ) _;
    · simp +decide [ Finset.filter_insert, below ];
    · intro J t; exact (by
      refine' Finset.sum_nonneg fun x hx => _;
      refine' mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( div_nonneg ( _ ) ( Nat.cast_nonneg _ ) );
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _);
    · -- Apply the variance budget bound to the sum over the range set.
      have h_range : (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => (p * (m : ℝ) / 2 ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ 2 * p * (m : ℝ))), windowProb J p * (∑ t ∈ J, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below J t)))) ≤ V := by
        refine' le_trans ( Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left ( hvar J _ _ ) ( windowProb_nonneg J p ( by linarith ) ( by linarith ) ) ) _;
        · grind;
        · nlinarith [ show ( J.card : ℝ ) ≤ 2 * p * m by exact_mod_cast Finset.mem_filter.mp hJ |>.2.2 ];
        · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( windowProb_nonneg _ _ ( by linarith ) ( by linarith ) ) hV ) _;
          rw [ ← Finset.sum_mul _ _ _, sum_windowProb_eq_one_univ m p hp0 ( by linarith ) ] ; norm_num;
      -- Apply the variance budget bound to the sum over the complement set.
      have h_complement : (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => ¬(p * (m : ℝ) / 2 ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ 2 * p * (m : ℝ))), windowProb J p * (∑ t ∈ J, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below J t)))) ≤ m * (2 * Real.exp (-p * (m : ℝ) / 8)) := by
        refine' le_trans ( Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun t ht => _ ) ( windowProb_nonneg J p ( by positivity ) ( by linarith ) ) ) _;
        use fun J t => 1;
        · -- Since the variance of a [0,1]-valued random variable is at most 1, we have uCondVar A g_t (proj (below J t)) ≤ 1.
          have h_var_le_one : ∀ (f : Cube m → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → uCondVar A f (proj (below J t)) ≤ 1 := by
            intros f hf
            have h_var_le_one : ∀ (x : Cube m), (f x - uE (A.filter (fun y => proj (below J t) y = proj (below J t) x)) f) ^ 2 ≤ 1 := by
              intros x
              have h_avg_bounds : 0 ≤ uE (A.filter (fun y => proj (below J t) y = proj (below J t) x)) f ∧ uE (A.filter (fun y => proj (below J t) y = proj (below J t) x)) f ≤ 1 := by
                exact ⟨ div_nonneg ( Finset.sum_nonneg fun _ _ => hf _ |>.1 ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ ( le_trans ( Finset.sum_le_sum fun _ _ => hf _ |>.2 ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ⟩;
              nlinarith only [ hf x, h_avg_bounds ];
            rw [ uCondVar_eq_uE_fiber_sq ];
            exact le_trans ( div_le_div_of_nonneg_right ( Finset.sum_le_sum fun _ _ => h_var_le_one _ ) ( Nat.cast_nonneg _ ) ) ( by norm_num [ hA.ne_empty ] );
          exact h_var_le_one _ fun x => ⟨ rho_nonneg _ _ _, rho_le_one _ _ _ ⟩;
        · refine' le_trans ( Finset.sum_le_sum fun J hJ => mul_le_mul_of_nonneg_left ( show ( ∑ i ∈ J, 1 : ℝ ) ≤ m by simpa using Finset.card_le_univ J ) ( windowProb_nonneg J p ( by positivity ) ( by linarith ) ) ) _;
          convert mul_le_mul_of_nonneg_left ( windowProb_tail_bound m p hp0 ( by linarith ) ) ( Nat.cast_nonneg m ) using 1 ; ring;
          rw [ Finset.mul_sum _ _ _ ];
      convert mul_le_mul_of_nonneg_left ( add_le_add h_range h_complement ) ( one_div_nonneg.mpr hp0.le ) using 1 ; ring;
      · rw [ ← mul_add, Finset.sum_filter_add_sum_filter_not ];
      · ring

/-
The per-offset expected estimator error is integrable on `[0,w)`.
-/
lemma s4_error_integrableOn (m : ℕ) (A : Finset (Cube m)) (w p : ℝ) :
    MeasureTheory.IntegrableOn
      (fun o => expectedEstimatorError A (binnedFoldField A w o)
        (s4_canonicalEstimator m A w o) p)
      (Set.Ico (0 : ℝ) w) := by
  by_contra h;
  have h_measurable : Measurable (fun o => expectedEstimatorError A (binnedFoldField A w o) (s4_canonicalEstimator m A w o) p) := by
    refine' Finset.measurable_sum _ fun J _ => Measurable.mul _ _;
    · exact measurable_const;
    · refine' Measurable.div_const _ _;
      refine' Finset.measurable_sum _ fun x _ => _;
      refine' Measurable.comp ( show Measurable ( fun n : ℕ => ( n : ℝ ) ) from by measurability ) _;
      simp +decide [ binnedFoldField, s4_canonicalEstimator ];
      simp +decide only [Finset.card_filter];
      refine' Finset.measurable_sum _ fun i _ => _;
      refine' Measurable.ite _ measurable_const measurable_const;
      simp +zetaDelta at *;
      exact MeasurableSet.mem ( MeasurableSet.compl ( measurableSet_eq_fun ( by measurability ) ( by measurability ) ) );
  have h_bounded : ∃ C, ∀ o ∈ Set.Ico 0 w, |expectedEstimatorError A (binnedFoldField A w o) (s4_canonicalEstimator m A w o) p| ≤ C := by
    refine' ⟨ ∑ J : Finset ( Fin m ), |windowProb J p| * m, fun o ho => _ ⟩;
    refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun J _ => _ );
    rw [ abs_mul ];
    gcongr;
    rw [ abs_of_nonneg ( by exact div_nonneg ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ];
    refine' le_trans ( div_le_div_of_nonneg_right ( Finset.sum_le_sum fun x hx => Nat.cast_le.mpr <| Finset.card_le_univ _ ) <| Nat.cast_nonneg _ ) _ ; norm_num;
    by_cases hA : A = ∅ <;> simp_all +decide [ mul_div_cancel_left₀ ];
  obtain ⟨ C, hC ⟩ := h_bounded;
  refine' h ( MeasureTheory.Integrable.mono' _ _ _ );
  exacts [ fun _ => C, by norm_num, h_measurable.aestronglyMeasurable, Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ico ) fun x hx => hC x hx ]

set_option maxHeartbeats 4000000 in
/-- The integral over one offset period of the expected estimator error is at
most `sqrt` of the budget expression. -/
lemma s4_integral_error_bound (m : ℕ) (A : Finset (Cube m)) (w p : ℝ)
    (hw : 0 < w) (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) (hA : A.Nonempty)
    (V : ℝ) (hV : 0 ≤ V) (hvar : varianceBudgetLE A (p / 2) V) :
    (∫ o in Set.Ico (0 : ℝ) w,
        expectedEstimatorError A (binnedFoldField A w o)
          (s4_canonicalEstimator m A w o) p)
      ≤ Real.sqrt ((V / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)) := by
  have h_integral_bound : ∫ o in Set.Ico (0 : ℝ) w, expectedEstimatorError A (binnedFoldField A w o) (s4_canonicalEstimator m A w o) p ≤ ∑ J : Finset (Fin m), windowProb J p * Real.sqrt ((m : ℝ) * (∑ t : Fin m, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj J))) := by
    have h_integral_bound : ∫ o in Set.Ico (0 : ℝ) w, expectedEstimatorError A (binnedFoldField A w o) (s4_canonicalEstimator m A w o) p ≤ ∑ J : Finset (Fin m), windowProb J p * ((∑ x ∈ A, ∑ t : Fin m, |(rho A t (proj (below Finset.univ t) x)) - uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y))|) / A.card) := by
      have h_integral_bound : ∀ J : Finset (Fin m), ∫ o in Set.Ico (0 : ℝ) w, uE A (fun x => ((Finset.univ.filter fun t => binnedFoldField A w o x t ≠ s4_canonicalEstimator m A w o J x t).card : ℝ)) ≤ (∑ x ∈ A, ∑ t : Fin m, |(rho A t (proj (below Finset.univ t) x)) - uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y))|) / A.card := by
        intro J
        have h_integral_bound : ∫ o in Set.Ico (0 : ℝ) w, ∑ x ∈ A, ∑ t : Fin m, (if binnedFoldField A w o x t ≠ s4_canonicalEstimator m A w o J x t then (1 : ℝ) else 0) ≤ ∑ x ∈ A, ∑ t : Fin m, ∫ o in Set.Ico (0 : ℝ) w, (if binnedFoldField A w o x t ≠ s4_canonicalEstimator m A w o J x t then (1 : ℝ) else 0) := by
          rw [ MeasureTheory.integral_finset_sum ];
          · refine' Finset.sum_le_sum fun x hx => _;
            rw [ MeasureTheory.integral_finset_sum ];
            intro i hi;
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun _ => 1;
            · norm_num;
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.ite _ measurable_const measurable_const;
              refine' MeasurableSet.compl _;
              refine' measurableSet_eq_fun _ _;
              · exact Measurable.floor ( Measurable.div_const ( measurable_const.sub measurable_id' ) _ );
              · refine' Measurable.comp ( show Measurable ( fun a : ℝ => Int.floor a ) from _ ) _;
                · exact Measurable.floor measurable_id;
                · exact Measurable.mul ( measurable_const.sub measurable_id' ) measurable_const;
            · exact Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num;
          · intro x hx;
            refine' MeasureTheory.integrable_finset_sum _ _;
            intro t ht;
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun o => 1;
            · norm_num;
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.ite _ measurable_const measurable_const;
              refine' MeasurableSet.compl _;
              refine' measurableSet_eq_fun _ _;
              · exact Measurable.floor ( Measurable.div_const ( measurable_const.sub measurable_id' ) _ );
              · refine' Measurable.comp ( show Measurable ( fun a : ℝ => Int.floor a ) from _ ) _;
                · exact Measurable.floor measurable_id;
                · exact Measurable.mul ( measurable_const.sub measurable_id' ) measurable_const;
            · exact Filter.Eventually.of_forall fun o => by split_ifs <;> norm_num;
        have h_pointwise : ∀ x ∈ A, ∀ t : Fin m, ∫ o in Set.Ico (0 : ℝ) w, (if binnedFoldField A w o x t ≠ s4_canonicalEstimator m A w o J x t then (1 : ℝ) else 0) ≤ |(rho A t (proj (below Finset.univ t) x)) - uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y))| := by
          intros x hx t
          have h_off : ∫ o in Set.Ico (0 : ℝ) w, (if Int.floor ((fold (rho A t (proj (below Finset.univ t) x)) - o) / w) ≠ Int.floor ((fold (uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y))) - o) / w) then (1 : ℝ) else 0) ≤ |fold (rho A t (proj (below Finset.univ t) x)) - fold (uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y)))| := by
            apply offset_floor_bad_integral;
            exact hw;
          convert h_off.trans ( fold_sub_abs_le _ _ ) using 1;
        convert div_le_div_of_nonneg_right ( le_trans ‹_› ( Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun t ht => h_pointwise x hx t ) ) ( Nat.cast_nonneg A.card ) using 1;
        rw [ ← MeasureTheory.integral_div ] ; congr ; ext ; simp +decide [ uE ] ;
        simp +decide [ Finset.sum_ite ];
      refine' le_trans _ ( Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left ( h_integral_bound J ) ( _ ) );
      · rw [ ← Finset.sum_congr rfl fun _ _ => MeasureTheory.integral_const_mul _ _ ];
        rw [ ← MeasureTheory.integral_finset_sum ];
        · unfold expectedEstimatorError; norm_num [ Finset.sum_mul _ _ _ ] ;
          grind;
        · intro J _; apply_rules [ MeasureTheory.Integrable.const_mul, MeasureTheory.integrable_const ] ;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun o => ( m : ℝ );
          · norm_num;
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.div_const _ _;
            refine' Finset.measurable_sum _ fun x _ => _;
            refine' Measurable.comp ( show Measurable ( fun n : ℕ => ( n : ℝ ) ) from by measurability ) _;
            simp +decide [ binnedFoldField, s4_canonicalEstimator ];
            simp +decide only [Finset.card_filter];
            refine' Finset.measurable_sum _ fun i _ => _;
            refine' Measurable.ite _ measurable_const measurable_const;
            simp +zetaDelta at *;
            fun_prop;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ico ] with o ho;
            rw [ Real.norm_of_nonneg ];
            · refine' le_trans ( div_le_div_of_nonneg_right ( Finset.sum_le_sum fun x hx => Nat.cast_le.mpr <| Finset.card_le_univ _ ) <| Nat.cast_nonneg _ ) _ ; norm_num;
              rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr hA.card_pos.ne' ) ];
            · exact div_nonneg ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
      · exact windowProb_nonneg J p hp0.le ( by linarith );
    refine le_trans h_integral_bound <| Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left ?_ <| ?_;
    · have h_inner : (∑ x ∈ A, ∑ t : Fin m, |(rho A t (proj (below Finset.univ t) x)) - uE (A.filter fun y => proj J y = proj J x) (fun y => rho A t (proj (below Finset.univ t) y))|) / A.card ≤ ∑ t : Fin m, Real.sqrt (uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj J)) := by
        rw [ Finset.sum_comm, Finset.sum_div ];
        exact Finset.sum_le_sum fun i _ => by simpa only [ uE ] using uE_abs_fiber_le_sqrt_uCondVar A ( fun x => rho A i ( proj ( below Finset.univ i ) x ) ) ( proj J ) ;
      refine le_trans h_inner ?_;
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin m)),
          0 ≤ uCondVar A (fun x => rho A i (proj (below Finset.univ i) x)) (proj J) := by
        intro i _
        rw [uCondVar_eq_uE_fiber_sq]
        exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
      have hcs := sum_sqrt_le_sqrt_card_mul_sum (Finset.univ : Finset (Fin m))
        (fun t => uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj J)) hnn
      simpa using hcs
    · exact windowProb_nonneg J p hp0.le ( by linarith );
  refine le_trans h_integral_bound ?_;
  have hjensen := @sum_weight_sqrt_le_sqrt_sum_weight ( Finset ( Fin m ) );
  specialize hjensen Finset.univ ( fun J => windowProb J p ) ( fun J => ( m : ℝ ) * ∑ t : Fin m, uCondVar A ( fun x => rho A t ( proj ( below Finset.univ t ) x ) ) ( proj J ) ) ; norm_num at *;
  refine le_trans ( hjensen ( fun _ => by
    exact windowProb_nonneg _ _ hp0.le ( by linarith ) ) ( fun _ => by
    refine' mul_nonneg ( Nat.cast_nonneg _ ) ( Finset.sum_nonneg fun _ _ => _ );
    unfold uCondVar;
    refine' Finset.sum_nonneg fun _ _ => mul_nonneg _ _ <;> norm_num [ pOn, varOn ];
    · positivity;
    · exact div_nonneg ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( by
    exact sum_windowProb_eq_one p hp0.le ( by linarith ) ) ) ?_;
  rw [ ← Real.sqrt_mul' ];
  · refine Real.sqrt_le_sqrt ?_;
    convert mul_le_mul_of_nonneg_right ( s4_avg_variance_bound m A p hp0 ( by linarith ) hA V hV hvar ) ( Nat.cast_nonneg m ) using 1;
    · simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm, mul_assoc];
    · ring;
  · positivity

lemma s4_canonicalEstimator_expectedError (m : ℕ) (A : Finset (Cube m)) (w p : ℝ)
    (hw : 0 < w) (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (vFam : ℝ → ℕ → ℝ)
    (hv_nonneg : 0 ≤ vFam (p / 2) m)
    (hA : A.Nonempty)
    (hvar : varianceBudgetLE A (p / 2) (vFam (p / 2) m)) :
    ∃ o : ℝ, 0 ≤ o ∧ o < w ∧
      expectedEstimatorError A (binnedFoldField A w o) (s4_canonicalEstimator m A w o) p ≤
        s4_errorBound w vFam p m := by
  refine exists_offset_le_of_setIntegral_le w (s4_errorBound w vFam p m) hw
    (fun o => expectedEstimatorError A (binnedFoldField A w o)
      (s4_canonicalEstimator m A w o) p)
    (s4_error_integrableOn m A w p) ?_
  have hb := s4_integral_error_bound m A w p hw hp0 hp1 hA (vFam (p / 2) m) hv_nonneg hvar
  have hbridge : w * s4_errorBound w vFam p m
      = Real.sqrt ((vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8))
          * (m : ℝ)) := by
    unfold s4_errorBound
    simp only
    rw [Real.sqrt_eq_rpow]
    field_simp
  rw [hbridge]
  exact hb

lemma s4_offset_exists (m : ℕ) (A : Finset (Cube m)) (w p : ℝ)
    (hw : 0 < w) (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (vFam : ℝ → ℕ → ℝ)
    (hv_nonneg : 0 ≤ vFam (p / 2) m)
    (hA : A.Nonempty)
    (hvar : varianceBudgetLE A (p / 2) (vFam (p / 2) m)) :
    ∃ o : ℝ, 0 ≤ o ∧ o < w ∧
      ∃ G : Finset (Fin m) → Cube m → Fin m → ℤ,
        (∀ J : Finset (Fin m), dependsOnWindow J (G J)) ∧
        expectedEstimatorError A (binnedFoldField A w o) G p ≤
          s4_errorBound w vFam p m := by
  obtain ⟨o, ho1, ho2, ho3⟩ := s4_canonicalEstimator_expectedError m A w p hw hp0 hp1 vFam hv_nonneg hA hvar
  exact ⟨o, ho1, ho2, s4_canonicalEstimator m A w o, s4_canonicalEstimator_dependsOnWindow m A w o, ho3⟩

lemma int_floor_Icc_card_le (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc (Int.floor a) (Int.floor b)).card : ℝ) ≤ b - a + 2 := by
  have hle_floor : Int.floor a ≤ Int.floor b := Int.floor_le_floor hab
  have hcard_int :=
    Int.card_Icc_of_le (a := Int.floor a) (b := Int.floor b) (by omega)
  have hcard_real : ((Finset.Icc (Int.floor a) (Int.floor b)).card : ℝ) =
      ((Int.floor b + 1 - Int.floor a : ℤ) : ℝ) := by
    exact_mod_cast hcard_int
  rw [hcard_real]
  have hb : ((Int.floor b : ℤ) : ℝ) ≤ b := Int.floor_le b
  have ha : a - 1 < ((Int.floor a : ℤ) : ℝ) := Int.sub_one_lt_floor a
  norm_num
  linarith

lemma fold_rho_bounds (m : ℕ) (A : Finset (Cube m)) (t : Fin m) (u : Cube m) :
    0 ≤ fold (rho A t u) ∧ fold (rho A t u) ≤ (1 / 2 : ℝ) := by
  have h0 : 0 ≤ rho A t u := rho_nonneg A t u
  have h1 : rho A t u ≤ 1 := rho_le_one A t u
  constructor
  · unfold fold
    exact le_min h0 (by linarith)
  · unfold fold
    by_cases hhalf : rho A t u ≤ (1 / 2 : ℝ)
    · exact (min_le_left _ _).trans hhalf
    · have hge : (1 / 2 : ℝ) ≤ rho A t u := le_of_not_ge hhalf
      have hright : 1 - rho A t u ≤ (1 / 2 : ℝ) := by linarith
      exact (min_le_right _ _).trans hright

lemma s4_binnedFoldField_size (m : ℕ) (A : Finset (Cube m)) (w o : ℝ) (hw : 0 < w) (t : Fin m) :
    ((A.image fun x => binnedFoldField A w o x t).card : ℝ) ≤ max 1 (1 / w + 2) := by
  let lo : ℤ := Int.floor ((0 - o) / w)
  let hi : ℤ := Int.floor (((1 / 2 : ℝ) - o) / w)
  have hsubset : (A.image fun x => binnedFoldField A w o x t) ⊆ Finset.Icc lo hi := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
    dsimp [binnedFoldField, lo, hi]
    rw [Finset.mem_Icc]
    have hbounds :=
      fold_rho_bounds m A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
    have hlow :
        (0 - o) / w ≤
          (fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - o) / w := by
      exact div_le_div_of_nonneg_right (by linarith [hbounds.1]) (le_of_lt hw)
    have hhigh :
        (fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - o) / w ≤
          ((1 / 2 : ℝ) - o) / w := by
      exact div_le_div_of_nonneg_right (by linarith [hbounds.2]) (le_of_lt hw)
    exact ⟨Int.floor_le_floor hlow, Int.floor_le_floor hhigh⟩
  have hcard_le : ((A.image fun x => binnedFoldField A w o x t).card : ℝ) ≤
      ((Finset.Icc lo hi).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hab : (0 - o) / w ≤ ((1 / 2 : ℝ) - o) / w := by
    exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hw)
  have hIcc := int_floor_Icc_card_le ((0 - o) / w) (((1 / 2 : ℝ) - o) / w) hab
  have hspan : ((Finset.Icc lo hi).card : ℝ) ≤ 1 / w + 2 := by
    dsimp [lo, hi]
    calc
      ((Finset.Icc (Int.floor ((0 - o) / w))
          (Int.floor (((1 / 2 : ℝ) - o) / w))).card : ℝ)
          ≤ ((1 / 2 : ℝ) - o) / w - (0 - o) / w + 2 := hIcc
      _ = 1 / (2 * w) + 2 := by
            field_simp [hw.ne']
            ring
      _ ≤ 1 / w + 2 := by
            have hinv_nonneg : 0 ≤ 1 / w := by positivity
            have hhalf_eq : 1 / (2 * w) = (1 / w) / 2 := by
              field_simp [hw.ne']
            rw [hhalf_eq]
            nlinarith
  exact hcard_le.trans (hspan.trans (le_max_right _ _))

lemma uH_proj_le_I_log_two (m : ℕ) (A : Finset (Cube m)) (hA : A.Nonempty) (I : Finset (Fin m)) :
    uH A (proj I) ≤ Real.log 2 * (I.card : ℝ) := by
  rw [uH_proj_chain A hA I]
  calc
    (∑ t ∈ I, uCondH A (coord t) (proj (below I t)))
        ≤ ∑ _t ∈ I, Real.log 2 := by
          exact Finset.sum_le_sum fun t _ =>
            uCondH_coord_le_log_two A hA t (proj (below I t))
    _ = Real.log 2 * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

/-- Analytic core of the S3 → S4 reduction (per instance, per density).

Using block regularity (with `kappa ≤ log 2` since binary entropy is bounded
by `log 2`), the per-density variance budget, and offset averaging to build a
window-computable estimator of the binned fold field, S3 yields for each fixed
density `p ∈ (0, 1/2]` an offset `o ∈ [0, w)` with
`uH A (binnedFoldField A w o) ≤ Sfam p m + 2 · log 2 · p · m`, where `Sfam` is
a density family that is `Sublinear` in `m` for every fixed `p` and does not
depend on `A` or `q` (all `A`-dependence is absorbed through the supplied
variance/block-regularity families). -/
lemma s4_analytic_core (w : ℝ) (hw : 0 < w) (hS3 : S3Statement)
    (sFam vFam : ℝ → ℕ → ℝ)
    (hsF : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow))
    (hvF : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow)) :
    ∃ Sfam : ℝ → ℕ → ℝ,
      (∀ p : ℝ, 0 < p → p ≤ 1 / 2 → Sublinear (Sfam p)) ∧
      ∀ (m : ℕ) (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty →
        blockRegularFamily m A q sFam →
        (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
          varianceBudgetLE A pLow (vFam pLow m)) →
        ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
          ∃ o : ℝ, 0 ≤ o ∧ o < w ∧
            uH A (binnedFoldField A w o) ≤
              Sfam p m + 2 * Real.log 2 * p * (m : ℝ) := by
  use s4_Sfam w sFam vFam
  constructor
  · intro p hp0 hp1
    exact s4_Sfam_sublinear w hw sFam vFam hsF hvF p hp0 hp1
  · intro m A q hA hBR hVar p hp0 hp1
    let pUse := s4_pUse p
    have hpUse0 : 0 < pUse := by
      dsimp [pUse, s4_pUse]
      exact lt_min hp0 (by norm_num)
    have hpUse_third : pUse ≤ 1 / 3 := by
      dsimp [pUse, s4_pUse]
      exact min_le_right _ _
    have hpUse_half : pUse ≤ 1 / 2 := hpUse_third.trans (by norm_num)
    have hpUse_le_p : pUse ≤ p := by
      dsimp [pUse, s4_pUse]
      exact min_le_left _ _
    have hpLow0 : 0 < pUse / 2 := by linarith
    have hpLow1 : pUse / 2 ≤ 1 / 2 := by linarith
    have hvar_p := hVar (pUse / 2) hpLow0 hpLow1
    have hv_nonneg : 0 ≤ vFam (pUse / 2) m := (hvF (pUse / 2) hpLow0 hpLow1).1 m
    rcases s4_offset_exists m A w pUse hw hpUse0 hpUse_third vFam hv_nonneg hA hvar_p with
      ⟨o, ho_nonneg, ho_lt, G, hG_dep, hG_err⟩
    use o
    refine ⟨ho_nonneg, ho_lt, ?_⟩
    let e := s4_errorBound w vFam pUse m
    let BSize := max 1 (1 / w + 2)
    have he_nonneg : 0 ≤ e := by
      let pLow := pUse / 2
      have hv_nonneg : 0 ≤ vFam pLow m := (hvF pLow hpLow0 hpLow1).1 m
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      have htail_nonneg :
          0 ≤ 2 * (m : ℝ) / pUse * Real.exp (-pUse * (m : ℝ) / 8) := by
        positivity
      have hbase_nonneg :
          0 ≤ vFam pLow m / pUse +
            2 * (m : ℝ) / pUse * Real.exp (-pUse * (m : ℝ) / 8) := by
        have hmain_nonneg : 0 ≤ vFam pLow m / pUse := div_nonneg hv_nonneg hpUse0.le
        linarith
      have hprod :
          0 ≤ (vFam pLow m / pUse +
            2 * (m : ℝ) / pUse * Real.exp (-pUse * (m : ℝ) / 8)) * (m : ℝ) :=
        mul_nonneg hbase_nonneg hm_nonneg
      have hpow :
          0 ≤ (((vFam pLow m / pUse +
            2 * (m : ℝ) / pUse * Real.exp (-pUse * (m : ℝ) / 8)) * (m : ℝ)) ^
              (1 / 2 : ℝ)) := Real.rpow_nonneg hprod _
      exact div_nonneg hpow (le_of_lt hw)
    have hBSize_ge_1 : 1 ≤ BSize := le_max_left 1 _
    have hkappa_nonneg : 0 ≤ Real.log 2 := by positivity
    have hs_nonneg : 0 ≤ (0 : ℝ) := by rfl
    have hS3_apply := hS3 m A (Real.log 2) 0 ℤ (binnedFoldField A w o) pUse e BSize
      hA hkappa_nonneg hs_nonneg hpUse0 hpUse_half he_nonneg hBSize_ge_1
      (by
        intro I hI_low hI_high
        have h_bound := uH_proj_le_I_log_two m A hA I
        linarith
      )
      (by convert s4_binnedFoldField_size m A w o hw)
      ⟨G, hG_dep, hG_err⟩
    have h_reorder :
        2 * Real.log 2 * pUse * ↑m + 0 +
            ↑m * H (min (e / ↑m) (1 / 2)) +
            e * Real.log BSize + 2 * ↑m * Real.exp (-pUse * ↑m / 8)
          = s4_Sfam w sFam vFam p m + 2 * Real.log 2 * pUse * ↑m := by
        dsimp [s4_Sfam, s4_pUse, s4_errorBound, e, BSize, pUse]
        ring
    have hS3_bound :
        uH A (binnedFoldField A w o) ≤
          s4_Sfam w sFam vFam p m + 2 * Real.log 2 * pUse * (m : ℝ) := by
      linarith [hS3_apply]
    have hp_term :
        2 * Real.log 2 * pUse * (m : ℝ) ≤ 2 * Real.log 2 * p * (m : ℝ) := by
      have hcoef : 0 ≤ 2 * Real.log 2 * (m : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hpUse_le_p hcoef
      nlinarith
    linarith

theorem S4_skeleton (_hS3 : S3Statement) : S4Statement := by
  intro w hw sFam vFam hsF hvF
  obtain ⟨Sfam, hSfam_sub, hSfam_bound⟩ :=
    s4_analytic_core w hw _hS3 sFam vFam hsF hvF
  have hc : (0 : ℝ) ≤ 2 * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  obtain ⟨env, P, henv, hP, hdom⟩ :=
    sublinear_diagonalize Sfam (2 * Real.log 2) hc hSfam_sub
  refine ⟨env, henv, ?_⟩
  intro m A q hA hbr hvar
  obtain ⟨o, ho0, how, hle⟩ :=
    hSfam_bound m A q hA hbr hvar (P m) (hP m).1 (hP m).2
  refine ⟨o, ho0, how, ?_⟩
  have hd := hdom m
  nlinarith [hle, hd]

end HarperStability