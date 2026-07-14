import HarperStability.Reductions.EffectiveR1
import HarperStability.Interface.EffectiveUniform

/-!
# Uniform R1a (v0.4)

Target: `R1aEffU` — peeling with a class-only constant.

Route: binder reshuffle of the CLOSED `r1a_eff` in
`Reductions/EffectiveR1.lean`: its final constant is
`K_final = K_hbl·C_R·16384 + K_hbl + L_eps + 1` where `K_hbl` comes from
the HBL hypothesis (class-only via `R2EffU`), `C_R` from the volume
calculus (class-only), and `L_eps = max 0 (-log epsCover)` — all available
BEFORE `sigma`.  The peeling recursion is `sigma`-pointwise.
Do NOT modify the frozen interfaces.
-/

namespace HarperStability

lemma effLog_le_sigma_uniform {K : ℝ} (hK : 0 ≤ K)
    {sigma : ℕ → ℝ} (hs : Sublinear sigma)
    (hlog : ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) :
    ∀ n, effLog K n ≤ max 1 (K * (Real.log 3 + 1)) * (sigma n + 1) := by
  intro n
  unfold effLog
  have hC : K * (Real.log 3 + 1) ≤ max 1 (K * (Real.log 3 + 1)) :=
    le_max_right 1 _
  have hsig_nn : 0 ≤ sigma n := hs.1 n
  have h_base :
      K * (Real.log ((n : ℝ) + 2) + 1) ≤
        K * (Real.log 3 + 1) * (sigma n + 1) := by
    by_cases hn : n = 0
    · subst hn
      have hlog23 : Real.log 2 ≤ Real.log 3 :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h_cast : (((0 : ℕ) : ℝ) + 2) = 2 := by norm_num
      rw [h_cast]
      have h2 : K * (Real.log 2 + 1) ≤ K * (Real.log 3 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      have h3 : K * (Real.log 3 + 1) ≤
          K * (Real.log 3 + 1) * (sigma 0 + 1) := by
        have h_pos : 0 ≤ K * (Real.log 3 + 1) := by positivity
        have h_ge1 : 1 ≤ sigma 0 + 1 := by linarith [hs.1 0]
        nlinarith
      exact le_trans h2 h3
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log (3 * (n : ℝ)) := by
        apply Real.log_le_log (by linarith)
        linarith
      have h2 : Real.log (3 * (n : ℝ)) = Real.log 3 + Real.log (n : ℝ) := by
        apply Real.log_mul (by norm_num) (by linarith)
      have h3 : Real.log (n : ℝ) ≤ sigma n := hlog n hn1
      have h4 : Real.log ((n : ℝ) + 2) + 1 ≤ Real.log 3 + 1 + sigma n := by
        linarith
      have h5 :
          K * (Real.log ((n : ℝ) + 2) + 1) ≤
            K * (Real.log 3 + 1 + sigma n) :=
        mul_le_mul_of_nonneg_left h4 hK
      have h6 :
          K * (Real.log 3 + 1 + sigma n) ≤
            K * (Real.log 3 + 1) * (sigma n + 1) := by
        have h_log3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        have h_pos : 0 ≤ K * sigma n := mul_nonneg hK hsig_nn
        have : 1 * (K * sigma n) ≤ (Real.log 3 + 1) * (K * sigma n) :=
          mul_le_mul_of_nonneg_right (by linarith) h_pos
        linarith
      exact le_trans h5 h6
  exact le_trans h_base (mul_le_mul_of_nonneg_right hC (by linarith))

private lemma rmin_monoU {n k1 k2 : ℕ} (h : k1 ≤ k2) : rmin n k1 ≤ rmin n k2 := by
  classical
  let vals1 := (Finset.range (n + 1)).filter fun r => k1 ≤ (ball (∅ : Cube n) r).card
  let vals2 := (Finset.range (n + 1)).filter fun r => k2 ≤ (ball (∅ : Cube n) r).card
  have hsubset : vals2 ⊆ vals1 := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hr'.1, le_trans h hr'.2⟩
  unfold rmin
  change (if h1 : vals1.Nonempty then vals1.min' h1 else n) ≤
    (if h2 : vals2.Nonempty then vals2.min' h2 else n)
  by_cases h2 : vals2.Nonempty
  · have h1 : vals1.Nonempty := by
      rcases h2 with ⟨r, hr⟩
      exact ⟨r, hsubset hr⟩
    rw [dif_pos h1, dif_pos h2]
    exact vals1.min'_le (vals2.min' h2) (hsubset (vals2.min'_mem h2))
  · rw [dif_neg h2]
    by_cases h1 : vals1.Nonempty
    · rw [dif_pos h1]
      exact Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp (vals1.min'_mem h1)).1)
    · rw [dif_neg h1]

private lemma coveredByBalls_mono_radiusU {n : ℕ} (S centers : Finset (Cube n))
    {radius radius' : ℕ} (hradius : radius ≤ radius') :
    coveredByBalls S centers radius ⊆ coveredByBalls S centers radius' := by
  intro x hx
  rcases (by simpa [coveredByBalls] using hx) with ⟨hxS, c, hc, hdist⟩
  exact (by
    simp [coveredByBalls, hxS]
    exact ⟨c, hc, le_trans hdist hradius⟩)

private lemma greedy_peel_coverU {n : ℕ} (S : Finset (Cube n)) (radius : ℕ)
    (δ thresh : ℝ) (hδ1 : δ ≤ 1)
    (hstep : ∀ R : Finset (Cube n), R ⊆ S → thresh ≤ (R.card : ℝ) →
        ∃ a : Cube n,
          δ * (R.card : ℝ) ≤
            ((R.filter fun x => hDist x a ≤ radius).card : ℝ)) :
    ∀ k : ℕ, ∃ centers : Finset (Cube n),
        centers.card ≤ k ∧
        ((S.card : ℝ) - ((coveredByBalls S centers radius).card : ℝ) ≤ thresh
          ∨ (S.card : ℝ) - ((coveredByBalls S centers radius).card : ℝ)
              ≤ (1 - δ) ^ k * (S.card : ℝ)) := by
  intro k;
  induction' k with k ih generalizing S;
  · unfold coveredByBalls; aesop;
  · obtain ⟨ centers, hcenters₁, hcenters₂ ⟩ := ih S hstep;
    by_cases h : (S.card : ℝ) - (coveredByBalls S centers radius).card ≤ thresh;
    · exact ⟨ centers, Nat.le_succ_of_le hcenters₁, Or.inl h ⟩;
    · obtain ⟨ a, ha ⟩ := hstep ( S \ coveredByBalls S centers radius ) ( Finset.sdiff_subset ) ( by
        rw [ Finset.card_sdiff ];
        rw [ Nat.cast_sub ];
        · rw [ Finset.inter_eq_left.mpr ];
          · linarith;
          · exact fun x hx => Finset.mem_filter.mp hx |>.1;
        · exact Finset.card_le_card fun x hx => by aesop; );
      refine' ⟨ Insert.insert a centers, _, _ ⟩ <;> simp_all +decide [ Finset.card_sdiff ];
      · exact Finset.card_insert_le _ _ |> le_trans <| Nat.succ_le_succ hcenters₁;
      · have h_covered : (coveredByBalls S (insert a centers) radius).card ≥ (coveredByBalls S centers radius).card + (Finset.filter (fun x => hDist x a ≤ radius) (S \ coveredByBalls S centers radius)).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · refine Finset.card_mono ?_;
            simp +decide [ Finset.subset_iff, coveredByBalls ];
            grind;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₂ |>.1 ) |>.2 hx₁;
        rw [ Nat.cast_sub ] at *;
        · rw [ show ( coveredByBalls S centers radius ∩ S : Finset ( Cube n ) ) = coveredByBalls S centers radius from Finset.inter_eq_left.mpr <| Finset.filter_subset _ _ ] at ha;
          exact Or.inr ( by rw [ pow_succ' ] ; nlinarith [ show ( Finset.card ( coveredByBalls S ( insert a centers ) radius ) : ℝ ) ≥ Finset.card ( coveredByBalls S centers radius ) + Finset.card ( Finset.filter ( fun x => hDist x a ≤ radius ) ( S \ coveredByBalls S centers radius ) ) by exact_mod_cast h_covered ] );
        · exact Finset.card_le_card fun x hx => by aesop;

/-- The uniform R1a envelope for a fixed `sigma`. -/
noncomputable def effUEnvelope (C_V K_vol C_dich cSize epsCover : ℝ) (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  sigma n + 2 * C_V * (cSize * sigma n - Real.log epsCover) + 2 * effLog K_vol n
    + C_dich * (sigma n + 1)

/-
Sublinearity of the uniform R1a envelope.
-/
lemma sublinear_effUEnvelope (C_V K_vol C_dich cSize epsCover : ℝ)
    (hC_V : 0 ≤ C_V) (hK_vol : 0 ≤ K_vol) (hC_dich : 0 ≤ C_dich) (hcSize : 0 ≤ cSize)
    (hepsCover : 0 < epsCover) (hepsCover_le : epsCover ≤ 1)
    (sigma : ℕ → ℝ) (hsigma : Sublinear sigma) :
    Sublinear (effUEnvelope C_V K_vol C_dich cSize epsCover sigma) := by
  apply Sublinear_add;
  · apply Sublinear_add;
    · apply Sublinear_add;
      · assumption;
      · convert Sublinear_add ( Sublinear_smul ( show 0 ≤ 2 * C_V * cSize by positivity ) hsigma ) ( Sublinear_const ( show 0 ≤ - ( 2 * C_V * Real.log epsCover ) by nlinarith [ Real.log_le_sub_one_of_pos hepsCover, mul_nonneg hC_V hcSize ] ) ) using 1 ; ext ; ring;
    · exact Sublinear_smul ( by norm_num ) ( sublinear_effLog hK_vol );
  · convert Sublinear_smul hC_dich ( Sublinear_add hsigma ( Sublinear_const zero_le_one ) ) using 1

/-
Near-optimal core for the uniform R1a envelope: given the volume calculus
`hcalc` at `(alphaMin, c0)` and the range-or-large-slack dichotomy `hdich`,
every large subset `R` of a class member `S` satisfies the near-optimal
neighbourhood bound with the envelope as slack.
-/
set_option maxHeartbeats 1000000 in
lemma r1a_nearOptimal_core
    (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ)
    (hcSize : 1 ≤ cSize) (halphaMax : alphaMax < 1 / 2)
    (hepsCover : 0 < epsCover) (hepsCover_le : epsCover ≤ 1)
    (C_V K_vol c0 C_dich : ℝ) (hC_V : 1 ≤ C_V) (hK_vol : 1 ≤ K_vol) (hC_dich : 1 ≤ C_dich)
    (sigma : ℕ → ℝ) (hsigma : Sublinear sigma)
    (hlog : ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n)
    (hcalc : ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 → 0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) → alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |Real.log ((V n k r : ℝ)) - H (alpha + beta) * (n : ℝ)| ≤
            C_V * sizeSlack + effLog K_vol n ∧
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K_vol n)
    (hdich : ∀ (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
        classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta →
        S.Nonempty →
        alpha + beta ≤ 1 / 2 - c0 ∨ (n : ℝ) * Real.log 2 ≤ C_dich * (sigma n + 1)) :
    ∀ (n r : ℕ) (S R : Finset (Cube n)) (alpha beta : ℝ),
      classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      ((neighborhood r R).card : ℝ) ≤
        Real.exp (effUEnvelope C_V K_vol C_dich cSize epsCover sigma n) * (V n R.card r : ℝ) := by
  -- Let's unfold the definition of `effUEnvelope`.
  intro n r S R alpha beta hmem hsub hlarge
  simp [HarperStability.effUEnvelope] at *;
  by_cases hSpos : 0 < S.card;
  · rcases hdich n r S alpha beta hmem ( Finset.card_pos.mp hSpos ) with ( h | h );
    · obtain ⟨hVS, _⟩ := hcalc n S.card r alpha beta (cSize * sigma n) (by
      exact hmem.2.2.1) (by
      linarith [ hmem.2.2.2.1 ]) (by
      exact mul_nonneg ( by linarith ) ( hsigma.1 n ) |> le_trans ( by norm_num )) (by
      exact hmem.2.1) h (by
      finiteness) (by
      exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Fintype.card_finset ] )) (by
      exact hmem.2.2.2.2.2.1);
      obtain ⟨hVR, _⟩ := hcalc n R.card r alpha beta (cSize * sigma n - Real.log epsCover) (by
      exact hmem.2.2.1) (by
      linarith [ hmem.2.2.2.1 ]) (by
      exact sub_nonneg_of_le ( by nlinarith [ Real.log_nonpos hepsCover.le hepsCover_le, show 0 ≤ sigma n from hsigma.1 n ] )) (by
      exact hmem.2.1) h (by
      exact Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at hlarge; linarith [ show ( 0 : ℝ ) < epsCover * S.card by positivity ] )) (by
      exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Finset.card_univ ] )) (by
      apply r1a_subset_sizeHyp hepsCover hepsCover_le hsub hlarge hmem.2.2.2.2.2.1);
      have hlog_le : Real.log (V n S.card r) ≤ (2 * C_V * (cSize * sigma n - Real.log epsCover) + 2 * effLog K_vol n) + Real.log (V n R.card r) := by
        nlinarith [ abs_le.mp hVS, abs_le.mp hVR, Real.log_nonpos hepsCover.le hepsCover_le, show 0 ≤ cSize * sigma n from mul_nonneg ( by positivity ) ( hsigma.1 n ), show 0 ≤ effLog K_vol n from mul_nonneg ( by positivity ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_one ) ];
      have hVcompare : (V n S.card r : ℝ) ≤ Real.exp (2 * C_V * (cSize * sigma n - Real.log epsCover) + 2 * effLog K_vol n) * (V n R.card r : ℝ) := by
        rw [ ← Real.log_le_log_iff ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
          exact ne_of_gt <| Nat.cast_pos.mp <| lt_of_lt_of_le ( Nat.cast_pos.mpr hSpos ) <| card_le_V _ _ <| Finset.card_le_univ _ |> le_trans <| by norm_num; ) ( mul_pos ( Real.exp_pos _ ) <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
          exact ne_of_gt <| Nat.pos_of_ne_zero <| by
            have hRpos : 0 < R.card := by
              exact_mod_cast hlarge.trans_lt' ( mul_pos hepsCover ( Nat.cast_pos.mpr hSpos ) )
            exact ne_of_gt <| Nat.pos_of_ne_zero <| by
              have hRcap : R.card ≤ 2 ^ n := by
                exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Cube ] )
              exact ne_of_gt <| Nat.pos_of_ne_zero <| by
                have hV_R_ge : (R.card : ℝ) ≤ (V n R.card r : ℝ) := by
                  exact_mod_cast HarperStability.card_le_V R.card r hRcap
                exact ne_of_gt <| Nat.cast_pos.mp <| lt_of_lt_of_le (Nat.cast_pos.mpr hRpos) hV_R_ge ), Real.log_mul ( by positivity ) ( by
          exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
            exact ne_of_gt <| Nat.pos_of_ne_zero <| by
              have hRpos : 0 < R.card := by
                exact_mod_cast hlarge.trans_lt' ( mul_pos hepsCover ( Nat.cast_pos.mpr hSpos ) )
              exact ne_of_gt <| Nat.pos_of_ne_zero <| by
                have hRcap : R.card ≤ 2 ^ n := by
                  exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Cube ] )
                exact ne_of_gt <| Nat.pos_of_ne_zero <| by
                  have hV_R_ge : (R.card : ℝ) ≤ (V n R.card r : ℝ) := by
                    exact_mod_cast HarperStability.card_le_V R.card r hRcap
                  exact ne_of_gt <| Nat.cast_pos.mp <| lt_of_lt_of_le (Nat.cast_pos.mpr hRpos) hV_R_ge ), Real.log_exp ] ; linarith;
      have hmono : ((neighborhood r R).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card ( HarperStability.neighborhood_mono_set hsub );
      refine le_trans hmono ?_;
      refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| show sigma n + 2 * C_V * ( cSize * sigma n - Real.log epsCover ) + 2 * effLog K_vol n + C_dich * ( sigma n + 1 ) ≥ sigma n + 2 * C_V * ( cSize * sigma n - Real.log epsCover ) + 2 * effLog K_vol n by nlinarith [ show 0 ≤ sigma n from hsigma.1 n ] ) <| Nat.cast_nonneg _ );
      convert le_trans hmem.2.2.2.2.2.2.1 ( mul_le_mul_of_nonneg_left hVcompare <| Real.exp_nonneg _ ) using 1 ; ring_nf;
      rw [ show sigma n + ( sigma n * C_V * cSize * 2 - C_V * Real.log epsCover * 2 ) + effLog K_vol n * 2 = sigma n + ( sigma n * C_V * cSize * 2 - C_V * Real.log epsCover * 2 + effLog K_vol n * 2 ) by ring ] ; rw [ Real.exp_add ] ; ring;
    · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show ( V n R.card r : ℝ ) ≥ 1 from _ ) ( by positivity ) );
      · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr h ) zero_le_one ) |> le_trans <| _;
        · convert cube_card_le_two_pow ( neighborhood r R ) using 1 ; norm_num [ Real.exp_nat_mul, Real.exp_log ];
        · norm_num [ effLog ];
          by_cases hn : 1 ≤ n;
          · nlinarith [ hlog n hn, Real.log_nonneg ( show ( n:ℝ ) ≥ 1 by norm_cast ), Real.log_nonneg ( show ( n+2:ℝ ) ≥ 1 by linarith ), mul_le_mul_of_nonneg_left hcSize ( show 0 ≤ sigma n by linarith [ hlog n hn, Real.log_nonneg ( show ( n:ℝ ) ≥ 1 by norm_cast ) ] ), Real.log_le_sub_one_of_pos hepsCover ];
          · interval_cases n ; norm_num at *;
            nlinarith [ Real.log_nonpos hepsCover.le hepsCover_le, Real.log_nonneg one_le_two, show 0 ≤ sigma 0 from by have := hsigma.1 0; norm_num at this; linarith, mul_le_mul_of_nonneg_left hcSize <| show 0 ≤ sigma 0 from by have := hsigma.1 0; norm_num at this; linarith ];
      · refine' mod_cast Nat.one_le_iff_ne_zero.mpr _;
        intro hVzero
        have hRcard : R.card = 0 := by
          contrapose! hVzero;
          exact ne_of_gt <| by have := card_le_V R.card r ( show R.card ≤ 2 ^ n from le_trans ( Finset.card_le_univ _ ) <| by simp +decide [ Cube ] ) ; exact_mod_cast this.trans_lt' <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hVzero;
        have hRempty : R = ∅ := by
          exact Finset.card_eq_zero.mp hRcard
        have hSempty : S = ∅ := by
          exact Finset.eq_empty_of_forall_notMem fun x hx => by nlinarith [ show ( S.card : ℝ ) ≥ 1 by exact_mod_cast hSpos, show ( R.card : ℝ ) = 0 by exact_mod_cast hRcard ] ;
        have hSpos' : S.card = 0 := by
          exact hSempty.symm ▸ rfl
        exact absurd hSpos' (by linarith);
  · rw [ show R = ∅ by exact Finset.eq_empty_of_forall_notMem fun x hx => hSpos <| Finset.card_pos.mpr ⟨ x, hsub hx ⟩ ];
    unfold neighborhood; norm_num; positivity;

/-
Uniform subset near-optimal envelope.  Produces a class-only constant
`C_R` such that for every `sigma` there is a degraded tuple `D_R` whose
envelope is `C_R`-controlled and whose size-slack dominates the shrunk size,
and which satisfies the near-optimal neighbourhood bound on every large
subset `R` of a class member `S`.  This is the uniform analogue of
`r1a_subset_nearOptimalHyp_eff`: the sigma-dependent finite prefix is replaced
by the uniform range-or-large-slack dichotomy `r1_range_control_uniform`.
-/
lemma r1a_subset_nearOptimalHyp_effU (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff)
  (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ)
  (hrho : 0 < rho) (hdeltaCap : 0 < deltaCap) (hdeltaCap1 : deltaCap < 1)
  (hcSize : 1 ≤ cSize) (halphaMin : 0 < alphaMin) (halpha_le : alphaMin ≤ alphaMax) (halphaMax : alphaMax < 1 / 2)
  (hepsCover : 0 < epsCover) (hepsCover_le : epsCover ≤ 1) :
  ∃ C_R : ℝ, 1 ≤ C_R ∧
  ∀ sigma : ℕ → ℝ, Sublinear sigma → (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
  ∃ D_R : StabilityData, degradedData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ D_R ∧
    D_R.cSize ≤ cSize ∧
    (∀ n, D_R.sigma n ≤ C_R * (sigma n + 1)) ∧
    (∀ n, D_R.cSize * D_R.sigma n ≥ cSize * sigma n - Real.log epsCover) ∧
    ∀ n r S R alpha beta, classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      nearOptimalHyp D_R n r R := by
  obtain ⟨c0, hc0, C_dich, hC_dich, hdich⟩ := r1_range_control_uniform (BallVolumeTwoSidedStatement_of_Eff hBV) hVPlus (InteriorVolumeCalculusStatement_of_Eff hIVC) rho deltaCap cSize alphaMin alphaMax hrho hdeltaCap hdeltaCap1 hcSize halphaMin halpha_le halphaMax;
  obtain ⟨C_V, hC_V, K_vol, hK_vol, hcalc⟩ := hIVC alphaMin c0 halphaMin hc0;
  refine' ⟨ 1 + 2 * C_V * cSize + 2 * C_V * ( -Real.log epsCover ) + 2 * ( K_vol * ( Real.log 3 + 1 ) ) + C_dich, _, _ ⟩;
  · nlinarith [ Real.log_le_sub_one_of_pos hepsCover, Real.log_nonneg ( show ( 3 : ℝ ) ≥ 1 by norm_num ) ];
  · intro sigma hsigma hlog;
    refine' ⟨ ⟨ rho, deltaCap, cSize, alphaMin, alphaMax, fun n => effUEnvelope C_V K_vol C_dich cSize epsCover sigma n ⟩, _, _, _, _, _ ⟩ <;> norm_num;
    · refine' ⟨ _, rfl, rfl, le_rfl, rfl, rfl, _ ⟩;
      · refine' ⟨ hrho, hdeltaCap, hdeltaCap1, hcSize, halphaMin, halpha_le, halphaMax, _, _ ⟩;
        · apply_rules [ sublinear_effUEnvelope ];
          · lia;
          · linarith;
          · linarith;
          · linarith;
        · intro n hn;
          refine' le_trans ( hlog n hn ) _;
          unfold effUEnvelope;
          unfold effLog; norm_num; ring_nf;
          nlinarith [ show 0 ≤ sigma n * C_V * cSize by exact mul_nonneg ( mul_nonneg ( hsigma.1 n ) ( by positivity ) ) ( by positivity ), show 0 ≤ sigma n * C_dich by exact mul_nonneg ( hsigma.1 n ) ( by positivity ), show 0 ≤ K_vol * 2 by positivity, show 0 ≤ K_vol * Real.log ( 2 + n ) * 2 by exact mul_nonneg ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ), Real.log_nonpos hepsCover.le hepsCover_le ];
      · intro n; exact (by
        unfold effUEnvelope; norm_num;
        nlinarith [ show 0 ≤ C_V * cSize * sigma n by exact mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( hsigma.1 n ), show 0 ≤ effLog K_vol n by exact mul_nonneg ( by linarith ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_one ), show 0 ≤ C_dich * ( sigma n + 1 ) by exact mul_nonneg ( by linarith ) ( add_nonneg ( hsigma.1 n ) zero_le_one ), Real.log_le_sub_one_of_pos hepsCover ]);
    · intro n
      simp [effUEnvelope];
      have := effLog_le_sigma_uniform ( show 0 ≤ K_vol by linarith ) hsigma hlog n;
      rw [ max_eq_right ( by nlinarith [ Real.log_nonneg ( show ( 3 : ℝ ) ≥ 1 by norm_num ) ] ) ] at this;
      nlinarith [ show 0 ≤ C_V * cSize by positivity, show 0 ≤ C_V * ( -Real.log epsCover ) by exact mul_nonneg ( by positivity ) ( neg_nonneg_of_nonpos ( Real.log_nonpos hepsCover.le hepsCover_le ) ), show 0 ≤ K_vol * ( Real.log 3 + 1 ) by positivity, show 0 ≤ C_dich by positivity, hsigma.1 n ];
    · intro n
      have h_term : cSize * sigma n - Real.log epsCover ≤ effUEnvelope C_V K_vol C_dich cSize epsCover sigma n := by
        unfold effUEnvelope;
        have h_term : 0 ≤ cSize * sigma n - Real.log epsCover := by
          have h_term : 0 ≤ sigma n := by
            exact hsigma.1 n;
          nlinarith [ Real.log_le_sub_one_of_pos hepsCover ];
        have h_term : 0 ≤ effLog K_vol n := by
          exact mul_nonneg ( by positivity ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_one );
        nlinarith [ show 0 ≤ sigma n from hsigma.1 n ];
      nlinarith [ show 0 ≤ effUEnvelope C_V K_vol C_dich cSize epsCover sigma n from by
                    unfold effUEnvelope;
                    have h_sigma_nonneg : 0 ≤ sigma n := by
                      exact hsigma.1 n;
                    exact add_nonneg ( add_nonneg ( add_nonneg h_sigma_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( by nlinarith [ Real.log_le_sub_one_of_pos hepsCover ] ) ) ) ) ( mul_nonneg zero_le_two ( by unfold effLog; exact mul_nonneg ( by positivity ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_one ) ) ) ) ( mul_nonneg ( by positivity ) ( by linarith ) ) ];
    · convert r1a_nearOptimal_core rho deltaCap cSize alphaMin alphaMax epsCover hcSize halphaMax hepsCover hepsCover_le C_V K_vol c0 C_dich hC_V hK_vol hC_dich sigma hsigma hlog hcalc ( hdich sigma hsigma hlog ) using 1

lemma r1a_degraded_for_subset_effU (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff)
  (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ)
  (hrho : 0 < rho) (hdeltaCap : 0 < deltaCap) (hdeltaCap1 : deltaCap < 1)
  (hcSize : 1 ≤ cSize) (halphaMin : 0 < alphaMin) (halpha_le : alphaMin ≤ alphaMax) (halphaMax : alphaMax < 1 / 2)
  (hepsCover : 0 < epsCover) (hepsCover_le : epsCover ≤ 1) :
  ∃ C_R : ℝ, 1 ≤ C_R ∧
  ∀ sigma : ℕ → ℝ, Sublinear sigma → (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
  ∃ D_R : StabilityData, degradedData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ D_R ∧
    D_R.cSize ≤ cSize ∧
    (∀ n, D_R.sigma n ≤ C_R * (sigma n + 1)) ∧
    ∀ n r S R alpha beta, classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      classMember D_R n r R alpha beta := by
  obtain ⟨C_R, hC_R, hbody⟩ :=
    r1a_subset_nearOptimalHyp_effU hBV hVPlus hIVC rho deltaCap cSize alphaMin alphaMax epsCover
      hrho hdeltaCap hdeltaCap1 hcSize halphaMin halpha_le halphaMax hepsCover hepsCover_le
  refine ⟨C_R, hC_R, ?_⟩
  intro sigma hsublin hlog
  obtain ⟨D_R, hdeg, hcSizeR, hCRbound, hslack, hnear⟩ := hbody sigma hsublin hlog
  refine ⟨D_R, hdeg, hcSizeR, hCRbound, ?_⟩
  intro n r S R alpha beta hmem hsub hlarge
  have hcap_S : capHyp ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S := hmem.2.2.2.2.2.2.2
  have hcap_R : capHyp D_R n r R := r1a_subset_capHyp hsub hdeg hcap_S
  have hsize_S : sizeHyp ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n S alpha := hmem.2.2.2.2.2.1
  have hsize_R_bound :
      |Real.log (R.card : ℝ) - H alpha * (n : ℝ)| ≤ cSize * sigma n - Real.log epsCover :=
    r1a_subset_sizeHyp hepsCover hepsCover_le hsub hlarge hsize_S
  have hsize_R : sizeHyp D_R n R alpha := le_trans hsize_R_bound (hslack n)
  refine ⟨hdeg.1, hmem.2.1, ?_, ?_, ?_, hsize_R, hnear n r S R alpha beta hmem hsub hlarge, hcap_R⟩
  · exact le_trans (by rw [← hdeg.2.2.2.2.1]; exact hmem.2.2.1) le_rfl
  · exact le_trans le_rfl (by rw [← hdeg.2.2.2.2.2.1]; exact hmem.2.2.2.1)
  · exact (by rw [← hdeg.2.1]; exact hmem.2.2.2.2.1)

theorem r1a_effU (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (_hIV : InteriorVStatement) (hIVC : InteriorVolumeCalculusEff) : R1aEffU := by
  intro hHBL_oracle rho deltaCap cSize alphaMin alphaMax epsCover hrho hdeltaCap hdeltaCap1 hcSize halphaMin halpha_le halphaMax hepsCover
  by_cases hepsCover_le : epsCover ≤ 1
  · obtain ⟨C_R, hC_R, hsubset_oracle⟩ := r1a_degraded_for_subset_effU hBV hVPlus hIVC rho deltaCap cSize alphaMin alphaMax epsCover hrho hdeltaCap hdeltaCap1 hcSize halphaMin halpha_le halphaMax hepsCover hepsCover_le
    obtain ⟨K_hbl, hK_hbl, hHBL⟩ := hHBL_oracle rho deltaCap cSize alphaMin alphaMax hrho hdeltaCap hdeltaCap1 hcSize halphaMin halpha_le halphaMax
    set L_eps := max 0 (-Real.log epsCover)
    set K_final := K_hbl * C_R * 16384 + K_hbl + L_eps + 1
    use K_final
    constructor
    · have h0 : 0 ≤ K_hbl := le_trans zero_le_one hK_hbl
      have h1 : 0 ≤ C_R := le_trans zero_le_one hC_R
      have h2 : 0 ≤ L_eps := le_max_left _ _
      have h3 : 0 ≤ K_hbl * C_R * 16384 := by positivity
      linarith
    · intro sigma hsublin hlog
      let Din : StabilityData := ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
      obtain ⟨D_R, hdeg, hcSizeR, hCRbound, hsubset_mem⟩ := hsubset_oracle sigma hsublin hlog
      have hDR_eq : D_R = ⟨rho, deltaCap, cSize, alphaMin, alphaMax, D_R.sigma⟩ := by
        obtain ⟨hvalid, hrho', hdeltaCap', hcSize', halphaMin', halphaMax', hsigma'⟩ := hdeg
        rcases D_R with ⟨rho_R, deltaCap_R, cSize_R, alphaMin_R, alphaMax_R, sigma_R⟩
        have h1 : rho = rho_R := hrho'
        have h2 : deltaCap = deltaCap_R := hdeltaCap'
        have h3 : cSize = cSize_R := le_antisymm hcSize' hcSizeR
        have h4 : alphaMin = alphaMin_R := halphaMin'
        have h5 : alphaMax = alphaMax_R := halphaMax'
        rw [← h1, ← h2, ← h3, ← h4, ← h5]
      set Dhbl := effDegrade D_R K_hbl 14
      set Dcover := {Dhbl with sigma := fun n => Dhbl.sigma n + Real.log (L_eps + 1)}
      set Dfinal := effDegrade Din K_final 14
      intro n r S alpha beta hmem
      have hvalid : validData Din := hmem.1
      have hdeg_hbl : degradedData D_R Dhbl := degradedData_effDegrade D_R hdeg.1 K_hbl hK_hbl 14
      have hdeg_Din_Dhbl : degradedData Din Dhbl := degradedData_trans hdeg hdeg_hbl
      have hdeg_cover : degradedData Din Dcover := by
        obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10, h11, h12, h13, h14, h15⟩ := hdeg_Din_Dhbl
        have hLeps : 0 ≤ Real.log (L_eps + 1) := by
          have : 0 ≤ L_eps := le_max_left _ _
          have : 1 ≤ L_eps + 1 := by linarith
          exact Real.log_nonneg this
        refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩, h10, h11, h12, h13, h14, ?_⟩
        · exact Sublinear_add h8 (Sublinear_const (show 0 ≤ Real.log (L_eps + 1) from hLeps))
        · intro m hm
          exact (h9 m hm).trans (by linarith)
        · intro m
          exact (h15 m).trans (by linarith)
      have hCov : stabilityCoverConclusion n S epsCover (Dcover.sigma n) (Nat.ceil (Dcover.sigma n)) := by
        set radius := rmin n S.card + Nat.ceil (Dhbl.sigma n)
        set δ := Real.exp (-(Dhbl.sigma n))
        set thresh := epsCover * (S.card : ℝ)
        obtain ⟨centers, hcenters_card, hcenters_bound⟩ := greedy_peel_coverU S radius δ thresh (by
          have := hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (this.1 n))) (by
          intros R hR_sub hR_thresh
          have hsublin_DR : Sublinear D_R.sigma := hdeg.1.2.2.2.2.2.2.2.1
          have hlog_DR : ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ D_R.sigma n := hdeg.1.2.2.2.2.2.2.2.2
          have hHBL_sub : HBLFor D_R (effDegrade D_R K_hbl 14) := by
            rw [hDR_eq]
            exact hHBL D_R.sigma hsublin_DR hlog_DR
          obtain ⟨a, ha⟩ := hHBL_sub (hsubset_mem n r S R alpha beta hmem hR_sub hR_thresh)
          refine' ⟨a, ha.trans _⟩
          gcongr
          exact add_le_add (rmin_monoU <| Finset.card_le_card hR_sub) le_rfl) (Nat.ceil (Real.exp (Dhbl.sigma n) * L_eps))
        refine' ⟨centers, _, _⟩
        · refine' le_trans (Nat.cast_le.mpr hcenters_card) _
          refine' le_trans (Nat.ceil_lt_add_one (by positivity) |> le_of_lt) _
          rw [Real.exp_add, Real.exp_log (by positivity)]
          nlinarith [Real.add_one_le_exp (Dhbl.sigma n), show 0 ≤ Dhbl.sigma n from hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1.1 n]
        · rw [Nat.cast_sub]
          · refine' le_trans _ (hcenters_bound.elim (fun h => h) fun h => h.trans _)
            · gcongr
              refine' coveredByBalls_mono_radiusU _ _ _
              exact Nat.add_le_add_left (Nat.ceil_mono <| le_add_of_nonneg_right <| Real.log_nonneg <| by linarith [le_max_left 0 (-Real.log epsCover), le_max_right 0 (-Real.log epsCover)]) _
            · have h_exp : (1 - δ) ^ ⌈Real.exp (Dhbl.sigma n) * L_eps⌉₊ ≤ Real.exp (-δ * ⌈Real.exp (Dhbl.sigma n) * L_eps⌉₊) := by
                have h_exp : (1 - δ) ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
                exact le_trans (pow_le_pow_left₀ (sub_nonneg.2 <| Real.exp_le_one_iff.2 <| neg_nonpos.2 <| show 0 ≤ Dhbl.sigma n from hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1.1 _) h_exp _) <| by rw [← Real.exp_nat_mul]; ring_nf; norm_num
              refine' mul_le_mul_of_nonneg_right (h_exp.trans _) (Nat.cast_nonneg _)
              rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_exp]
              simp +zetaDelta at *
              rw [Real.exp_neg]
              cases max_cases (0 : ℝ) (-Real.log epsCover) <;> nlinarith [Nat.le_ceil (Real.exp (Dhbl.sigma n) * max 0 (-Real.log epsCover)), Real.exp_pos (Dhbl.sigma n), mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (Dhbl.sigma n))), Real.log_le_sub_one_of_pos hepsCover]
          · exact Finset.card_filter_le _ _
      have hvalid_final : validData Dfinal := validData_effDegrade Din hvalid K_final (by
        have h0 : 0 ≤ K_hbl := le_trans zero_le_one hK_hbl
        have h1 : 0 ≤ C_R := le_trans zero_le_one hC_R
        have h2 : 0 ≤ L_eps := le_max_left _ _
        have h3 : 0 ≤ K_hbl * C_R * 16384 := by positivity
        linarith) 14
      have hdeg_final : degradedData Dcover Dfinal := by
        refine ⟨hvalid_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact Eq.trans hdeg_cover.2.1.symm rfl
        · exact Eq.trans hdeg_cover.2.2.1.symm rfl
        · exact hcSizeR
        · exact Eq.trans hdeg_cover.2.2.2.2.1.symm rfl
        · exact Eq.trans hdeg_cover.2.2.2.2.2.1.symm rfl
        · intro m
          have hb2 : Dhbl.sigma m = K_hbl * (effEnv 14 D_R.sigma m + 1) := rfl
          have hb3 : Dfinal.sigma m = K_final * (effEnv 14 Din.sigma m + 1) := rfl
          have hL_eps_le : Real.log (L_eps + 1) ≤ L_eps := by
            have := Real.log_le_sub_one_of_pos (show 0 < L_eps + 1 by positivity)
            linarith
          have hd1 : Dcover.sigma m = K_hbl * (effEnv 14 D_R.sigma m + 1) + Real.log (L_eps + 1) := rfl
          have hDR_le : ∀ l, D_R.sigma l ≤ C_R * (Din.sigma l + 1) := hCRbound
          have hEnv_le := effEnv_mono hDR_le 14 m
          have hcomp := effEnv_comp 14 (i := 0) (C := C_R) hC_R (hvalid.2.2.2.2.2.2.2.1.1) m
          have h0_eq : (fun l => C_R * (effEnv 0 Din.sigma l + 1)) = fun l => C_R * (Din.sigma l + 1) := rfl
          rw [h0_eq] at hcomp
          have h_pow : (2 : ℝ) ^ 14 = 16384 := by norm_num
          rw [h_pow] at hcomp
          have hEnv_pos : 1 ≤ effEnv 14 Din.sigma m + 1 := by
            have : 0 ≤ effEnv 14 Din.sigma m := effEnv_nonneg 14 Din.sigma (hvalid.2.2.2.2.2.2.2.1.1) m
            linarith
          have h0 : 0 ≤ K_hbl := le_trans zero_le_one hK_hbl
          have h1 : 0 ≤ C_R := le_trans zero_le_one hC_R
          have h2 : 0 ≤ L_eps := le_max_left _ _
          have hDcover_le : Dcover.sigma m ≤ K_hbl * ((16384 * C_R) * (effEnv 14 Din.sigma m + 1) + 1) + L_eps := by nlinarith
          have heq : K_hbl * ((16384 * C_R) * (effEnv 14 Din.sigma m + 1) + 1) + L_eps = K_hbl * C_R * 16384 * (effEnv 14 Din.sigma m + 1) + K_hbl + L_eps := by ring
          have hle : K_hbl * C_R * 16384 * (effEnv 14 Din.sigma m + 1) + K_hbl + L_eps ≤ (K_hbl * C_R * 16384 + K_hbl + L_eps + 1) * (effEnv 14 Din.sigma m + 1) := by nlinarith
          have heq2 : (K_hbl * C_R * 16384 + K_hbl + L_eps + 1) * (effEnv 14 Din.sigma m + 1) = Dfinal.sigma m := hb3.symm
          exact le_trans hDcover_le (le_trans (le_of_eq heq) (le_trans hle (le_of_eq heq2)))
      exact stabilityCoverConclusion_mono (hdeg_final.2.2.2.2.2.2 n) (Nat.ceil_mono (hdeg_final.2.2.2.2.2.2 n)) hCov
  · use 1
    constructor
    · linarith
    · intro sigma hsublin hlog n r S alpha beta hmem
      have h_eps : 1 ≤ epsCover := by linarith
      have h_empty :=
        stabilityCoverConclusion_empty_of_one_le (n := n) (S := S)
          (epsCover := epsCover) (coverSlack := 0) (radiusSlack := 0) h_eps
      exact stabilityCoverConclusion_mono (by
        have hvalid_1 : validData (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ 1 14) := validData_effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ hmem.1 1 le_rfl 14
        exact hvalid_1.2.2.2.2.2.2.2.1.1 n) (Nat.zero_le _) h_empty

end HarperStability