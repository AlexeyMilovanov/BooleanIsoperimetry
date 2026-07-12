import HarperStability.Reductions.Basic
import HarperStability.Interface.Effective
import HarperStability.Volume.Basic

namespace HarperStability

lemma sublinear_effLog {K : ℝ} (hK : 0 ≤ K) : Sublinear (effLog K) := by
  unfold effLog
  apply Sublinear_smul hK
  refine Sublinear_of_le
    (s := fun n => Real.log ((n : ℝ) + 1) + (Real.log 2 + 1))
    (t := fun n => Real.log ((n : ℝ) + 2) + 1)
    (fun n => ?_) (fun n => ?_) ?_
  · have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hn
    linarith
  · have hpos : 0 < (n : ℝ) + 2 := by positivity
    have hle_arg : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by nlinarith
    have hlog_le := Real.log_le_log hpos hle_arg
    have hlog_mul :
        Real.log (2 * ((n : ℝ) + 1)) = Real.log 2 + Real.log ((n : ℝ) + 1) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  · exact Sublinear_add sublinear_log_succ
      (Sublinear_const (by positivity : 0 ≤ Real.log 2 + 1))

lemma effLog_le_sigma (D : StabilityData) (hvalid : validData D) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, effLog K n ≤ C * (D.sigma n + 1) := by
  use K * (Real.log 3 + 1) * (D.sigma 0 + 1) + max 1 (K * (Real.log 3 + 1))
  constructor
  · have h_pos : 0 ≤ K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
      have h1 : 0 ≤ K := hK
      have h2 : 0 ≤ Real.log 3 + 1 := by
        have : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        linarith
      have h3 : 0 ≤ D.sigma 0 + 1 := by
        have : 0 ≤ D.sigma 0 := hvalid.2.2.2.2.2.2.2.1.1 0
        linarith
      positivity
    have h_max : 1 ≤ max 1 (K * (Real.log 3 + 1)) := le_max_left 1 _
    linarith
  · intro n
    have hC : K * (Real.log 3 + 1) ≤ max 1 (K * (Real.log 3 + 1)) := le_max_right 1 _
    have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
    have h_base : K * (Real.log ((n : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := by
      by_cases hn : n = 0
      · subst hn
        have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
        have h_cast : (((0 : ℕ) : ℝ) + 2) = 2 := by norm_num
        rw [h_cast]
        have h2 : K * (Real.log 2 + 1) ≤ K * (Real.log 3 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hK
        have h3 : K * (Real.log 3 + 1) ≤ K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
          have h_pos : 0 ≤ K * (Real.log 3 + 1) := mul_nonneg hK (by positivity)
          have h_ge1 : 1 ≤ D.sigma 0 + 1 := by linarith
          nlinarith
        exact le_trans h2 h3
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
        have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log (3 * (n : ℝ)) := by
          apply Real.log_le_log (by linarith)
          linarith
        have h2 : Real.log (3 * (n : ℝ)) = Real.log 3 + Real.log (n : ℝ) := by
          apply Real.log_mul (by norm_num) (by linarith)
        have h3 : Real.log (n : ℝ) ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.2 n hn1
        have h4 : Real.log ((n : ℝ) + 2) + 1 ≤ Real.log 3 + 1 + D.sigma n := by linarith
        have h5 : K * (Real.log ((n : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1 + D.sigma n) :=
          mul_le_mul_of_nonneg_left h4 hK
        have h6 : K * (Real.log 3 + 1 + D.sigma n) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := by
          have h_log3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          have h_pos : 0 ≤ K * D.sigma n := mul_nonneg hK (hvalid.2.2.2.2.2.2.2.1.1 n)
          have : 1 * (K * D.sigma n) ≤ (Real.log 3 + 1) * (K * D.sigma n) :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos
          linarith
        exact le_trans h5 h6
    have h_step2 : K * (Real.log 3 + 1) * (D.sigma n + 1) ≤ max 1 (K * (Real.log 3 + 1)) * (D.sigma n + 1) := mul_le_mul_of_nonneg_right hC (by linarith)
    have h_step3 : max 1 (K * (Real.log 3 + 1)) * (D.sigma n + 1) ≤ (K * (Real.log 3 + 1) * (D.sigma 0 + 1) + max 1 (K * (Real.log 3 + 1))) * (D.sigma n + 1) := by
      have hh1 : 0 ≤ K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
        have hlog : 0 ≤ Real.log 3 + 1 := by positivity
        have hs0 : 0 ≤ D.sigma 0 + 1 := by
          have := hvalid.2.2.2.2.2.2.2.1.1 0
          linarith
        exact mul_nonneg (mul_nonneg hK hlog) hs0
      have hh2 : 0 ≤ D.sigma n + 1 := by linarith
      nlinarith
    exact le_trans h_base (le_trans h_step2 h_step3)

lemma BallVolumeTwoSidedStatement_of_Eff (h : BallVolumeTwoSidedEff) :
    BallVolumeTwoSidedStatement := by
  unfold BallVolumeTwoSidedStatement
  obtain ⟨C, hC, hcalc⟩ := h
  exact ⟨effLog C, sublinear_effLog (le_trans zero_le_one hC), hcalc⟩

lemma InteriorVolumeCalculusStatement_of_Eff (h : InteriorVolumeCalculusEff) :
    InteriorVolumeCalculusStatement := by
  unfold InteriorVolumeCalculusStatement
  intro alpha c0 h1 h2
  obtain ⟨C, hC, K, hK, hcalc⟩ := h alpha c0 h1 h2
  use C, hC, effLog K
  refine ⟨sublinear_effLog (le_trans zero_le_one hK), hcalc⟩

lemma r1a_subset_nearOptimalHyp_eff (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusEff)
    (Din : StabilityData) (epsCover : ℝ) (hvalid : validData Din) (heps : 0 < epsCover)
    (heps_le : epsCover ≤ 1) :
    ∃ (C_R : ℝ), 1 ≤ C_R ∧ ∃ (D_R : StabilityData), degradedData Din D_R ∧
      D_R.cSize ≤ Din.cSize ∧
      (∀ n, D_R.sigma n ≤ C_R * (Din.sigma n + 1)) ∧
      (∀ n, D_R.cSize * D_R.sigma n ≥ Din.cSize * Din.sigma n - Real.log epsCover) ∧
    ∀ n r S R alpha beta, classMember Din n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      nearOptimalHyp D_R n r R := by
  classical
  obtain ⟨c0, hc0, N, hN1, hrange⟩ := r1_range_control hBV hVPlus (InteriorVolumeCalculusStatement_of_Eff hVC) Din hvalid
  obtain ⟨C_V, hC_V, K_vol, hK_vol, hcalc⟩ :=
    hVC Din.alphaMin c0 hvalid.2.2.2.2.1 hc0
  have hlogeps : Real.log epsCover ≤ 0 := Real.log_nonpos heps.le heps_le
  have hsigma0 : ∀ n, 0 ≤ Din.sigma n := hvalid.2.2.2.2.2.2.2.1.1
  have hcSize1 : (1 : ℝ) ≤ Din.cSize := hvalid.2.2.2.1
  set E : ℕ → ℝ := fun n =>
    Din.sigma n + 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
      2 * effLog K_vol n with hE
  set sigma' : ℕ → ℝ := fun n =>
    (if n < N then (n : ℝ) * Real.log 2 else 0) + E n with hsigma'
  have hterm_nonneg : ∀ n, 0 ≤ Din.cSize * Din.sigma n - Real.log epsCover := by
    intro n
    have h := mul_nonneg (le_trans zero_le_one hcSize1) (hsigma0 n)
    linarith
  have hE_ge_sigma : ∀ n, Din.sigma n ≤ E n := by
    intro n
    have h1 : 0 ≤ 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) := by
      nlinarith [hterm_nonneg n, hC_V]
    have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show 1 ≤ n + 2 by omega)
    have h2 : 0 ≤ effLog K_vol n := mul_nonneg (le_trans zero_le_one hK_vol) (add_nonneg (Real.log_nonneg hn2) zero_le_one)
    simp only [hE]
    linarith
  have hE_sub : Sublinear E := by
    have h1 : Sublinear (fun n => 2 * C_V * (Din.cSize * Din.sigma n)) := by
      have := sublinear_const_mul (2 * C_V * Din.cSize)
        (by nlinarith [hC_V, hcSize1]) hvalid.2.2.2.2.2.2.2.1
      convert this using 2 with n
      ring
    have h2 : Sublinear (fun n => 2 * C_V * (-Real.log epsCover)) :=
      sublinear_const _ (by nlinarith [hC_V, hlogeps])
    have h3 : Sublinear (fun n => 2 * effLog K_vol n) :=
      sublinear_const_mul 2 (by norm_num) (sublinear_effLog (le_trans zero_le_one hK_vol))
    have h12 := reductions_sublinear_add h1 h2
    have h123 := reductions_sublinear_add h12 h3
    have h := reductions_sublinear_add hvalid.2.2.2.2.2.2.2.1 h123
    convert h using 2 with n
    simp only [hE]
    ring
  have hif_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ if n < N then (n : ℝ) * Real.log 2 else 0 := by
    intro n
    by_cases h : n < N
    · simp only [if_pos h]
      exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)
    · simp [h]
  have hsigma'_sub : Sublinear sigma' :=
    reductions_sublinear_add
      (sublinear_indicator_prefix _
        (fun n => mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)) N)
      hE_sub
  have hsigma'_ge_sigma : ∀ n, Din.sigma n ≤ sigma' n := by
    intro n
    have h1 := hif_nonneg n
    have := hE_ge_sigma n
    simp only [hsigma']
    linarith
  have hsigma'_nonneg : ∀ n, 0 ≤ sigma' n := fun n =>
    le_trans (hsigma0 n) (hsigma'_ge_sigma n)
  set D_R : StabilityData := { Din with sigma := sigma' } with hD_R
  have hvalidR : validData D_R := by
    refine ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
      hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1, hvalid.2.2.2.2.2.2.1,
      hsigma'_sub, ?_⟩
    intro n hn
    exact le_trans (hvalid.2.2.2.2.2.2.2.2 n hn) (hsigma'_ge_sigma n)
  have hdeg : degradedData Din D_R :=
    ⟨hvalidR, rfl, rfl, le_rfl, rfl, rfl, hsigma'_ge_sigma⟩
  have hslack_ge : ∀ n, D_R.cSize * D_R.sigma n ≥
      Din.cSize * Din.sigma n - Real.log epsCover := by
    intro n
    have h1 : sigma' n ≥ E n := by
      have h0 := hif_nonneg n
      simp only [hsigma']
      linarith
    have h2 : E n ≥ Din.cSize * Din.sigma n - Real.log epsCover := by
      have ht := hterm_nonneg n
      have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show 1 ≤ n + 2 by omega)
      have hv : 0 ≤ effLog K_vol n := by
        unfold effLog
        exact mul_nonneg (le_trans zero_le_one hK_vol)
          (add_nonneg (Real.log_nonneg hn2) zero_le_one)
      have hs := hsigma0 n
      have : 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) ≥
          Din.cSize * Din.sigma n - Real.log epsCover := by nlinarith [hC_V, ht]
      simp only [hE]
      linarith
    have h3 : D_R.cSize * D_R.sigma n ≥ D_R.sigma n := by
      have hDRsig : D_R.sigma n = sigma' n := rfl
      have hDRc : D_R.cSize = Din.cSize := rfl
      rw [hDRsig, hDRc]
      have hs' := hsigma'_nonneg n
      nlinarith [hcSize1, hs']
    calc D_R.cSize * D_R.sigma n ≥ D_R.sigma n := h3
      _ = sigma' n := rfl
      _ ≥ E n := h1
      _ ≥ Din.cSize * Din.sigma n - Real.log epsCover := h2
  obtain ⟨C_eff, hC_eff_ge1, hC_eff⟩ := effLog_le_sigma Din hvalid K_vol (le_trans zero_le_one hK_vol)
  have h_bound : ∃ C_R : ℝ, 1 ≤ C_R ∧ ∀ n, D_R.sigma n ≤ C_R * (Din.sigma n + 1) := by
    set L_eps := max 0 (-Real.log epsCover)
    use (N : ℝ) * Real.log 2 + 1 + 2 * C_V * Din.cSize + 2 * C_V * L_eps + 2 * C_eff
    constructor
    · have h0 : 0 ≤ (N : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
      have h1 : 0 ≤ 2 * C_V * Din.cSize := by positivity
      have h2 : 0 ≤ 2 * C_V * L_eps := mul_nonneg (by positivity) (le_max_left _ _)
      have h3 : 0 ≤ 2 * C_eff := by positivity
      linarith
    · intro n
      have hs : 0 ≤ Din.sigma n := hsigma0 n
      have h_D_R_sigma : D_R.sigma n = sigma' n := rfl
      rw [h_D_R_sigma, hsigma', hE]
      have hb : (if n < N then (n : ℝ) * Real.log 2 else 0) ≤ (N : ℝ) * Real.log 2 * (Din.sigma n + 1) := by
        by_cases hn : n < N
        · simp only [if_pos hn]
          have : (n : ℝ) * Real.log 2 ≤ (N : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) (Real.log_nonneg one_le_two)
          have : (N : ℝ) * Real.log 2 ≤ (N : ℝ) * Real.log 2 * (Din.sigma n + 1) := by
            have : 1 ≤ Din.sigma n + 1 := by linarith
            nlinarith [mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg one_le_two : 0 ≤ Real.log 2)]
          linarith
        · simp only [if_neg hn]
          positivity
      have hE1 : Din.sigma n ≤ 1 * (Din.sigma n + 1) := by linarith
      have hE2 : 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) ≤ (2 * C_V * Din.cSize + 2 * C_V * L_eps) * (Din.sigma n + 1) := by
        have h_log : -Real.log epsCover ≤ L_eps := le_max_right _ _
        have : 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) ≤ 2 * C_V * (Din.cSize * Din.sigma n + L_eps) := by nlinarith [hC_V, h_log]
        have : 2 * C_V * (Din.cSize * Din.sigma n + L_eps) = 2 * C_V * Din.cSize * Din.sigma n + 2 * C_V * L_eps := by ring
        have : 2 * C_V * Din.cSize * (Din.sigma n + 1) + 2 * C_V * L_eps * (Din.sigma n + 1) = 2 * C_V * Din.cSize * Din.sigma n + 2 * C_V * Din.cSize + 2 * C_V * L_eps * Din.sigma n + 2 * C_V * L_eps := by ring
        have h1 : 0 ≤ 2 * C_V * Din.cSize := by positivity
        have h2 : 0 ≤ 2 * C_V * L_eps * Din.sigma n := mul_nonneg (by positivity) hs
        linarith
      have hE3 : 2 * effLog K_vol n ≤ 2 * C_eff * (Din.sigma n + 1) := by
        have h_eff_bound := hC_eff n
        linarith [hC_eff n]
      linarith
  rcases h_bound with ⟨C_R, hC_R, hC_R_bound⟩
  refine ⟨C_R, hC_R, D_R, hdeg, le_rfl, hC_R_bound, hslack_ge, ?_⟩
  intro n r S R alpha beta hmem hsub hlarge
  dsimp [nearOptimalHyp]
  by_cases hS0 : S.card = 0
  · have hR0 : R.card = 0 :=
      Nat.eq_zero_of_le_zero (le_trans (Finset.card_le_card hsub) (le_of_eq hS0))
    have hRempty : R = ∅ := Finset.card_eq_zero.mp hR0
    have hΓ : neighborhood r R = ∅ := by
      rw [hRempty]
      ext x
      simp [mem_neighborhood_iff]
    rw [hΓ]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hSpos : 0 < (S.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hS0
    have hRpos : 0 < (R.card : ℝ) := lt_of_lt_of_le (by positivity) hlarge
    have hRpos_nat : 1 ≤ R.card := by exact_mod_cast hRpos
    have hR1 : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hRpos_nat
    have hRcap : R.card ≤ 2 ^ n := by
      calc R.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ R
        _ = 2 ^ n := by
            rw [Finset.card_univ]
            exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
    have hV_R_ge : (R.card : ℝ) ≤ (V n R.card r : ℝ) := card_le_V R.card r hRcap
    have hV_R_pos : 0 < (V n R.card r : ℝ) := lt_of_lt_of_le hRpos hV_R_ge
    by_cases hn_small : n < N
    · have hbump : sigma' n = (n : ℝ) * Real.log 2 + E n := by
        simp only [hsigma', if_pos hn_small]
      have hcard := cube_card_le_two_pow (neighborhood r R)
      have hEn : 0 ≤ E n := le_trans (hsigma0 n) (hE_ge_sigma n)
      calc ((neighborhood r R).card : ℝ)
          ≤ Real.exp ((n : ℝ) * Real.log 2) := hcard
        _ ≤ Real.exp ((n : ℝ) * Real.log 2) * (V n R.card r : ℝ) :=
            le_mul_of_one_le_right (Real.exp_pos _).le (le_trans hR1 hV_R_ge)
        _ ≤ Real.exp (D_R.sigma n) * (V n R.card r : ℝ) := by
            have hle : Real.exp ((n : ℝ) * Real.log 2) ≤ Real.exp (D_R.sigma n) := by
              apply Real.exp_le_exp.mpr
              show (n : ℝ) * Real.log 2 ≤ sigma' n
              rw [hbump]
              linarith
            exact mul_le_mul_of_nonneg_right hle hV_R_pos.le
    · have hnN : N ≤ n := not_lt.mp hn_small
      have hn1 : 1 ≤ n := le_trans hN1 hnN
      have hrange_n := hrange n hnN r S alpha beta hmem
      have hαmin : Din.alphaMin ≤ alpha := hmem.2.2.1
      have hαhalf : alpha ≤ 1 / 2 :=
        le_of_lt (lt_of_le_of_lt hmem.2.2.2.1 hvalid.2.2.2.2.2.2.1)
      have hbeta : beta = (r : ℝ) / (n : ℝ) := hmem.2.1
      have hScap : S.card ≤ 2 ^ n := by
        calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
          _ = 2 ^ n := by
              rw [Finset.card_univ]
              exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
      have hS1 : 1 ≤ S.card := by
        exact_mod_cast Nat.pos_of_ne_zero hS0
      have hsizeS := hmem.2.2.2.2.2.1
      have hslackS : (0 : ℝ) ≤ Din.cSize * Din.sigma n :=
        mul_nonneg (le_trans zero_le_one hcSize1) (hsigma0 n)
      obtain ⟨hVS, _⟩ := hcalc n S.card r alpha beta (Din.cSize * Din.sigma n)
        hαmin hαhalf hslackS hbeta hrange_n hS1 hScap hsizeS
      have hsizeR := r1a_subset_sizeHyp heps heps_le hsub hlarge hsizeS
      obtain ⟨hVR, _⟩ := hcalc n R.card r alpha beta
        (Din.cSize * Din.sigma n - Real.log epsCover)
        hαmin hαhalf (hterm_nonneg n) hbeta hrange_n hRpos_nat hRcap hsizeR
      have hV_S_pos : 0 < (V n S.card r : ℝ) :=
        lt_of_lt_of_le hSpos (card_le_V S.card r hScap)
      have hVS' := abs_le.mp hVS
      have hVR' := abs_le.mp hVR
      have hlog_le : Real.log (V n S.card r : ℝ) ≤
          (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
            2 * effLog K_vol n) + Real.log (V n R.card r : ℝ) := by
        have h1 : C_V * (Din.cSize * Din.sigma n) ≤
            C_V * (Din.cSize * Din.sigma n - Real.log epsCover) := by
          nlinarith [hC_V, hlogeps]
        linarith [hVS'.2, hVR'.1]
      have hVcompare : (V n S.card r : ℝ) ≤
          Real.exp (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
            2 * effLog K_vol n) * (V n R.card r : ℝ) := by
        have h := Real.exp_le_exp.mpr hlog_le
        rwa [Real.exp_log hV_S_pos, Real.exp_add, Real.exp_log hV_R_pos] at h
      have hnearS := hmem.2.2.2.2.2.2.1
      have hmono : ((neighborhood r R).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (neighborhood_mono_set hsub)
      have hnoBump : sigma' n = E n := by
        simp only [hsigma', if_neg hn_small, zero_add]
      calc ((neighborhood r R).card : ℝ)
          ≤ ((neighborhood r S).card : ℝ) := hmono
        _ ≤ Real.exp (Din.sigma n) * (V n S.card r : ℝ) := hnearS
        _ ≤ Real.exp (Din.sigma n) *
              (Real.exp (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
                2 * effLog K_vol n) * (V n R.card r : ℝ)) :=
            mul_le_mul_of_nonneg_left hVcompare (Real.exp_pos (Din.sigma n)).le
        _ = Real.exp (E n) * (V n R.card r : ℝ) := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 1
            simp only [hE]
            ring_nf
        _ = Real.exp (D_R.sigma n) * (V n R.card r : ℝ) := by
            rw [show D_R.sigma n = sigma' n from rfl, hnoBump]

lemma r1a_degraded_for_subset_eff (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusEff)
    (Din : StabilityData) (epsCover : ℝ) (hvalid : validData Din) (heps : 0 < epsCover)
    (heps_le : epsCover ≤ 1) :
    ∃ C_R : ℝ, 1 ≤ C_R ∧ ∃ D_R : StabilityData, degradedData Din D_R ∧
    D_R.cSize ≤ Din.cSize ∧
    (∀ n, D_R.sigma n ≤ C_R * (Din.sigma n + 1)) ∧
    ∀ n r S R alpha beta, classMember Din n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      classMember D_R n r R alpha beta := by
  obtain ⟨C_R, hC_R, D_R, hdeg, hcSize, hCRbound, hsigma, hnear⟩ :=
    r1a_subset_nearOptimalHyp_eff hBV hVPlus hVC Din epsCover hvalid heps heps_le
  refine ⟨C_R, hC_R, D_R, hdeg, hcSize, hCRbound, ?_⟩
  intro n r S R alpha beta hmem hsub hlarge
  have hcap_S : capHyp Din n r S := hmem.2.2.2.2.2.2.2
  have hcap_R : capHyp D_R n r R := r1a_subset_capHyp hsub hdeg hcap_S
  have hsize_S : sizeHyp Din n S alpha := hmem.2.2.2.2.2.1
  have hsize_R_bound : |Real.log (R.card : ℝ) - H alpha * (n : ℝ)| ≤ Din.cSize * Din.sigma n - Real.log epsCover :=
    r1a_subset_sizeHyp heps heps_le hsub hlarge hsize_S
  have hsize_R : sizeHyp D_R n R alpha := le_trans hsize_R_bound (hsigma n)
  refine ⟨hdeg.1, hmem.2.1, ?_, ?_, ?_, hsize_R, hnear n r S R alpha beta hmem hsub hlarge, hcap_R⟩
  · exact le_trans (by rw [← hdeg.2.2.2.2.1]; exact hmem.2.2.1) le_rfl
  · exact le_trans le_rfl (by rw [← hdeg.2.2.2.2.2.1]; exact hmem.2.2.2.1)
  · exact (by rw [← hdeg.2.1]; exact hmem.2.2.2.2.1)

private lemma rmin_mono {n k1 k2 : ℕ} (h : k1 ≤ k2) : rmin n k1 ≤ rmin n k2 := by
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

private lemma coveredByBalls_mono_radius {n : ℕ} (S centers : Finset (Cube n))
    {radius radius' : ℕ} (hradius : radius ≤ radius') :
    coveredByBalls S centers radius ⊆ coveredByBalls S centers radius' := by
  intro x hx
  rcases (by simpa [coveredByBalls] using hx) with ⟨hxS, c, hc, hdist⟩
  exact (by
    simp [coveredByBalls, hxS]
    exact ⟨c, hc, le_trans hdist hradius⟩)

private lemma greedy_peel_cover {n : ℕ} (S : Finset (Cube n)) (radius : ℕ)
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

lemma CoverFor_mono (Din D1 D2 : StabilityData) (epsCover : ℝ)
    (hdeg : degradedData D1 D2) (hCov : CoverFor Din D1 epsCover) :
    CoverFor Din D2 epsCover := by
  intro n r S alpha beta hmem
  have h1 := hCov hmem
  exact stabilityCoverConclusion_mono (hdeg.2.2.2.2.2.2 n) (Nat.ceil_mono (hdeg.2.2.2.2.2.2 n)) h1

lemma reductions_Sublinear_geomMean {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (fun m => Real.sqrt ((s m + 1) * ((m : ℝ) + 1))) := by
  constructor
  · exact fun _ => Real.sqrt_nonneg _
  · intro ε hε
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ m ≥ N0, s m ≤ (ε ^ 2 / 4) * m :=
      hs.2 (ε ^ 2 / 4) (by positivity)
    refine ⟨N0 + ⌈4 / ε ^ 2⌉₊ + 1, fun n hn => ?_⟩
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hs_bound := hN0 n (by linarith)
    have hn_large : (n : ℝ) ≥ ⌈4 / ε ^ 2⌉₊ + 1 := by
      norm_cast
      linarith
    nlinarith [hn_large, Nat.le_ceil (4 / ε ^ 2),
      mul_div_cancel₀ (4 : ℝ) (ne_of_gt (sq_pos_of_pos hε)),
      pow_two_nonneg (ε * n - 2), pow_two_nonneg (ε * n + 2), hs.1 n]

lemma reductions_effGeo_sublinear {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effGeo s) := by
  refine Sublinear_of_le (fun n => effGeo_nonneg s n) (fun n => ?_)
    (Sublinear_add hs (reductions_Sublinear_geomMean hs))
  exact max_le_add_of_nonneg (hs.1 n) (Real.sqrt_nonneg _)

lemma reductions_effEnv_sublinear (k : ℕ) {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effEnv k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact reductions_effGeo_sublinear ih

lemma degradedData_effDegrade (D : StabilityData) (hvalid : validData D) (K : ℝ) (hK : 1 ≤ K) (k : ℕ) :
    degradedData D (effDegrade D K k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hvalid
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hsig_nonneg : ∀ n, 0 ≤ D.sigma n := h8.1
  have hle : ∀ n, D.sigma n ≤ K * (effEnv k D.sigma n + 1) := by
    intro n
    have henv_ge := le_effEnv k D.sigma n
    have henv_nonneg := effEnv_nonneg k D.sigma hsig_nonneg n
    nlinarith
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩,
    rfl, rfl, le_rfl, rfl, rfl, hle⟩
  · have hE : Sublinear (effEnv k D.sigma) := reductions_effEnv_sublinear k h8
    have hE1 : Sublinear (fun n => effEnv k D.sigma n + 1) :=
      Sublinear_add hE (Sublinear_const (show (0 : ℝ) ≤ 1 by norm_num))
    exact Sublinear_smul hK0 hE1
  · intro n hn
    exact (h9 n hn).trans (hle n)

lemma validData_effDegrade (D : StabilityData) (hvalid : validData D) (K : ℝ) (hK : 1 ≤ K) (k : ℕ) :
    validData (effDegrade D K k) := by
  exact (degradedData_effDegrade D hvalid K hK k).1

theorem r1a_eff (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (_hIV : InteriorVStatement) (hIVC : InteriorVolumeCalculusEff) :
    R1aEff := by
  let hBVstmt : BallVolumeTwoSidedStatement := BallVolumeTwoSidedStatement_of_Eff hBV
  intro hHBL_oracle Din epsCover hvalid heps
  by_cases heps_le : epsCover ≤ 1
  · obtain ⟨C_R, hC_R, D_R, hdeg, hcSize, hCRbound, hsubset_mem⟩ :=
      r1a_degraded_for_subset_eff hBVstmt hVPlus hIVC Din epsCover hvalid heps heps_le
    obtain ⟨K_hbl, hK_hbl, hHBL⟩ := hHBL_oracle D_R hdeg.1
    set Dhbl := effDegrade D_R K_hbl 14
    have hdeg_hbl : degradedData D_R Dhbl := degradedData_effDegrade D_R hdeg.1 K_hbl hK_hbl 14
    have hdeg_Din_Dhbl : degradedData Din Dhbl := degradedData_trans hdeg hdeg_hbl
    set L_eps := max 0 (-Real.log epsCover)
    set Dcover := {Dhbl with sigma := fun n => Dhbl.sigma n + Real.log (L_eps + 1)}
    have hdeg_cover : degradedData Din Dcover := by
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10, h11, h12, h13, h14, h15⟩ := hdeg_Din_Dhbl
      have hLeps : 0 ≤ Real.log (L_eps + 1) := by
        have : 0 ≤ L_eps := le_max_left _ _
        have : 1 ≤ L_eps + 1 := by linarith
        exact Real.log_nonneg this
      refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩, h10, h11, h12, h13, h14, ?_⟩
      · exact Sublinear_add h8 (Sublinear_const (show 0 ≤ Real.log (L_eps + 1) from hLeps))
      · intro n hn
        exact (h9 n hn).trans (by linarith)
      · intro n
        exact (h15 n).trans (by linarith)
    have hCov : CoverFor Din Dcover epsCover := by
      intro n r S alpha beta hmem
      set radius := rmin n S.card + Nat.ceil (Dhbl.sigma n)
      set δ := Real.exp (-(Dhbl.sigma n))
      set thresh := epsCover * (S.card : ℝ)
      obtain ⟨centers, hcenters_card, hcenters_bound⟩ := greedy_peel_cover S radius δ thresh (by
        have := hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (this.1 n))) (by
        intros R hR_sub hR_thresh
        obtain ⟨a, ha⟩ := hHBL (hsubset_mem n r S R alpha beta hmem hR_sub hR_thresh)
        refine' ⟨a, ha.trans _⟩
        gcongr
        exact add_le_add (rmin_mono <| Finset.card_le_card hR_sub) le_rfl) (Nat.ceil (Real.exp (Dhbl.sigma n) * L_eps))
      refine' ⟨centers, _, _⟩
      · refine' le_trans (Nat.cast_le.mpr hcenters_card) _
        refine' le_trans (Nat.ceil_lt_add_one (by positivity) |> le_of_lt) _
        rw [Real.exp_add, Real.exp_log (by positivity)]
        nlinarith [Real.add_one_le_exp (Dhbl.sigma n), show 0 ≤ Dhbl.sigma n from hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1.1 n]
      · rw [Nat.cast_sub]
        · refine' le_trans _ (hcenters_bound.elim (fun h => h) fun h => h.trans _)
          · gcongr
            refine' coveredByBalls_mono_radius _ _ _
            exact Nat.add_le_add_left (Nat.ceil_mono <| le_add_of_nonneg_right <| Real.log_nonneg <| by linarith [le_max_left 0 (-Real.log epsCover), le_max_right 0 (-Real.log epsCover)]) _
          · have h_exp : (1 - δ) ^ ⌈Real.exp (Dhbl.sigma n) * L_eps⌉₊ ≤ Real.exp (-δ * ⌈Real.exp (Dhbl.sigma n) * L_eps⌉₊) := by
              have h_exp : (1 - δ) ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
              exact le_trans (pow_le_pow_left₀ (sub_nonneg.2 <| Real.exp_le_one_iff.2 <| neg_nonpos.2 <| show 0 ≤ Dhbl.sigma n from hdeg_Din_Dhbl.1.2.2.2.2.2.2.2.1.1 _) h_exp _) <| by rw [← Real.exp_nat_mul]; ring_nf; norm_num
            refine' mul_le_mul_of_nonneg_right (h_exp.trans _) (Nat.cast_nonneg _)
            rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_exp]
            simp +zetaDelta at *
            rw [Real.exp_neg]
            cases max_cases (0 : ℝ) (-Real.log epsCover) <;> nlinarith [Nat.le_ceil (Real.exp (Dhbl.sigma n) * max 0 (-Real.log epsCover)), Real.exp_pos (Dhbl.sigma n), mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (Dhbl.sigma n))), Real.log_le_sub_one_of_pos heps]
        · exact Finset.card_filter_le _ _
    set K_final := K_hbl * C_R * 16384 + K_hbl + L_eps + 1
    use K_final
    constructor
    · have h0 : 0 ≤ K_hbl := le_trans zero_le_one hK_hbl
      have h1 : 0 ≤ C_R := le_trans zero_le_one hC_R
      have h2 : 0 ≤ L_eps := le_max_left _ _
      have h3 : 0 ≤ K_hbl * C_R * 16384 := by positivity
      linarith
    · set Dfinal := effDegrade Din K_final 14
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
        · exact hcSize
        · exact Eq.trans hdeg_cover.2.2.2.2.1.symm rfl
        · exact Eq.trans hdeg_cover.2.2.2.2.2.1.symm rfl
        · intro n
          have hb2 : Dhbl.sigma n = K_hbl * (effEnv 14 D_R.sigma n + 1) := rfl
          have hb3 : Dfinal.sigma n = K_final * (effEnv 14 Din.sigma n + 1) := rfl
          have hL_eps_le : Real.log (L_eps + 1) ≤ L_eps := by
            have := Real.log_le_sub_one_of_pos (show 0 < L_eps + 1 by positivity)
            linarith
          have hd1 : Dcover.sigma n = K_hbl * (effEnv 14 D_R.sigma n + 1) + Real.log (L_eps + 1) := rfl
          have hDR_le : ∀ m, D_R.sigma m ≤ C_R * (Din.sigma m + 1) := hCRbound
          have hEnv_le := effEnv_mono hDR_le 14 n
          have hcomp := effEnv_comp 14 (i := 0) (C := C_R) hC_R (hvalid.2.2.2.2.2.2.2.1.1) n
          have h0_eq : (fun m => C_R * (effEnv 0 Din.sigma m + 1)) = fun m => C_R * (Din.sigma m + 1) := rfl
          rw [h0_eq] at hcomp
          have h_pow : (2 : ℝ) ^ 14 = 16384 := by norm_num
          rw [h_pow] at hcomp
          have hEnv_pos : 1 ≤ effEnv 14 Din.sigma n + 1 := by
            have : 0 ≤ effEnv 14 Din.sigma n := effEnv_nonneg 14 Din.sigma (hvalid.2.2.2.2.2.2.2.1.1) n
            linarith
          have h0 : 0 ≤ K_hbl := le_trans zero_le_one hK_hbl
          have h1 : 0 ≤ C_R := le_trans zero_le_one hC_R
          have h2 : 0 ≤ L_eps := le_max_left _ _
          have hDcover_le : Dcover.sigma n ≤ K_hbl * ((16384 * C_R) * (effEnv 14 Din.sigma n + 1) + 1) + L_eps := by nlinarith
          have heq : K_hbl * ((16384 * C_R) * (effEnv 14 Din.sigma n + 1) + 1) + L_eps = K_hbl * C_R * 16384 * (effEnv 14 Din.sigma n + 1) + K_hbl + L_eps := by ring
          have hle : K_hbl * C_R * 16384 * (effEnv 14 Din.sigma n + 1) + K_hbl + L_eps ≤ (K_hbl * C_R * 16384 + K_hbl + L_eps + 1) * (effEnv 14 Din.sigma n + 1) := by nlinarith
          have heq2 : (K_hbl * C_R * 16384 + K_hbl + L_eps + 1) * (effEnv 14 Din.sigma n + 1) = Dfinal.sigma n := hb3.symm
          exact le_trans hDcover_le (le_trans (le_of_eq heq) (le_trans hle (le_of_eq heq2)))
      intro n r S alpha beta hmem
      exact stabilityCoverConclusion_mono
        (hdeg_final.2.2.2.2.2.2 n)
        (Nat.ceil_mono (hdeg_final.2.2.2.2.2.2 n))
        (hCov hmem)
  · use 1
    constructor
    · linarith
    · intro n r S alpha beta hmem
      have h_eps : 1 ≤ epsCover := by linarith
      have h_empty :=
        stabilityCoverConclusion_empty_of_one_le (n := n) (S := S)
          (epsCover := epsCover) (coverSlack := 0) (radiusSlack := 0) h_eps
      exact stabilityCoverConclusion_mono (by
        have hvalid_1 : validData (effDegrade Din 1 14) := validData_effDegrade Din hvalid 1 le_rfl 14
        exact hvalid_1.2.2.2.2.2.2.2.1.1 n) (Nat.zero_le _) h_empty

end HarperStability
