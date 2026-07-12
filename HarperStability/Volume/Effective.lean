import HarperStability.Volume.Basic
import HarperStability.Volume.BallEntropy
import HarperStability.Interface.Effective

/-!
# Effective volume toolbox (v0.3)

Both targets re-expose the slack of the PROVED v0.2 volume theorems as
an explicit logarithmic envelope `effLog K n = K * (log (n+2) + 1)`.
Route: the existing proofs of `BallVolumeTwoSidedStatement` /
`InteriorVolumeCalculusStatement` construct their sublinear slack from
Stirling-type estimates and finitely many polynomial factors — replay
the same chains keeping the explicit `C * log (n+2) + C` bound instead
of packaging it as `Sublinear`; absorb finitely many small dimensions
into `K`.  Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

attribute [local instance] Classical.propDecidable

private lemma effLog_one_dominates_log_succ (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ effLog 1 n := by
  unfold effLog
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

private theorem ball_volume_two_sided_log :
    ∀ n t : ℕ, t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) -
          Real.log ((n : ℝ) + 1)) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤
        Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) +
          Real.log ((n : ℝ) + 1)) := by
  intro n t ht
  by_cases ht0 : t = 0
  · simp +decide [ht0, ball]
    simp +decide [hDist_eq_zero_iff, Real.exp_add, Real.exp_sub,
      Real.exp_log (Nat.cast_add_one_pos _)]
    unfold H
    norm_num [Finset.filter_eq']
    exact inv_le_one_of_one_le₀ <| by linarith
  · constructor
    · have h_ball_ge_choose : (ball (∅ : Cube n) t).card ≥ (n.choose t : ℝ) := by
        rw [ball_empty_card_eq_binomPrefix]
        exact_mod_cast Finset.single_le_sum
          (fun x _ => Nat.zero_le (Nat.choose n x))
          (Finset.mem_range.mpr (Nat.lt_succ_self t))
      have h_choose_ge_exp :
          (n.choose t : ℝ) ≥
            (Real.exp (H ((t : ℝ) / n) * (n : ℝ))) / (n + 1) := by
        have h_choose_ge_exp :
            (n.choose t : ℝ) * ((t : ℝ) / n) ^ t *
                (1 - (t : ℝ) / n) ^ (n - t) ≥ 1 / (n + 1) := by
          have h_choose_ge_exp :
              (n.choose t : ℝ) * ((t : ℝ) / n) ^ t *
                  (1 - (t : ℝ) / n) ^ (n - t) ≥
                binTerm ((t : ℝ) / n) n t := by
            unfold binTerm
            ring_nf
            norm_num
          exact le_trans
            (mode_ge_inv (Nat.pos_of_ne_zero (by aesop)) (by omega))
            h_choose_ge_exp
        have h_exp_eq :
            Real.exp (H ((t : ℝ) / n) * (n : ℝ)) =
              (((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t))⁻¹ := by
          convert exp_H_eq (Nat.pos_of_ne_zero ht0) (by omega : t + 1 ≤ n) using 1
        field_simp
        rw [mul_comm, h_exp_eq, inv_eq_one_div, div_le_iff₀]
        · rw [ge_iff_le, div_le_iff₀] at h_choose_ge_exp <;>
            first | positivity | linarith
        · exact mul_pos
            (pow_pos
              (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht0))
                (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by aesop_cat)))) _)
            (pow_pos
              (sub_pos.mpr (by
                rw [div_lt_iff₀
                  (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by aesop_cat)))]
                norm_cast
                linarith [Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0])) _)
      rw [Real.exp_sub, Real.exp_log (by positivity)]
      linarith
    · have h_binom :
          (ball (∅ : Cube n) t).card * ((t : ℝ) / n) ^ t *
              (1 - (t : ℝ) / n) ^ (n - t) ≤ 1 := by
        have h_binom :
            (ball (∅ : Cube n) t).card * ((t : ℝ) / n) ^ t *
                (1 - (t : ℝ) / n) ^ (n - t) ≤
              ∑ i ∈ Finset.range (t + 1), binTerm ((t : ℝ) / n) n i := by
          convert Finset.sum_le_sum fun i hi =>
            choose_mul_modeWeight_le (Finset.mem_range_succ_iff.mp hi)
              (by linarith [Nat.div_mul_le_self n 2])
              (show (t : ℝ) / n ≤ 1 / 2 from by
                rw [div_le_div_iff₀] <;> norm_cast <;>
                  linarith [Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0]) using 1
          · norm_num [mul_assoc, Finset.sum_mul _ _ _]
            rw [ball_empty_card_eq_binomPrefix]
            unfold binomPrefix
            norm_num [Finset.sum_mul _ _ _]
        exact h_binom.trans
          (le_trans
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono
                (Nat.succ_le_succ
                  (show t ≤ n from ht.trans (Nat.div_le_self _ _))))
              fun _ _ _ => binTerm_nonneg (by positivity)
                (by
                  exact div_le_one_of_le₀
                    (by norm_cast; linarith [Nat.div_mul_le_self n 2])
                    (by positivity)) _ _)
            (by rw [binTerm_sum]))
      by_cases hn : n = 0 <;> simp_all +decide [mul_assoc]
      rw [Real.exp_add, Real.exp_log (by positivity)]
      rw [exp_H_eq]
      · rw [inv_mul_eq_div, le_div_iff₀]
        · exact h_binom.trans (by norm_cast; linarith)
        · exact mul_pos (pow_pos (by positivity) _)
            (pow_pos
              (sub_pos.mpr (by
                rw [div_lt_iff₀ (by positivity)]
                norm_cast
                linarith [Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0])) _)
      · exact Nat.pos_of_ne_zero ht0
      · omega

theorem ball_volume_two_sided_eff : BallVolumeTwoSidedEff := by
  refine ⟨1, by norm_num, ?_⟩
  intro n t ht
  obtain ⟨hLower, hUpper⟩ := ball_volume_two_sided_log n t ht
  have hlog := effLog_one_dominates_log_succ n
  constructor
  · exact (Real.exp_le_exp.mpr (by linarith)).trans hLower
  · exact hUpper.trans (Real.exp_le_exp.mpr (by linarith))

set_option maxHeartbeats 1600000 in
lemma interior_rmin_slack_eff :
  ∀ alphaMin c0 : ℝ, 0 < alphaMin → 0 < c0 →
    ∃ C_V : ℝ, 1 ≤ C_V ∧
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 →
        0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K n := by
  intro alphaMin c0 halphaMin hc0
  by_cases hcase : alphaMin ≤ 1 / 2 - c0
  · -- Main interior case.
    set lo := alphaMin / 2 with hlo_def
    set hi := 1 / 2 - c0 / 2 with hhi_def
    have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
    have hhi_lt : hi < 1 / 2 := by rw [hhi_def]; linarith
    have hlohi : lo ≤ hi := by rw [hlo_def, hhi_def]; linarith
    have hc0_half : c0 < 1 / 2 := by linarith
    obtain ⟨C0, hC0_pos, hinv⟩ := entropy_inversion_compact lo hi hlo_pos hhi_lt hlohi
    have hvol0_log := ball_volume_two_sided_log
    set vol0 : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1)
    have hvol0_sub : Sublinear vol0 := sublinear_log_succ
    have hvol0 : ∀ n t : ℕ, t ≤ n / 2 → Real.exp (H ((t : ℝ) / n) * n - vol0 n) ≤ (ball (∅ : Cube n) t).card ∧ (ball (∅ : Cube n) t).card ≤ Real.exp (H ((t : ℝ) / n) * n + vol0 n) := by
      intro n t ht
      have h1 := (hvol0_log n t ht).1
      have h2 := (hvol0_log n t ht).2
      exact ⟨h1, h2⟩
    set δ := H alphaMin - H lo with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def]; apply sub_pos.mpr
      exact H_lt_H hlo_pos.le (by rw [hlo_def]; linarith) (by linarith)
    set M := min (c0 / (4 * C0)) (δ / 2) with hM_def
    have hM_pos : 0 < M := lt_min (by positivity) (by linarith)
    have hM_le1 : M ≤ c0 / (4 * C0) := min_le_left _ _
    have hM_le2 : M ≤ δ / 2 := min_le_right _ _
    set C_V := max 1 (max (1 / M) C0) with hCV_def
    have hCV1 : (1 : ℝ) ≤ C_V := le_max_left _ _
    have hCV_invM : 1 / M ≤ C_V := le_trans (le_max_left _ _) (le_max_right _ _)
    have hCV_C0 : C0 ≤ C_V := le_trans (le_max_right _ _) (le_max_right _ _)
    obtain ⟨NA, hNA⟩ := hvol0_sub.2 (c0 / (8 * C0)) (by positivity)
    obtain ⟨NB, hNB⟩ := hvol0_sub.2 (M / 4) (by positivity)
    obtain ⟨NC, hNC⟩ := exists_nat_ge (8 / c0)
    set N0 := max (max NA NB) (max NC 1) + 1 with hN0_def
    have hN0_ge1 : 1 ≤ N0 := by omega
    have hN0_props : ∀ n : ℕ, N0 ≤ n →
        C0 * vol0 n + 1 ≤ (c0 / 4) * n ∧ vol0 n ≤ (M / 4) * n := by
      intro n hn
      have hnA : NA ≤ n := by omega
      have hnB : NB ≤ n := by omega
      have hnC : NC ≤ n := by omega
      have hvA : vol0 n ≤ (c0 / (8 * C0)) * n := hNA n hnA
      have hvB : vol0 n ≤ (M / 4) * n := hNB n hnB
      have hcn : (8 : ℝ) / c0 ≤ (n : ℝ) := le_trans hNC (by exact_mod_cast hnC)
      have h1 : (1 : ℝ) ≤ (c0 / 8) * n := by
        rw [div_le_iff₀ hc0] at hcn; nlinarith
      refine ⟨?_, hvB⟩
      have hC0ne : C0 ≠ 0 := hC0_pos.ne'
      have hstep : C0 * vol0 n ≤ (c0 / 8) * n := by
        have h := mul_le_mul_of_nonneg_left hvA hC0_pos.le
        have heq : C0 * (c0 / (8 * C0) * (n : ℝ)) = (c0 / 8) * n := by
          field_simp
        rw [heq] at h; exact h
      linarith
    set K := max (C0 + 1) ((N0 : ℝ) + 1)
    have hK1 : 1 ≤ K := by
      have hN0_real : (1 : ℝ) ≤ (N0 : ℝ) + 1 := by
        have hN0_nonneg : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast Nat.zero_le N0
        linarith
      exact hN0_real.trans (le_max_right _ _)
    refine ⟨C_V, hCV1, K, hK1, ?_⟩
    · intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
      have h_alpha_le : alpha ≤ 1 / 2 - c0 := by linarith
      have h_alpha_lo : lo ≤ alpha := by rw [hlo_def]; linarith
      have h_alpha_hi : alpha ≤ hi := by rw [hhi_def]; linarith
      set s := rmin n k with hs_def
      set E := C_V * sizeSlack + (C0 * vol0 n + 1 + (if n < N0 then (n : ℝ) else 0)) with hE_def
      have hE_le_effLog : E ≤ C_V * sizeSlack + effLog K n := by
        rw [hE_def, effLog]
        have hvol : vol0 n ≤ Real.log ((n : ℝ) + 2) := by
          have hn_nn : (0 : ℝ) ≤ n := by positivity
          apply Real.log_le_log (by positivity) (by linarith)
        by_cases hn_small : n < N0
        · have hbump : (if n < N0 then (n : ℝ) else 0) = (n : ℝ) := if_pos hn_small
          rw [hbump]
          have hnN0 : (n : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast (le_of_lt hn_small)
          have hk1 : C0 * vol0 n ≤ K * Real.log ((n : ℝ) + 2) := by
            calc C0 * vol0 n ≤ C0 * Real.log ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left hvol hC0_pos.le
              _ ≤ K * Real.log ((n : ℝ) + 2) := by
                have hK_C0 : C0 ≤ K := (by linarith : C0 ≤ C0 + 1).trans (le_max_left _ _)
                exact mul_le_mul_of_nonneg_right hK_C0 (Real.log_nonneg (by linarith))
          have hk2 : 1 + (n : ℝ) ≤ K := by
            calc 1 + (n : ℝ) ≤ 1 + (N0 : ℝ) := by linarith [hnN0]
              _ ≤ K := by
                have : (N0 : ℝ) + 1 ≤ K := le_max_right _ _
                linarith
          linarith
        · have hbump0 : (if n < N0 then (n : ℝ) else 0) = 0 := if_neg hn_small
          rw [hbump0]
          have hk1 : C0 * vol0 n ≤ K * Real.log ((n : ℝ) + 2) := by
            calc C0 * vol0 n ≤ C0 * Real.log ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left hvol hC0_pos.le
              _ ≤ K * Real.log ((n : ℝ) + 2) := by
                have hkC : C0 ≤ K := (by linarith : C0 ≤ C0 + 1).trans (le_max_left _ _)
                exact mul_le_mul_of_nonneg_right hkC (Real.log_nonneg (by linarith))
          have hk2 : (1 : ℝ) ≤ K := by
            have : C0 + 1 ≤ K := le_max_left _ _
            linarith [hC0_pos]
          linarith
      apply le_trans _ hE_le_effLog
      show |(s : ℝ) - alpha * n| ≤ E
      have hs_le_n : (s : ℝ) ≤ n := by exact_mod_cast rmin_le_n n k
      have hs_nn : (0 : ℝ) ≤ (s : ℝ) := by positivity
      have h_an_0 : 0 ≤ alpha * n := mul_nonneg (by linarith) hn_nn
      have h_an_n : alpha * n ≤ n := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - alpha by linarith) hn_nn]
      have hvol0n : 0 ≤ vol0 n := hvol0_sub.1 n
      have hCVs0 : 0 ≤ C_V * sizeSlack := mul_nonneg (by linarith) h_s0
      have h_triv : |(s : ℝ) - alpha * n| ≤ n := by
        rw [abs_le]; constructor <;> linarith
      by_cases hn_small : n < N0
      · have hbump : (if n < N0 then (n : ℝ) else 0) = (n : ℝ) := if_pos hn_small
        have hEn : (n : ℝ) ≤ E := by
          rw [hE_def, hbump]; nlinarith [hCVs0, mul_nonneg hC0_pos.le hvol0n]
        linarith [h_triv, hEn]
      · have hnN0 : N0 ≤ n := Nat.not_lt.mp hn_small
        have hn1 : 1 ≤ n := le_trans hN0_ge1 hnN0
        obtain ⟨hA, hB⟩ := hN0_props n hnN0
        have hbump0 : (if n < N0 then (n : ℝ) else 0) = 0 := if_neg hn_small
        have hE_eq : E = C_V * sizeSlack + (C0 * vol0 n + 1) := by rw [hE_def, hbump0]; ring
        by_cases hslack : M * n ≤ sizeSlack
        · have hEn : (n : ℝ) ≤ E := by
            have h1 : (n : ℝ) ≤ C_V * sizeSlack := by
              have h2 : (1 / M) * (M * n) ≤ C_V * sizeSlack :=
                mul_le_mul hCV_invM hslack (by positivity) (by linarith)
              have h3 : (1 / M) * (M * (n : ℝ)) = n := by field_simp
              linarith [h2, h3.ge, h3.le]
            rw [hE_eq]; nlinarith [mul_nonneg hC0_pos.le hvol0n]
          linarith [h_triv, hEn]
        · push_neg at hslack
          have hlogU : Real.log k ≤ H alpha * n + sizeSlack := by
            have := (abs_le.mp h_log).2; linarith
          have hlogL : H alpha * n - sizeSlack ≤ Real.log k := by
            have := (abs_le.mp h_log).1; linarith
          have hCs : C0 * sizeSlack ≤ (c0 / 4) * n := by
            have hs_le : sizeSlack ≤ (c0 / (4 * C0)) * n :=
              le_trans hslack.le (mul_le_mul_of_nonneg_right hM_le1 hn_nn)
            have hmul := mul_le_mul_of_nonneg_left hs_le hC0_pos.le
            rw [show C0 * ((c0 / (4 * C0)) * (n : ℝ)) = (c0 / 4) * n by field_simp] at hmul
            linarith
          have halpha_mul : alpha * n ≤ (1 / 2 - c0) * n :=
            mul_le_mul_of_nonneg_right h_alpha_le hn_nn
          have hfit : alpha * n + C0 * sizeSlack + C0 * vol0 n + 1 ≤ hi * n := by
            rw [hhi_def]; nlinarith [hA, hCs, halpha_mul]
          have hgap : sizeSlack + vol0 n < δ * n := by
            have h1 : sizeSlack < (δ / 2) * n :=
              lt_of_lt_of_le hslack (mul_le_mul_of_nonneg_right hM_le2 hn_nn)
            have h2 : vol0 n ≤ (δ / 8) * n :=
              le_trans hB (mul_le_mul_of_nonneg_right (by linarith) hn_nn)
            have h3 : (δ / 2) * n + (δ / 8) * n ≤ δ * n := by nlinarith [mul_nonneg hδ_pos.le hn_nn]
            linarith
          have hUp := rmin_clean_upper (n := n) (k := k) (alpha := alpha)
            (sizeSlack := sizeSlack) (C0 := C0) (vn := vol0 n) (lo := lo) (hi := hi)
            hn1 hC0_pos hk1 hk2 hlo_pos hlohi hhi_lt h_alpha_lo h_alpha_hi h_s0 hvol0n
            hinv (fun t ht => (hvol0 n t ht).1) hlogU hfit
          have hLo := rmin_clean_lower (n := n) (k := k) (alpha := alpha)
            (sizeSlack := sizeSlack) (C0 := C0) (vn := vol0 n) (lo := lo) (hi := hi)
            (alphaMin := alphaMin)
            hn1 hC0_pos hk1 hk2 hlo_pos hlohi hhi_lt h_alpha_lo h_alpha_hi h_s0 hvol0n
            hinv (fun t ht => (hvol0 n t ht).2) hlogL (by rw [hlo_def]; linarith) h_aM
            (by linarith) (by rw [← hδ_def]; exact hgap)
          rw [abs_le, hE_eq]
          have hCsCV : C0 * sizeSlack ≤ C_V * sizeSlack :=
            mul_le_mul_of_nonneg_right hCV_C0 h_s0
          exact ⟨by linarith [hLo, hCsCV], by linarith [hUp, hCsCV]⟩
  · -- Degenerate case: no admissible `alpha` exists.
    refine ⟨1, le_refl 1, 1, le_refl 1, ?_⟩
    intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
    exfalso
    apply hcase
    have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
    linarith

set_option maxHeartbeats 3200000 in
lemma interior_v_slack_eff :
  ∀ alphaMin c0 : ℝ, 0 < alphaMin → 0 < c0 →
    ∃ C_V : ℝ, 1 ≤ C_V ∧
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 →
        0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |Real.log ((V n k r : ℝ)) - H (alpha + beta) * (n : ℝ)| ≤
            C_V * sizeSlack + effLog K n := by
  intro alphaMin c0 halphaMin hc0
  by_cases hcase : alphaMin ≤ 1 / 2 - c0
  ·
    set lo := alphaMin / 2 with hlo_def
    set hi := 1 / 2 - c0 / 2 with hhi_def
    have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
    have hhi_lt1 : hi < 1 := by rw [hhi_def]; linarith
    have hlohi : lo ≤ hi := by rw [hlo_def, hhi_def]; linarith
    obtain ⟨C1, hC1, K1, hK1, hrmin⟩ := interior_rmin_slack_eff alphaMin c0 halphaMin hc0
    set vol1 : ℕ → ℝ := fun n => effLog K1 n
    have hvol1_sub : Sublinear (effLog K1) := by
      have hlog_add : ∀ n : ℕ, Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 1) + Real.log 2 := by
        intro n
        rw [← Real.log_mul (by positivity) (by positivity)]
        apply Real.log_le_log (by positivity)
        have hn_nn : 0 ≤ (n : ℝ) := by positivity
        linarith
      have hK10 : 0 ≤ K1 := by linarith
      refine Sublinear_of_le (fun n => by
        unfold effLog
        exact mul_nonneg hK10 (add_nonneg (Real.log_nonneg (by linarith)) zero_le_one))
        (fun n => ?_)
        (Sublinear_add
          (Sublinear_smul hK10 sublinear_log_succ)
          (@Sublinear_const (K1 * (Real.log 2 + 1))
            (mul_nonneg hK10 (add_nonneg (Real.log_nonneg (by norm_num)) zero_le_one))))
      unfold effLog
      have : K1 * (Real.log ((n : ℝ) + 2) + 1) ≤ K1 * (Real.log ((n : ℝ) + 1) + Real.log 2 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hlog_add n]) hK10
      have h_eq : K1 * (Real.log ((n : ℝ) + 1) + Real.log 2 + 1) = K1 * Real.log ((n : ℝ) + 1) + K1 * (Real.log 2 + 1) := by ring
      rw [h_eq] at this
      exact this
    have hC1pos : 0 < C1 := by linarith
    obtain ⟨L, hL0, hlip⟩ := entropy_lipschitz lo hi hlo_pos hhi_lt1 hlohi
    have hvol0_log := ball_volume_two_sided_log
    set vol0 : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1)
    have hvol0_sub : Sublinear vol0 := sublinear_log_succ
    have hvol0 : ∀ n t : ℕ, t ≤ n / 2 → Real.exp (H ((t : ℝ) / n) * n - vol0 n) ≤ (ball (∅ : Cube n) t).card ∧ (ball (∅ : Cube n) t).card ≤ Real.exp (H ((t : ℝ) / n) * n + vol0 n) := by
      intro n t ht
      have h1 := (hvol0_log n t ht).1
      have h2 := (hvol0_log n t ht).2
      exact ⟨h1, h2⟩
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hHaM_pos : 0 < H alphaMin := Real.binEntropy_pos halphaMin (by
      rw [hlo_def] at hlohi; linarith)
    set η := min (c0 / 2) (alphaMin / 2) with hη_def
    have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
    have hη_le1 : η ≤ c0 / 2 := min_le_left _ _
    have hη_le2 : η ≤ alphaMin / 2 := min_le_right _ _
    set C_V := max 1 (max (L * C1) (max (2 * C1 * Real.log 2 / η) (Real.log 2 / H alphaMin)))
      with hCV_def
    have hCV1 : (1 : ℝ) ≤ C_V := le_max_left _ _
    have hCV_LC1 : L * C1 ≤ C_V :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hCV_slack : 2 * C1 * Real.log 2 / η ≤ C_V :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hCV_logHaM : Real.log 2 / H alphaMin ≤ C_V :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    obtain ⟨NA, hNA⟩ := hvol1_sub.2 (η / 4) (by linarith)
    obtain ⟨NC, hNC⟩ := exists_nat_ge (4 / η)
    set N0 := max NA (max NC 1) + 1 with hN0_def
    have hN0_ge1 : 1 ≤ N0 := by omega
    have hN0v : ∀ n : ℕ, N0 ≤ n → vol1 n + 1 ≤ (η / 2) * n := by
      intro n hn
      have hnA : NA ≤ n := by omega
      have hnC : NC ≤ n := by omega
      have hv : vol1 n ≤ (η / 4) * n := hNA n hnA
      have hcn : (4 : ℝ) / η ≤ (n : ℝ) := le_trans hNC (by exact_mod_cast hnC)
      have h1 : (1 : ℝ) ≤ (η / 4) * n := by
        rw [div_le_iff₀ hη_pos] at hcn; nlinarith
      linarith
    set K := max (L * K1 + L + 2 + (N0 : ℝ) * Real.log 2) 1
    have hK1_bound : 1 ≤ K := by
      exact le_max_right _ _
    refine ⟨C_V, hCV1, K, hK1_bound, ?_⟩
    · intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
      have hab_le : alpha + beta ≤ 1 / 2 - c0 := h_sum
      have hab0 : 0 ≤ alpha + beta := by linarith
      have hab1 : alpha + beta ≤ 1 := by linarith
      have hab_lo : lo ≤ alpha + beta := by rw [hlo_def]; linarith
      have hab_hi : alpha + beta ≤ hi := by rw [hhi_def]; linarith
      set s := rmin n k with hs_def
      set G := H (alpha + beta) * (n : ℝ) with hG_def
      set U := Real.log ((V n k r : ℝ)) with hU_def
      set volS := L * vol1 n + vol0 n + (L + 1) + (if n < N0 then (n : ℝ) * Real.log 2 else 0)
        with hvolS_def
      have hvolS_le_effLog : volS ≤ effLog K n := by
        rw [hvolS_def, effLog]
        have hvol0 : vol0 n ≤ Real.log ((n : ℝ) + 2) := by
          have hn_nn : (0 : ℝ) ≤ n := by positivity
          apply Real.log_le_log (by positivity) (by linarith)
        by_cases hn_small : n < N0
        · have hbump : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = (n : ℝ) * Real.log 2 := if_pos hn_small
          rw [hbump]
          have hnN0 : (n : ℝ) * Real.log 2 ≤ (N0 : ℝ) * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt hn_small)) (by positivity)
          have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
          have hlog_ge_one : 1 ≤ Real.log ((n : ℝ) + 2) + 1 := by linarith
          have hbump_nonneg : 0 ≤ (N0 : ℝ) * Real.log 2 :=
            mul_nonneg (by exact_mod_cast Nat.zero_le N0) (Real.log_nonneg (by norm_num))
          have h_part1 : L * vol1 n + vol0 n + (L + 1) ≤
              (L * K1 + L + 2) * (Real.log ((n : ℝ) + 2) + 1) := by
            calc L * vol1 n + vol0 n + (L + 1)
              _ = L * (K1 * (Real.log ((n : ℝ) + 2) + 1)) + vol0 n + (L + 1) := by unfold vol1 effLog; ring
              _ ≤ L * K1 * (Real.log ((n : ℝ) + 2) + 1) + Real.log ((n : ℝ) + 2) + (L + 1) := by linarith
              _ = (L * K1 + 1) * Real.log ((n : ℝ) + 2) + (L * K1 + L + 1) := by ring
              _ ≤ (L * K1 + L + 2) * Real.log ((n : ℝ) + 2) + (L * K1 + L + 2) := by
                have : L * K1 + L + 1 ≤ L * K1 + L + 2 := by linarith
                have : (L * K1 + 1) * Real.log ((n : ℝ) + 2) ≤ (L * K1 + L + 2) * Real.log ((n : ℝ) + 2) :=
                  mul_le_mul_of_nonneg_right (by linarith [hL0]) hlog_nonneg
                linarith
              _ = (L * K1 + L + 2) * (Real.log ((n : ℝ) + 2) + 1) := by ring
          have h_bump : (n : ℝ) * Real.log 2 ≤
              ((N0 : ℝ) * Real.log 2) * (Real.log ((n : ℝ) + 2) + 1) := by
            calc (n : ℝ) * Real.log 2 ≤ (N0 : ℝ) * Real.log 2 := hnN0
              _ ≤ ((N0 : ℝ) * Real.log 2) * (Real.log ((n : ℝ) + 2) + 1) := by
                nlinarith
          calc
            L * vol1 n + vol0 n + (L + 1) + (n : ℝ) * Real.log 2
                ≤ ((L * K1 + L + 2) + (N0 : ℝ) * Real.log 2) *
                    (Real.log ((n : ℝ) + 2) + 1) := by
                  nlinarith [h_part1, h_bump]
            _ ≤ K * (Real.log ((n : ℝ) + 2) + 1) := by
                  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        · have hbump0 : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = 0 := if_neg hn_small
          rw [hbump0]
          have h_part1 : L * vol1 n + vol0 n + (L + 1) + 0 ≤ K * (Real.log ((n : ℝ) + 2) + 1) := by
            calc L * vol1 n + vol0 n + (L + 1) + 0
              _ = L * (K1 * (Real.log ((n : ℝ) + 2) + 1)) + vol0 n + (L + 1) := by unfold vol1 effLog; ring
              _ ≤ L * K1 * (Real.log ((n : ℝ) + 2) + 1) + Real.log ((n : ℝ) + 2) + (L + 1) := by linarith
              _ = (L * K1 + 1) * Real.log ((n : ℝ) + 2) + (L * K1 + L + 1) := by ring
              _ ≤ (L * K1 + L + 2) * Real.log ((n : ℝ) + 2) + (L * K1 + L + 2) := by
                  have : L * K1 + L + 1 ≤ L * K1 + L + 2 := by linarith
                  have : (L * K1 + 1) * Real.log ((n : ℝ) + 2) ≤ (L * K1 + L + 2) * Real.log ((n : ℝ) + 2) :=
                    mul_le_mul_of_nonneg_right (by linarith [hL0]) (Real.log_nonneg (by linarith))
                  linarith
              _ = (L * K1 + L + 2) * (Real.log ((n : ℝ) + 2) + 1) := by ring
              _ ≤ K * (Real.log ((n : ℝ) + 2) + 1) := by
                have hbase_le : L * K1 + L + 2 ≤ K := by
                  have hbump_nonneg : 0 ≤ (N0 : ℝ) * Real.log 2 :=
                    mul_nonneg (by exact_mod_cast Nat.zero_le N0) (Real.log_nonneg (by norm_num))
                  exact (by linarith : L * K1 + L + 2 ≤ L * K1 + L + 2 + (N0 : ℝ) * Real.log 2).trans
                    (le_max_left _ _)
                exact mul_le_mul_of_nonneg_right hbase_le
                  (add_nonneg (Real.log_nonneg (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)) zero_le_one)
          linarith
      apply le_trans _ (by linarith [hvolS_le_effLog] : C_V * sizeSlack + volS ≤ C_V * sizeSlack + effLog K n)
      show |U - G| ≤ C_V * sizeSlack + volS
      -- V is between `1` and `2^n`.
      have hVle : V n k r ≤ (ball (∅ : Cube n) (s + r)).card := V_le_ball_rmin_add n k r hk2
      obtain ⟨t, ht_le, ht_ball_le, ht_max, ht_lower⟩ := vplus_skeleton n k r hk1 hk2
      have hV_ge1 : (1 : ℝ) ≤ (V n k r : ℝ) :=
        le_trans (by exact_mod_cast ball_card_pos n (t + r)) ht_lower
      have hVpos : (0 : ℝ) < (V n k r : ℝ) := by linarith
      have htriv : |U - G| ≤ (n : ℝ) * Real.log 2 := V_log_trivial hk1 hk2 hab0 hab1
      have hvolS_nn : 0 ≤ volS := by
        rw [hvolS_def]
        have : 0 ≤ (if n < N0 then (n : ℝ) * Real.log 2 else 0) := by
          split_ifs with h
          · positivity
          · exact le_refl 0
        have := hvol1_sub.1 n; have := hvol0_sub.1 n
        nlinarith [mul_nonneg hL0 (hvol1_sub.1 n)]
      have hCVs0 : 0 ≤ C_V * sizeSlack := mul_nonneg (by linarith) h_s0
      by_cases hn_small : n < N0
      · -- Burn-in regime: the trivial bound is absorbed by the bump term.
        have hbump : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = (n : ℝ) * Real.log 2 :=
          if_pos hn_small
        have : (n : ℝ) * Real.log 2 ≤ volS := by
          rw [hvolS_def, hbump]
          nlinarith [mul_nonneg hL0 (hvol1_sub.1 n), hvol0_sub.1 n, hL0]
        linarith [htriv, this]
      · have hnN0 : N0 ≤ n := Nat.not_lt.mp hn_small
        have hn1 : 1 ≤ n := le_trans hN0_ge1 hnN0
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hbump0 : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = 0 := if_neg hn_small
        have hvolS_eq : volS = L * vol1 n + vol0 n + (L + 1) := by rw [hvolS_def, hbump0]; ring
        have hN0prop : vol1 n + 1 ≤ (η / 2) * n := hN0v n hnN0
        by_cases hs0case : s = 0
        · -- `rmin n k = 0` forces `k = 1`, so the size slack itself dominates.
          have hb0 : (ball (∅ : Cube n) 0).card = 1 := by
            simp [ball_empty_card_eq_binomPrefix, binomPrefix]
          have hk_le1 : k ≤ 1 := by
            have := rmin_spec hk2; rw [← hs_def, hs0case, hb0] at this; exact this
          have hk_eq : k = 1 := le_antisymm hk_le1 hk1
          have hlogk0 : Real.log ((k : ℝ)) = 0 := by rw [hk_eq]; simp
          have hHan : H alpha * n ≤ sizeSlack := by
            have := (abs_le.mp h_log).1; rw [hlogk0] at this; linarith
          have hHaM_le : H alphaMin ≤ H alpha := H_le_H (by linarith) h_aM h_ah
          have h1 : H alphaMin * n ≤ sizeSlack :=
            le_trans (mul_le_mul_of_nonneg_right hHaM_le hn_nn) hHan
          have h3 : (n : ℝ) * Real.log 2 ≤ (Real.log 2 / H alphaMin) * sizeSlack := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hHaM_pos]; nlinarith [h1, hlog2_pos]
          have h4 : (Real.log 2 / H alphaMin) * sizeSlack ≤ C_V * sizeSlack :=
            mul_le_mul_of_nonneg_right hCV_logHaM h_s0
          linarith [htriv, h3, h4, hvolS_nn]
        · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0case
          have herr : |(s : ℝ) - alpha * n| ≤ C1 * sizeSlack + vol1 n :=
            hrmin n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
          set errRHS := C1 * sizeSlack + vol1 n with herrRHS_def
          by_cases hclean : errRHS + 1 ≤ η * n
          · -- Clean interior regime.
            have hbetan : beta * (n : ℝ) = r := by rw [h_beta]; field_simp
            have herr' := abs_le.mp herr
            -- Location of `(s+r)/n` and `(s-1+r)/n` inside `[lo, hi]`.
            have hsr_ratio_hi : ((s + r : ℕ) : ℝ) / n ≤ hi := by
              rw [div_le_iff₀ hnpos]; push_cast
              rw [hhi_def]; nlinarith [herr'.2, hbetan, hη_le1]
            have hsr_ratio_lo : lo ≤ ((s + r : ℕ) : ℝ) / n := by
              rw [le_div_iff₀ hnpos]; push_cast
              rw [hlo_def]; nlinarith [herr'.1, hbetan, hη_le2]
            have hs1r_ratio_hi : ((s - 1 + r : ℕ) : ℝ) / n ≤ hi := by
              rw [div_le_iff₀ hnpos]
              rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one]
              rw [hhi_def]; nlinarith [herr'.2, hbetan, hη_le1]
            have hs1r_ratio_lo : lo ≤ ((s - 1 + r : ℕ) : ℝ) / n := by
              rw [le_div_iff₀ hnpos]
              rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one]
              rw [hlo_def]; nlinarith [herr'.1, hbetan, hη_le2]
            have hsr_half : s + r ≤ n / 2 := by
              rw [Nat.le_div_iff_mul_le (by norm_num)]
              have : ((s + r : ℕ) : ℝ) ≤ hi * n := by
                rw [← div_le_iff₀ hnpos]; exact hsr_ratio_hi
              have h2 : ((s + r : ℕ) : ℝ) * 2 < n := by nlinarith [hhi_lt1, hhi_def, this]
              exact_mod_cast le_of_lt (by exact_mod_cast h2)
            have hs1r_half : s - 1 + r ≤ n / 2 := le_trans (by omega) hsr_half
            -- Logarithmic two-sided ball bounds.
            have logball : ∀ m : ℕ, m ≤ n / 2 →
                H ((m : ℝ) / n) * n - vol0 n ≤ Real.log ((ball (∅ : Cube n) m).card) ∧
                Real.log ((ball (∅ : Cube n) m).card) ≤ H ((m : ℝ) / n) * n + vol0 n := by
              intro m hm
              obtain ⟨hlo', hhi'⟩ := hvol0 n m hm
              refine ⟨?_, ?_⟩
              · calc H ((m : ℝ) / n) * n - vol0 n
                    = Real.log (Real.exp (H ((m : ℝ) / n) * n - vol0 n)) := (Real.log_exp _).symm
                  _ ≤ Real.log ((ball (∅ : Cube n) m).card) :=
                      Real.log_le_log (Real.exp_pos _) hlo'
              · calc Real.log ((ball (∅ : Cube n) m).card)
                    ≤ Real.log (Real.exp (H ((m : ℝ) / n) * n + vol0 n)) :=
                      Real.log_le_log (by exact_mod_cast ball_card_pos n m) hhi'
                  _ = H ((m : ℝ) / n) * n + vol0 n := Real.log_exp _
            -- Upper bound on `U`.
            obtain ⟨hbL_u, hbU_u⟩ := logball (s + r) hsr_half
            have hUp := log_ball_approx (n := n) (m := s + r) (gamma := alpha + beta)
              (vol := vol0 n) (L := L) (lo := lo) (hi := hi) hn1 hL0 hlip hbL_u hbU_u
              hsr_ratio_lo hsr_ratio_hi hab_lo hab_hi
            have heq_u : |((s + r : ℕ) : ℝ) - (alpha + beta) * n| = |(s : ℝ) - alpha * n| := by
              congr 1; push_cast; rw [add_mul, hbetan]; ring
            rw [heq_u] at hUp
            have hlogVle : U ≤ Real.log ((ball (∅ : Cube n) (s + r)).card) := by
              rw [hU_def]; exact Real.log_le_log hVpos (by exact_mod_cast hVle)
            -- Lower bound on `U`.
            obtain ⟨hbL_l, hbU_l⟩ := logball (s - 1 + r) hs1r_half
            have hLo := log_ball_approx (n := n) (m := s - 1 + r) (gamma := alpha + beta)
              (vol := vol0 n) (L := L) (lo := lo) (hi := hi) hn1 hL0 hlip hbL_l hbU_l
              hs1r_ratio_lo hs1r_ratio_hi hab_lo hab_hi
            have heq_l : |((s - 1 + r : ℕ) : ℝ) - (alpha + beta) * n| = |(s : ℝ) - 1 - alpha * n| := by
              congr 1; rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one, add_mul, hbetan]; ring
            rw [heq_l] at hLo
            have hs1_le_t : s - 1 ≤ t :=
              ht_max (s - 1) (by omega)
                (le_of_lt (ball_card_lt_of_lt_rmin (by omega : s - 1 < s)))
            have hball_mono : (ball (∅ : Cube n) (s - 1 + r)).card ≤ (ball (∅ : Cube n) (t + r)).card :=
              Finset.card_le_card (ball_subset_ball_of_le (by omega))
            have hlogVge : Real.log ((ball (∅ : Cube n) (s - 1 + r)).card) ≤ U := by
              rw [hU_def]
              exact Real.log_le_log (by exact_mod_cast ball_card_pos n (s - 1 + r))
                (le_trans (by exact_mod_cast hball_mono) ht_lower)
            -- Shift bound: `|s - 1 - alpha*n| ≤ errRHS + 1`.
            have hshift : |(s : ℝ) - 1 - alpha * n| ≤ errRHS + 1 := by
              rw [abs_le]; rw [herrRHS_def]; constructor <;> linarith [herr'.1, herr'.2]
            -- Combine into a two-sided estimate.
            have habs : |U - G| ≤ L * (errRHS + 1) + vol0 n := by
              rw [abs_le]
              refine ⟨?_, ?_⟩
              · have h1 : Real.log ((ball (∅ : Cube n) (s - 1 + r)).card) - G ≥
                    -(L * (errRHS + 1) + vol0 n) := by
                  have := (abs_le.mp hLo).1
                  have hle : L * |(s : ℝ) - 1 - alpha * n| ≤ L * (errRHS + 1) :=
                    mul_le_mul_of_nonneg_left hshift hL0
                  rw [hG_def]; linarith
                linarith [hlogVge]
              · have hle : L * |(s : ℝ) - alpha * n| ≤ L * (errRHS + 1) :=
                  mul_le_mul_of_nonneg_left (by rw [herrRHS_def]; linarith [herr'.1, herr'.2, abs_le.mpr ⟨herr'.1, herr'.2⟩]) hL0
                have := (abs_le.mp hUp).2
                rw [hG_def]; linarith [hlogVle]
            -- Absorb into `C_V * sizeSlack + volS`.
            have hfinal : L * (errRHS + 1) + vol0 n ≤ C_V * sizeSlack + volS := by
              rw [hvolS_eq, herrRHS_def]
              have hmul : L * C1 * sizeSlack ≤ C_V * sizeSlack :=
                mul_le_mul_of_nonneg_right hCV_LC1 h_s0
              nlinarith [hmul, hL0]
            exact le_trans habs hfinal
          · -- Non-clean regime with `n ≥ N0`: the size slack is large.
            push_neg at hclean
            have hbig : (η / 2) * n < C1 * sizeSlack := by
              rw [herrRHS_def] at hclean; linarith [hN0prop]
            have hss : (η / (2 * C1)) * n < sizeSlack := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hbig]
            have hcoef_nn : 0 ≤ 2 * C1 * Real.log 2 / η := by positivity
            have hb2 : (2 * C1 * Real.log 2 / η) * ((η / (2 * C1)) * n) ≤
                (2 * C1 * Real.log 2 / η) * sizeSlack :=
              mul_le_mul_of_nonneg_left hss.le hcoef_nn
            have hb3 : (2 * C1 * Real.log 2 / η) * ((η / (2 * C1)) * n) = (n : ℝ) * Real.log 2 := by
              field_simp
            have hb4 : (2 * C1 * Real.log 2 / η) * sizeSlack ≤ C_V * sizeSlack :=
              mul_le_mul_of_nonneg_right hCV_slack h_s0
            have : (n : ℝ) * Real.log 2 ≤ C_V * sizeSlack := by
              rw [← hb3]; linarith [hb2, hb4]
            linarith [htriv, this, hvolS_nn]
  · -- Degenerate case: no admissible `alpha` exists.
    refine ⟨1, le_refl 1, 1, le_refl 1, ?_⟩
    intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
    exfalso
    apply hcase
    have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
    linarith

theorem interior_volume_calculus_eff : InteriorVolumeCalculusEff := by
  intro alphaMin c0 halphaMin hc0
  obtain ⟨C_V1, hC_V1, K1, hK1, hV⟩ := interior_v_slack_eff alphaMin c0 halphaMin hc0
  obtain ⟨C_V2, hC_V2, K2, hK2, hrmin⟩ := interior_rmin_slack_eff alphaMin c0 halphaMin hc0
  use max C_V1 C_V2
  refine ⟨le_max_of_le_left hC_V1, max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog
  constructor
  · exact (hV n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog).trans (by
      have h1 : C_V1 * sizeSlack ≤ max C_V1 C_V2 * sizeSlack := mul_le_mul_of_nonneg_right (le_max_left C_V1 C_V2) hsizeSlack
      have h2 : effLog K1 n ≤ effLog (max K1 K2) n := by
        unfold effLog
        exact mul_le_mul_of_nonneg_right (le_max_left K1 K2) (add_nonneg (Real.log_nonneg (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)) zero_le_one)
      linarith)
  · exact (hrmin n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog).trans (by
      have h1 : C_V2 * sizeSlack ≤ max C_V1 C_V2 * sizeSlack := mul_le_mul_of_nonneg_right (le_max_right C_V1 C_V2) hsizeSlack
      have h2 : effLog K2 n ≤ effLog (max K1 K2) n := by
        unfold effLog
        exact mul_le_mul_of_nonneg_right (le_max_right K1 K2) (add_nonneg (Real.log_nonneg (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)) zero_le_one)
      linarith)


end HarperStability
