import HarperStability.Core.S7
import HarperStability.Interface.Effective

/-!
# Effective S7 (v0.3): the heavy ball at grade 10

Target: `S7Eff` — for fat+pinned `A` and `m ≥ K/eps^8`: a ball of radius
`⌈(q+4eps)m⌉` carrying an `exp(-((K/eps^8)*(effEnv 10 Q.sigma m + 1)))` mass
fraction.

Route: mirror `Core/S7.lean` (HBL-FAT, PROVED), replacing its
`∃ env, Sublinear env` packaging and the `∃ m1` threshold by explicit
envelopes:
* inputs: `hS5` (grade 8) and `hS6` (grade 10, v0.3.4) — their slacks add;
* the Fano/counting core of the v0.2 proof is quantitative already; its
  entropy budgets combine to `≤ K·(effEnv 9 Q.sigma m + 1)` with
  `1/eps`-polynomial constants (fold into `K`);
* grade 10 = one `effGeo` of padding for the assembly arithmetic;
* the v0.2 `∃ m1` threshold becomes `K/eps^8 ≤ m`, and `K` is UNIFORM over `eps` (v0.3.1): the `1/eps`-polynomial factors of the S5+S6+Fano chain (≈ `1/eps^6`) go into the explicit `K/eps^8`, NOT into a per-`eps` constant — the finitely many
  dimensions below any explicit threshold are absorbed by enlarging
  `K` (for `m < K` the statement is not claimed).
Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

lemma s7_eff_math_large {K K5 eps m : ℝ} {s7 s9 : ℝ} (heps : 0 < eps) (heps_half : eps ≤ 1 / 2)
    (hK5 : 1 ≤ K5) (hK : K5 * Real.log 2 ≤ K) (hm : 0 ≤ m) (hs9 : Real.sqrt ((s7 + 1) * (m + 1)) ≤ s9)
    (hmass : eps * m < (K5 / eps ^ 4) * (s7 + 1)) (hlog : 0 ≤ Real.log 2) :
    m * Real.log 2 ≤ (K / eps ^ 8) * (s9 + 1) := by
  have hs7_pos : 0 < s7 + 1 := by
    have h_zero_lt : 0 < (K5 / eps ^ 4) * (s7 + 1) := by
      calc 0 ≤ eps * m := mul_nonneg (le_of_lt heps) hm
        _ < (K5 / eps ^ 4) * (s7 + 1) := hmass
    have hk5_pos : 0 < K5 / eps ^ 4 := by positivity
    exact pos_of_mul_pos_right h_zero_lt (le_of_lt hk5_pos)
  have hm_bound : m < (K5 / eps ^ 5) * (s7 + 1) := by
    have : eps * m / eps < (K5 / eps ^ 4) * (s7 + 1) / eps :=
      div_lt_div_of_pos_right hmass heps
    have h1 : eps * m / eps = m := by
      rw [mul_comm, mul_div_cancel_right₀ _ (ne_of_gt heps)]
    have h2 : (K5 / eps ^ 4) * (s7 + 1) / eps = (K5 / eps ^ 5) * (s7 + 1) := by ring
    rwa [h1, h2] at this
  have hk5eps_nonneg : 0 ≤ K5 / eps ^ 5 := by positivity
  have h_sqrt_m : Real.sqrt m < Real.sqrt (K5 / eps ^ 5) * Real.sqrt (s7 + 1) := by
    have : Real.sqrt m < Real.sqrt ((K5 / eps ^ 5) * (s7 + 1)) := Real.sqrt_lt_sqrt hm hm_bound
    rwa [Real.sqrt_mul hk5eps_nonneg] at this
  have h_m_le2 : m ≤ Real.sqrt (K5 / eps ^ 5) * s9 := by
    calc m = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm).symm
      _ ≤ (Real.sqrt (K5 / eps ^ 5) * Real.sqrt (s7 + 1)) * Real.sqrt m := by
        have : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
        exact mul_le_mul_of_nonneg_right (le_of_lt h_sqrt_m) this
      _ ≤ (Real.sqrt (K5 / eps ^ 5) * Real.sqrt (s7 + 1)) * Real.sqrt (m + 1) := by
        have : Real.sqrt m ≤ Real.sqrt (m + 1) := by gcongr; linarith
        have : 0 ≤ Real.sqrt (K5 / eps ^ 5) * Real.sqrt (s7 + 1) := by positivity
        gcongr
      _ = Real.sqrt (K5 / eps ^ 5) * (Real.sqrt (s7 + 1) * Real.sqrt (m + 1)) := by ring
      _ = Real.sqrt (K5 / eps ^ 5) * Real.sqrt ((s7 + 1) * (m + 1)) := by
        have : 0 ≤ s7 + 1 := le_of_lt hs7_pos
        rw [← Real.sqrt_mul this]
      _ ≤ Real.sqrt (K5 / eps ^ 5) * s9 := by gcongr
  have hs9_pos : 0 ≤ s9 := by
    calc 0 ≤ Real.sqrt ((s7 + 1) * (m + 1)) := Real.sqrt_nonneg _
      _ ≤ s9 := hs9
  have h_sqrt_bound : Real.sqrt (K5 / eps ^ 5) * Real.log 2 ≤ K / eps ^ 8 := by
    have h1 : Real.sqrt (K5 / eps ^ 5) = Real.sqrt K5 * (1 / Real.sqrt (eps ^ 5)) := by
      have : K5 / eps ^ 5 = K5 * (1 / eps ^ 5) := by ring
      rw [this, Real.sqrt_mul (by positivity)]
      have : Real.sqrt (1 / eps ^ 5) = 1 / Real.sqrt (eps ^ 5) := by
        rw [Real.sqrt_div (by positivity)]
        have : Real.sqrt 1 = 1 := Real.sqrt_one
        rw [this]
      rw [this]
    have h2 : Real.sqrt K5 ≤ K5 := by
      have : Real.sqrt K5 ≤ Real.sqrt (K5 ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc K5 ≤ K5 * K5 := by nlinarith [hK5]
          _ = K5 ^ 2 := by ring
      rwa [Real.sqrt_sq (by positivity)] at this
    have h3 : 1 / Real.sqrt (eps ^ 5) ≤ 1 / eps ^ 8 := by
      have hpos : 0 < Real.sqrt (eps ^ 5) := by positivity
      have hpos2 : 0 < eps ^ 8 := by positivity
      rw [div_le_div_iff₀ hpos hpos2, one_mul, one_mul]
      have h_sq_bound : (eps ^ 8) ^ 2 ≤ (Real.sqrt (eps ^ 5)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]
        calc (eps ^ 8) ^ 2 = eps ^ 16 := by ring
          _ = eps ^ 5 * eps ^ 11 := by ring
          _ ≤ eps ^ 5 * (1 / 2) ^ 11 := by gcongr
          _ = eps ^ 5 / 2048 := by ring
          _ ≤ eps ^ 5 := by
            have : 0 ≤ eps ^ 5 := by positivity
            linarith
      have h_sqrt := Real.sqrt_le_sqrt h_sq_bound
      rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h_sqrt
      exact h_sqrt
    calc Real.sqrt (K5 / eps ^ 5) * Real.log 2
      _ = Real.sqrt K5 * (Real.log 2 / Real.sqrt (eps ^ 5)) := by rw [h1]; ring
      _ ≤ K5 * (Real.log 2 / Real.sqrt (eps ^ 5)) := by
        have : 0 ≤ Real.log 2 / Real.sqrt (eps ^ 5) := by positivity
        exact mul_le_mul_of_nonneg_right h2 this
      _ = K5 * Real.log 2 * (1 / Real.sqrt (eps ^ 5)) := by ring
      _ ≤ K * (1 / Real.sqrt (eps ^ 5)) := by
        have : 0 ≤ 1 / Real.sqrt (eps ^ 5) := by positivity
        exact mul_le_mul_of_nonneg_right hK this
      _ ≤ K * (1 / eps ^ 8) := by
        have : 0 ≤ K := by
          have h_k5log2_nonneg : 0 ≤ K5 * Real.log 2 := mul_nonneg (by positivity) hlog
          exact le_trans h_k5log2_nonneg hK
        exact mul_le_mul_of_nonneg_left h3 this
      _ = K / eps ^ 8 := by ring
  calc m * Real.log 2
    _ ≤ (Real.sqrt (K5 / eps ^ 5) * s9) * Real.log 2 := mul_le_mul_of_nonneg_right h_m_le2 hlog
    _ = Real.sqrt (K5 / eps ^ 5) * Real.log 2 * s9 := by ring
    _ ≤ (K / eps ^ 8) * s9 := mul_le_mul_of_nonneg_right h_sqrt_bound hs9_pos
    _ ≤ (K / eps ^ 8) * (s9 + 1) := by
      have hk_pos : 0 ≤ K / eps ^ 8 := by
        have : 0 ≤ K5 * Real.log 2 := mul_nonneg (by positivity) hlog
        have : 0 ≤ K := le_trans this hK
        positivity
      have hs9_le : s9 ≤ s9 + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hs9_le hk_pos

lemma s7_eff_math_small {K K6 eps c m : ℝ} {s8 s9 : ℝ} (heps : 0 < eps) (heps_half : eps ≤ 1 / 2)
    (hc : c = 2 * eps / (1 / 2 + 4 * eps))
    (hK6 : 1 ≤ K6) (hK : (5 / 2) * K6 + 2 ≤ K) (_hm : 0 ≤ m) (hs9_nonneg : 0 ≤ s9)
    (hs9 : s8 ≤ s9) (_h_m : K / eps ^ 8 ≤ m) :
    2 * (K6 * (s8 + 1)) / c - Real.log (c / 2) ≤ (K / eps ^ 8) * (s9 + 1) := by
  have hc_pos : 0 < c := by
    rw [hc]; positivity
  have hc2_inv : (c / 2)⁻¹ = (1 / 2 + 4 * eps) / eps := by
    rw [hc]
    have : 2 * eps / (1 / 2 + 4 * eps) / 2 = eps / (1 / 2 + 4 * eps) := by ring
    rw [this, inv_div]
  have hlog : - Real.log (c / 2) ≤ (1 / 2 + 4 * eps) / eps := by
    rw [← Real.log_inv]
    rw [hc2_inv]
    exact Real.log_le_self (by positivity)
  have h1 : 2 * (K6 * (s9 + 1)) / c = (K6 * (s9 + 1)) * ((1 / 2 + 4 * eps) / eps) := by
    rw [hc]
    have hc_den_pos : 0 < (1 / 2 : ℝ) + 4 * eps := by linarith
    have heps_pos : 0 < eps := heps
    field_simp
  have hs9_1 : 1 ≤ s9 + 1 := by linarith
  have h_bound_c_eps : (1 / 2 + 4 * eps) / eps ≤ 2.5 / eps := by
    have : 1 / 2 + 4 * eps ≤ 2.5 := by linarith
    have : 0 < eps := heps
    exact div_le_div_of_nonneg_right ‹1 / 2 + 4 * eps ≤ 2.5› (by linarith)
  have h3 : (K6 * (s9 + 1)) * ((1 / 2 + 4 * eps) / eps) + (1 / 2 + 4 * eps) / eps ≤ (K6 * (s9 + 1) + 1) * (2.5 / eps) := by
    calc (K6 * (s9 + 1)) * ((1 / 2 + 4 * eps) / eps) + (1 / 2 + 4 * eps) / eps
      _ = (K6 * (s9 + 1) + 1) * ((1 / 2 + 4 * eps) / eps) := by ring
      _ ≤ (K6 * (s9 + 1) + 1) * (2.5 / eps) := by
        have : 0 ≤ K6 * (s9 + 1) + 1 := by positivity
        exact mul_le_mul_of_nonneg_left h_bound_c_eps this
  have h4 : 2.5 / eps ≤ 2 / eps ^ 8 := by
    have h4_1 : 2.5 * eps ^ 7 ≤ 2 := by
      calc 2.5 * eps ^ 7 ≤ 2.5 * (1 / 2) ^ 7 := by
            have h_pow : eps ^ 7 ≤ (1 / 2) ^ 7 := by gcongr
            have h_pos : (0 : ℝ) ≤ 2.5 := by norm_num
            exact mul_le_mul_of_nonneg_left h_pow h_pos
        _ = 2.5 / 128 := by ring
        _ ≤ 2 := by norm_num
    have heps_pos : 0 < eps := heps
    rw [div_le_div_iff₀ heps_pos (by positivity)]
    calc 2.5 * eps ^ 8 = (2.5 * eps ^ 7) * eps := by ring
      _ ≤ 2 * eps := by
        have : 0 ≤ eps := by positivity
        exact mul_le_mul_of_nonneg_right h4_1 this
  have h5 : (K6 * (s9 + 1) + 1) * (2.5 / eps) ≤ (5 / 2 * K6 + 2) / eps ^ 8 * (s9 + 1) := by
    calc (K6 * (s9 + 1) + 1) * (2.5 / eps)
      _ = 2.5 * K6 * (s9 + 1) / eps + 2.5 / eps := by ring
      _ ≤ 2.5 * K6 * (s9 + 1) / eps + 2 / eps ^ 8 := by
        exact add_le_add (le_refl _) h4
      _ = (5 / 2 * K6) * (s9 + 1) / eps + 2 / eps ^ 8 := by ring_nf
      _ ≤ (5 / 2 * K6) * (s9 + 1) / eps ^ 8 + 2 * (s9 + 1) / eps ^ 8 := by
        have h_eps_inv_le : 1 / eps ≤ 1 / eps ^ 8 := by
          have h_eps8_le_eps : eps ^ 8 ≤ eps := by
            calc eps ^ 8 = eps * eps ^ 7 := by ring
              _ ≤ eps * (1 / 2) ^ 7 := by
                have h_pow : eps ^ 7 ≤ (1 / 2) ^ 7 := by gcongr
                have h_pos : 0 ≤ eps := by positivity
                exact mul_le_mul_of_nonneg_left h_pow h_pos
              _ = eps / 128 := by ring
              _ ≤ eps := by linarith
          have h_pos : 0 < eps ^ 8 := by positivity
          exact one_div_le_one_div_of_le h_pos h_eps8_le_eps
        have h_term1 : (5 / 2 * K6) * (s9 + 1) / eps ≤ (5 / 2 * K6) * (s9 + 1) / eps ^ 8 := by
          have h_rw : (5 / 2 * K6) * (s9 + 1) / eps = (5 / 2 * K6) * (s9 + 1) * (1 / eps) := by ring
          have h_rw2 : (5 / 2 * K6) * (s9 + 1) / eps ^ 8 = (5 / 2 * K6) * (s9 + 1) * (1 / eps ^ 8) := by ring
          rw [h_rw, h_rw2]
          have : 0 ≤ (5 / 2 * K6) * (s9 + 1) := by positivity
          exact mul_le_mul_of_nonneg_left h_eps_inv_le this
        have h_term2 : 2 / eps ^ 8 ≤ 2 * (s9 + 1) / eps ^ 8 := by
          have h_rw : 2 / eps ^ 8 = 2 * (1 / eps ^ 8) := by ring
          have h_rw2 : 2 * (s9 + 1) / eps ^ 8 = 2 * (s9 + 1) * (1 / eps ^ 8) := by ring
          rw [h_rw, h_rw2]
          have : 2 ≤ 2 * (s9 + 1) := by linarith
          have : 0 ≤ 1 / eps ^ 8 := by positivity
          exact mul_le_mul_of_nonneg_right ‹2 ≤ 2 * (s9 + 1)› this
        exact add_le_add h_term1 h_term2
      _ = (5 / 2 * K6 + 2) / eps ^ 8 * (s9 + 1) := by ring
  calc 2 * (K6 * (s8 + 1)) / c - Real.log (c / 2)
    _ ≤ 2 * (K6 * (s9 + 1)) / c - Real.log (c / 2) := by
      have : s8 + 1 ≤ s9 + 1 := by linarith
      have : 0 ≤ 2 * K6 / c := by positivity
      have h_le : 2 * (K6 * (s8 + 1)) / c ≤ 2 * (K6 * (s9 + 1)) / c := by
        have h_rw : 2 * (K6 * (s8 + 1)) / c = (2 * K6 / c) * (s8 + 1) := by ring
        have h_rw2 : 2 * (K6 * (s9 + 1)) / c = (2 * K6 / c) * (s9 + 1) := by ring
        rw [h_rw, h_rw2]
        exact mul_le_mul_of_nonneg_left ‹s8 + 1 ≤ s9 + 1› this
      exact sub_le_sub_right h_le _
    _ = 2 * (K6 * (s9 + 1)) / c + (- Real.log (c / 2)) := by ring
    _ ≤ 2 * (K6 * (s9 + 1)) / c + (1 / 2 + 4 * eps) / eps := add_le_add (le_refl _) hlog
    _ = (K6 * (s9 + 1)) * ((1 / 2 + 4 * eps) / eps) + (1 / 2 + 4 * eps) / eps := by rw [h1]
    _ ≤ (K6 * (s9 + 1) + 1) * (2.5 / eps) := h3
    _ ≤ (5 / 2 * K6 + 2) / eps ^ 8 * (s9 + 1) := h5
    _ ≤ (K / eps ^ 8) * (s9 + 1) := by
      have h_rw : (5 / 2 * K6 + 2) / eps ^ 8 * (s9 + 1) = (5 / 2 * K6 + 2) * ((s9 + 1) / eps ^ 8) := by ring
      have h_rw2 : (K / eps ^ 8) * (s9 + 1) = K * ((s9 + 1) / eps ^ 8) := by ring
      rw [h_rw, h_rw2]
      have : 0 ≤ (s9 + 1) / eps ^ 8 := by positivity
      exact mul_le_mul_of_nonneg_right hK this

lemma s7_good_event_size_apply {m : ℕ} (A : Finset (Cube m))
    (q eps massSlack : ℝ) (hq : 0 ≤ q) (heps : 0 < eps) (hqeps : q + eps ≤ 1 / 2)
    (hA : A.Nonempty) (hPF : averageBadStepsLE A q eps massSlack)
    (hm_pos : 0 < (m : ℝ)) (hmass : massSlack ≤ eps * m) :
    let G := A.filter (fun x => (hDist x (predictableCenter A x) : ℝ) ≤ (q + 4 * eps) * m)
    let c := 2 * eps / (1 / 2 + 4 * eps)
    c * A.card ≤ G.card := by
  let G := A.filter (fun x => (hDist x (predictableCenter A x) : ℝ) ≤ (q + 4 * eps) * m)
  let c := 2 * eps / (1 / 2 + 4 * eps)
  change c * (A.card : ℝ) ≤ (G.card : ℝ)
  have hG_size :
      (3 * eps * (m : ℝ) - massSlack) * (A.card : ℝ) ≤
        (q + 4 * eps) * (m : ℝ) * (G.card : ℝ) := by
    simpa [G] using
      s7_good_event_size A q eps massSlack hq (le_of_lt heps) hqeps hA hPF
  have h1 : 2 * eps * (m : ℝ) * (A.card : ℝ) ≤
      (3 * eps * (m : ℝ) - massSlack) * (A.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith [hmass]
  have h2 : (2 * eps * (m : ℝ)) * (A.card : ℝ) ≤
      (q + 4 * eps) * (m : ℝ) * (G.card : ℝ) := le_trans h1 hG_size
  have h2' : (2 * eps) * (A.card : ℝ) ≤ (q + 4 * eps) * (G.card : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right h2 (le_of_lt hm_pos)
    field_simp [hm_pos.ne'] at hdiv
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hden_pos : 0 < (1 / 2 : ℝ) + 4 * eps := by positivity
  have hq_den : q + 4 * eps ≤ (1 / 2 : ℝ) + 4 * eps := by
    linarith [hqeps]
  have h3 : (2 * eps) * (A.card : ℝ) ≤
      ((1 / 2 : ℝ) + 4 * eps) * (G.card : ℝ) :=
    h2'.trans (mul_le_mul_of_nonneg_right hq_den (Nat.cast_nonneg _))
  dsimp [c]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
  nlinarith [h3]

lemma s7_eff_exp_bound {K eps m : ℝ} {s9 : ℝ} (A_card : ℝ)
    (h1 : A_card ≤ 2 ^ (m : ℝ)) (h2 : m * Real.log 2 ≤ (K / eps ^ 8) * (s9 + 1)) :
    Real.exp (-((K / eps ^ 8) * (s9 + 1))) * A_card ≤ 1 := by
  let M := (K / eps ^ 8) * (s9 + 1)
  have hpow_exp : (2 : ℝ) ^ (m : ℝ) = Real.exp (m * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hA_le_exp_m : A_card ≤ Real.exp (m * Real.log 2) := by
    simpa [hpow_exp] using h1
  have hA_le_exp_M : A_card ≤ Real.exp M :=
    hA_le_exp_m.trans (Real.exp_le_exp.mpr (by simpa [M] using h2))
  calc
    Real.exp (-M) * A_card ≤ Real.exp (-M) * Real.exp M :=
      mul_le_mul_of_nonneg_left hA_le_exp_M (le_of_lt (Real.exp_pos _))
    _ = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero

theorem s7_eff (_hR3 : R3Eff) (hS5 : S5Eff) (hS6 : S6Eff) : S7Eff := by
  intro Q hQ
  rcases hS5 Q hQ with ⟨K5, hK5, hS5_eps⟩
  rcases hS6 Q hQ with ⟨K6, hK6, hS6_eps⟩
  let K := max (K5 * Real.log 2) ((5 / 2) * K6 + 2)
  have hK_ge1 : 1 ≤ K := by
    have h1 : 1 ≤ (5 / 2 : ℝ) * K6 + 2 := by linarith
    exact le_trans h1 (le_max_right _ _)
  refine ⟨K, hK_ge1, ?_⟩
  intro eps heps heps_qMin heps_qMax m hm A q hA hfat hpinned
  have heps_half : eps ≤ 1 / 2 := by
    have hqMax_pos : 0 < Q.qMax := lt_of_lt_of_le hQ.1 hQ.2.1
    linarith [heps_qMax, hqMax_pos]
  have hq_nonneg : 0 ≤ q := by
    exact (le_of_lt hQ.1).trans hfat.2.2.1
  have hqeps : q + eps ≤ 1 / 2 := by
    linarith [hfat.2.2.2.1, heps_qMax]
  let massSlack := (K5 / eps ^ 4) * (effEnv 8 Q.sigma m + 1)
  have hPF : averageBadStepsLE A q eps massSlack :=
    hS5_eps eps heps heps_qMin m A q hA hfat hpinned
  have hCenterBound : uH A (predictableCenter A) ≤ K6 * (effEnv 10 Q.sigma m + 1) :=
    hS6_eps m A q hA hfat hpinned
  have h_m_pos : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h_m_strict_pos : 0 < (m : ℝ) := by
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK_ge1
    exact lt_of_lt_of_le (div_pos hK_pos (pow_pos heps 8)) hm
  let s7 := effEnv 8 Q.sigma m
  let s8 := effEnv 10 Q.sigma m
  let s9 := effEnv 10 Q.sigma m
  have hSigma_nonneg : ∀ n, 0 ≤ Q.sigma n :=
    hQ.2.2.2.2.2.2.1.1
  have hs9_nonneg : 0 ≤ s9 := by
    simpa [s9] using effEnv_nonneg 10 Q.sigma hSigma_nonneg m
  have hs8_lower : Real.sqrt ((s7 + 1) * (m + 1)) ≤ s9 := by
    calc Real.sqrt ((s7 + 1) * (m + 1)) ≤ effEnv 9 Q.sigma m := le_max_right _ _
      _ ≤ s9 := le_max_left _ _
  have hs9_lower : s8 ≤ s9 := le_refl _
  have hlog : 0 ≤ Real.log 2 := by positivity
  by_cases h_mass : massSlack ≤ eps * m
  · let c := 2 * eps / (1 / 2 + 4 * eps)
    have hc_pos : 0 < c := by positivity
    let G := A.filter (fun x => (hDist x (predictableCenter A x) : ℝ) ≤ (q + 4 * eps) * m)
    have hG_card : c * A.card ≤ G.card :=
      s7_good_event_size_apply A q eps massSlack hq_nonneg heps hqeps hA hPF h_m_strict_pos h_mass
    have hG_sub : G ⊆ A := Finset.filter_subset _ _
    let E := K6 * (s8 + 1)
    rcases heavy_fiber_in_good_set A G (predictableCenter A) E c hG_sub hG_card hc_pos hCenterBound hA with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h_math_small : 2 * E / c - Real.log (c / 2) ≤ (K / eps ^ 8) * (s9 + 1) :=
      s7_eff_math_small heps heps_half rfl hK6 (le_max_right _ _) h_m_pos hs9_nonneg hs9_lower hm
    have h_exp : Real.exp (- ((K / eps ^ 8) * (s9 + 1))) ≤ Real.exp (Real.log (c / 2) - 2 * E / c) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h_exp2 : Real.exp (Real.log (c / 2) - 2 * E / c) = (c / 2) * Real.exp (- 2 * E / c) := by
      have hc2_pos : 0 < c / 2 := by positivity
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hc2_pos]
      ring_nf
    have h_final1 : Real.exp (- ((K / eps ^ 8) * (s9 + 1))) * (A.card : ℝ) ≤ (c / 2) * Real.exp (- 2 * E / c) * (A.card : ℝ) := by
      calc
        Real.exp (-((K / eps ^ 8) * (s9 + 1))) * (A.card : ℝ)
            ≤ Real.exp (Real.log (c / 2) - 2 * E / c) * (A.card : ℝ) :=
              mul_le_mul_of_nonneg_right h_exp (Nat.cast_nonneg _)
        _ = (c / 2) * Real.exp (-2 * E / c) * (A.card : ℝ) := by
              rw [h_exp2]
    have h_final2 : (c / 2) * Real.exp (- 2 * E / c) * (A.card : ℝ) ≤ ((A.filter (fun x => hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ)))).card : ℝ) := by
      refine le_trans ha ?_
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      rcases hx with ⟨hxG, hxa⟩
      rw [Finset.mem_filter] at hxG
      refine ⟨hxG.1, ?_⟩
      have hd : (hDist x a : ℝ) ≤ (q + 4 * eps) * (m : ℝ) := by
        rw [← hxa]
        exact hxG.2
      have hd2 : (hDist x a : ℝ) ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ)) :=
        le_trans hd (Nat.le_ceil _)
      exact_mod_cast hd2
    exact le_trans h_final1 h_final2
  · push_neg at h_mass
    have h_math_large : m * Real.log 2 ≤ (K / eps ^ 8) * (s9 + 1) :=
      s7_eff_math_large heps heps_half hK5 (le_max_left _ _) h_m_pos hs8_lower h_mass hlog
    rcases hA with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h_card_le : (A.card : ℝ) ≤ (2 : ℝ) ^ (m : ℝ) := by
      have hcard_nat : A.card ≤ 2 ^ m := by
        calc
          A.card ≤ (Finset.univ : Finset (Cube m)).card := Finset.card_le_univ A
          _ = 2 ^ m := by simp +decide [Finset.card_univ]
      exact_mod_cast hcard_nat
    have h_exp_bound : Real.exp (- ((K / eps ^ 8) * (s9 + 1))) * A.card ≤ 1 :=
      s7_eff_exp_bound A.card h_card_le h_math_large
    have h_final1 : Real.exp (- ((K / eps ^ 8) * (s9 + 1))) * (A.card : ℝ) ≤ 1 := h_exp_bound
    have h_final2 : 1 ≤ ((A.filter (fun y => hDist y x ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ)))).card : ℝ) := by
      have hxmem : x ∈ A.filter (fun y => hDist y x ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))) := by
        simp [hx, hDist_self_eq_zero]
      have hpos : 0 < (A.filter (fun y => hDist y x ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ)))).card :=
        Finset.card_pos.mpr ⟨x, hxmem⟩
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    exact le_trans h_final1 h_final2

end HarperStability
