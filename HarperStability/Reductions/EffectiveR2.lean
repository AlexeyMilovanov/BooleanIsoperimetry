import HarperStability.Reductions.Basic
import HarperStability.Reductions.R2HBL
import HarperStability.Interface.Effective
import HarperStability.Volume.Basic

/-!
# Effective R2 (v0.3): the heavy-ball lemma at grade 11

Target: `R2Eff` — every valid tuple `D` satisfies
`HBLFor D (effDegrade D K 14)`.

Route: replay the PROVED v0.2 chain (downward pinning + contradiction
scheme + `sublinear_diag_envelope`) with explicit schedules instead of
the `δ → 0` diagonal:
* from `hS7` (`S7Eff`, grade 10): for each admissible precision `eps`
  the heavy ball exists with grade-10 mass slack and radius excess
  `4*eps*m` beyond the pinned radius; the window-to-cube transfer and
  the `rmin` conversion use the effective volume calculus (`hIVC`) and
  `hVPlus` exactly as in v0.2;
* choose the precision schedule explicitly (v0.3.1):
  `eps(n) := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((effEnv 10 D.sigma n + 1)/((n:ℝ)+1)))))`
  — i.e. `((effEnv 10 σ n + 1)/(n+1))^(1/16)`, clamped into the
  admissible window.  Then the radius excess
  `4*eps(n)*n ≈ 4*(n+1)^(15/16)*(effEnv 10 σ n + 1)^(1/16)` is exactly
  four `effGeo`-steps above grade 10, i.e. grade 14, and the S7Eff mass
  slack `(K/eps(n)^8)*(effEnv 10 σ n + 1) = K*sqrt((effEnv 10 σ n + 1)*((n:ℝ)+1))`
  is grade 11 ≤ 13; the threshold `K/eps(n)^8 ≤ m` holds for
  `n ≥ n₀(K)` since the left side is `O(sqrt(n))`;
* the QData construction (`r2_hbl_from_q_and_dp`-style) transfers
  `D.sigma` to `Q.sigma` verbatim; small `n` are absorbed into `K`
  (the trivial ball `a ∈ S` witnesses HBL when
  `K*(effEnv 14 σ n + 1) ≥ n*log 2`).
Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

/-- The explicit precision schedule for R2. -/
noncomputable def r2EffEps (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)))))

/-- The clamped precision schedule that fits into the admissible window for S7. -/
noncomputable def r2EffEpsClamped (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffEps sigma n)

lemma r2_eff_eps_pos (sigma : ℕ → ℝ) (n : ℕ) (hsigma : 0 ≤ sigma n) :
    0 < r2EffEps sigma n := by
  have henv : 0 ≤ effEnv 10 sigma n := le_trans hsigma (le_effEnv 10 sigma n)
  have hbase : 0 < (effEnv 10 sigma n + 1) / ((n : ℝ) + 1) := by
    exact div_pos (by linarith) (by positivity)
  unfold r2EffEps
  repeat' apply Real.sqrt_pos.mpr
  exact hbase

lemma r2_eff_eps_clamped_pos (Q : QData) (sigma : ℕ → ℝ) (n : ℕ)
    (hsigma : 0 ≤ sigma n) (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) :
    0 < r2EffEpsClamped Q sigma n := by
  unfold r2EffEpsClamped
  rw [lt_min_iff]
  constructor
  · rw [lt_min_iff]
    exact ⟨by linarith, by linarith⟩
  · exact r2_eff_eps_pos sigma n hsigma

lemma r2_eff_eps_clamped_admissible (Q : QData) (sigma : ℕ → ℝ) (n : ℕ)
    (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) :
    r2EffEpsClamped Q sigma n < Q.qMin ∧ r2EffEpsClamped Q sigma n < 1 / 2 - Q.qMax := by
  unfold r2EffEpsClamped
  constructor
  ·
    have hle :
        min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffEps sigma n) ≤
          Q.qMin / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    exact lt_of_le_of_lt hle (by linarith)
  ·
    have hle :
        min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffEps sigma n) ≤
          (1 / 2 - Q.qMax) / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    exact lt_of_le_of_lt hle (by linarith)

private lemma r2_sqrt_mul_succ_le_effGeo (s : ℕ → ℝ) (n : ℕ) {e : ℝ}
    (he : 0 ≤ e) (h : e * ((n : ℝ) + 1) ≤ s n + 1) :
    Real.sqrt e * ((n : ℝ) + 1) ≤ effGeo s n := by
  let b : ℝ := (n : ℝ) + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have heb : 0 ≤ e * b := mul_nonneg he hb
  have hs1 : 0 ≤ s n + 1 := le_trans heb h
  have harg : 0 ≤ (s n + 1) * b := mul_nonneg hs1 hb
  have hsq :
      (Real.sqrt e * b) ^ 2 ≤ (Real.sqrt ((s n + 1) * b)) ^ 2 := by
    calc
      (Real.sqrt e * b) ^ 2 = e * b * b := by
        rw [mul_pow, Real.sq_sqrt he]
        ring
      _ ≤ (s n + 1) * b := by
        have hm := mul_le_mul_of_nonneg_right h hb
        simpa [mul_assoc] using hm
      _ = (Real.sqrt ((s n + 1) * b)) ^ 2 := by
        rw [Real.sq_sqrt harg]
  have hroot :
      Real.sqrt e * b ≤ Real.sqrt ((s n + 1) * b) := by
    have hl : 0 ≤ Real.sqrt e * b := mul_nonneg (Real.sqrt_nonneg _) hb
    have hr : 0 ≤ Real.sqrt ((s n + 1) * b) := Real.sqrt_nonneg _
    nlinarith
  exact le_trans hroot (by
    unfold effGeo
    exact le_max_right _ _)

private lemma r2_eff_eps_mul_succ_le_effEnv13 (sigma : ℕ → ℝ) (n : ℕ) :
    r2EffEps sigma n * ((n : ℝ) + 1) ≤ effEnv 14 sigma n := by
  let b : ℝ := (n : ℝ) + 1
  let e0 : ℝ := (effEnv 10 sigma n + 1) / b
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb : 0 ≤ b := hbpos.le
  have h9_nonneg : 0 ≤ effEnv 10 sigma n := effGeo_nonneg _ n
  have h9_num_nonneg : 0 ≤ effEnv 10 sigma n + 1 := add_nonneg h9_nonneg zero_le_one
  have he0 : 0 ≤ e0 := by
    dsimp [e0]
    exact div_nonneg h9_num_nonneg hb
  have h0 : e0 * b ≤ effEnv 10 sigma n + 1 := by
    dsimp [e0, b]
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
  have h1 :
      Real.sqrt e0 * b ≤ effEnv 11 sigma n := by
    have := r2_sqrt_mul_succ_le_effGeo (effEnv 10 sigma) n he0 (by simpa [b] using h0)
    simpa using this
  have he1 : 0 ≤ Real.sqrt e0 := Real.sqrt_nonneg _
  have h2 :
      Real.sqrt (Real.sqrt e0) * b ≤ effEnv 12 sigma n := by
    have h1' : Real.sqrt e0 * ((n : ℝ) + 1) ≤ effEnv 11 sigma n + 1 := by
      have hb_eq : b = (n : ℝ) + 1 := rfl
      linarith
    have := r2_sqrt_mul_succ_le_effGeo (effEnv 11 sigma) n he1 h1'
    simpa using this
  have he2 : 0 ≤ Real.sqrt (Real.sqrt e0) := Real.sqrt_nonneg _
  have h3 :
      Real.sqrt (Real.sqrt (Real.sqrt e0)) * b ≤ effEnv 13 sigma n := by
    have h2' :
        Real.sqrt (Real.sqrt e0) * ((n : ℝ) + 1) ≤ effEnv 12 sigma n + 1 := by
      linarith
    have := r2_sqrt_mul_succ_le_effGeo (effEnv 12 sigma) n he2 h2'
    simpa using this
  have he3 : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt e0)) := Real.sqrt_nonneg _
  have h4 :
      Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt e0))) * b ≤ effEnv 14 sigma n := by
    have h3' :
        Real.sqrt (Real.sqrt (Real.sqrt e0)) * ((n : ℝ) + 1) ≤
          effEnv 13 sigma n + 1 := by
      linarith
    have := r2_sqrt_mul_succ_le_effGeo (effEnv 13 sigma) n he3 h3'
    simpa using this
  simpa [r2EffEps, e0, b] using h4

private lemma r2_eff_eps_pow_eight (sigma : ℕ → ℝ) (n : ℕ) :
    (r2EffEps sigma n) ^ 8 =
      Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)) := by
  let e0 : ℝ := (effEnv 10 sigma n + 1) / ((n : ℝ) + 1)
  have he1 : 0 ≤ Real.sqrt e0 := Real.sqrt_nonneg _
  have he2 : 0 ≤ Real.sqrt (Real.sqrt e0) := Real.sqrt_nonneg _
  have he3 : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt e0)) := Real.sqrt_nonneg _
  calc
    (r2EffEps sigma n) ^ 8
        = (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt e0)))) ^ 8 := by
            simp [r2EffEps, e0]
    _ = ((Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt e0)))) ^ 2) ^ 4 := by ring
    _ = (Real.sqrt (Real.sqrt (Real.sqrt e0))) ^ 4 := by rw [Real.sq_sqrt he3]
    _ = ((Real.sqrt (Real.sqrt (Real.sqrt e0))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (Real.sqrt e0)) ^ 2 := by rw [Real.sq_sqrt he2]
    _ = Real.sqrt e0 := by rw [Real.sq_sqrt he1]

private lemma r2_eff_eps_mass_schedule_bound (sigma : ℕ → ℝ) (n : ℕ) :
    (effEnv 10 sigma n + 1) / (r2EffEps sigma n) ^ 8 ≤ effEnv 11 sigma n := by
  let b : ℝ := (n : ℝ) + 1
  let e0 : ℝ := (effEnv 10 sigma n + 1) / b
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb : 0 ≤ b := hbpos.le
  have h9_nonneg : 0 ≤ effEnv 10 sigma n := effGeo_nonneg _ n
  have h9_num_pos : 0 < effEnv 10 sigma n + 1 := by linarith
  have he0_pos : 0 < e0 := by
    dsimp [e0]
    exact div_pos h9_num_pos hbpos
  have he0_nonneg : 0 ≤ e0 := he0_pos.le
  have h0 : e0 * b ≤ effEnv 10 sigma n + 1 := by
    dsimp [e0, b]
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
  have hgeo :
      Real.sqrt e0 * b ≤ effEnv 11 sigma n := by
    have := r2_sqrt_mul_succ_le_effGeo (effEnv 10 sigma) n he0_nonneg
      (by simpa [b] using h0)
    simpa using this
  have hpow := r2_eff_eps_pow_eight sigma n
  have hratio :
      (effEnv 10 sigma n + 1) / (r2EffEps sigma n) ^ 8 =
        Real.sqrt e0 * b := by
    rw [hpow]
    change (effEnv 10 sigma n + 1) / Real.sqrt e0 = Real.sqrt e0 * b
    have hsqrt_ne : Real.sqrt e0 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr he0_pos)
    have ha : effEnv 10 sigma n + 1 = e0 * b := by
      dsimp [e0]
      rw [div_mul_cancel₀ _ hbpos.ne']
    rw [ha]
    field_simp [hsqrt_ne]
    nlinarith [Real.mul_self_sqrt he0_nonneg]
  rw [hratio]
  exact hgeo

/-- The radius excess `4*eps(n)*n` is bounded by grade 14. -/
lemma r2_eff_radius_excess_bound (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) :
    4 * r2EffEpsClamped Q sigma n * (n : ℝ) ≤ 4 * effEnv 14 sigma n + 4 := by
  have hclamp : r2EffEpsClamped Q sigma n ≤ r2EffEps sigma n := by
    unfold r2EffEpsClamped
    exact min_le_right _ _
  have heps_nonneg : 0 ≤ r2EffEps sigma n := by
    unfold r2EffEps
    positivity
  have hn_le : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have heps_n :
      r2EffEps sigma n * (n : ℝ) ≤ r2EffEps sigma n * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hn_le heps_nonneg
  have heps_bound : r2EffEps sigma n * (n : ℝ) ≤ effEnv 14 sigma n :=
    le_trans heps_n (r2_eff_eps_mul_succ_le_effEnv13 sigma n)
  have hclamp_bound :
      r2EffEpsClamped Q sigma n * (n : ℝ) ≤ effEnv 14 sigma n := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact le_trans (mul_le_mul_of_nonneg_right hclamp hn_nonneg) heps_bound
  nlinarith

/-- The mass slack `(K/eps(n)^8)*(effEnv 10 σ n + 1)` is bounded by grade 11 (which is ≤ 13). -/
lemma r2_eff_mass_slack_bound (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    (K / (r2EffEpsClamped Q sigma n) ^ 8) * (effEnv 10 sigma n + 1) ≤
      K * effEnv 11 sigma n + K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) + K * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 sigma n + 1) := by
  have h10_nonneg : 0 ≤ effEnv 11 sigma n := effGeo_nonneg _ n
  have h9_nonneg : 0 ≤ effEnv 10 sigma n := effGeo_nonneg _ n
  have h9p_nonneg : 0 ≤ effEnv 10 sigma n + 1 := add_nonneg h9_nonneg zero_le_one
  have hmain_nonneg : 0 ≤ K * effEnv 11 sigma n := mul_nonneg hK h10_nonneg
  have hq_nonneg : 0 ≤ K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) :=
    mul_nonneg (mul_nonneg hK (Even.pow_nonneg (by norm_num) _)) h9p_nonneg
  have hgap_nonneg :
      0 ≤ K * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 sigma n + 1) :=
    mul_nonneg (mul_nonneg hK (Even.pow_nonneg (by norm_num) _)) h9p_nonneg
  unfold r2EffEpsClamped
  by_cases hinner :
      min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2) ≤ r2EffEps sigma n
  · rw [min_eq_left hinner]
    by_cases hq : Q.qMin / 2 ≤ (1 / 2 - Q.qMax) / 2
    · rw [min_eq_left hq]
      calc
        (K / (Q.qMin / 2) ^ 8) * (effEnv 10 sigma n + 1)
            = K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) := by ring_nf
        _ ≤ K * effEnv 11 sigma n +
              K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) +
              K * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 sigma n + 1) := by
            nlinarith
    · have hgap : (1 / 2 - Q.qMax) / 2 ≤ Q.qMin / 2 := le_of_not_ge hq
      rw [min_eq_right hgap]
      let g : ℝ := 1 / 2 - Q.qMax
      change
        (K / (g / 2) ^ 8) * (effEnv 10 sigma n + 1) ≤
          K * effEnv 11 sigma n +
            K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) +
            K * (2 / g) ^ 8 * (effEnv 10 sigma n + 1)
      calc
        (K / (g / 2) ^ 8) * (effEnv 10 sigma n + 1)
            = K * (2 / g) ^ 8 * (effEnv 10 sigma n + 1) := by ring_nf
        _ ≤ K * effEnv 11 sigma n +
              K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) +
              K * (2 / g) ^ 8 * (effEnv 10 sigma n + 1) := by
            nlinarith
  · have heps :
        r2EffEps sigma n ≤ min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2) :=
      le_of_not_ge hinner
    rw [min_eq_right heps]
    have hsched := r2_eff_eps_mass_schedule_bound sigma n
    have hschedK :
        K * ((effEnv 10 sigma n + 1) / (r2EffEps sigma n) ^ 8) ≤
          K * effEnv 11 sigma n :=
      mul_le_mul_of_nonneg_left hsched hK
    calc
      (K / (r2EffEps sigma n) ^ 8) * (effEnv 10 sigma n + 1)
          = K * ((effEnv 10 sigma n + 1) / (r2EffEps sigma n) ^ 8) := by ring
      _ ≤ K * effEnv 11 sigma n := hschedK
      _ ≤ K * effEnv 11 sigma n +
            K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) +
            K * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 sigma n + 1) := by
          nlinarith

noncomputable def r2EffQData (D : StabilityData) (C : ℝ) : QData := {
  qMin := D.alphaMin
  qMax := D.alphaMax
  s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
  mu0 := (1 / 2 - D.alphaMax) / 2
  sigma := fun n => C * (D.sigma n + 1)
}

private lemma r2_eff_sublinear_scale_add_one {s : ℕ → ℝ} (hs : Sublinear s)
    {C : ℝ} (hC : 0 ≤ C) :
    Sublinear (fun n => C * (s n + 1)) := by
  refine ⟨fun n => mul_nonneg hC (by linarith [hs.1 n]), fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := hs.2 (ε / (2 * (C + 1))) (by positivity)
  let N2 : ℕ := Nat.ceil (2 * C / ε) + 1
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hs_small := hN1 n hn1
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hC1_pos : 0 < C + 1 := by linarith
  have hden_pos : 0 < 2 * (C + 1) := by positivity
  have hscale :
      C * (ε / (2 * (C + 1)) * (n : ℝ)) ≤ (ε / 2) * (n : ℝ) := by
    have hratio : C / (C + 1) ≤ 1 := by
      rw [div_le_iff₀ hC1_pos]
      linarith
    have hnonneg : 0 ≤ (ε / 2) * (n : ℝ) := by positivity
    calc
      C * (ε / (2 * (C + 1)) * (n : ℝ))
          = (C / (C + 1)) * ((ε / 2) * (n : ℝ)) := by
              field_simp [hC1_pos.ne', hden_pos.ne']
      _ ≤ 1 * ((ε / 2) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hratio hnonneg
      _ = (ε / 2) * (n : ℝ) := by ring
  have hCs : C * s n ≤ (ε / 2) * (n : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hs_small hC) hscale
  have hceil : 2 * C / ε ≤ (Nat.ceil (2 * C / ε) : ℝ) := Nat.le_ceil _
  have hn2real : (Nat.ceil (2 * C / ε) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hn2
  have hCsmall : C ≤ (ε / 2) * (n : ℝ) := by
    have hbound : 2 * C / ε ≤ (n : ℝ) := by linarith
    have hbound_mul : 2 * C ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hbound
    nlinarith
  nlinarith

lemma r2_eff_valid_qdata (D : StabilityData) (hvalid : validData D) (C : ℝ) (hC : 1 ≤ C) :
    validQData (r2EffQData D C) := by
  rcases hvalid with
    ⟨hrho, _hdelta_pos, _hdelta_lt, hcsize, hamin, haminmax, hamaxhalf,
      hsubD, hlogD⟩
  have hC0 : 0 ≤ C := by linarith
  dsimp [r2EffQData, validQData]
  refine ⟨hamin, haminmax, hamaxhalf, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · linarith
  · have hs0_le : min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) ≤
        (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
    nlinarith
  · exact r2_eff_sublinear_scale_add_one hsubD hC0
  · intro m hm
    calc
      Real.log (m : ℝ) ≤ D.sigma m := hlogD m hm
      _ ≤ D.sigma m + 1 := by linarith
      _ ≤ C * (D.sigma m + 1) :=
          le_mul_of_one_le_left (by linarith [hsubD.1 m]) hC

lemma r2_eff_sublinear_effLog {K : ℝ} (hK : 0 ≤ K) : Sublinear (effLog K) := by
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

lemma r2_eff_effLog_le_sigma (D : StabilityData) (hvalid : validData D) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, effLog K n ≤ C * (D.sigma n + 1) := by
  have hK0 : 0 ≤ K := by linarith
  use K * (Real.log 3 + 1) * (D.sigma 0 + 1) + max 1 (K * (Real.log 3 + 1))
  constructor
  · have h_pos : 0 ≤ K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
      have hlog : 0 ≤ Real.log 3 + 1 := by positivity
      have hs0 : 0 ≤ D.sigma 0 + 1 := by
        have := hvalid.2.2.2.2.2.2.2.1.1 0
        linarith
      exact mul_nonneg (mul_nonneg hK0 hlog) hs0
    have h_max : 1 ≤ max 1 (K * (Real.log 3 + 1)) := le_max_left 1 _
    linarith
  · intro n
    have hC : K * (Real.log 3 + 1) ≤ max 1 (K * (Real.log 3 + 1)) :=
      le_max_right 1 _
    have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
    have h_base :
        K * (Real.log ((n : ℝ) + 2) + 1) ≤
          K * (Real.log 3 + 1) * (D.sigma n + 1) := by
      by_cases hn : n = 0
      · subst n
        have hlog23 : Real.log 2 ≤ Real.log 3 :=
          Real.log_le_log (by norm_num) (by norm_num)
        have h2 : K * (Real.log 2 + 1) ≤ K * (Real.log 3 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
        have h3 : K * (Real.log 3 + 1) ≤
            K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
          have h_pos : 0 ≤ K * (Real.log 3 + 1) := mul_nonneg hK0 (by positivity)
          have h_ge1 : 1 ≤ D.sigma 0 + 1 := by
            have := hvalid.2.2.2.2.2.2.2.1.1 0
            linarith
          nlinarith
        simpa using le_trans h2 h3
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
        have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log (3 * (n : ℝ)) := by
          apply Real.log_le_log (by linarith)
          linarith
        have h2 : Real.log (3 * (n : ℝ)) = Real.log 3 + Real.log (n : ℝ) := by
          apply Real.log_mul (by norm_num) (by linarith)
        have h3 : Real.log (n : ℝ) ≤ D.sigma n :=
          hvalid.2.2.2.2.2.2.2.2 n hn1
        have h4 : Real.log ((n : ℝ) + 2) + 1 ≤ Real.log 3 + 1 + D.sigma n := by
          linarith
        have h5 :
            K * (Real.log ((n : ℝ) + 2) + 1) ≤
              K * (Real.log 3 + 1 + D.sigma n) :=
          mul_le_mul_of_nonneg_left h4 hK0
        have h6 :
            K * (Real.log 3 + 1 + D.sigma n) ≤
              K * (Real.log 3 + 1) * (D.sigma n + 1) := by
          have h_log3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          have h_pos : 0 ≤ K * D.sigma n := mul_nonneg hK0 hsig_nn
          have : 1 * (K * D.sigma n) ≤ (Real.log 3 + 1) * (K * D.sigma n) :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos
          nlinarith
        exact le_trans h5 h6
    have h_step2 :
        K * (Real.log 3 + 1) * (D.sigma n + 1) ≤
          max 1 (K * (Real.log 3 + 1)) * (D.sigma n + 1) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have h_step3 :
        max 1 (K * (Real.log 3 + 1)) * (D.sigma n + 1) ≤
          (K * (Real.log 3 + 1) * (D.sigma 0 + 1) +
            max 1 (K * (Real.log 3 + 1))) * (D.sigma n + 1) := by
      have hh1 : 0 ≤ K * (Real.log 3 + 1) * (D.sigma 0 + 1) := by
        have hlog : 0 ≤ Real.log 3 + 1 := by positivity
        have hs0 : 0 ≤ D.sigma 0 + 1 := by
          have := hvalid.2.2.2.2.2.2.2.1.1 0
          linarith
        exact mul_nonneg (mul_nonneg hK0 hlog) hs0
      have hh2 : 0 ≤ D.sigma n + 1 := by linarith
      nlinarith
    simpa [effLog] using le_trans h_base (le_trans h_step2 h_step3)

lemma r2_eff_prefix_le_sigma (D : StabilityData) (hvalid : validData D) (N : ℕ) (a : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, (if n < N then a else 0) ≤ C * (D.sigma n + 1) := by
  refine ⟨max 1 a, le_max_left _ _, fun n => ?_⟩
  have hsig1 : 1 ≤ D.sigma n + 1 := by
    have := hvalid.2.2.2.2.2.2.2.1.1 n
    linarith
  by_cases hn : n < N
  · have ha : a ≤ max 1 a := le_max_right _ _
    simp [hn]
    exact le_trans ha (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) hsig1)
  · simp [hn]
    exact le_trans zero_le_one hsig1

lemma r2_eff_linear_combo_le_sigma (D : StabilityData) (hvalid : validData D)
    (s1 s2 : ℕ → ℝ) (C1 C2 : ℝ) (h1 : ∀ n, s1 n ≤ C1 * (D.sigma n + 1)) (h2 : ∀ n, s2 n ≤ C2 * (D.sigma n + 1))
    (a1 a2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, a1 * s1 n + a2 * s2 n ≤ C * (D.sigma n + 1) := by
  refine ⟨max 1 (a1 * C1 + a2 * C2), le_max_left _ _, fun n => ?_⟩
  have hsig_nonneg : 0 ≤ D.sigma n + 1 := by
    have := hvalid.2.2.2.2.2.2.2.1.1 n
    linarith
  have hsum :
      a1 * s1 n + a2 * s2 n ≤
        (a1 * C1 + a2 * C2) * (D.sigma n + 1) := by
    have h1' := mul_le_mul_of_nonneg_left (h1 n) ha1
    have h2' := mul_le_mul_of_nonneg_left (h2 n) ha2
    nlinarith
  have hcoef : a1 * C1 + a2 * C2 ≤ max 1 (a1 * C1 + a2 * C2) :=
    le_max_right _ _
  exact le_trans hsum (mul_le_mul_of_nonneg_right hcoef hsig_nonneg)

lemma r2_eff_BVStatement_of_Eff (hBV : BallVolumeTwoSidedEff) :
    BallVolumeTwoSidedStatement := by
  unfold BallVolumeTwoSidedStatement
  obtain ⟨K, hK, hcalc⟩ := hBV
  exact ⟨effLog K, r2_eff_sublinear_effLog (le_trans zero_le_one hK), hcalc⟩

lemma r2_eff_IVCStatement_of_Eff (hIVC : InteriorVolumeCalculusEff) :
    InteriorVolumeCalculusStatement := by
  unfold InteriorVolumeCalculusStatement
  intro alpha c0 hAlpha hc0
  obtain ⟨C, hC, K, hK, hcalc⟩ := hIVC alpha c0 hAlpha hc0
  exact ⟨C, hC, effLog K, r2_eff_sublinear_effLog (le_trans zero_le_one hK), hcalc⟩

lemma r2_eff_fat_of_classMember (D : StabilityData) (hvalid : validData D)
    (C : ℝ) (hC : 1 ≤ C) (hCsize : D.cSize ≤ C)
    (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hclass : classMember D n r S alpha beta) (hS : S.Nonempty) :
    fat (r2EffQData D C) n S alpha := by
  refine ⟨hS, r2_eff_valid_qdata D hvalid C hC, hclass.2.2.1, hclass.2.2.2.1, ?_⟩
  have hsig_nonneg : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hC0 : 0 ≤ C := by linarith
  have hsize : |Real.log (S.card : ℝ) - H alpha * (n : ℝ)| ≤ D.cSize * D.sigma n :=
    hclass.2.2.2.2.2.1
  refine le_trans hsize ?_
  dsimp [r2EffQData]
  have hmain : D.cSize * D.sigma n ≤ C * D.sigma n :=
    mul_le_mul_of_nonneg_right hCsize hsig_nonneg
  nlinarith

lemma r2_eff_pinned_mono_C (D : StabilityData) (hvalid : validData D)
    {C0 C : ℝ} (hC0C : C0 ≤ C)
    {n : ℕ} {S : Finset (Cube n)} {alpha : ℝ} :
    pinned (r2EffQData D C0) n S alpha →
      pinned (r2EffQData D C) n S alpha := by
  intro hp s hs
  have hs0 : s ≤ Nat.ceil ((r2EffQData D C0).s0 * (n : ℝ)) := by
    simpa [r2EffQData] using hs
  have hbase := hp s hs0
  refine le_trans hbase (Real.exp_le_exp.mpr ?_)
  have hsig_nonneg : 0 ≤ D.sigma n + 1 := by
    have := hvalid.2.2.2.2.2.2.2.1.1 n
    linarith
  dsimp [r2EffQData]
  have hmul := mul_le_mul_of_nonneg_right hC0C hsig_nonneg
  nlinarith

/-
Effective interior-volume upper bound: an explicit-slack clone of
`V_upper_of_classMember`, where the sublinear `volSlack` is replaced by the
explicit envelope `CG * (D.sigma n + 1)`.  The proof specializes
`InteriorVolumeCalculusEff` at `(D.alphaMin, c0)` and dominates the resulting
`C_V * (D.cSize * D.sigma n) + effLog K n` slack using
`r2_eff_effLog_le_sigma`.
-/
lemma r2_eff_V_upper (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ CG : ℝ, 1 ≤ CG ∧ ∀ (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
      D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → beta = (r : ℝ) / (n : ℝ) →
      alpha + beta ≤ 1 / 2 - c0 → 1 ≤ S.card → S.card ≤ 2 ^ n →
      sizeHyp D n S alpha →
      (V n S.card r : ℝ) ≤
        Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1)) := by
  obtain ⟨ C_V, hC_V, K, hK, hcalc ⟩ := hIVC D.alphaMin c0 hvalid.2.2.2.2.1 hc0;
  obtain ⟨ Ceff, hCeff1, hCeff ⟩ := r2_eff_effLog_le_sigma D hvalid K hK;
  refine' ⟨ Max.max 1 ( C_V * D.cSize + Ceff ), le_max_left _ _, fun n r S alpha beta halpha halpha' hbeta hrange hS1 hS2 hsize => _ ⟩;
  rw [ ← Real.log_le_iff_le_exp ];
  · have := hcalc n S.card r alpha beta ( D.cSize * D.sigma n ) halpha halpha' ( by exact mul_nonneg ( by linarith [ hvalid.2.2.2.1 ] ) ( by linarith [ hvalid.2.2.2.2.2.2.2.1.1 n ] ) ) hbeta hrange hS1 hS2 hsize;
    nlinarith [ abs_le.mp this.1, hCeff n, hvalid.2.2.2.1, hvalid.2.2.2.2.2.2.2.1.1 n, le_max_left 1 ( C_V * D.cSize + Ceff ), le_max_right 1 ( C_V * D.cSize + Ceff ), mul_nonneg ( show 0 ≤ C_V by linarith ) ( show 0 ≤ D.cSize by linarith [ hvalid.2.2.2.1 ] ), mul_nonneg ( show 0 ≤ C_V by linarith ) ( show 0 ≤ D.sigma n by linarith [ hvalid.2.2.2.2.2.2.2.1.1 n ] ) ];
  · exact_mod_cast card_le_V S.card r hS2 |> lt_of_lt_of_le ( Nat.cast_pos.mpr hS1 )

/-
Effective volume-calculus inversion: an explicit-slack clone of
`logsize_le_of_V_upper`.  Given an upper bound on the Harper minimum at
effective density `target + rho/n` with explicit slack `Gf n ≤ CG*(σ+1)`, it
returns a `log |T|` bound at density `target` with explicit slack `Cw*(σ+1)`.
The proof runs the (already proved) `logsize_le_of_V_upper_large` on the
explicit `volumeSlack = effLog K` (from `hBV`) and `Gf`, then bounds the
explicit affine output slack by `Cw*(σ+1)` via `r2_eff_effLog_le_sigma`,
`r2_eff_prefix_le_sigma`, and `r2_eff_linear_combo_le_sigma`.
-/
set_option maxHeartbeats 1000000 in
lemma r2_eff_logsize (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (D : StabilityData) (hvalid : validData D)
    (c0 lo : ℝ) (hc0 : 0 < c0) (hlo : 0 < lo) (hlohalf : lo ≤ 1 / 2 - c0)
    (Gf : ℕ → ℝ) (CG : ℝ)
    (hGfnn : ∀ n, 0 ≤ Gf n) (hGf : ∀ n, Gf n ≤ CG * (D.sigma n + 1)) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ (n rho : ℕ) (T : Finset (Cube n)) (target : ℝ),
      T.Nonempty → T.card < 2 ^ n → lo ≤ target →
      target + (rho : ℝ) / (n : ℝ) ≤ 1 / 2 - c0 →
      (V n T.card rho : ℝ) ≤
        Real.exp (H (target + (rho : ℝ) / (n : ℝ)) * (n : ℝ) + Gf n) →
      Real.log (T.card : ℝ) ≤ H target * (n : ℝ) + Cw * (D.sigma n + 1) := by
  revert hBV hVPlus D hvalid;
  intro hBV hVPlus D hvalid hGf
  obtain ⟨K, hK, hbv⟩ := hBV
  have hK0 : 0 ≤ K := by linarith
  have hvssub : Sublinear (effLog K) := r2_eff_sublinear_effLog hK0
  have hvsnn : ∀ n, 0 ≤ effLog K n := hvssub.1
  obtain ⟨Ceff, hCeff1, hCeffbd⟩ := r2_eff_effLog_le_sigma D hvalid K hK
  generalize_proofs at *;
  -- Set up constants exactly as in `logsize_le_of_V_upper`.
  set hc0half : c0 < 1 / 2 := by
    linarith
  set κ := Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2))
  set L := Real.log ((1 - lo) / lo)
  have hκpos : 0 < κ := by
    exact Real.log_pos ( by rw [ lt_div_iff₀ ] <;> linarith )
  have hLnn : 0 ≤ L := by
    exact Real.log_nonneg ( by rw [ le_div_iff₀ hlo ] ; linarith )
  set hγ : H (1 / 2 - c0 / 2) - H (1 / 2 - c0) > 0 := by
    exact sub_pos_of_lt ( H_lt_H ( by linarith ) ( by linarith ) ( by linarith ) )
  set rate := min (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) (κ * (c0 / 2))
  have hrate_pos : 0 < rate := by
    exact lt_min hγ ( mul_pos hκpos ( half_pos hc0 ) )
  have hGf_sub : Sublinear (fun n => Gf n + effLog K n) := by
    apply Sublinear_add;
    · apply Sublinear_of_le (fun n => hGfnn n) (fun n => hGf n) (r2_eff_sublinear_scale_add_one hvalid.2.2.2.2.2.2.2.1 (by
      contrapose! hGf;
      exact ⟨ 0, by nlinarith [ hGfnn 0, hvalid.2.2.2.2.2.2.2.1.1 0 ] ⟩));
    · grind
  have hN1 : ∃ N1, 1 ≤ N1 ∧ ∀ n, N1 ≤ n → Gf n + effLog K n < rate * n := by
    exact sublinear_lt_of_pos hGf_sub hrate_pos |> fun ⟨ N1, hN1pos, hN1 ⟩ => ⟨ N1, hN1pos, fun n hn => hN1 n hn ⟩
  obtain ⟨N1, hN1pos, hN1⟩ := hN1
  set N := max N1 (⌈(2 : ℝ) / c0⌉₊ + 1) with hN_def
  obtain ⟨Cpre, hCpre1, hCprebd⟩ := r2_eff_prefix_le_sigma D hvalid N ((N : ℝ) * Real.log 2)
  generalize_proofs at *;
  refine' ⟨ 1 + Cpre + ( L / κ + 1 ) * ( CG + Ceff ) + ( L + 2 ), _, _ ⟩ <;> norm_num at *;
  · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_add_of_nonneg_right ( by positivity ) ) ( mul_nonneg ( add_nonneg ( div_nonneg hLnn hκpos.le ) zero_le_one ) ( add_nonneg ( show 0 ≤ CG by nlinarith [ hGf 0, hGfnn 0, hvalid.2.2.2.2.2.2.2.1.1 0 ] ) ( by positivity ) ) ) ) ( by positivity );
  · intro n rho T target hT hT2 htar hg hV
    by_cases hn : n < N;
    · have hcard : (T.card : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast hT2.le
      have hlogcard : Real.log (T.card : ℝ) ≤ n * Real.log 2 := by
        simpa using Real.log_le_log ( Nat.cast_pos.mpr hT.card_pos ) hcard
      have hlogcard_le : n * Real.log 2 ≤ N * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hn.le ) ( Real.log_nonneg one_le_two )
      have hlogcard_le_Cpre : N * Real.log 2 ≤ Cpre * (D.sigma n + 1) := by
        simpa [ hn ] using hCprebd n
      have hlogcard_le_Cw : N * Real.log 2 ≤ (1 + Cpre + (L / κ + 1) * (CG + Ceff) + (L + 2)) * (D.sigma n + 1) := by
        refine le_trans hlogcard_le_Cpre ?_;
        gcongr;
        · exact add_nonneg ( hvalid.2.2.2.2.2.2.2.1.1 n ) zero_le_one;
        · nlinarith [ show 0 ≤ L / κ by positivity, show 0 ≤ CG + Ceff by nlinarith [ hGf n, hGfnn n, hvalid.2.2.2.2.2.2.2.1.1 n ] ]
      linarith [hlogcard, hlogcard_le, hlogcard_le_Cpre, hlogcard_le_Cw, show 0 ≤ H target * n by
                                                                          exact mul_nonneg ( Real.binEntropy_nonneg ( by linarith ) ( by linarith [ show target ≤ 1 / 2 by linarith [ show ( rho : ℝ ) / n ≥ 0 by positivity ] ] ) ) ( Nat.cast_nonneg _ )];
    · have hthr1 : Gf n + effLog K n < (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) * n := by
        exact lt_of_lt_of_le ( hN1 n ( le_trans ( le_max_left _ _ ) ( le_of_not_gt hn ) ) ) ( mul_le_mul_of_nonneg_right ( min_le_left _ _ ) ( Nat.cast_nonneg _ ) )
      have hthr2 : Gf n + effLog K n < κ * (c0 / 2) * n := by
        exact lt_of_lt_of_le ( hN1 n ( le_trans ( le_max_left _ _ ) ( le_of_not_gt hn ) ) ) ( mul_le_mul_of_nonneg_right ( min_le_right _ _ ) ( Nat.cast_nonneg _ ) )
      have hthr3 : 1 < c0 / 2 * n := by
        nlinarith [ Nat.le_ceil ( 2 / c0 ), mul_div_cancel₀ 2 hc0.ne', show ( n : ℝ ) ≥ ⌈2 / c0⌉₊ + 1 by exact_mod_cast le_of_not_gt hn |> le_trans ( le_max_right _ _ ) ]
      have hmain := logsize_le_of_V_upper_large hVPlus c0 lo hc0 hc0half hlo hlohalf (effLog K) Gf hbv n rho T target hT hT2 htar hg hV hthr1 hthr2 hthr3 (by
      exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at hthr3 )) (hvsnn n) (hGfnn n)
      generalize_proofs at *;
      have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
      have hsig1 : 1 ≤ D.sigma n + 1 := by linarith
      have hcoefnn : 0 ≤ L / κ + 1 := by
        exact add_nonneg ( div_nonneg hLnn hκpos.le ) zero_le_one
      generalize_proofs at *;
      nlinarith [ hGf n, hCeffbd n, mul_le_mul_of_nonneg_left ( hGf n ) hcoefnn, mul_le_mul_of_nonneg_left ( hCeffbd n ) hcoefnn ]

set_option maxHeartbeats 1000000 in
/-- Effective downward-pinning core (sub-equatorial branch): an explicit-slack
clone of `r2_dp_core`, with the sublinear envelope `sigmaDP` replaced by
`Cdp * (D.sigma n + 1)`.  The proof mirrors `r2_dp_core` verbatim, using
`r2_eff_V_upper` in place of `V_upper_of_classMember` and `r2_eff_logsize` in
place of `logsize_le_of_V_upper`; the range control `c0` is obtained from
`r1_range_control` applied to the converted statements
`r2_eff_BVStatement_of_Eff hBV` and `r2_eff_IVCStatement_of_Eff hIVC`, and the
finite `n < N` prefix (cube bound) is absorbed via `r2_eff_prefix_le_sigma`. -/
lemma r2_eff_dp_core (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ Cdp : ℝ, 1 ≤ Cdp ∧ ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta → alpha + tau < 1 / 2 →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (alpha + tau) * (n : ℝ) + Cdp * (D.sigma n + 1)) := by
  classical
  obtain ⟨c0, hc0pos, N, hNpos, hc0⟩ :=
    r1_range_control (r2_eff_BVStatement_of_Eff hBV) hVPlus
      (r2_eff_IVCStatement_of_Eff hIVC) D hvalid
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_le_max : D.alphaMin ≤ D.alphaMax := hvalid.2.2.2.2.2.1
  set c0star := min c0 ((1 / 2 - D.alphaMax) / 2) with hc0stardef
  have hc0star_pos : 0 < c0star := by
    rw [hc0stardef]; exact lt_min hc0pos (by linarith)
  have hc0star_le : c0star ≤ c0 := min_le_left _ _
  have hc0star_le2 : c0star ≤ (1 / 2 - D.alphaMax) / 2 := min_le_right _ _
  have hlo_half : D.alphaMin ≤ 1 / 2 - c0star := by linarith
  have hL''nn : 0 ≤ Real.log ((1 - D.alphaMin) / D.alphaMin) := by
    apply Real.log_nonneg; rw [le_div_iff₀ halphaMin_pos]; linarith
  obtain ⟨CG, hCG1, hVup⟩ := r2_eff_V_upper hIVC D hvalid c0star hc0star_pos
  set Gf : ℕ → ℝ := fun n => CG * (D.sigma n + 1) + D.sigma n +
    Real.log ((1 - D.alphaMin) / D.alphaMin) with hGf_def
  have hGfnn : ∀ n, 0 ≤ Gf n := by
    intro n
    have hsig := hvalid.2.2.2.2.2.2.2.1.1 n
    have hCG0 : 0 ≤ CG := le_trans zero_le_one hCG1
    have hcgt : 0 ≤ CG * (D.sigma n + 1) := mul_nonneg hCG0 (by linarith)
    rw [hGf_def]; dsimp only; linarith
  have hGfbd : ∀ n, Gf n ≤
      (CG + 1 + Real.log ((1 - D.alphaMin) / D.alphaMin)) * (D.sigma n + 1) := by
    intro n
    have hsig := hvalid.2.2.2.2.2.2.2.1.1 n
    have hCG0 : 0 ≤ CG := le_trans zero_le_one hCG1
    rw [hGf_def]; dsimp only
    nlinarith [hL''nn, hsig, mul_nonneg hL''nn hsig]
  obtain ⟨Cw, hCw1, hw⟩ := r2_eff_logsize hBV hVPlus D hvalid c0star D.alphaMin
    hc0star_pos halphaMin_pos hlo_half Gf
    (CG + 1 + Real.log ((1 - D.alphaMin) / D.alphaMin)) hGfnn hGfbd
  obtain ⟨Cpre, hCpre1, hCprebd⟩ :=
    r2_eff_prefix_le_sigma D hvalid N ((N : ℝ) * Real.log 2)
  refine ⟨max Cw Cpre, le_trans hCw1 (le_max_left _ _), ?_⟩
  intro n r S alpha beta hmem tau htau htaub hhalf
  obtain ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ := hmem
  have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hHtar_nn : 0 ≤ H (alpha + tau) := by
    unfold H; exact Real.binEntropy_nonneg (by linarith) (by linarith)
  by_cases hSne : S.Nonempty
  · by_cases hn : n < N
    · -- small `n`: cube bound absorbed by the finite prefix.
      have hcard : ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp ((n : ℝ) * Real.log 2) := cube_card_le_two_pow _
      have hpre := hCprebd n
      rw [if_pos hn] at hpre
      have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hnN : (n : ℝ) * Real.log 2 ≤ (N : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) hlog2nn
      have hmax : Cpre * (D.sigma n + 1) ≤ max Cw Cpre * (D.sigma n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
      have hHnn : 0 ≤ H (alpha + tau) * (n : ℝ) := mul_nonneg hHtar_nn (Nat.cast_nonneg n)
      refine le_trans hcard (Real.exp_le_exp.mpr ?_)
      linarith [hnN, hpre, hmax, hHnn]
    · -- large `n`: peeling argument (mirror of `r2_dp_core`).
      push_neg at hn
      have hn1 : 1 ≤ n := le_trans hNpos hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hrange : alpha + beta ≤ 1 / 2 - c0 :=
        hc0 n hn r S alpha beta
          ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
      have hrange' : alpha + beta ≤ 1 / 2 - c0star := by linarith
      have halpha_half : alpha ≤ 1 / 2 := le_of_lt (lt_of_le_of_lt halpha_max halphaMax_half)
      have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
      have hScard2 : S.card ≤ 2 ^ n := by
        calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
          _ = 2 ^ n := by
              rw [Finset.card_univ]
              exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
      have hr'r : ⌈tau * (n : ℝ)⌉₊ ≤ r := by
        rw [Nat.ceil_le]
        have hh := htaub
        rw [hbeta, le_div_iff₀ hnR] at hh
        exact hh
      set r'N := ⌈tau * (n : ℝ)⌉₊ with hr'Ndef
      have hpeel : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
          Real.exp (D.sigma n) * (V n S.card r : ℝ) :=
        V_peel_le S r'N r hr'r (D.sigma n) hnear
      have hVupS : (V n S.card r : ℝ) ≤
          Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1)) :=
        hVup n r S alpha beta halpha_min halpha_half hbeta hrange' hScard1 hScard2 hsize
      have hcombined : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
          Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1) + D.sigma n) := by
        calc (V n (neighborhood r'N S).card (r - r'N) : ℝ)
            ≤ Real.exp (D.sigma n) * (V n S.card r : ℝ) := hpeel
          _ ≤ Real.exp (D.sigma n) *
              Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1)) :=
              mul_le_mul_of_nonneg_left hVupS (Real.exp_nonneg _)
          _ = Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1) + D.sigma n) := by
              rw [← Real.exp_add]; congr 1; ring
      have hcast_sub : ((r - r'N : ℕ) : ℝ) = (r : ℝ) - (r'N : ℝ) := Nat.cast_sub hr'r
      set a := alpha + tau + ((r - r'N : ℕ) : ℝ) / (n : ℝ) with hadef
      have hbma : alpha + beta - a = (r'N : ℝ) / (n : ℝ) - tau := by
        rw [hadef, hbeta, hcast_sub]; ring
      have htau_le : tau ≤ (r'N : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hnR, hr'Ndef]; exact Nat.le_ceil _
      have hbma_nn : 0 ≤ alpha + beta - a := by rw [hbma]; linarith
      have ha_pos : 0 < a := by
        rw [hadef]
        have hnn : 0 ≤ ((r - r'N : ℕ) : ℝ) / (n : ℝ) := by positivity
        linarith
      have hab : a ≤ alpha + beta := by linarith
      have hb_half : alpha + beta ≤ 1 / 2 := by linarith
      have hlo_a : D.alphaMin ≤ a := by
        rw [hadef]
        have hnn : 0 ≤ ((r - r'N : ℕ) : ℝ) / (n : ℝ) := by positivity
        linarith
      have ha_half : a ≤ 1 / 2 := by linarith
      have hslope : Real.log ((1 - a) / a) ≤ Real.log ((1 - D.alphaMin) / D.alphaMin) :=
        log_ratio_upper halphaMin_pos hlo_a ha_half
      have hHdiff : H (alpha + beta) - H a ≤
          (alpha + beta - a) * Real.log ((1 - D.alphaMin) / D.alphaMin) :=
        H_diff_le ha_pos hab hb_half hslope
      have hban_eq : (alpha + beta - a) * (n : ℝ) = (r'N : ℝ) - tau * (n : ℝ) := by
        rw [hbma, sub_mul, div_mul_cancel₀ _ (ne_of_gt hnR)]
      have hban_le : (alpha + beta - a) * (n : ℝ) ≤ 1 := by
        rw [hban_eq, hr'Ndef]
        have hlt := Nat.ceil_lt_add_one (show 0 ≤ tau * (n : ℝ) by positivity)
        linarith
      have hprod : (H (alpha + beta) - H a) * (n : ℝ) ≤
          Real.log ((1 - D.alphaMin) / D.alphaMin) := by
        have h1 : (H (alpha + beta) - H a) * (n : ℝ) ≤
            (alpha + beta - a) * Real.log ((1 - D.alphaMin) / D.alphaMin) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hHdiff hnR.le
        have h3 : Real.log ((1 - D.alphaMin) / D.alphaMin) * ((alpha + beta - a) * (n : ℝ)) ≤
            Real.log ((1 - D.alphaMin) / D.alphaMin) * 1 :=
          mul_le_mul_of_nonneg_left hban_le hL''nn
        nlinarith [h1, h3]
      have hVbound : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
          Real.exp (H a * (n : ℝ) + Gf n) := by
        refine le_trans hcombined (Real.exp_le_exp.mpr ?_)
        rw [hGf_def]; dsimp only
        nlinarith [hprod]
      have hTne : (neighborhood r'N S).Nonempty :=
        hSne.mono (subset_neighborhood_self r'N S)
      have hpow_exp : ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hk'lt : (neighborhood r'N S).card < 2 ^ n := by
        have hle1 : ((neighborhood r'N S).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (neighborhood_mono_radius hr'r S)
        have hlt2 : Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) <
            Real.exp ((n : ℝ) * Real.log 2) := by
          apply Real.exp_lt_exp.mpr
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have hd : 0 < D.deltaCap := hvalid.2.1
          nlinarith [mul_pos (mul_pos hd hnR) hlog2]
        have hlt3 : ((neighborhood r'N S).card : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
          rw [hpow_exp]
          exact lt_of_le_of_lt (le_trans hle1 hcap) hlt2
        exact_mod_cast hlt3
      have hlo_target : D.alphaMin ≤ alpha + tau := by linarith
      have ha_le : a ≤ 1 / 2 - c0star := by linarith
      have hdens : (alpha + tau) + ((r - r'N : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 - c0star := by
        rw [← hadef]; exact ha_le
      have hVbound' : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
          Real.exp (H ((alpha + tau) + ((r - r'N : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) + Gf n) := by
        rw [← hadef]; exact hVbound
      have hlogk' := hw n (r - r'N) (neighborhood r'N S) (alpha + tau) hTne
        hk'lt hlo_target hdens hVbound'
      have hposc : (0 : ℝ) < ((neighborhood r'N S).card : ℝ) :=
        by exact_mod_cast Finset.card_pos.mpr hTne
      rw [← Real.log_le_iff_le_exp hposc]
      have hmax : Cw * (D.sigma n + 1) ≤ max Cw Cpre * (D.sigma n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      linarith [hlogk', hmax]
  · -- `S` empty: the neighborhood is empty.
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    have hEmpty : neighborhood ⌈tau * (n : ℝ)⌉₊ S = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      rw [mem_neighborhood_iff] at hx
      rcases hx with ⟨u, hu, _⟩
      rw [hSempty] at hu
      exact absurd hu (Finset.notMem_empty u)
    rw [hEmpty, Finset.card_empty]
    simp only [Nat.cast_zero]
    exact le_of_lt (Real.exp_pos _)

/-- Effective downward pinning (the `min (·) (1/2)` form used by `pinned`):
an explicit-slack clone of `r2_downward_pinning`.  Proof: obtain `Cdp` from
`r2_eff_dp_core`; for `alpha + tau < 1/2` use the core directly, and at or
above the equator use the cube bound `cube_card_le_two_pow` with
`H (1/2) = Real.log 2`. -/
lemma r2_eff_downward_pinning_bound
    (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ Cdp : ℝ, 1 ≤ Cdp ∧ ∀ n r S alpha beta,
      classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) +
            Cdp * (D.sigma n + 1)) := by
  obtain ⟨Cdp, hCdp1, hcore⟩ := r2_eff_dp_core hBV hVPlus hIVC D hvalid
  refine ⟨Cdp, hCdp1, ?_⟩
  intro n r S alpha beta hmem tau htau htaub
  by_cases hhalf : alpha + tau < 1 / 2
  · rw [min_eq_left hhalf.le]
    exact hcore n r S alpha beta hmem tau htau htaub hhalf
  · rw [min_eq_right (not_lt.mp hhalf)]
    have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
    have hCdp_nn : 0 ≤ Cdp := by linarith
    have hslack_nn : 0 ≤ Cdp * (D.sigma n + 1) :=
      mul_nonneg hCdp_nn (by linarith)
    have hHhalf : H (1 / 2 : ℝ) = Real.log 2 := by
      unfold H
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num]
      exact Real.binEntropy_two_inv
    have hcard := cube_card_le_two_pow (neighborhood ⌈tau * (n : ℝ)⌉₊ S)
    calc ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ)
        ≤ Real.exp ((n : ℝ) * Real.log 2) := hcard
      _ ≤ Real.exp (H (1 / 2) * (n : ℝ) + Cdp * (D.sigma n + 1)) := by
          apply Real.exp_le_exp.mpr
          rw [hHhalf, mul_comm]
          linarith

/-
The binary entropy `H` is bounded below on the compact window `[-1, 2]`,
by a constant `Hlb ≤ Real.log 2`.  Used to absorb the finite `n`-prefix of the
pinned bound where the shifted density `alpha + r/n` may exceed `1`, so that
`H` can be (mildly) negative.  Proved from `binEntropy_continuous` and
compactness of `Set.Icc (-1) 2`.
-/
lemma r2_eff_H_lower_bound :
    ∃ Hlb : ℝ, Hlb ≤ Real.log 2 ∧ ∀ y : ℝ, -1 ≤ y → y ≤ 2 → Hlb ≤ H y := by
  obtain ⟨x, _hx, hmin⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 2)).exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) (Real.binEntropy_continuous.continuousOn);
  exact ⟨ Min.min ( Real.binEntropy x ) ( Real.log 2 ), min_le_right _ _, fun y hy₁ hy₂ => le_trans ( min_le_left _ _ ) ( hmin ⟨ hy₁, hy₂ ⟩ ) ⟩

set_option maxHeartbeats 1000000 in
/-- Effective pinned core: every class member (with nonempty `S`) is `pinned`
for the buffered `r2EffQData D Cpin` with a single absorbing constant `Cpin`.
Explicit-slack clone of `pinned_buffered_of_classMember_large`, extended to
cover all `n` (the finite `n` where the `1/n ≤ ...` gap conditions fail are
absorbed into `Cpin` via the cube bound and `r2_eff_prefix_le_sigma`). -/
lemma r2_eff_pinned_core (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ Cpin : ℝ, 1 ≤ Cpin ∧
      ∀ n r S alpha beta, classMember D n r S alpha beta → S.Nonempty →
        pinned (r2EffQData D Cpin) n S alpha := by
  classical
  obtain ⟨Cdp, hCdp1, hDP⟩ := r2_eff_downward_pinning_bound hBV hVPlus hIVC D hvalid
  obtain ⟨Hlb, hHlb_le, hHlb⟩ := r2_eff_H_lower_bound
  have hrho : 0 < D.rho := hvalid.1
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_le_max : D.alphaMin ≤ D.alphaMax := hvalid.2.2.2.2.2.1
  have hcSize : 1 ≤ D.cSize := hvalid.2.2.2.1
  have hgap_pos : 0 < 1 / 2 - D.alphaMax := by linarith
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2Hlb_nn : 0 ≤ Real.log 2 - Hlb := by linarith
  set N0 : ℕ := max (⌈2 / D.rho⌉₊ + 1) (⌈4 / (1 / 2 - D.alphaMax)⌉₊ + 1) with hN0def
  obtain ⟨Cpre, hCpre1, hCprebd⟩ :=
    r2_eff_prefix_le_sigma D hvalid N0 ((N0 : ℝ) * (Real.log 2 - Hlb))
  refine ⟨max (max 1 Cdp) (max D.cSize Cpre),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  set Cpin := max (max 1 Cdp) (max D.cSize Cpre) with hCpindef
  have hCpin1 : 1 ≤ Cpin := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCdp_le : Cdp ≤ Cpin := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcSize_le : D.cSize ≤ Cpin := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCpre_le : Cpre ≤ Cpin := le_trans (le_max_right _ _) (le_max_right _ _)
  intro n r S alpha beta hmem hSne
  obtain ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ := hmem
  have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hsig1 : (1 : ℝ) ≤ D.sigma n + 1 := by linarith
  have hCpin_nn : 0 ≤ Cpin := le_trans zero_le_one hCpin1
  intro r' hr'
  simp only [r2EffQData] at hr' ⊢
  set s0 : ℝ := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) with hs0def
  have hs0_pos : 0 < s0 := lt_min (by linarith) (by linarith)
  have hs0_nn : 0 ≤ s0 := le_of_lt hs0_pos
  have hs0_le_rho : s0 ≤ D.rho / 2 := min_le_left _ _
  have hs0_le_gap : s0 ≤ (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
  by_cases hr0 : r' = 0
  · -- radius zero: the size hypothesis suffices.
    subst r'
    rw [neighborhood_zero_eq]
    have hzero : alpha + ((0 : ℕ) : ℝ) / (n : ℝ) = alpha := by simp
    rw [hzero]
    have hScard_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
    rw [← Real.log_le_iff_le_exp hScard_pos]
    have hupper := (abs_le.mp hsize).2
    have hcsz : D.cSize * D.sigma n ≤ Cpin * (D.sigma n + 1) := by
      have h1 : D.cSize * D.sigma n ≤ Cpin * D.sigma n :=
        mul_le_mul_of_nonneg_right hcSize_le hsig_nn
      nlinarith [hCpin_nn, hsig_nn]
    linarith [hupper, hcsz]
  · -- positive radius.
    have hr'pos : 1 ≤ r' := Nat.one_le_iff_ne_zero.mpr hr0
    have hn1 : 1 ≤ n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      · simp only [Nat.cast_zero, mul_zero, Nat.ceil_zero, Nat.le_zero] at hr'
        exact hr0 hr'
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    set tau : ℝ := (r' : ℝ) / (n : ℝ) with htaudef
    have htau_pos : 0 < tau := div_pos (by exact_mod_cast hr'pos) hnR
    have hceil_tau : ⌈tau * (n : ℝ)⌉₊ = r' := by
      have hmul : tau * (n : ℝ) = (r' : ℝ) := by rw [htaudef]; field_simp
      rw [hmul, Nat.ceil_natCast]
    have hceil_lt : ((Nat.ceil (s0 * (n : ℝ)) : ℕ) : ℝ) < s0 * (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hs0_nn hnR.le)
    have hr'_real : (r' : ℝ) ≤ (Nat.ceil (s0 * (n : ℝ)) : ℕ) := by exact_mod_cast hr'
    have htau_le_s0_plus : tau ≤ s0 + (1 : ℝ) / (n : ℝ) := by
      rw [htaudef]
      have hlt : (r' : ℝ) < s0 * (n : ℝ) + 1 := lt_of_le_of_lt hr'_real hceil_lt
      rw [div_le_iff₀ hnR]
      have heq : (s0 + (1 : ℝ) / (n : ℝ)) * (n : ℝ) = s0 * (n : ℝ) + 1 := by
        field_simp
      rw [heq]; exact hlt.le
    have hs0n_le_r : s0 * (n : ℝ) ≤ (r : ℝ) := by
      have h1 : s0 * (n : ℝ) ≤ D.rho * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hs0_le_rho]) hnR.le
      linarith [hradius]
    have hceil_le_r : Nat.ceil (s0 * (n : ℝ)) ≤ r := Nat.ceil_le.mpr hs0n_le_r
    have hr'_le_r : r' ≤ r := le_trans hr' hceil_le_r
    have htau_le_beta : tau ≤ beta := by
      have hcast : (r' : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr'_le_r
      rw [htaudef, hbeta]; gcongr
    by_cases hbign : N0 ≤ n
    · -- large `n`: `alpha + tau ≤ 1/2`, apply downward pinning.
      have h1n_gap : (1 : ℝ) / (n : ℝ) ≤ (1 / 2 - D.alphaMax) / 4 := by
        have hle : ⌈4 / (1 / 2 - D.alphaMax)⌉₊ + 1 ≤ n :=
          le_trans (le_max_right _ _) hbign
        have hn_gt : 4 / (1 / 2 - D.alphaMax) < (n : ℝ) := by
          have h1 : 4 / (1 / 2 - D.alphaMax) ≤ (⌈4 / (1 / 2 - D.alphaMax)⌉₊ : ℝ) :=
            Nat.le_ceil _
          have h2 : ((⌈4 / (1 / 2 - D.alphaMax)⌉₊ : ℕ) : ℝ) < (n : ℝ) := by
            have : ⌈4 / (1 / 2 - D.alphaMax)⌉₊ < n := by omega
            exact_mod_cast this
          linarith
        rw [div_lt_iff₀ hgap_pos] at hn_gt
        rw [div_le_iff₀ hnR]
        nlinarith [hn_gt]
      have htau_le_half_gap : tau ≤ (1 / 2 - D.alphaMax) / 2 := by
        linarith [htau_le_s0_plus, hs0_le_gap, h1n_gap]
      have halpha_tau_half : alpha + tau ≤ 1 / 2 := by
        linarith [htau_le_half_gap, halpha_max]
      have hDP' := hDP n r S alpha beta
        ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
        tau htau_pos htau_le_beta
      rw [hceil_tau, min_eq_left halpha_tau_half] at hDP'
      refine le_trans hDP' (Real.exp_le_exp.mpr ?_)
      have hstep : Cdp * (D.sigma n + 1) ≤ Cpin * (D.sigma n + 1) :=
        mul_le_mul_of_nonneg_right hCdp_le (by linarith)
      linarith [hstep]
    · -- small `n`: cube bound absorbed by the finite prefix.
      push_neg at hbign
      have hcard : ((neighborhood r' S).card : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) :=
        cube_card_le_two_pow _
      have harg_nn : (0 : ℝ) ≤ alpha + tau := by linarith [halpha_min, htau_pos]
      have harg_ge : (-1 : ℝ) ≤ alpha + tau := by linarith [harg_nn]
      have hinv_le_one : (1 : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnR]; exact_mod_cast hn1
      have htau_le_2 : tau ≤ s0 + 1 := by linarith [htau_le_s0_plus, hinv_le_one]
      have hs0_lt_half : s0 < 1 / 2 := lt_of_le_of_lt hs0_le_gap (by linarith)
      have harg_le : alpha + tau ≤ 2 := by
        linarith [halpha_max, halphaMax_half, htau_le_2, hs0_lt_half]
      have hHlb_arg : Hlb ≤ H (alpha + tau) := hHlb (alpha + tau) harg_ge harg_le
      have hpre := hCprebd n
      rw [if_pos hbign] at hpre
      have hnN0 : (n : ℝ) * (Real.log 2 - Hlb) ≤ (N0 : ℝ) * (Real.log 2 - Hlb) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hbign.le) hlog2Hlb_nn
      have hCpre_step : Cpre * (D.sigma n + 1) ≤ Cpin * (D.sigma n + 1) :=
        mul_le_mul_of_nonneg_right hCpre_le (by linarith)
      have hbudget : (n : ℝ) * (Real.log 2 - Hlb) ≤ Cpin * (D.sigma n + 1) :=
        le_trans hnN0 (le_trans hpre hCpre_step)
      have hHn : Hlb * (n : ℝ) ≤ H (alpha + tau) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hHlb_arg (Nat.cast_nonneg n)
      refine le_trans hcard (Real.exp_le_exp.mpr ?_)
      nlinarith [hHn, hbudget]

/-- Every class member yields a fat + pinned set for the buffered `r2EffQData D C`,
with a single absorbing constant `C`.

The `S.Nonempty` hypothesis (added relative to the original leaf statement) is
necessary: `fat` requires the set to be nonempty, yet `classMember D n r S alpha
beta` can hold with `S = ∅` (e.g. at `n = 0`), so the unconditional statement is
false.  The R2 composer only ever needs fat + pinned for nonempty `S`. -/
lemma r2_eff_classMember_fat_pinned (D : StabilityData) (hvalid : validData D)
    (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n r S alpha beta, classMember D n r S alpha beta → S.Nonempty →
    fat (r2EffQData D C) n S alpha ∧ pinned (r2EffQData D C) n S alpha := by
  obtain ⟨Cpin, hCpin1, hpinned⟩ := r2_eff_pinned_core hBV hVPlus hIVC D hvalid
  refine ⟨max Cpin D.cSize, le_trans hCpin1 (le_max_left _ _), ?_⟩
  intro n r S alpha beta hclass hS
  have hC1 : 1 ≤ max Cpin D.cSize := le_trans hCpin1 (le_max_left _ _)
  constructor
  · exact r2_eff_fat_of_classMember D hvalid (max Cpin D.cSize) hC1
      (le_max_right _ _) n r S alpha beta hclass hS
  · exact r2_eff_pinned_mono_C D hvalid (C0 := Cpin) (C := max Cpin D.cSize)
      (le_max_left _ _) (hpinned n r S alpha beta hclass hS)

lemma r2_eff_s7_output_to_hbl (D : StabilityData) (C : ℝ)
    (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ)
    (K_s7 : ℝ)
    (eps : ℝ)
    (a : Cube n)
    (hmass : Real.exp (-((K_s7 / eps ^ 8) * (effEnv 10 (r2EffQData D C).sigma n + 1))) * (S.card : ℝ) ≤
      ((S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + 4 * eps) * (n : ℝ))).card : ℝ))
    (K_out : ℝ)
    (hK_bound : (K_s7 / eps ^ 8) * (effEnv 10 (r2EffQData D C).sigma n + 1) ≤ K_out * (effEnv 14 D.sigma n + 1))
    (h_radius_absorb : alpha * (n : ℝ) + 4 * eps * (n : ℝ) ≤ (rmin n S.card : ℝ) + K_out * (effEnv 14 D.sigma n + 1)) :
    heavyBallConclusion n S (K_out * (effEnv 14 D.sigma n + 1)) (Nat.ceil (K_out * (effEnv 14 D.sigma n + 1))) := by
  classical
  refine ⟨a, ?_⟩
  let mass_s7 : ℝ := (K_s7 / eps ^ 8) * (effEnv 10 (r2EffQData D C).sigma n + 1)
  let mass_out : ℝ := K_out * (effEnv 14 D.sigma n + 1)
  have hmass_le :
      Real.exp (-mass_out) * (S.card : ℝ) ≤ Real.exp (-mass_s7) * (S.card : ℝ) := by
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le S.card
    have hneg : -mass_out ≤ -mass_s7 := by
      dsimp [mass_s7, mass_out]
      exact neg_le_neg hK_bound
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hneg) hcard_nonneg
  have h_radius_nat :
      Nat.ceil ((alpha + 4 * eps) * (n : ℝ)) ≤
        rmin n S.card + Nat.ceil mass_out := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_add]
    calc
      (alpha + 4 * eps) * (n : ℝ)
          = alpha * (n : ℝ) + 4 * eps * (n : ℝ) := by ring
      _ ≤ (rmin n S.card : ℝ) + mass_out := by
          dsimp [mass_out]
          exact h_radius_absorb
      _ ≤ (rmin n S.card : ℝ) + Nat.ceil mass_out := by
          have hceil_mass : mass_out ≤ (Nat.ceil mass_out : ℝ) := Nat.le_ceil mass_out
          linarith
  have hsub :
      (S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + 4 * eps) * (n : ℝ))) ⊆
        (S.filter fun x =>
          hDist x a ≤ rmin n S.card + Nat.ceil (K_out * (effEnv 14 D.sigma n + 1))) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 (by simpa [mass_out] using h_radius_nat)⟩
  have hcard_mono :
      ((S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + 4 * eps) * (n : ℝ))).card : ℝ) ≤
        ((S.filter fun x =>
          hDist x a ≤ rmin n S.card + Nat.ceil (K_out * (effEnv 14 D.sigma n + 1))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans (le_trans hmass_le (by simpa [mass_s7] using hmass)) hcard_mono

/-
`effEnv` is monotone in the grade.
-/
lemma effEnv_le_grade (s : ℕ → ℝ) {k j : ℕ} (hkj : k ≤ j) (n : ℕ) :
    effEnv k s n ≤ effEnv j s n := by
  induction' hkj with j hj ih;
  · rfl;
  · exact le_trans ih ( le_effGeo _ _ )

/-
The logarithmic slack `effLog K` is dominated by the grade-14 envelope of a
valid tuple.
-/
lemma r2_eff_effLog_bound (D : StabilityData) (hvalid : validData D)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, effLog K n ≤ A * (effEnv 14 D.sigma n + 1) := by
  refine' ⟨ K * ( Real.log 3 + 1 ), by positivity, fun n => _ ⟩;
  -- By definition of `effLog`, we have `effLog K n = K * (Real.log (n + 2) + 1)`.
  have h_effLog : effLog K n = K * (Real.log (n + 2) + 1) := by
    rfl;
  -- By definition of `effEnv`, we have `effEnv 14 D.sigma n ≥ D.sigma n`.
  have h_effEnv : effEnv 14 D.sigma n ≥ D.sigma n := by
    exact le_effEnv _ _ _;
  by_cases hn : 1 ≤ n <;> simp_all +decide [ validData ];
  · rw [ mul_assoc ];
    gcongr;
    have h_log_bound : Real.log (n + 2) ≤ Real.log 3 + Real.log n := by
      rw [ ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith;
    nlinarith [ Real.log_nonneg ( show ( 3 : ℝ ) ≥ 1 by norm_num ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast ), hvalid.2.2.2.2.2.2.2.2 n hn ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_left <| effGeo_nonneg _ _ ) <| by positivity );
    rw [ mul_one ] ; gcongr ; norm_num

/-
The S7 mass threshold `K / eps(n)^8 ≤ n` holds for every large `n`.
-/
lemma r2_eff_threshold (Q : QData) (sigma : ℕ → ℝ) (hsigma : ∀ n, 0 ≤ sigma n)
    (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) (K : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      K / (r2EffEpsClamped Q sigma n) ^ 8 ≤ (n : ℝ) := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, K ≤ n * (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) ^ 8 := by
    exact ⟨ ⌈K / ( Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ) ^ 8⌉₊, fun n hn => by nlinarith [ Nat.ceil_le.mp hn, show 0 < Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ^ 8 by exact pow_pos ( lt_min ( by linarith ) ( by linarith ) ) _, div_mul_cancel₀ K ( show ( Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ) ^ 8 ≠ 0 by exact pow_ne_zero _ ( ne_of_gt ( lt_min ( by linarith ) ( by linarith ) ) ) ) ] ⟩;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * (r2EffEps sigma n) ^ 8 := by
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * Real.sqrt ((effEnv 10 sigma n + 1) / (n + 1)) := by
      obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * Real.sqrt (1 / (n + 1)) := by
        norm_num [ ← div_eq_mul_inv ];
        exact ⟨ Nat.ceil ( K ^ 2 + 1 ), fun n hn => by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ Nat.ceil_le.mp hn, Real.sqrt_nonneg ( n + 1 : ℝ ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( n : ℝ ) + 1 ) ] ⟩;
      use N₂;
      intro n hn; specialize hN₂ n hn; refine le_trans hN₂ ?_; gcongr;
      exact le_add_of_nonneg_left ( effGeo_nonneg _ _ );
    exact ⟨ N₂, fun n hn => le_trans ( hN₂ n hn ) ( by rw [ r2_eff_eps_pow_eight ] ) ⟩;
  use max N₁ N₂; intros n hn; rw [ div_le_iff₀ ] <;> simp_all +decide [ r2EffEpsClamped ] ;
  · grind;
  · exact pow_pos ( lt_min ( lt_min ( by positivity ) ( by norm_num at *; linarith ) ) ( r2_eff_eps_pos sigma n ( hsigma n ) ) ) _

/-
Interior volume calculus gives `alpha * n ≤ rmin + grade-14 slack` for every
class member (applied at radius `0`).
-/
lemma r2_eff_rmin_lower_bound (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ),
      1 ≤ S.card → S.card ≤ 2 ^ n →
      D.alphaMin ≤ alpha → alpha ≤ D.alphaMax → sizeHyp D n S alpha →
      alpha * (n : ℝ) ≤ (rmin n S.card : ℝ) + B * (effEnv 14 D.sigma n + 1) := by
  -- Set c0 := (1/2 - D.alphaMax)/2.
  set c0 := (1 / 2 - D.alphaMax) / 2 with hc0_def;
  have hc0_pos : 0 < c0 := by
    linarith [ hvalid.2.2.2.2.2.2.1 ];
  obtain ⟨C_V, hC_V, K, hK, hcalc⟩ := hIVC D.alphaMin c0 (by
  cases hvalid ; aesop) hc0_pos;
  obtain ⟨A, hA, hAbd⟩ := r2_eff_effLog_bound D hvalid K (by linarith);
  refine' ⟨ C_V * D.cSize + A, _, _ ⟩;
  · exact add_nonneg ( mul_nonneg ( by linarith ) ( by linarith [ hvalid.2.2.2.1 ] ) ) hA;
  · intro n S alpha hS1 hS2 halpha1 halpha2 hsize
    have hcalc_applied : |(rmin n S.card : ℝ) - alpha * n| ≤ C_V * (D.cSize * D.sigma n) + effLog K n := by
      specialize hcalc n S.card 0 alpha 0 (D.cSize * D.sigma n);
      simp_all +decide [ sizeHyp ];
      grind +qlia;
    have h_bound : C_V * (D.cSize * D.sigma n) ≤ C_V * D.cSize * (effEnv 14 D.sigma n + 1) := by
      have h_bound : D.sigma n ≤ effEnv 14 D.sigma n + 1 := by
        exact le_add_of_le_of_nonneg ( le_effEnv 14 D.sigma n ) zero_le_one;
      nlinarith [ show 0 ≤ C_V * D.cSize by exact mul_nonneg ( by positivity ) ( by linarith [ hvalid.2.2.2.1 ] ) ];
    linarith [ abs_le.mp hcalc_applied, hAbd n ]

/-- HBL extraction for a single class data tuple, using the explicit precision schedule. -/
lemma r2_eff_hbl_from_q_and_dp (hS7 : S7Eff) (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ K : ℝ, 1 ≤ K ∧ HBLFor D (effDegrade D K 14) := by
  classical
  obtain ⟨C, hC1, hC_pinned⟩ := r2_eff_classMember_fat_pinned D hvalid hBV hVPlus hIVC
  let Q := r2EffQData D C
  have hQvalid : validQData Q := r2_eff_valid_qdata D hvalid C hC1
  have hDsigma_nonneg : ∀ m, 0 ≤ D.sigma m := fun m => hvalid.2.2.2.2.2.2.2.1.1 m
  have hQsigma_nonneg : ∀ m, 0 ≤ Q.sigma m := fun m => hQvalid.2.2.2.2.2.2.1.1 m
  have hqmin : (0 : ℝ) < Q.qMin := hQvalid.1
  have hqmax : Q.qMax < 1 / 2 := hQvalid.2.2.1
  obtain ⟨K_s7, hK_s7, hS7_bound⟩ := hS7 Q hQvalid
  obtain ⟨B, hB, hB_bound⟩ := r2_eff_rmin_lower_bound hIVC D hvalid
  -- Domination of `Q`'s grade-14 envelope by `D`'s grade-14 envelope.
  obtain ⟨G, hG1, hG⟩ : ∃ G : ℝ, 1 ≤ G ∧
      ∀ n : ℕ, effEnv 14 Q.sigma n ≤ G * (effEnv 14 D.sigma n + 1) := by
    refine ⟨2 ^ 14 * C, ?_, fun n => ?_⟩
    · have h : (1 : ℝ) ≤ 2 ^ 14 := by norm_num
      nlinarith [hC1, h]
    · have h := effEnv_comp 14 (i := 0) hC1 hDsigma_nonneg n
      simpa [Q, r2EffQData] using h
  have hE1 : ∀ n : ℕ, (1 : ℝ) ≤ effEnv 14 D.sigma n + 1 := fun n => by
    have := effEnv_nonneg 14 D.sigma hDsigma_nonneg n; linarith
  -- Mass constant absorbing the S7 slack.
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ n : ℕ,
      K_s7 * effEnv 11 Q.sigma n
        + K_s7 * (2 / Q.qMin) ^ 8 * (effEnv 10 Q.sigma n + 1)
        + K_s7 * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 Q.sigma n + 1)
      ≤ M * (effEnv 14 D.sigma n + 1) := by
    have hks7 : (0 : ℝ) ≤ K_s7 := by linarith
    refine ⟨K_s7 * G + K_s7 * (2 / Q.qMin) ^ 8 * (G + 1)
        + K_s7 * (2 / (1 / 2 - Q.qMax)) ^ 8 * (G + 1) + 1, ?_, fun n => ?_⟩
    · have t1 : (0 : ℝ) ≤ K_s7 * G := mul_nonneg hks7 (by linarith)
      have t2 : (0 : ℝ) ≤ K_s7 * (2 / Q.qMin) ^ 8 * (G + 1) :=
        mul_nonneg (mul_nonneg hks7 (by positivity)) (by linarith)
      have t3 : (0 : ℝ) ≤ K_s7 * (2 / (1 / 2 - Q.qMax)) ^ 8 * (G + 1) :=
        mul_nonneg (mul_nonneg hks7 (by positivity)) (by linarith)
      linarith
    · have hEn : (1 : ℝ) ≤ effEnv 14 D.sigma n + 1 := hE1 n
      have h9 : effEnv 10 Q.sigma n ≤ G * (effEnv 14 D.sigma n + 1) :=
        le_trans (effEnv_le_grade Q.sigma (by norm_num) n) (hG n)
      have h10 : effEnv 11 Q.sigma n ≤ G * (effEnv 14 D.sigma n + 1) :=
        le_trans (effEnv_le_grade Q.sigma (by norm_num) n) (hG n)
      have h9' : effEnv 10 Q.sigma n + 1 ≤ (G + 1) * (effEnv 14 D.sigma n + 1) := by
        nlinarith [h9, hEn]
      have hc1 : (0 : ℝ) ≤ K_s7 * (2 / Q.qMin) ^ 8 := by positivity
      have hc2 : (0 : ℝ) ≤ K_s7 * (2 / (1 / 2 - Q.qMax)) ^ 8 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h10 hks7,
        mul_le_mul_of_nonneg_left h9' hc1,
        mul_le_mul_of_nonneg_left h9' hc2]
  obtain ⟨n0, hn0⟩ := r2_eff_threshold Q Q.sigma hQsigma_nonneg hqmin hqmax K_s7
  refine ⟨max 1 (max ((n0 : ℝ) * Real.log 2) (max M (B + 4 * (G + 1)))),
    le_max_left _ _, ?_⟩
  intro n r S alpha beta hclass
  set K : ℝ := max 1 (max ((n0 : ℝ) * Real.log 2) (max M (B + 4 * (G + 1)))) with hKdef
  have hsig : (effDegrade D K 14).sigma n = K * (effEnv 14 D.sigma n + 1) := rfl
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one (by rw [hKdef]; exact le_max_left _ _)
  by_cases hSempty : S.Nonempty
  · by_cases hn : n < n0
    · -- Small `n`: the trivial ball centred at any point of `S`.
      obtain ⟨a, ha⟩ := hSempty
      refine ⟨a, ?_⟩
      have hcard2 : (S.card : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
        have h1 : S.card ≤ 2 ^ n := by
          calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
            _ = 2 ^ n := by
                rw [Finset.card_univ]
                exact (Fintype.card_finset).trans (by rw [Fintype.card_fin])
        have h2 : ((2 : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        calc (S.card : ℝ) ≤ ((2 : ℝ)) ^ n := by exact_mod_cast h1
          _ = _ := h2
      have hmass_ge : (n : ℝ) * Real.log 2 ≤ (effDegrade D K 14).sigma n := by
        rw [hsig]
        have hK_ge : (n0 : ℝ) * Real.log 2 ≤ K := by
          rw [hKdef]; exact le_max_of_le_right (le_max_left _ _)
        have hn_le : (n : ℝ) * Real.log 2 ≤ (n0 : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) (Real.log_nonneg one_le_two)
        have hKge : (n : ℝ) * Real.log 2 ≤ K := le_trans hn_le hK_ge
        nlinarith [hKge, hE1 n, hK0]
      have hle1 : Real.exp (-(effDegrade D K 14).sigma n) * (S.card : ℝ) ≤ 1 := by
        have hstep := mul_le_mul_of_nonneg_left hcard2
          (Real.exp_nonneg (-(effDegrade D K 14).sigma n))
        refine le_trans hstep ?_
        rw [← Real.exp_add]
        have hle0 : -(effDegrade D K 14).sigma n + (n : ℝ) * Real.log 2 ≤ 0 := by
          linarith [hmass_ge]
        calc Real.exp (-(effDegrade D K 14).sigma n + (n : ℝ) * Real.log 2)
              ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
          _ = 1 := Real.exp_zero
      have hmem : a ∈ S.filter fun x =>
          hDist x a ≤ rmin n S.card + Nat.ceil ((effDegrade D K 14).sigma n) := by
        rw [Finset.mem_filter]
        exact ⟨ha, by simp [hDist]⟩
      have h1le : (1 : ℝ) ≤
          ((S.filter fun x =>
            hDist x a ≤ rmin n S.card + Nat.ceil ((effDegrade D K 14).sigma n)).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨a, hmem⟩
      exact le_trans hle1 h1le
    · -- Large `n`: use S7 with the explicit precision schedule.
      push_neg at hn
      obtain ⟨hfat, hpinned⟩ := hC_pinned n r S alpha beta hclass hSempty
      have hadm := r2_eff_eps_clamped_admissible Q Q.sigma n hqmin hqmax
      have heps_pos := r2_eff_eps_clamped_pos Q Q.sigma n (hQsigma_nonneg n) hqmin hqmax
      obtain ⟨a, ha⟩ := hS7_bound (r2EffEpsClamped Q Q.sigma n) heps_pos hadm.1 hadm.2 n
        (hn0 n hn) S alpha hSempty hfat hpinned
      have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSempty
      have hScard2 : S.card ≤ 2 ^ n := by
        calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
          _ = 2 ^ n := by
              rw [Finset.card_univ]
              exact (Fintype.card_finset).trans (by rw [Fintype.card_fin])
      have hK_bound :
          (K_s7 / (r2EffEpsClamped Q Q.sigma n) ^ 8) * (effEnv 10 Q.sigma n + 1)
            ≤ K * (effEnv 14 D.sigma n + 1) := by
        refine le_trans (r2_eff_mass_slack_bound Q Q.sigma n K_s7 (by linarith)) ?_
        refine le_trans (hM n) ?_
        have hMK : M ≤ K := by
          rw [hKdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
        exact mul_le_mul_of_nonneg_right hMK (by linarith [hE1 n])
      have hE0 : (0 : ℝ) ≤ effEnv 14 D.sigma n + 1 := by linarith [hE1 n]
      have h_radius_absorb :
          alpha * (n : ℝ) + 4 * (r2EffEpsClamped Q Q.sigma n) * (n : ℝ)
            ≤ (rmin n S.card : ℝ) + K * (effEnv 14 D.sigma n + 1) := by
        have hr := hB_bound n S alpha hScard1 hScard2 hclass.2.2.1 hclass.2.2.2.1
          hclass.2.2.2.2.2.1
        have hexc := r2_eff_radius_excess_bound Q Q.sigma n
        have hGn := hG n
        have hBK : B + 4 * (G + 1) ≤ K := by
          rw [hKdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
        have t1 := mul_le_mul_of_nonneg_right hBK hE0
        nlinarith [hr, hexc, hGn, hE1 n, t1]
      exact r2_eff_s7_output_to_hbl D C n S alpha K_s7 (r2EffEpsClamped Q Q.sigma n) a ha
        K hK_bound h_radius_absorb
  · -- `S` empty: the empty ball trivially works.
    rw [Finset.not_nonempty_iff_eq_empty] at hSempty
    refine ⟨(∅ : Cube n), ?_⟩
    simp [hSempty]

theorem r2_eff (hS7 : S7Eff) (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff) :
    R2Eff := by
  intro D hvalid
  exact r2_eff_hbl_from_q_and_dp hS7 hBV hVPlus hIVC D hvalid

end HarperStability