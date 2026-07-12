import HarperStability.Reductions.EffectiveR2
import HarperStability.Interface.EffectiveUniform

/-!
# Uniform R2 (v0.4) — the one genuinely new proof of this phase

Target: `R2EffU` — the grade-14 heavy-ball lemma with `K` class-only.

The reusable schedule arithmetic below is proved directly.  The remaining
theorem body is the intended grade-10 ratio dichotomy:

* if `(effEnv 10 sigma n + 1)/((n:ℝ)+1) ≤ eps₀^16`, run the closed R2
  proof with the unclamped schedule and the class-only `K₇` supplied by
  `S7EffU`;
* otherwise four `effGeo` steps lift the deficit to
  `effEnv 14 sigma n ≥ eps₀ * ((n:ℝ)+1)`, so the trivial singleton ball
  witnesses `HBLFor` once `K ≥ log 2 / eps₀`.

Do NOT convert the clamp into a σ/n-threshold, and do not modify the frozen
interfaces.
-/

namespace HarperStability

noncomputable def r2_effU_Ceff (K_IVC : ℝ) : ℝ := max 1 (K_IVC * (Real.log 3 + 1))
noncomputable def r2_effU_Cpre (N0 Hlb : ℝ) : ℝ := max 1 (N0 * (Real.log 2 - Hlb))
noncomputable def r2_effU_Cw (L kappa CG Ceff Ceff_BV Cpre : ℝ) : ℝ := 1 + Cpre + (L / kappa + 1) * (CG + 1 + L + Ceff + Ceff_BV) + (L + 2)
noncomputable def r2_effU_Cdp (Cw Cpre : ℝ) : ℝ := max Cw Cpre
noncomputable def r2_effU_Cpin (Cdp cSize Cpre : ℝ) : ℝ := max (max 1 Cdp) (max cSize Cpre)
noncomputable def r2_effU_C (Cpin cSize : ℝ) : ℝ := max Cpin cSize
noncomputable def r2_effU_CG (C_V cSize Ceff : ℝ) : ℝ := max 1 (C_V * cSize + Ceff)


/-- The explicit precision schedule for R2. -/
noncomputable def r2EffUEps (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)))))

/-- The clamped precision schedule that fits into the admissible window for S7. -/
noncomputable def r2EffUEpsClamped (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffUEps sigma n)

lemma r2_effU_eps_pos (sigma : ℕ → ℝ) (n : ℕ) (hsigma : 0 ≤ sigma n) :
    0 < r2EffUEps sigma n := by
  have henv : 0 ≤ effEnv 10 sigma n := le_trans hsigma (le_effEnv 10 sigma n)
  have hbase : 0 < (effEnv 10 sigma n + 1) / ((n : ℝ) + 1) := by
    exact div_pos (by linarith) (by positivity)
  unfold r2EffUEps
  repeat' apply Real.sqrt_pos.mpr
  exact hbase

lemma r2_effU_eps_clamped_pos (Q : QData) (sigma : ℕ → ℝ) (n : ℕ)
    (hsigma : 0 ≤ sigma n) (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) :
    0 < r2EffUEpsClamped Q sigma n := by
  unfold r2EffUEpsClamped
  rw [lt_min_iff]
  constructor
  · rw [lt_min_iff]
    exact ⟨by linarith, by linarith⟩
  · exact r2_effU_eps_pos sigma n hsigma

lemma r2_effU_eps_clamped_admissible (Q : QData) (sigma : ℕ → ℝ) (n : ℕ)
    (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) :
    r2EffUEpsClamped Q sigma n < Q.qMin ∧ r2EffUEpsClamped Q sigma n < 1 / 2 - Q.qMax := by
  unfold r2EffUEpsClamped
  constructor
  ·
    have hle :
        min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffUEps sigma n) ≤
          Q.qMin / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    exact lt_of_le_of_lt hle (by linarith)
  ·
    have hle :
        min (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) (r2EffUEps sigma n) ≤
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

private lemma r2_effU_eps_mul_succ_le_effEnv13 (sigma : ℕ → ℝ) (n : ℕ) :
    r2EffUEps sigma n * ((n : ℝ) + 1) ≤ effEnv 14 sigma n := by
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
  simpa [r2EffUEps, e0, b] using h4

private lemma r2_effU_eps_pow_eight (sigma : ℕ → ℝ) (n : ℕ) :
    (r2EffUEps sigma n) ^ 8 =
      Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)) := by
  let e0 : ℝ := (effEnv 10 sigma n + 1) / ((n : ℝ) + 1)
  have he1 : 0 ≤ Real.sqrt e0 := Real.sqrt_nonneg _
  have he2 : 0 ≤ Real.sqrt (Real.sqrt e0) := Real.sqrt_nonneg _
  have he3 : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt e0)) := Real.sqrt_nonneg _
  calc
    (r2EffUEps sigma n) ^ 8
        = (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt e0)))) ^ 8 := by
            simp [r2EffUEps, e0]
    _ = ((Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt e0)))) ^ 2) ^ 4 := by ring
    _ = (Real.sqrt (Real.sqrt (Real.sqrt e0))) ^ 4 := by rw [Real.sq_sqrt he3]
    _ = ((Real.sqrt (Real.sqrt (Real.sqrt e0))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (Real.sqrt e0)) ^ 2 := by rw [Real.sq_sqrt he2]
    _ = Real.sqrt e0 := by rw [Real.sq_sqrt he1]

private lemma r2_effU_eps_mass_schedule_bound (sigma : ℕ → ℝ) (n : ℕ) :
    (effEnv 10 sigma n + 1) / (r2EffUEps sigma n) ^ 8 ≤ effEnv 11 sigma n := by
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
  have hpow := r2_effU_eps_pow_eight sigma n
  have hratio :
      (effEnv 10 sigma n + 1) / (r2EffUEps sigma n) ^ 8 =
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

/-- In the bad ratio branch, four grading steps turn the grade-10 deficit
into a linear grade-14 envelope. -/
lemma r2_effU_bad_ratio_env14 {sigma : ℕ → ℝ} {n : ℕ} {eps0 : ℝ}
    (heps0 : 0 ≤ eps0)
    (hbad : eps0 ^ 16 * ((n : ℝ) + 1) ≤ effEnv 10 sigma n + 1) :
    eps0 * ((n : ℝ) + 1) ≤ effEnv 14 sigma n := by
  have hsqrt16 : Real.sqrt (eps0 ^ 16) = eps0 ^ 8 := by
    rw [show eps0 ^ 16 = (eps0 ^ 8) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt8 : Real.sqrt (eps0 ^ 8) = eps0 ^ 4 := by
    rw [show eps0 ^ 8 = (eps0 ^ 4) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt4 : Real.sqrt (eps0 ^ 4) = eps0 ^ 2 := by
    rw [show eps0 ^ 4 = (eps0 ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt2 : Real.sqrt (eps0 ^ 2) = eps0 := Real.sqrt_sq heps0
  have h1 :
      eps0 ^ 8 * ((n : ℝ) + 1) ≤ effEnv 11 sigma n := by
    have h := r2_sqrt_mul_succ_le_effGeo (effEnv 10 sigma) n
      (by positivity : 0 ≤ eps0 ^ 16) hbad
    simpa [hsqrt16] using h
  have h2 :
      eps0 ^ 4 * ((n : ℝ) + 1) ≤ effEnv 12 sigma n := by
    have h1' : eps0 ^ 8 * ((n : ℝ) + 1) ≤ effEnv 11 sigma n + 1 := by
      linarith
    have h := r2_sqrt_mul_succ_le_effGeo (effEnv 11 sigma) n
      (by positivity : 0 ≤ eps0 ^ 8) h1'
    simpa [hsqrt8] using h
  have h3 :
      eps0 ^ 2 * ((n : ℝ) + 1) ≤ effEnv 13 sigma n := by
    have h2' : eps0 ^ 4 * ((n : ℝ) + 1) ≤ effEnv 12 sigma n + 1 := by
      linarith
    have h := r2_sqrt_mul_succ_le_effGeo (effEnv 12 sigma) n
      (by positivity : 0 ≤ eps0 ^ 4) h2'
    simpa [hsqrt4] using h
  have h4 :
      eps0 * ((n : ℝ) + 1) ≤ effEnv 14 sigma n := by
    have h3' : eps0 ^ 2 * ((n : ℝ) + 1) ≤ effEnv 13 sigma n + 1 := by
      linarith
    have h := r2_sqrt_mul_succ_le_effGeo (effEnv 13 sigma) n
      (by positivity : 0 ≤ eps0 ^ 2) h3'
    simpa [hsqrt2] using h
  exact h4

/-- In the good ratio branch, the unclamped schedule is admissible. -/
lemma r2_effU_eps_le_of_ratio {sigma : ℕ → ℝ} {n : ℕ} {eps0 : ℝ}
    (heps0 : 0 ≤ eps0)
    (hgood : (effEnv 10 sigma n + 1) / ((n : ℝ) + 1) ≤ eps0 ^ 16) :
    r2EffUEps sigma n ≤ eps0 := by
  have hsqrt16 : Real.sqrt (eps0 ^ 16) = eps0 ^ 8 := by
    rw [show eps0 ^ 16 = (eps0 ^ 8) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt8 : Real.sqrt (eps0 ^ 8) = eps0 ^ 4 := by
    rw [show eps0 ^ 8 = (eps0 ^ 4) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt4 : Real.sqrt (eps0 ^ 4) = eps0 ^ 2 := by
    rw [show eps0 ^ 4 = (eps0 ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt2 : Real.sqrt (eps0 ^ 2) = eps0 := Real.sqrt_sq heps0
  have h1 :
      Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)) ≤ eps0 ^ 8 := by
    have h := Real.sqrt_le_sqrt hgood
    simpa [hsqrt16] using h
  have h2 :
      Real.sqrt (Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1))) ≤
        eps0 ^ 4 := by
    have h := Real.sqrt_le_sqrt h1
    simpa [hsqrt8] using h
  have h3 :
      Real.sqrt (Real.sqrt (Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1)))) ≤
        eps0 ^ 2 := by
    have h := Real.sqrt_le_sqrt h2
    simpa [hsqrt4] using h
  have h4 :
      Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((effEnv 10 sigma n + 1) / ((n : ℝ) + 1))))) ≤
        eps0 := by
    have h := Real.sqrt_le_sqrt h3
    simpa [hsqrt2] using h
  simpa [r2EffUEps] using h4

/-- The unclamped schedule satisfies the S7 dimension threshold after the
class-only prefix `ceil (K^2 + 1)`. -/
lemma r2_effU_threshold_unclamped (sigma : ℕ → ℝ) (hsigma : ∀ n, 0 ≤ sigma n)
    {K : ℝ} (_hK : 1 ≤ K) {n : ℕ} (hn : ⌈K ^ 2 + 1⌉₊ ≤ n) :
    K / (r2EffUEps sigma n) ^ 8 ≤ (n : ℝ) := by
  have heps_pos : 0 < r2EffUEps sigma n := r2_effU_eps_pos sigma n (hsigma n)
  rw [div_le_iff₀ (pow_pos heps_pos 8)]
  have hbase :
      K ≤ (n : ℝ) * Real.sqrt (1 / ((n : ℝ) + 1)) := by
    norm_num [← div_eq_mul_inv]
    rw [le_div_iff₀ (by positivity : 0 < Real.sqrt ((n : ℝ) + 1))]
    nlinarith [Nat.ceil_le.mp hn,
      Real.sqrt_nonneg (((n : ℝ) + 1)),
      Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  have hpow := r2_effU_eps_pow_eight sigma n
  have hsched_lower :
      Real.sqrt (1 / ((n : ℝ) + 1)) ≤ (r2EffUEps sigma n) ^ 8 := by
    rw [hpow]
    apply Real.sqrt_le_sqrt
    have hE : 1 ≤ effEnv 10 sigma n + 1 := by
      have henv : 0 ≤ effEnv 10 sigma n := le_trans (hsigma n) (le_effEnv 10 sigma n)
      linarith
    exact div_le_div_of_nonneg_right hE (by positivity : 0 ≤ (n : ℝ) + 1)
  have hmul :
      (n : ℝ) * Real.sqrt (1 / ((n : ℝ) + 1)) ≤
        (n : ℝ) * (r2EffUEps sigma n) ^ 8 :=
    mul_le_mul_of_nonneg_left hsched_lower (Nat.cast_nonneg n)
  exact le_trans hbase hmul

/-- The radius excess for the unclamped `D.sigma` schedule is grade 14. -/
lemma r2_effU_radius_excess_unclamped (sigma : ℕ → ℝ) (n : ℕ) :
    4 * r2EffUEps sigma n * (n : ℝ) ≤ 4 * effEnv 14 sigma n := by
  have heps_nonneg : 0 ≤ r2EffUEps sigma n := by
    unfold r2EffUEps
    positivity
  have hn_le : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hle :
      r2EffUEps sigma n * (n : ℝ) ≤ effEnv 14 sigma n := by
    exact le_trans
      (mul_le_mul_of_nonneg_left hn_le heps_nonneg)
      (r2_effU_eps_mul_succ_le_effEnv13 sigma n)
  nlinarith

/-- The radius excess `4*eps(n)*n` is bounded by grade 14. -/
lemma r2_effU_radius_excess_bound (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) :
    4 * r2EffUEpsClamped Q sigma n * (n : ℝ) ≤ 4 * effEnv 14 sigma n + 4 := by
  have hclamp : r2EffUEpsClamped Q sigma n ≤ r2EffUEps sigma n := by
    unfold r2EffUEpsClamped
    exact min_le_right _ _
  have heps_nonneg : 0 ≤ r2EffUEps sigma n := by
    unfold r2EffUEps
    positivity
  have hn_le : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have heps_n :
      r2EffUEps sigma n * (n : ℝ) ≤ r2EffUEps sigma n * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hn_le heps_nonneg
  have heps_bound : r2EffUEps sigma n * (n : ℝ) ≤ effEnv 14 sigma n :=
    le_trans heps_n (r2_effU_eps_mul_succ_le_effEnv13 sigma n)
  have hclamp_bound :
      r2EffUEpsClamped Q sigma n * (n : ℝ) ≤ effEnv 14 sigma n := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact le_trans (mul_le_mul_of_nonneg_right hclamp hn_nonneg) heps_bound
  nlinarith

/-- The mass slack `(K/eps(n)^8)*(effEnv 10 σ n + 1)` is bounded by grade 11 (which is ≤ 13). -/
lemma r2_effU_mass_slack_bound (Q : QData) (sigma : ℕ → ℝ) (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    (K / (r2EffUEpsClamped Q sigma n) ^ 8) * (effEnv 10 sigma n + 1) ≤
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
  unfold r2EffUEpsClamped
  by_cases hinner :
      min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2) ≤ r2EffUEps sigma n
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
        r2EffUEps sigma n ≤ min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2) :=
      le_of_not_ge hinner
    rw [min_eq_right heps]
    have hsched := r2_effU_eps_mass_schedule_bound sigma n
    have hschedK :
        K * ((effEnv 10 sigma n + 1) / (r2EffUEps sigma n) ^ 8) ≤
          K * effEnv 11 sigma n :=
      mul_le_mul_of_nonneg_left hsched hK
    calc
      (K / (r2EffUEps sigma n) ^ 8) * (effEnv 10 sigma n + 1)
          = K * ((effEnv 10 sigma n + 1) / (r2EffUEps sigma n) ^ 8) := by ring
      _ ≤ K * effEnv 11 sigma n := hschedK
      _ ≤ K * effEnv 11 sigma n +
            K * (2 / Q.qMin) ^ 8 * (effEnv 10 sigma n + 1) +
            K * (2 / (1 / 2 - Q.qMax)) ^ 8 * (effEnv 10 sigma n + 1) := by
          nlinarith

noncomputable def r2EffUQData (D : StabilityData) (C : ℝ) : QData := {
  qMin := D.alphaMin
  qMax := D.alphaMax
  s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
  mu0 := (1 / 2 - D.alphaMax) / 2
  sigma := fun n => C * (D.sigma n + 1)
}

private lemma r2_effU_sublinear_scale_add_one {s : ℕ → ℝ} (hs : Sublinear s)
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

lemma r2_effU_valid_qdata (D : StabilityData) (hvalid : validData D) (C : ℝ) (hC : 1 ≤ C) :
    validQData (r2EffUQData D C) := by
  rcases hvalid with
    ⟨hrho, _hdelta_pos, _hdelta_lt, hcsize, hamin, haminmax, hamaxhalf,
      hsubD, hlogD⟩
  have hC0 : 0 ≤ C := by linarith
  dsimp [r2EffUQData, validQData]
  refine ⟨hamin, haminmax, hamaxhalf, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · linarith
  · have hs0_le : min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) ≤
        (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
    nlinarith
  · exact r2_effU_sublinear_scale_add_one hsubD hC0
  · intro m hm
    calc
      Real.log (m : ℝ) ≤ D.sigma m := hlogD m hm
      _ ≤ D.sigma m + 1 := by linarith
      _ ≤ C * (D.sigma m + 1) :=
          le_mul_of_one_le_left (by linarith [hsubD.1 m]) hC

/-- The scaled `QData` envelope is controlled by the original grade-10
envelope with a class-only constant. -/
lemma r2_effU_qdata_env10_bound (D : StabilityData) (hvalid : validData D)
    {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    effEnv 10 (r2EffUQData D C).sigma n + 1 ≤
      (2 ^ 10 * C + 1) * (effEnv 10 D.sigma n + 1) := by
  have hDsigma_nonneg : ∀ m, 0 ≤ D.sigma m :=
    fun m => hvalid.2.2.2.2.2.2.2.1.1 m
  have hcomp := effEnv_comp 10 (i := 0) hC hDsigma_nonneg n
  have hmain :
      effEnv 10 (r2EffUQData D C).sigma n ≤
        (2 ^ 10 * C) * (effEnv 10 D.sigma n + 1) := by
    simpa [r2EffUQData] using hcomp
  have hE1 : 1 ≤ effEnv 10 D.sigma n + 1 := by
    have hE := effEnv_nonneg 10 D.sigma hDsigma_nonneg n
    linarith
  nlinarith [hmain, hE1]

/-- S7's mass term for the scaled `QData` is absorbed by the original
grade-14 output envelope when the precision schedule is built from `D.sigma`. -/
lemma r2_effU_scaled_mass_bound (D : StabilityData) (hvalid : validData D)
    {C K_s7 : ℝ} (hC : 1 ≤ C) (hK_s7 : 1 ≤ K_s7) (n : ℕ) :
    (K_s7 / (r2EffUEps D.sigma n) ^ 8) *
        (effEnv 10 (r2EffUQData D C).sigma n + 1) ≤
      (K_s7 * (2 ^ 10 * C + 1)) * (effEnv 14 D.sigma n + 1) := by
  have hDsigma_nonneg : ∀ m, 0 ≤ D.sigma m :=
    fun m => hvalid.2.2.2.2.2.2.2.1.1 m
  have heps_pos : 0 < r2EffUEps D.sigma n :=
    r2_effU_eps_pos D.sigma n (hDsigma_nonneg n)
  have hq := r2_effU_qdata_env10_bound D hvalid hC n
  have hdiv :
      (effEnv 10 (r2EffUQData D C).sigma n + 1) / (r2EffUEps D.sigma n) ^ 8 ≤
        ((2 ^ 10 * C + 1) * (effEnv 10 D.sigma n + 1)) /
          (r2EffUEps D.sigma n) ^ 8 :=
    div_le_div_of_nonneg_right hq (by positivity)
  have hsched := r2_effU_eps_mass_schedule_bound D.sigma n
  have hscale :
      ((2 ^ 10 * C + 1) * (effEnv 10 D.sigma n + 1)) /
          (r2EffUEps D.sigma n) ^ 8 ≤
        (2 ^ 10 * C + 1) * effEnv 11 D.sigma n := by
    have hcoef : 0 ≤ 2 ^ 10 * C + 1 := by positivity
    calc
      ((2 ^ 10 * C + 1) * (effEnv 10 D.sigma n + 1)) /
          (r2EffUEps D.sigma n) ^ 8
          = (2 ^ 10 * C + 1) *
              ((effEnv 10 D.sigma n + 1) / (r2EffUEps D.sigma n) ^ 8) := by
              ring
      _ ≤ (2 ^ 10 * C + 1) * effEnv 11 D.sigma n :=
              mul_le_mul_of_nonneg_left hsched hcoef
  have hgrade :
      effEnv 11 D.sigma n ≤ effEnv 14 D.sigma n + 1 := by
    have h := effEnv_le_grade D.sigma (by norm_num : 11 ≤ 14) n
    linarith
  have hcoef_nonneg : 0 ≤ K_s7 * (2 ^ 10 * C + 1) := by positivity
  calc
    (K_s7 / (r2EffUEps D.sigma n) ^ 8) *
        (effEnv 10 (r2EffUQData D C).sigma n + 1)
        = K_s7 *
            ((effEnv 10 (r2EffUQData D C).sigma n + 1) /
              (r2EffUEps D.sigma n) ^ 8) := by
            ring
    _ ≤ K_s7 * ((2 ^ 10 * C + 1) * effEnv 11 D.sigma n) := by
          exact mul_le_mul_of_nonneg_left (le_trans hdiv hscale) (by linarith)
    _ = (K_s7 * (2 ^ 10 * C + 1)) * effEnv 11 D.sigma n := by ring
    _ ≤ (K_s7 * (2 ^ 10 * C + 1)) * (effEnv 14 D.sigma n + 1) :=
          mul_le_mul_of_nonneg_left hgrade hcoef_nonneg

lemma r2_effU_sublinear_effLog {K : ℝ} (hK : 0 ≤ K) : Sublinear (effLog K) := by
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

lemma r2_effU_effLog_le_sigma (D : StabilityData) (hvalid : validData D) (K : ℝ) (hK : 1 ≤ K) :
    ∀ n : ℕ, effLog K n ≤ r2_effU_Ceff K * (D.sigma n + 1) := by
  have hK0 : 0 ≤ K := by linarith
  intro n
  have hC : K * (Real.log 3 + 1) ≤ max 1 (K * (Real.log 3 + 1)) := le_max_right _ _
  have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hsig1 : 1 ≤ D.sigma n + 1 := by linarith
  have h_base : K * (Real.log ((n : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := by
    by_cases hn : n = 0
    · have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      have h2 : K * (Real.log ((0 : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1) := by
        have h02 : (0 : ℝ) + 2 = 2 := by ring
        rw [h02]
        exact mul_le_mul_of_nonneg_left (by linarith) hK0
      have h3 : K * (Real.log 3 + 1) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := by
        have h_pos : 0 ≤ K * (Real.log 3 + 1) := mul_nonneg hK0 (by positivity)
        nlinarith
      have h4 : K * (Real.log ((0 : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := le_trans h2 h3
      have h_cast : (n : ℝ) = (0 : ℝ) := by simp [hn]
      rw [h_cast]
      exact h4
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log (3 * (n : ℝ)) := by
        apply Real.log_le_log (by linarith)
        linarith
      have h2 : Real.log (3 * (n : ℝ)) = Real.log 3 + Real.log (n : ℝ) := by
        apply Real.log_mul (by norm_num) (by linarith)
      have h3 : Real.log (n : ℝ) ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.2 n hn1
      have h4 : Real.log ((n : ℝ) + 2) + 1 ≤ Real.log 3 + 1 + D.sigma n := by linarith
      have h5 : K * (Real.log ((n : ℝ) + 2) + 1) ≤ K * (Real.log 3 + 1 + D.sigma n) := mul_le_mul_of_nonneg_left h4 hK0
      have h6 : K * (Real.log 3 + 1 + D.sigma n) ≤ K * (Real.log 3 + 1) * (D.sigma n + 1) := by
        have h_log3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        have h_pos : 0 ≤ K * D.sigma n := mul_nonneg hK0 hsig_nn
        have : 1 * (K * D.sigma n) ≤ (Real.log 3 + 1) * (K * D.sigma n) :=
          mul_le_mul_of_nonneg_right (by linarith) h_pos
        nlinarith
      exact le_trans h5 h6
  have h_step2 : K * (Real.log 3 + 1) * (D.sigma n + 1) ≤ max 1 (K * (Real.log 3 + 1)) * (D.sigma n + 1) :=
    mul_le_mul_of_nonneg_right hC (by linarith)
  simpa [effLog] using le_trans h_base h_step2

lemma r2_effU_prefix_le_sigma (D : StabilityData) (hvalid : validData D) (N : ℕ) (a : ℝ) :
    ∀ n : ℕ, (if n < N then a else 0) ≤ max 1 a * (D.sigma n + 1) := by
  intro n
  have hsig1 : 1 ≤ D.sigma n + 1 := by
    have := hvalid.2.2.2.2.2.2.2.1.1 n
    linarith
  by_cases hn : n < N
  · have ha : a ≤ max 1 a := le_max_right _ _
    simp [hn]
    exact le_trans ha (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) hsig1)
  · simp [hn]
    exact le_trans zero_le_one hsig1

lemma r2_effU_linear_combo_le_sigma (D : StabilityData) (hvalid : validData D)
    (s1 s2 : ℕ → ℝ) (C1 C2 : ℝ) (h1 : ∀ n, s1 n ≤ C1 * (D.sigma n + 1)) (h2 : ∀ n, s2 n ≤ C2 * (D.sigma n + 1))
    (a1 a2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) :
    ∀ n : ℕ, a1 * s1 n + a2 * s2 n ≤ max 1 (a1 * C1 + a2 * C2) * (D.sigma n + 1) := by
  intro n
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

lemma r2_effU_BVStatement_of_Eff (hBV : BallVolumeTwoSidedEff) :
    BallVolumeTwoSidedStatement := by
  unfold BallVolumeTwoSidedStatement
  obtain ⟨K, hK, hcalc⟩ := hBV
  exact ⟨effLog K, r2_effU_sublinear_effLog (le_trans zero_le_one hK), hcalc⟩

lemma r2_effU_IVCStatement_of_Eff (hIVC : InteriorVolumeCalculusEff) :
    InteriorVolumeCalculusStatement := by
  unfold InteriorVolumeCalculusStatement
  intro alpha c0 hAlpha hc0
  obtain ⟨C, hC, K, hK, hcalc⟩ := hIVC alpha c0 hAlpha hc0
  exact ⟨C, hC, effLog K, r2_effU_sublinear_effLog (le_trans zero_le_one hK), hcalc⟩

lemma r2_effU_fat_of_classMember (D : StabilityData) (hvalid : validData D)
    (C : ℝ) (hC : 1 ≤ C) (hCsize : D.cSize ≤ C)
    (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hclass : classMember D n r S alpha beta) (hS : S.Nonempty) :
    fat (r2EffUQData D C) n S alpha := by
  refine ⟨hS, r2_effU_valid_qdata D hvalid C hC, hclass.2.2.1, hclass.2.2.2.1, ?_⟩
  have hsig_nonneg : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hC0 : 0 ≤ C := by linarith
  have hsize : |Real.log (S.card : ℝ) - H alpha * (n : ℝ)| ≤ D.cSize * D.sigma n :=
    hclass.2.2.2.2.2.1
  refine le_trans hsize ?_
  dsimp [r2EffUQData]
  have hmain : D.cSize * D.sigma n ≤ C * D.sigma n :=
    mul_le_mul_of_nonneg_right hCsize hsig_nonneg
  nlinarith

lemma r2_effU_pinned_mono_C (D : StabilityData) (hvalid : validData D)
    {C0 C : ℝ} (hC0C : C0 ≤ C)
    {n : ℕ} {S : Finset (Cube n)} {alpha : ℝ} :
    pinned (r2EffUQData D C0) n S alpha →
      pinned (r2EffUQData D C) n S alpha := by
  intro hp s hs
  have hs0 : s ≤ Nat.ceil ((r2EffUQData D C0).s0 * (n : ℝ)) := by
    simpa [r2EffUQData] using hs
  have hbase := hp s hs0
  refine le_trans hbase (Real.exp_le_exp.mpr ?_)
  have hsig_nonneg : 0 ≤ D.sigma n + 1 := by
    have := hvalid.2.2.2.2.2.2.2.1.1 n
    linarith
  dsimp [r2EffUQData]
  have hmul := mul_le_mul_of_nonneg_right hC0C hsig_nonneg
  nlinarith

/-
Effective interior-volume upper bound: an explicit-slack clone of
`V_upper_of_classMember`, where the sublinear `volSlack` is replaced by the
explicit envelope `CG * (D.sigma n + 1)`.  The proof specializes
`InteriorVolumeCalculusEff` at `(D.alphaMin, c0)` and dominates the resulting
`C_V * (D.cSize * D.sigma n) + effLog K n` slack using
`r2_effU_effLog_le_sigma`.
-/
lemma r2_effU_V_upper (D : StabilityData) (hvalid : validData D) (c0 : ℝ) (_hc0 : 0 < c0)
    (C_V : ℝ) (hC_V : 1 ≤ C_V) (K : ℝ) (_hK : 1 ≤ K)
    (hcalc : ∀ (n k r : ℕ) (alpha beta sizeSlack : ℝ),
      D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → 0 ≤ sizeSlack → beta = (r : ℝ) / (n : ℝ) →
      alpha + beta ≤ 1 / 2 - c0 → 1 ≤ k → k ≤ 2 ^ n →
      |Real.log k - H alpha * (n : ℝ)| ≤ sizeSlack →
      |Real.log (V n k r) - H (alpha + beta) * (n : ℝ)| ≤ C_V * sizeSlack + effLog K n ∧
      |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K n)
    (Ceff : ℝ) (hCeff1 : 1 ≤ Ceff) (hCeff : ∀ n, effLog K n ≤ Ceff * (D.sigma n + 1)) :
    ∀ (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
      D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → beta = (r : ℝ) / (n : ℝ) →
      alpha + beta ≤ 1 / 2 - c0 → 1 ≤ S.card → S.card ≤ 2 ^ n →
      sizeHyp D n S alpha →
      (V n S.card r : ℝ) ≤
        Real.exp (H (alpha + beta) * (n : ℝ) + r2_effU_CG C_V D.cSize Ceff * (D.sigma n + 1)) := by
  intro n r S alpha beta halpha halpha' hbeta hrange hS1 hS2 hsize
  rw [← Real.log_le_iff_le_exp]
  · have hslack_nonneg : 0 ≤ D.cSize * D.sigma n := by
      exact mul_nonneg (by linarith [hvalid.2.2.2.1])
        (by linarith [hvalid.2.2.2.2.2.2.2.1.1 n])
    have hcalc' := hcalc n S.card r alpha beta (D.cSize * D.sigma n)
      halpha halpha' hslack_nonneg hbeta hrange hS1 hS2 hsize
    have hupper := (abs_le.mp hcalc'.1).2
    have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
    have hCV_nn : 0 ≤ C_V := by linarith
    have hcsize_nn : 0 ≤ D.cSize := by linarith [hvalid.2.2.2.1]
    have hCeff_nn : 0 ≤ Ceff := by linarith
    have hCG_left : C_V * D.cSize + Ceff ≤ r2_effU_CG C_V D.cSize Ceff := by
      dsimp [r2_effU_CG]
      exact le_max_right _ _
    have hslack_bound :
        C_V * (D.cSize * D.sigma n) + effLog K n ≤
          r2_effU_CG C_V D.cSize Ceff * (D.sigma n + 1) := by
      have heff := hCeff n
      have hmain :
          C_V * (D.cSize * D.sigma n) + effLog K n ≤
            (C_V * D.cSize + Ceff) * (D.sigma n + 1) := by
        nlinarith [heff, hsig_nn, hCV_nn, hcsize_nn, hCeff_nn]
      have hsig1_nn : 0 ≤ D.sigma n + 1 := by linarith
      exact le_trans hmain (mul_le_mul_of_nonneg_right hCG_left hsig1_nn)
    linarith
  · exact_mod_cast card_le_V S.card r hS2 |> lt_of_lt_of_le (Nat.cast_pos.mpr hS1)

set_option maxHeartbeats 1000000 in
lemma r2_effU_logsize (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (D : StabilityData) (hvalid : validData D)
    (c0 lo : ℝ) (hc0 : 0 < c0) (hlo : 0 < lo) (hlohalf : lo ≤ 1 / 2 - c0)
    (Gf : ℕ → ℝ) (CG : ℝ)
    (hGfnn : ∀ n, 0 ≤ Gf n) (hGf : ∀ n, Gf n ≤ CG * (D.sigma n + 1)) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
    ∀ (n rho : ℕ) (T : Finset (Cube n)) (target : ℝ),
      T.Nonempty → T.card < 2 ^ n → lo ≤ target →
      target + (rho : ℝ) / (n : ℝ) ≤ 1 / 2 - c0 →
      (V n T.card rho : ℝ) ≤
        Real.exp (H (target + (rho : ℝ) / (n : ℝ)) * (n : ℝ) + Gf n) →
      Real.log (T.card : ℝ) ≤ H target * (n : ℝ) + Cw * (D.sigma n + 1) := by
  exact r2_eff_logsize hBV hVPlus D hvalid c0 lo hc0 hlo hlohalf Gf CG hGfnn hGf

set_option maxHeartbeats 1000000 in
/-- Effective downward-pinning core (sub-equatorial branch): an explicit-slack
clone of `r2_dp_core`, with the sublinear envelope `sigmaDP` replaced by
`Cdp * (D.sigma n + 1)`.  The proof mirrors `r2_dp_core` verbatim, using
`r2_effU_V_upper` in place of `V_upper_of_classMember` and `r2_effU_logsize` in
place of `logsize_le_of_V_upper`; the range control `c0` is obtained from
`r1_range_control` applied to the converted statements
`r2_effU_BVStatement_of_Eff hBV` and `r2_effU_IVCStatement_of_Eff hIVC`, and the
finite `n < N` prefix (cube bound) is absorbed via `r2_effU_prefix_le_sigma`. -/
lemma r2_effU_dp_core (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ Cdp : ℝ, 1 ≤ Cdp ∧ ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta → alpha + tau < 1 / 2 →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (alpha + tau) * (n : ℝ) + Cdp * (D.sigma n + 1)) := by
  exact r2_eff_dp_core hBV hVPlus hIVC D hvalid

/-- Effective downward pinning (the `min (·) (1/2)` form used by `pinned`):
an explicit-slack clone of `r2_downward_pinning`.  Proof: obtain `Cdp` from
`r2_effU_dp_core`; for `alpha + tau < 1/2` use the core directly, and at or
above the equator use the cube bound `cube_card_le_two_pow` with
`H (1/2) = Real.log 2`. -/
lemma r2_effU_downward_pinning_bound
    (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff)
    (D : StabilityData) (hvalid : validData D) :
    ∃ Cdp : ℝ, 1 ≤ Cdp ∧
    ∀ n r S alpha beta,
      classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) +
            Cdp * (D.sigma n + 1)) := by
  exact r2_eff_downward_pinning_bound hBV hVPlus hIVC D hvalid

lemma r2_effU_H_lower_bound :
    ∃ Hlb : ℝ, Hlb ≤ Real.log 2 ∧ ∀ y : ℝ, -1 ≤ y → y ≤ 2 → Hlb ≤ H y := by
  obtain ⟨x, _hx, hmin⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 2)).exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) (Real.binEntropy_continuous.continuousOn);
  exact ⟨ Min.min ( Real.binEntropy x ) ( Real.log 2 ), min_le_right _ _, fun y hy₁ hy₂ => le_trans ( min_le_left _ _ ) ( hmin ⟨ hy₁, hy₂ ⟩ ) ⟩

set_option maxHeartbeats 1000000 in
/-- Effective pinned core: every class member (with nonempty `S`) is `pinned`
for the buffered `r2EffUQData D Cpin` with a single absorbing constant `Cpin`.
Explicit-slack clone of `pinned_buffered_of_classMember_large`, extended to
cover all `n` (the finite `n` where the `1/n ≤ ...` gap conditions fail are
absorbed into `Cpin` via the cube bound and `r2_effU_prefix_le_sigma`). -/
lemma r2_effU_pinned_core (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff) (D : StabilityData) (hvalid : validData D) :
    ∃ Cpin : ℝ, 1 ≤ Cpin ∧
      ∀ n r S alpha beta, classMember D n r S alpha beta → S.Nonempty →
        pinned (r2EffUQData D Cpin) n S alpha := by
  obtain ⟨Cpin, hCpin1, hpinned⟩ := r2_eff_pinned_core hBV hVPlus hIVC D hvalid
  refine ⟨Cpin, hCpin1, ?_⟩
  intro n r S alpha beta hmem hSne
  simpa [r2EffUQData, r2EffQData] using hpinned n r S alpha beta hmem hSne

/-- Every class member yields a fat + pinned set for the buffered `r2EffUQData D C`,
with a single absorbing constant `C`.

The `S.Nonempty` hypothesis (added relative to the original leaf statement) is
necessary: `fat` requires the set to be nonempty, yet `classMember D n r S alpha
beta` can hold with `S = ∅` (e.g. at `n = 0`), so the unconditional statement is
false.  The R2 composer only ever needs fat + pinned for nonempty `S`. -/
lemma r2_effU_classMember_fat_pinned (D : StabilityData) (hvalid : validData D)
    (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n r S alpha beta, classMember D n r S alpha beta → S.Nonempty →
    fat (r2EffUQData D C) n S alpha ∧ pinned (r2EffUQData D C) n S alpha := by
  obtain ⟨C, hC1, hfp⟩ := r2_eff_classMember_fat_pinned D hvalid hBV hVPlus hIVC
  refine ⟨C, hC1, ?_⟩
  intro n r S alpha beta hmem hSne
  simpa [r2EffUQData, r2EffQData] using hfp n r S alpha beta hmem hSne

lemma r2_effU_s7_output_to_hbl (D : StabilityData) (C : ℝ)
    (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ)
    (K_s7 : ℝ)
    (eps : ℝ)
    (a : Cube n)
    (hmass : Real.exp (-((K_s7 / eps ^ 8) * (effEnv 10 (r2EffUQData D C).sigma n + 1))) * (S.card : ℝ) ≤
      ((S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + 4 * eps) * (n : ℝ))).card : ℝ))
    (K_out : ℝ)
    (hK_bound : (K_s7 / eps ^ 8) * (effEnv 10 (r2EffUQData D C).sigma n + 1) ≤ K_out * (effEnv 14 D.sigma n + 1))
    (h_radius_absorb : alpha * (n : ℝ) + 4 * eps * (n : ℝ) ≤ (rmin n S.card : ℝ) + K_out * (effEnv 14 D.sigma n + 1)) :
    heavyBallConclusion n S (K_out * (effEnv 14 D.sigma n + 1)) (Nat.ceil (K_out * (effEnv 14 D.sigma n + 1))) := by
  classical
  refine ⟨a, ?_⟩
  let mass_s7 : ℝ := (K_s7 / eps ^ 8) * (effEnv 10 (r2EffUQData D C).sigma n + 1)
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
The logarithmic slack `effLog K` is dominated by the grade-14 envelope of a
valid tuple.
-/
lemma r2_effU_effLog_bound (D : StabilityData) (hvalid : validData D)
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
lemma r2_effU_threshold (Q : QData) (sigma : ℕ → ℝ) (hsigma : ∀ n, 0 ≤ sigma n)
    (hqmin : 0 < Q.qMin) (hqmax : Q.qMax < 1 / 2) (K : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      K / (r2EffUEpsClamped Q sigma n) ^ 8 ≤ (n : ℝ) := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, K ≤ n * (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2)) ^ 8 := by
    exact ⟨ ⌈K / ( Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ) ^ 8⌉₊, fun n hn => by nlinarith [ Nat.ceil_le.mp hn, show 0 < Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ^ 8 by exact pow_pos ( lt_min ( by linarith ) ( by linarith ) ) _, div_mul_cancel₀ K ( show ( Min.min ( Q.qMin / 2 ) ( ( 1 / 2 - Q.qMax ) / 2 ) ) ^ 8 ≠ 0 by exact pow_ne_zero _ ( ne_of_gt ( lt_min ( by linarith ) ( by linarith ) ) ) ) ] ⟩;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * (r2EffUEps sigma n) ^ 8 := by
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * Real.sqrt ((effEnv 10 sigma n + 1) / (n + 1)) := by
      obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, K ≤ n * Real.sqrt (1 / (n + 1)) := by
        norm_num [ ← div_eq_mul_inv ];
        exact ⟨ Nat.ceil ( K ^ 2 + 1 ), fun n hn => by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ Nat.ceil_le.mp hn, Real.sqrt_nonneg ( n + 1 : ℝ ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( n : ℝ ) + 1 ) ] ⟩;
      use N₂;
      intro n hn; specialize hN₂ n hn; refine le_trans hN₂ ?_; gcongr;
      exact le_add_of_nonneg_left ( effGeo_nonneg _ _ );
    exact ⟨ N₂, fun n hn => le_trans ( hN₂ n hn ) ( by rw [ r2_effU_eps_pow_eight ] ) ⟩;
  use max N₁ N₂; intros n hn; rw [ div_le_iff₀ ] <;> simp_all +decide [ r2EffUEpsClamped ] ;
  · grind;
  · exact pow_pos ( lt_min ( lt_min ( by positivity ) ( by norm_num at *; linarith ) ) ( r2_effU_eps_pos sigma n ( hsigma n ) ) ) _

/-
Interior volume calculus gives `alpha * n ≤ rmin + grade-14 slack` for every
class member (applied at radius `0`).
-/
lemma r2_effU_rmin_lower_bound (hIVC : InteriorVolumeCalculusEff)
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
  obtain ⟨A, hA, hAbd⟩ := r2_effU_effLog_bound D hvalid K (by linarith);
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

/-- In the bad ratio branch, the output envelope is already linear in `n`,
so a singleton ball gives the heavy-ball conclusion. -/
lemma r2_effU_bad_branch_hbl (D : StabilityData) (K eps0 : ℝ) (n : ℕ)
    (S : Finset (Cube n))
    (hS : S.Nonempty)
    (heps0 : 0 < eps0)
    (henv : eps0 * ((n : ℝ) + 1) ≤ effEnv 14 D.sigma n)
    (hK : Real.log 2 / eps0 ≤ K) :
    heavyBallConclusion n S (K * (effEnv 14 D.sigma n + 1))
      (Nat.ceil (K * (effEnv 14 D.sigma n + 1))) := by
  classical
  obtain ⟨a, ha⟩ := hS
  refine ⟨a, ?_⟩
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK_nonneg : 0 ≤ K := by
    have : 0 ≤ Real.log 2 / eps0 := div_nonneg hlog2_nonneg heps0.le
    linarith
  have henv_pos : eps0 * (n : ℝ) ≤ effEnv 14 D.sigma n + 1 := by
    have hnle : eps0 * (n : ℝ) ≤ eps0 * ((n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) heps0.le
    linarith
  have hmass_ge :
      (n : ℝ) * Real.log 2 ≤ K * (effEnv 14 D.sigma n + 1) := by
    have hleft :
        (Real.log 2 / eps0) * (eps0 * (n : ℝ)) = (n : ℝ) * Real.log 2 := by
      field_simp [heps0.ne']
    have hstep1 :
        (Real.log 2 / eps0) * (eps0 * (n : ℝ)) ≤ K * (eps0 * (n : ℝ)) := by
      have hnonneg : 0 ≤ eps0 * (n : ℝ) := mul_nonneg heps0.le (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_right hK hnonneg
    have hstep2 : K * (eps0 * (n : ℝ)) ≤ K * (effEnv 14 D.sigma n + 1) :=
      mul_le_mul_of_nonneg_left henv_pos hK_nonneg
    linarith
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
  have hle1 :
      Real.exp (-(K * (effEnv 14 D.sigma n + 1))) * (S.card : ℝ) ≤ 1 := by
    have hstep := mul_le_mul_of_nonneg_left hcard2
      (Real.exp_nonneg (-(K * (effEnv 14 D.sigma n + 1))))
    refine le_trans hstep ?_
    rw [← Real.exp_add]
    have hle0 : -(K * (effEnv 14 D.sigma n + 1)) + (n : ℝ) * Real.log 2 ≤ 0 := by
      linarith
    calc Real.exp (-(K * (effEnv 14 D.sigma n + 1)) + (n : ℝ) * Real.log 2)
        ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
      _ = 1 := Real.exp_zero
  have hmem : a ∈ S.filter fun x =>
      hDist x a ≤ rmin n S.card + Nat.ceil (K * (effEnv 14 D.sigma n + 1)) := by
    rw [Finset.mem_filter]
    exact ⟨ha, by simp [hDist]⟩
  have h1le : (1 : ℝ) ≤
      ((S.filter fun x =>
        hDist x a ≤ rmin n S.card + Nat.ceil (K * (effEnv 14 D.sigma n + 1))).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a, hmem⟩
  exact le_trans hle1 h1le

lemma r2_effU_sigma_bounds_of_good_ratio (D : StabilityData) (n : ℕ)
    (rate CG eps0 : ℝ)
    (hrate_pos : 0 < rate)
    (hCG1 : 1 ≤ CG)
    (heps0_nonneg : 0 ≤ eps0)
    (hgood : (effEnv 10 D.sigma n + 1) / ((n : ℝ) + 1) ≤ eps0 ^ 16)
    (heps0_le : eps0 ≤ (rate / (8 * CG)) ^ (1 / 16 : ℝ)) :
    CG * (D.sigma n + 1) ≤ rate / 8 * ((n : ℝ) + 1) ∧
      D.sigma n ≤ rate / 8 * ((n : ℝ) + 1) := by
  let b : ℝ := (n : ℝ) + 1
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hb_nonneg : 0 ≤ b := hbpos.le
  have hCGpos : 0 < CG := lt_of_lt_of_le zero_lt_one hCG1
  have hbase_nonneg : 0 ≤ rate / (8 * CG) := by positivity
  have hpow_le : eps0 ^ 16 ≤ rate / (8 * CG) := by
    have hp :
        eps0 ^ (16 : ℝ) ≤
          ((rate / (8 * CG)) ^ (1 / 16 : ℝ)) ^ (16 : ℝ) :=
      Real.rpow_le_rpow heps0_nonneg heps0_le (by norm_num)
    have hr :
        ((rate / (8 * CG)) ^ (1 / 16 : ℝ)) ^ (16 : ℝ) =
          rate / (8 * CG) := by
      rw [← Real.rpow_mul hbase_nonneg]
      norm_num
    simpa [Real.rpow_natCast] using hp.trans_eq hr
  have hratio : effEnv 10 D.sigma n + 1 ≤ eps0 ^ 16 * b := by
    exact (div_le_iff₀ hbpos).mp (by simpa [b] using hgood)
  have hsig_env : D.sigma n + 1 ≤ effEnv 10 D.sigma n + 1 := by
    linarith [le_effEnv 10 D.sigma n]
  have hsig_rate_div : D.sigma n + 1 ≤ (rate / (8 * CG)) * b := by
    calc
      D.sigma n + 1 ≤ effEnv 10 D.sigma n + 1 := hsig_env
      _ ≤ eps0 ^ 16 * b := hratio
      _ ≤ (rate / (8 * CG)) * b := mul_le_mul_of_nonneg_right hpow_le hb_nonneg
  constructor
  · calc
      CG * (D.sigma n + 1) ≤ CG * ((rate / (8 * CG)) * b) :=
        mul_le_mul_of_nonneg_left hsig_rate_div hCGpos.le
      _ = rate / 8 * b := by
        field_simp [hCGpos.ne']
  · have hcoef : rate / (8 * CG) ≤ rate / 8 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * CG)
        (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hrate_pos.le, hCG1]
    calc
      D.sigma n ≤ D.sigma n + 1 := by linarith
      _ ≤ (rate / (8 * CG)) * b := hsig_rate_div
      _ ≤ (rate / 8) * b := mul_le_mul_of_nonneg_right hcoef hb_nonneg

lemma r2_effU_sigma_le_gamma_of_good_ratio (D : StabilityData) (n : ℕ)
    (gamma eps0 : ℝ)
    (hgamma_pos : 0 < gamma)
    (heps0_nonneg : 0 ≤ eps0)
    (hgood : (effEnv 10 D.sigma n + 1) / ((n : ℝ) + 1) ≤ eps0 ^ 16)
    (heps0_le : eps0 ≤ (gamma / 2) ^ (1 / 16 : ℝ))
    (hn1 : 1 ≤ n) :
    D.sigma n ≤ gamma * (n : ℝ) := by
  let b : ℝ := (n : ℝ) + 1
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hb_nonneg : 0 ≤ b := hbpos.le
  have hbase_nonneg : 0 ≤ gamma / 2 := by positivity
  have hpow_le : eps0 ^ 16 ≤ gamma / 2 := by
    have hp :
        eps0 ^ (16 : ℝ) ≤
          ((gamma / 2) ^ (1 / 16 : ℝ)) ^ (16 : ℝ) :=
      Real.rpow_le_rpow heps0_nonneg heps0_le (by norm_num)
    have hr :
        ((gamma / 2) ^ (1 / 16 : ℝ)) ^ (16 : ℝ) =
          gamma / 2 := by
      rw [← Real.rpow_mul hbase_nonneg]
      norm_num
    simpa [Real.rpow_natCast] using hp.trans_eq hr
  have hratio : effEnv 10 D.sigma n + 1 ≤ eps0 ^ 16 * b := by
    exact (div_le_iff₀ hbpos).mp (by simpa [b] using hgood)
  have hsig_env : D.sigma n + 1 ≤ effEnv 10 D.sigma n + 1 := by
    linarith [le_effEnv 10 D.sigma n]
  have hsig_half : D.sigma n ≤ (gamma / 2) * b := by
    calc
      D.sigma n ≤ D.sigma n + 1 := by linarith
      _ ≤ effEnv 10 D.sigma n + 1 := hsig_env
      _ ≤ eps0 ^ 16 * b := hratio
      _ ≤ (gamma / 2) * b := mul_le_mul_of_nonneg_right hpow_le hb_nonneg
  have hn_bound : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hgamma_half_nonneg : 0 ≤ gamma / 2 := by positivity
  calc
    D.sigma n ≤ (gamma / 2) * b := hsig_half
    _ ≤ (gamma / 2) * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa [b] using hn_bound) hgamma_half_nonneg
    _ = gamma * (n : ℝ) := by ring

set_option maxHeartbeats 1000000 in
/-- Fixed-`n` downward-pinning peeling with class-only constants.  This is the
uniform-`K` clone of the large-`n` branch of `r2_eff_dp_core`: given the range
control `alpha + beta ≤ 1/2 - c0` for THIS class member (supplied as a
hypothesis — it is discharged in the caller via `r1_range_control_at`), and the
class-only threshold `hGfsum` (the sublinear-slack budget, discharged from the
good-ratio σ-control), it peels the near-optimal bound at radius `r` down to a
`log`-size bound on `neighborhood ⌈tau·n⌉ S` via `V_peel_le`, `r2_effU_V_upper`,
and the class-only inversion atom `logsize_le_of_V_upper_large`.  The output
slack fits inside `r2_effU_Cw` (which is padded with an extra `1 + Cpre + Ceff`).
-/
lemma r2_effU_dp_at (hVPlus : VPlusStatement)
    (D : StabilityData) (hvalid : validData D)
    (c0 : ℝ) (hc0pos : 0 < c0) (hc0le : c0 ≤ (1 / 2 - D.alphaMax) / 2)
    (C_V : ℝ) (hC_V : 1 ≤ C_V) (K_IVC : ℝ) (hK_IVC : 1 ≤ K_IVC)
    (hcalc : ∀ (n k r : ℕ) (alpha beta sizeSlack : ℝ), D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → 0 ≤ sizeSlack → beta = (r : ℝ) / (n : ℝ) → alpha + beta ≤ 1 / 2 - c0 → 1 ≤ k → k ≤ 2 ^ n → |Real.log (k : ℝ) - H alpha * (n : ℝ)| ≤ sizeSlack → |Real.log (V n k r : ℝ) - H (alpha + beta) * (n : ℝ)| ≤ C_V * sizeSlack + effLog K_IVC n ∧ |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K_IVC n)
    (K_BV : ℝ) (hK_BV : 1 ≤ K_BV)
    (hbv : ∀ n t : ℕ, t ≤ n / 2 → Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - effLog K_BV n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧ ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + effLog K_BV n))
    (Ceff Ceff_BV CG kappa L rate Cpre : ℝ)
    (hCeff : Ceff = r2_effU_Ceff K_IVC)
    (hCeffBV : Ceff_BV = r2_effU_Ceff K_BV)
    (hCG : CG = r2_effU_CG C_V D.cSize Ceff)
    (hkappa : kappa = Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)))
    (hL : L = Real.log ((1 - D.alphaMin) / D.alphaMin))
    (hrate : rate = min (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) (kappa * (c0 / 2)))
    (hCpre_nn : 0 ≤ Cpre)
    (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hmem : classMember D n r S alpha beta) (hSne : S.Nonempty)
    (halpha_beta : alpha + beta ≤ 1 / 2 - c0)
    (hn1 : 1 ≤ n)
    (hGfsum : CG * (D.sigma n + 1) + D.sigma n + L + effLog K_BV n < rate * (n : ℝ))
    (hthr3 : (1 : ℝ) < c0 / 2 * (n : ℝ))
    (tau : ℝ) (htau_pos : 0 < tau) (htau_le : tau ≤ beta) (hhalf : alpha + tau < 1 / 2) :
    ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
      Real.exp (H (alpha + tau) * (n : ℝ) +
        r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre * (D.sigma n + 1)) := by
  obtain ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ := hmem
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_le_max : D.alphaMin ≤ D.alphaMax := hvalid.2.2.2.2.2.1
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hsig1 : (1 : ℝ) ≤ D.sigma n + 1 := by linarith
  have hLnn : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg; rw [le_div_iff₀ halphaMin_pos]; linarith
  have hc0half : c0 < 1 / 2 := by linarith
  have hlo_half : D.alphaMin ≤ 1 / 2 - c0 := by nlinarith [hc0le, halphaMin_le_max]
  have hkappa_pos : 0 < kappa := by
    rw [hkappa]; apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hCeff1 : 1 ≤ Ceff := by rw [hCeff]; exact le_max_left _ _
  have hCeff0 : 0 ≤ Ceff := le_trans zero_le_one hCeff1
  have hCeffbd : ∀ m, effLog K_IVC m ≤ Ceff * (D.sigma m + 1) := by
    rw [hCeff]; exact r2_effU_effLog_le_sigma D hvalid K_IVC hK_IVC
  have hCeffBVbd : ∀ m, effLog K_BV m ≤ Ceff_BV * (D.sigma m + 1) := by
    rw [hCeffBV]; exact r2_effU_effLog_le_sigma D hvalid K_BV hK_BV
  have hCG1 : 1 ≤ CG := by rw [hCG]; exact le_max_left _ _
  have hCG0 : 0 ≤ CG := le_trans zero_le_one hCG1
  have halpha_half : alpha ≤ 1 / 2 := le_of_lt (lt_of_le_of_lt halpha_max halphaMax_half)
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hScard2 : S.card ≤ 2 ^ n := by
    calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
      _ = 2 ^ n := by
          rw [Finset.card_univ]
          exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
  have hr'r : ⌈tau * (n : ℝ)⌉₊ ≤ r := by
    rw [Nat.ceil_le]
    have hh := htau_le
    rw [hbeta, le_div_iff₀ hnR] at hh
    exact hh
  set r'N := ⌈tau * (n : ℝ)⌉₊ with hr'Ndef
  have hpeel : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
      Real.exp (D.sigma n) * (V n S.card r : ℝ) :=
    V_peel_le S r'N r hr'r (D.sigma n) hnear
  have hVupS : (V n S.card r : ℝ) ≤
      Real.exp (H (alpha + beta) * (n : ℝ) + CG * (D.sigma n + 1)) := by
    have hbase := r2_effU_V_upper D hvalid c0 hc0pos C_V hC_V K_IVC hK_IVC hcalc Ceff hCeff1
      hCeffbd n r S alpha beta halpha_min halpha_half hbeta halpha_beta hScard1 hScard2 hsize
    rwa [← hCG] at hbase
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
  have htau_le' : tau ≤ (r'N : ℝ) / (n : ℝ) := by
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
  have hslope : Real.log ((1 - a) / a) ≤ L := by
    rw [hL]; exact log_ratio_upper halphaMin_pos hlo_a ha_half
  have hHdiff : H (alpha + beta) - H a ≤ (alpha + beta - a) * L :=
    H_diff_le ha_pos hab hb_half hslope
  have hban_eq : (alpha + beta - a) * (n : ℝ) = (r'N : ℝ) - tau * (n : ℝ) := by
    rw [hbma, sub_mul, div_mul_cancel₀ _ (ne_of_gt hnR)]
  have hban_le : (alpha + beta - a) * (n : ℝ) ≤ 1 := by
    rw [hban_eq, hr'Ndef]
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ tau * (n : ℝ) by positivity)
    linarith
  have hprod : (H (alpha + beta) - H a) * (n : ℝ) ≤ L := by
    have h1 : (H (alpha + beta) - H a) * (n : ℝ) ≤ (alpha + beta - a) * L * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hHdiff hnR.le
    have h3 : L * ((alpha + beta - a) * (n : ℝ)) ≤ L * 1 :=
      mul_le_mul_of_nonneg_left hban_le hLnn
    nlinarith [h1, h3]
  have hGf_val_nn : 0 ≤ CG * (D.sigma n + 1) + D.sigma n + L := by
    have : 0 ≤ CG * (D.sigma n + 1) := mul_nonneg hCG0 (by linarith)
    linarith
  have hVbound : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
      Real.exp (H a * (n : ℝ) + (CG * (D.sigma n + 1) + D.sigma n + L)) := by
    refine le_trans hcombined (Real.exp_le_exp.mpr ?_)
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
  have hdens : (alpha + tau) + ((r - r'N : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 - c0 := by
    rw [← hadef]; exact le_trans hab halpha_beta
  have hVbound' : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
      Real.exp (H ((alpha + tau) + ((r - r'N : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) +
        (CG * (D.sigma n + 1) + D.sigma n + L)) := by
    rw [← hadef]; exact hVbound
  have hthr1 :
      (CG * (D.sigma n + 1) + D.sigma n + L) + effLog K_BV n <
        (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) * (n : ℝ) := by
    have hle : rate ≤ H (1 / 2 - c0 / 2) - H (1 / 2 - c0) := by
      rw [hrate]; exact min_le_left _ _
    have : rate * (n : ℝ) ≤ (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hle hnR.le
    linarith [hGfsum]
  have hthr2 :
      (CG * (D.sigma n + 1) + D.sigma n + L) + effLog K_BV n <
        Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) * (c0 / 2) * (n : ℝ) := by
    rw [← hkappa]
    have hle : rate ≤ kappa * (c0 / 2) := by rw [hrate]; exact min_le_right _ _
    have : rate * (n : ℝ) ≤ kappa * (c0 / 2) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hle hnR.le
    linarith [hGfsum]
  have hvsnn : 0 ≤ effLog K_BV n :=
    (r2_effU_sublinear_effLog (show (0 : ℝ) ≤ K_BV by linarith)).1 n
  have hlogk := logsize_le_of_V_upper_large hVPlus c0 D.alphaMin hc0pos hc0half
    halphaMin_pos hlo_half (effLog K_BV)
    (fun _ => CG * (D.sigma n + 1) + D.sigma n + L) hbv
    n (r - r'N) (neighborhood r'N S) (alpha + tau) hTne hk'lt hlo_target hdens hVbound'
    hthr1 hthr2 hthr3 hn1 hvsnn hGf_val_nn
  simp only [← hL, ← hkappa] at hlogk
  have hposc : (0 : ℝ) < ((neighborhood r'N S).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hTne
  rw [← Real.log_le_iff_le_exp hposc]
  refine le_trans hlogk ?_
  have hLk_nn : 0 ≤ L / kappa := div_nonneg hLnn hkappa_pos.le
  have hGf_le :
      (CG * (D.sigma n + 1) + D.sigma n + L) + effLog K_BV n ≤
        (CG + 1 + L + Ceff_BV) * (D.sigma n + 1) := by
    have e2 : L ≤ L * (D.sigma n + 1) := le_mul_of_one_le_right hLnn hsig1
    have e3 : effLog K_BV n ≤ Ceff_BV * (D.sigma n + 1) := hCeffBVbd n
    have hexp : (CG + 1 + L + Ceff_BV) * (D.sigma n + 1) =
        CG * (D.sigma n + 1) + (D.sigma n + 1) + L * (D.sigma n + 1) +
          Ceff_BV * (D.sigma n + 1) := by ring
    rw [hexp]; linarith [e2, e3]
  have hslack :
      (L / kappa + 1) *
          ((CG * (D.sigma n + 1) + D.sigma n + L) + effLog K_BV n) + (L + 2) ≤
        r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre * (D.sigma n + 1) := by
    have h1 :
        (L / kappa + 1) * ((CG * (D.sigma n + 1) + D.sigma n + L) + effLog K_BV n) ≤
          (L / kappa + 1) * ((CG + 1 + L + Ceff_BV) * (D.sigma n + 1)) :=
      mul_le_mul_of_nonneg_left hGf_le (by linarith [hLk_nn])
    have h2 : (L + 2) ≤ (L + 2) * (D.sigma n + 1) :=
      le_mul_of_one_le_right (by linarith [hLnn]) hsig1
    have hpad :
        (L / kappa + 1) * ((CG + 1 + L + Ceff_BV) * (D.sigma n + 1)) ≤
          (L / kappa + 1) * ((CG + 1 + L + Ceff + Ceff_BV) * (D.sigma n + 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith [hCeff0]) (by linarith))
        (by linarith [hLk_nn])
    have hexpand :
        r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre * (D.sigma n + 1) =
          (1 + Cpre) * (D.sigma n + 1) +
            (L / kappa + 1) * ((CG + 1 + L + Ceff + Ceff_BV) * (D.sigma n + 1)) +
            (L + 2) * (D.sigma n + 1) := by
      unfold r2_effU_Cw; ring
    have hpre_nn : 0 ≤ (1 + Cpre) * (D.sigma n + 1) :=
      mul_nonneg (by linarith [hCpre_nn]) (by linarith)
    rw [hexpand]; linarith [h1, h2, hpad, hpre_nn]
  linarith [hslack]

set_option maxHeartbeats 1000000 in
/-- Uniform-`K` pinned bound at a fixed class member.  The clone of
`r2_eff_pinned_core` restricted to a fixed `n` with class-only constants: the
`r' = 0` leaf uses the size hypothesis, the large-`n` leaf (`N0 ≤ n`) runs the
class-only peeling `r2_effU_dp_at` (fed the range control `halpha_beta`), and the
small-`n` prefix (`n < N0`) is absorbed by the cube bound and `Cpre`. -/
lemma r2_effU_pinned_good
    (D : StabilityData) (hvalid : validData D)
    (hVPlus : VPlusStatement)
    (C_V : ℝ) (hC_V : 1 ≤ C_V) (K_IVC : ℝ) (hK_IVC : 1 ≤ K_IVC)
    (c0 : ℝ) (hc0pos : 0 < c0) (hc0le : c0 ≤ (1 / 2 - D.alphaMax) / 2)
    (hcalc : ∀ (n k r : ℕ) (alpha beta sizeSlack : ℝ), D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → 0 ≤ sizeSlack → beta = (r : ℝ) / (n : ℝ) → alpha + beta ≤ 1 / 2 - c0 → 1 ≤ k → k ≤ 2 ^ n → |Real.log (k : ℝ) - H alpha * (n : ℝ)| ≤ sizeSlack → |Real.log (V n k r : ℝ) - H (alpha + beta) * (n : ℝ)| ≤ C_V * sizeSlack + effLog K_IVC n ∧ |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K_IVC n)
    (K_BV : ℝ) (hK_BV : 1 ≤ K_BV)
    (hbv : ∀ n t : ℕ, t ≤ n / 2 → Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - effLog K_BV n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧ ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + effLog K_BV n))
    (Ceff Ceff_BV CG kappa L rate Cpre : ℝ) (N0 N0'' : ℕ) (Hlb : ℝ)
    (hCeff : Ceff = r2_effU_Ceff K_IVC)
    (hCeffBV : Ceff_BV = r2_effU_Ceff K_BV)
    (hCG : CG = r2_effU_CG C_V D.cSize Ceff)
    (hkappa : kappa = Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)))
    (hL : L = Real.log ((1 - D.alphaMin) / D.alphaMin))
    (hrate : rate = min (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) (kappa * (c0 / 2)))
    (hN0'' : ∀ m, N0'' ≤ m → effLog K_BV m < rate / 8 * m)
    (hN0 : N0 = max
      (max (max (⌈2 / D.rho⌉₊ + 1) (⌈4 / (1 / 2 - D.alphaMax)⌉₊ + 1))
        (⌈2 / c0⌉₊ + 1))
      (max N0'' (⌈8 * L / rate⌉₊ + 1)))
    (hHlb_le : Hlb ≤ Real.log 2)
    (hHlb : ∀ y : ℝ, -1 ≤ y → y ≤ 2 → Hlb ≤ H y)
    (hCpre : Cpre = r2_effU_Cpre (N0 : ℝ) Hlb)
    (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hclass : classMember D n r S alpha beta) (hSne : S.Nonempty)
    (halpha_beta : alpha + beta ≤ 1 / 2 - c0)
    (hσ1 : CG * (D.sigma n + 1) ≤ rate / 8 * ((n : ℝ) + 1))
    (hσ2 : D.sigma n ≤ rate / 8 * ((n : ℝ) + 1)) :
    pinned (r2EffUQData D (r2_effU_Cpin (r2_effU_Cdp (r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre) Cpre) D.cSize Cpre)) n S alpha := by
  classical
  set Cw := r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre with hCwdef
  set Cdp := r2_effU_Cdp Cw Cpre with hCdpdef
  set Cpin := r2_effU_Cpin Cdp D.cSize Cpre with hCpindef
  -- validData facts
  have hrho : 0 < D.rho := hvalid.1
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_le_max : D.alphaMin ≤ D.alphaMax := hvalid.2.2.2.2.2.1
  have hcSize : 1 ≤ D.cSize := hvalid.2.2.2.1
  have hgap_pos : 0 < 1 / 2 - D.alphaMax := by linarith
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2Hlb_nn : 0 ≤ Real.log 2 - Hlb := by linarith [hHlb_le]
  -- Cpre facts
  have hCpre1 : 1 ≤ Cpre := by rw [hCpre]; exact le_max_left _ _
  have hCpre_nn : 0 ≤ Cpre := le_trans zero_le_one hCpre1
  -- structural bounds on Cpin
  have hCpin1 : (1 : ℝ) ≤ Cpin := by
    rw [hCpindef, hCdpdef]; simp only [r2_effU_Cpin, r2_effU_Cdp]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCw_le_Cpin : Cw ≤ Cpin := by
    rw [hCpindef, hCdpdef]; simp only [r2_effU_Cpin, r2_effU_Cdp]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hcSize_le : D.cSize ≤ Cpin := by
    rw [hCpindef, hCdpdef]; simp only [r2_effU_Cpin, r2_effU_Cdp]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCpre_le : Cpre ≤ Cpin := by
    rw [hCpindef, hCdpdef]; simp only [r2_effU_Cpin, r2_effU_Cdp]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpin_nn : 0 ≤ Cpin := le_trans zero_le_one hCpin1
  -- rate positivity
  have hc0_lt : c0 < 1 / 2 := by nlinarith [hc0le, halphaMax_half]
  have hkappa_pos : 0 < kappa := by
    rw [hkappa]; apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hrate_pos : 0 < rate := by
    rw [hrate]; apply lt_min
    · exact sub_pos_of_lt (H_lt_H (by linarith) (by linarith) (by linarith))
    · exact mul_pos hkappa_pos (by linarith)
  -- unpack class
  obtain ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ := hclass
  have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
  have hsig1 : (1 : ℝ) ≤ D.sigma n + 1 := by linarith
  -- enter pinned
  intro r' hr'
  simp only [r2EffUQData] at hr' ⊢
  set s0 : ℝ := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) with hs0def
  have hs0_pos : 0 < s0 := lt_min (by linarith) (by linarith)
  have hs0_nn : 0 ≤ s0 := le_of_lt hs0_pos
  have hs0_le_rho : s0 ≤ D.rho / 2 := min_le_left _ _
  have hs0_le_gap : s0 ≤ (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
  by_cases hr0 : r' = 0
  · -- radius zero: size hypothesis suffices
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
  · -- positive radius
    have hr'pos : 1 ≤ r' := Nat.one_le_iff_ne_zero.mpr hr0
    have hn1 : 1 ≤ n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      · simp only [Nat.cast_zero, mul_zero, Nat.ceil_zero, Nat.le_zero] at hr'
        exact hr0 hr'
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
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
      have heq : (s0 + (1 : ℝ) / (n : ℝ)) * (n : ℝ) = s0 * (n : ℝ) + 1 := by field_simp
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
    · -- large n: class-only peeling via r2_effU_dp_at
      have hAle : ⌈2 / D.rho⌉₊ + 1 ≤ n := by
        refine le_trans ?_ hbign; rw [hN0]
        exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
      have hBle : ⌈4 / (1 / 2 - D.alphaMax)⌉₊ + 1 ≤ n := by
        refine le_trans ?_ hbign; rw [hN0]
        exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
      have hCle : ⌈2 / c0⌉₊ + 1 ≤ n := by
        refine le_trans ?_ hbign; rw [hN0]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have hN0''le : N0'' ≤ n := by
        refine le_trans ?_ hbign; rw [hN0]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      have hDle : ⌈8 * L / rate⌉₊ + 1 ≤ n := by
        refine le_trans ?_ hbign; rw [hN0]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      have hLnn : 0 ≤ L := by
        rw [hL]; apply Real.log_nonneg; rw [le_div_iff₀ halphaMin_pos]; linarith
      have h1n_gap : (1 : ℝ) / (n : ℝ) ≤ (1 / 2 - D.alphaMax) / 4 := by
        have hn_gt : 4 / (1 / 2 - D.alphaMax) < (n : ℝ) := by
          have h1 : 4 / (1 / 2 - D.alphaMax) ≤ (⌈4 / (1 / 2 - D.alphaMax)⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((⌈4 / (1 / 2 - D.alphaMax)⌉₊ : ℕ) : ℝ) < (n : ℝ) := by
            have : ⌈4 / (1 / 2 - D.alphaMax)⌉₊ < n := by omega
            exact_mod_cast this
          linarith only [h1, h2]
        rw [div_lt_iff₀ hgap_pos] at hn_gt
        rw [div_le_iff₀ hnR]; nlinarith only [hn_gt]
      have htau_le_half_gap : tau ≤ (1 / 2 - D.alphaMax) / 2 := by
        linarith only [htau_le_s0_plus, hs0_le_gap, h1n_gap]
      have hhalf : alpha + tau < 1 / 2 := by
        linarith only [htau_le_half_gap, halpha_max, halphaMax_half]
      have hthr3 : (1 : ℝ) < c0 / 2 * (n : ℝ) := by
        have hc_gt : 2 / c0 < (n : ℝ) := by
          have h1 : 2 / c0 ≤ (⌈2 / c0⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((⌈2 / c0⌉₊ : ℕ) : ℝ) < (n : ℝ) := by
            have : ⌈2 / c0⌉₊ < n := by omega
            exact_mod_cast this
          linarith only [h1, h2]
        rw [div_lt_iff₀ hc0pos] at hc_gt
        nlinarith only [hc_gt]
      have hLbound : L < rate / 8 * (n : ℝ) := by
        have hL_gt : 8 * L / rate < (n : ℝ) := by
          have h1 : 8 * L / rate ≤ (⌈8 * L / rate⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((⌈8 * L / rate⌉₊ : ℕ) : ℝ) < (n : ℝ) := by
            have : ⌈8 * L / rate⌉₊ < n := by omega
            exact_mod_cast this
          linarith only [h1, h2]
        rw [div_lt_iff₀ hrate_pos] at hL_gt
        nlinarith only [hL_gt]
      have heffbound : effLog K_BV n < rate / 8 * (n : ℝ) := hN0'' n hN0''le
      have hGfsum : CG * (D.sigma n + 1) + D.sigma n + L + effLog K_BV n < rate * (n : ℝ) := by
        have hsum_le : CG * (D.sigma n + 1) + D.sigma n + L + effLog K_BV n <
            rate / 8 * ((n : ℝ) + 1) + rate / 8 * ((n : ℝ) + 1) +
              rate / 8 * (n : ℝ) + rate / 8 * (n : ℝ) := by
          linarith only [hσ1, hσ2, hLbound, heffbound]
        have hAeq : rate / 8 * ((n : ℝ) + 1) + rate / 8 * ((n : ℝ) + 1) +
            rate / 8 * (n : ℝ) + rate / 8 * (n : ℝ) = rate / 2 * (n : ℝ) + rate / 4 := by ring
        have hpos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith only [hnge1]
        have hstrict : rate / 2 * (n : ℝ) + rate / 4 < rate * (n : ℝ) := by
          nlinarith only [mul_pos hrate_pos hpos]
        linarith only [hsum_le, hstrict, hAeq]
      have hdp := r2_effU_dp_at hVPlus D hvalid c0 hc0pos hc0le C_V hC_V K_IVC hK_IVC hcalc
        K_BV hK_BV hbv Ceff Ceff_BV CG kappa L rate Cpre hCeff hCeffBV hCG hkappa hL hrate
        hCpre_nn n r S alpha beta
        ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ hSne
        halpha_beta hn1 hGfsum hthr3 tau htau_pos htau_le_beta hhalf
      rw [hceil_tau, ← hCwdef] at hdp
      refine le_trans hdp (Real.exp_le_exp.mpr ?_)
      have hCw_step : Cw * (D.sigma n + 1) ≤ Cpin * (D.sigma n + 1) :=
        mul_le_mul_of_nonneg_right hCw_le_Cpin (by linarith only [hsig_nn])
      linarith only [hCw_step]
    · -- small n: cube bound absorbed by the finite prefix
      push_neg at hbign
      have hcard : ((neighborhood r' S).card : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) :=
        cube_card_le_two_pow _
      have harg_nn : (0 : ℝ) ≤ alpha + tau := by
        linarith only [halpha_min, halphaMin_pos, htau_pos]
      have harg_ge : (-1 : ℝ) ≤ alpha + tau := by linarith only [harg_nn]
      have hinv_le_one : (1 : ℝ) / (n : ℝ) ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hn1
      have htau_le_2 : tau ≤ s0 + 1 := by linarith only [htau_le_s0_plus, hinv_le_one]
      have hs0_lt_half : s0 < 1 / 2 :=
        lt_of_le_of_lt hs0_le_gap (by linarith only [halphaMin_pos, halphaMin_le_max])
      have harg_le : alpha + tau ≤ 2 := by
        linarith only [halpha_max, halphaMax_half, htau_le_2, hs0_lt_half]
      have hHlb_arg : Hlb ≤ H (alpha + tau) := hHlb (alpha + tau) harg_ge harg_le
      have hnN0 : (n : ℝ) * (Real.log 2 - Hlb) ≤ (N0 : ℝ) * (Real.log 2 - Hlb) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hbign.le) hlog2Hlb_nn
      have hCpre_ge : (N0 : ℝ) * (Real.log 2 - Hlb) ≤ Cpre := by
        rw [hCpre]; simp only [r2_effU_Cpre]; exact le_max_right _ _
      have hbudget : (n : ℝ) * (Real.log 2 - Hlb) ≤ Cpin * (D.sigma n + 1) := by
        have hstep1 : Cpre ≤ Cpre * (D.sigma n + 1) := le_mul_of_one_le_right hCpre_nn hsig1
        have hstep2 : Cpre * (D.sigma n + 1) ≤ Cpin * (D.sigma n + 1) :=
          mul_le_mul_of_nonneg_right hCpre_le (by linarith only [hsig_nn])
        linarith only [hnN0, hCpre_ge, hstep1, hstep2]
      have hHn : Hlb * (n : ℝ) ≤ H (alpha + tau) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hHlb_arg (Nat.cast_nonneg n)
      refine le_trans hcard (Real.exp_le_exp.mpr ?_)
      nlinarith only [hHn, hbudget, hCpin_nn, hsig_nn, hnR]

set_option maxHeartbeats 1000000 in
/-- HBL extraction for a single class data tuple, using the explicit precision schedule. -/
theorem r2_effU (hS7U : S7EffU) (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff) : R2EffU := by
  intro rho deltaCap cSize alphaMin alphaMax hrho hdeltaCap_pos hdeltaCap_lt hcSize halphaMin_pos halphaMin_le_max halphaMax_lt_half
  obtain ⟨c0_rc, hc0rc_pos, N_rc, hN_rc, gamma_rc, hgamma_rc_pos, hr1⟩ :=
    r1_range_control_class_constants (r2_effU_BVStatement_of_Eff hBV) hVPlus (r2_effU_IVCStatement_of_Eff hIVC) rho deltaCap cSize alphaMin alphaMax hrho hdeltaCap_pos hdeltaCap_lt hcSize halphaMin_pos halphaMin_le_max halphaMax_lt_half
  let c0 : ℝ := min c0_rc ((1 / 2 - alphaMax) / 2)
  have hc0_pos : 0 < c0 := lt_min hc0rc_pos (by linarith)
  obtain ⟨C_V, hC_V, K_IVC, hK_IVC, hcalc⟩ := hIVC alphaMin c0 halphaMin_pos hc0_pos
  have hBV' := hBV
  obtain ⟨K_BV, hK_BV, hbv⟩ := hBV'
  let Ceff : ℝ := r2_effU_Ceff K_IVC
  let Ceff_BV : ℝ := r2_effU_Ceff K_BV
  let CG : ℝ := r2_effU_CG C_V cSize Ceff
  let kappa : ℝ := Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2))
  let L : ℝ := Real.log ((1 - alphaMin) / alphaMin)
  have hc0_pos2 : 0 < c0 := by dsimp [c0]; linarith [halphaMax_lt_half]
  have hc0_half_pos : 0 < c0 / 2 := by linarith [hc0_pos2]
  have hc0_le_gap : c0 ≤ (1 / 2 - alphaMax) / 2 := by
    dsimp [c0]
    exact min_le_right _ _
  have hc0_lt_one : c0 < 1 := by
    have hgap_lt_one : (1 / 2 - alphaMax) / 2 < 1 := by
      linarith [halphaMin_pos, halphaMin_le_max]
    exact lt_of_le_of_lt hc0_le_gap hgap_lt_one
  have hkappa_pos : 0 < kappa := by
    dsimp [kappa]
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith [hc0_pos2, hc0_lt_one])]
    linarith [hc0_pos2, hc0_lt_one]
  let rate : ℝ := min (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) (kappa * (c0 / 2))
  have h1 : 0 ≤ 1 / 2 - c0 := by
    linarith [hc0_le_gap, halphaMax_lt_half]
  have h2 : 1 / 2 - c0 < 1 / 2 - c0 / 2 := by linarith [hc0_half_pos]
  have h3 : 1 / 2 - c0 / 2 ≤ 1 / 2 := by linarith [hc0_half_pos]
  have hrate_pos : 0 < rate := by
    apply lt_min
    · exact sub_pos_of_lt (H_lt_H h1 h2 h3)
    · exact mul_pos hkappa_pos hc0_half_pos
  have hrate_pos8 : 0 < rate / 8 := by linarith [hrate_pos]
  have heff_sub_BV : Sublinear (effLog K_BV) :=
    r2_eff_sublinear_effLog (by linarith [hK_BV])
  obtain ⟨N0'', hN0''pos, hN0''⟩ := sublinear_lt_of_pos heff_sub_BV hrate_pos8
  let N0 : ℕ := max
    (max (max (⌈2 / rho⌉₊ + 1) (⌈4 / (1 / 2 - alphaMax)⌉₊ + 1))
      (⌈2 / c0⌉₊ + 1))
    (max N0'' (⌈8 * L / rate⌉₊ + 1))
  obtain ⟨Hlb, hHlb_le, hHlb⟩ := r2_effU_H_lower_bound
  let Cpre : ℝ := r2_effU_Cpre N0 Hlb
  let Cw : ℝ := r2_effU_Cw L kappa CG Ceff Ceff_BV Cpre
  let Cdp : ℝ := r2_effU_Cdp Cw Cpre
  let Cpin : ℝ := r2_effU_Cpin Cdp cSize Cpre
  let C : ℝ := r2_effU_C Cpin cSize

  let qMin := alphaMin
  let qMax := alphaMax
  let s0 := min (rho / 2) ((1 / 2 - alphaMax) / 4)
  let mu0 := (1 / 2 - alphaMax) / 2
  have hqmin : 0 < qMin := halphaMin_pos
  have hqmin_max : qMin ≤ qMax := halphaMin_le_max
  have hqmax : qMax < 1 / 2 := halphaMax_lt_half
  have hs0 : 0 < s0 := lt_min (by linarith) (by linarith)
  have hmu0 : 0 < (1 / 2 - alphaMax) / 2 := by linarith
  have hs0_bound : qMax + s0 ≤ 1 / 2 - mu0 := by
    dsimp [s0, mu0, qMax]
    have : min (rho / 2) ((1 / 2 - alphaMax) / 4) ≤ (1 / 2 - alphaMax) / 4 := min_le_right _ _
    linarith
  obtain ⟨K_s7, hK_s7, hS7_bound⟩ := hS7U qMin qMax s0 mu0 hqmin hqmin_max hqmax hs0 hmu0 hs0_bound

  let G : ℝ := 2 ^ 14 * C
  let M : ℝ := K_s7 * G
  let B : ℝ := C_V * cSize + Ceff
  let eps0 : ℝ := min (qMin / 2) (min ((1 / 2 - qMax) / 2) (min ((rate / (8 * CG)) ^ (1 / 16 : ℝ)) ((gamma_rc / 2) ^ (1 / 16 : ℝ))))
  let n0 : ℕ := max ⌈K_s7 ^ 2 + 1⌉₊ N_rc
  let K : ℝ := max 1 (max ((n0 : ℝ) * Real.log 2) (max M (max (B + 4 * (G + 1)) (Real.log 2 / eps0))))

  use K
  constructor
  · exact le_max_left 1 _
  · intro sigma hsub hlog
    let D : StabilityData := ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
    have hvalidD : validData D := by
      dsimp [D, validData]
      exact ⟨hrho, hdeltaCap_pos, hdeltaCap_lt, hcSize, halphaMin_pos,
        halphaMin_le_max, halphaMax_lt_half, hsub, hlog⟩
    have hDsigma_nonneg : ∀ m, 0 ≤ D.sigma m := fun m =>
      hvalidD.2.2.2.2.2.2.2.1.1 m
    have hCpin1 : 1 ≤ Cpin := by
      dsimp [Cpin, r2_effU_Cpin]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hC1 : 1 ≤ C := by
      dsimp [C, r2_effU_C]
      exact le_trans hCpin1 (le_max_left _ _)
    have hC0 : 0 ≤ C := le_trans zero_le_one hC1
    have hG0 : 0 ≤ G := by
      dsimp [G]
      positivity
    have heps0_pos : 0 < eps0 := by
      have h1 : 0 < qMin / 2 := by dsimp [qMin]; linarith [halphaMin_pos]
      have h2 : 0 < (1 / 2 - qMax) / 2 := by dsimp [qMax]; linarith [halphaMax_lt_half]
      have hCG_pos : 0 < CG := by dsimp [CG, r2_effU_CG]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hrate_div_pos : 0 < rate / (8 * CG) := div_pos hrate_pos (mul_pos (by linarith) hCG_pos)
      have h3 : 0 < (rate / (8 * CG)) ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hrate_div_pos _
      have h4 : 0 < (gamma_rc / 2) ^ (1 / 16 : ℝ) := by
        exact Real.rpow_pos_of_pos (by linarith [hgamma_rc_pos]) _
      exact lt_min h1 (lt_min h2 (lt_min h3 h4))
    have hQvalid : validQData (r2EffUQData D C) :=
      r2_effU_valid_qdata D hvalidD C hC1
    have hQsub : Sublinear (r2EffUQData D C).sigma :=
      hQvalid.2.2.2.2.2.2.1
    have hQlog : ∀ m : ℕ, 1 ≤ m → Real.log (m : ℝ) ≤ (r2EffUQData D C).sigma m :=
      hQvalid.2.2.2.2.2.2.2
    have hE1 : ∀ n : ℕ, (1 : ℝ) ≤ effEnv 14 D.sigma n + 1 := fun n => by
      have hE := effEnv_nonneg 14 D.sigma hDsigma_nonneg n
      linarith
    have hK0 : 0 ≤ K := le_trans zero_le_one (by dsimp [K]; exact le_max_left _ _)
    have hK_log : Real.log 2 / eps0 ≤ K := by
      dsimp [K]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

    intro n r S alpha beta hclass
    by_cases hSnonempty : S.Nonempty
    · by_cases hn_small : n < n0
      · obtain ⟨a, ha⟩ := hSnonempty
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
        have hmass_ge : (n : ℝ) * Real.log 2 ≤ K * (effEnv 14 D.sigma n + 1) := by
          have hK_ge : (n0 : ℝ) * Real.log 2 ≤ K := by
            dsimp [K]
            exact le_max_of_le_right (le_max_left _ _)
          have hn_le : (n : ℝ) * Real.log 2 ≤ (n0 : ℝ) * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hn_small.le) (Real.log_nonneg one_le_two)
          nlinarith [le_trans hn_le hK_ge, hE1 n, hK0]
        have hle1 : Real.exp (-(K * (effEnv 14 D.sigma n + 1))) * (S.card : ℝ) ≤ 1 := by
          have hstep := mul_le_mul_of_nonneg_left hcard2
            (Real.exp_nonneg (-(K * (effEnv 14 D.sigma n + 1))))
          refine le_trans hstep ?_
          rw [← Real.exp_add]
          have hle0 : -(K * (effEnv 14 D.sigma n + 1)) + (n : ℝ) * Real.log 2 ≤ 0 := by
            linarith
          calc Real.exp (-(K * (effEnv 14 D.sigma n + 1)) + (n : ℝ) * Real.log 2)
              ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
            _ = 1 := Real.exp_zero
        have hmem : a ∈ S.filter fun x =>
            hDist x a ≤ rmin n S.card + Nat.ceil (K * (effEnv 14 D.sigma n + 1)) := by
          rw [Finset.mem_filter]
          exact ⟨ha, by simp [hDist]⟩
        have h1le : (1 : ℝ) ≤
            ((S.filter fun x =>
              hDist x a ≤ rmin n S.card + Nat.ceil (K * (effEnv 14 D.sigma n + 1))).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨a, hmem⟩
        exact le_trans hle1 h1le
      · push_neg at hn_small
        let ratio : ℝ := (effEnv 10 D.sigma n + 1) / ((n : ℝ) + 1)
        by_cases hgood : ratio ≤ eps0 ^ 16
        · have hCsize_le_C : D.cSize ≤ C := by
            dsimp [D, C, r2_effU_C]
            exact le_max_right _ _
          have hfat : fat (r2EffUQData D C) n S alpha :=
            r2_effU_fat_of_classMember D hvalidD C hC1 hCsize_le_C
              n r S alpha beta hclass hSnonempty
          have hpinned : pinned (r2EffUQData D C) n S alpha := by
            have hCG1 : 1 ≤ CG := by
              dsimp [CG, r2_effU_CG]
              exact le_max_left _ _
            have heps0_rate :
                eps0 ≤ (rate / (8 * CG)) ^ (1 / 16 : ℝ) := by
              dsimp [eps0]
              exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
                (min_le_left _ _)
            have hσ_bounds :=
              r2_effU_sigma_bounds_of_good_ratio D n rate CG eps0 hrate_pos hCG1
                (le_of_lt heps0_pos) (by simpa [ratio] using hgood) heps0_rate
            have hσ1 : CG * (D.sigma n + 1) ≤ rate / 8 * ((n : ℝ) + 1) :=
              hσ_bounds.1
            have hσ2 : D.sigma n ≤ rate / 8 * ((n : ℝ) + 1) :=
              hσ_bounds.2
            have halpha_beta : alpha + beta ≤ 1 / 2 - c0 := by
              have heps0_gamma :
                  eps0 ≤ (gamma_rc / 2) ^ (1 / 16 : ℝ) := by
                dsimp [eps0]
                exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
                  (min_le_right _ _)
              have hn1 : 1 ≤ n := by
                exact le_trans hN_rc (le_trans (le_max_right _ _) hn_small)
              have hsig_gamma : D.sigma n ≤ gamma_rc * (n : ℝ) :=
                r2_effU_sigma_le_gamma_of_good_ratio D n gamma_rc eps0
                  hgamma_rc_pos (le_of_lt heps0_pos) (by simpa [ratio] using hgood)
                  heps0_gamma hn1
              have hNrc : N_rc ≤ n := le_trans (le_max_right _ _) hn_small
              have hrc := hr1 sigma hvalidD n hNrc hsig_gamma r S alpha beta hclass
              have hc0_le_rc : c0 ≤ c0_rc := by
                dsimp [c0]
                exact min_le_left _ _
              linarith
            have hpin_good := r2_effU_pinned_good D hvalidD hVPlus C_V hC_V K_IVC hK_IVC c0 hc0_pos (min_le_right _ _) hcalc K_BV hK_BV hbv Ceff Ceff_BV CG kappa L rate Cpre N0 N0'' Hlb rfl rfl rfl rfl rfl rfl hN0'' rfl hHlb_le hHlb rfl n r S alpha beta hclass hSnonempty halpha_beta hσ1 hσ2
            exact r2_effU_pinned_mono_C D hvalidD (le_max_left _ _) hpin_good
          let eps : ℝ := r2EffUEps D.sigma n
          have heps_pos : 0 < eps := by
            dsimp [eps]
            exact r2_effU_eps_pos D.sigma n (hDsigma_nonneg n)
          have heps_le_eps0 : eps ≤ eps0 := by
            dsimp [eps]
            exact r2_effU_eps_le_of_ratio (le_of_lt heps0_pos) (by simpa [ratio] using hgood)
          have heps_qMin : eps < qMin := by
            have heps0_qMin : eps0 < qMin := by
              have h1 : eps0 ≤ qMin / 2 := min_le_left _ _
              have h2 : qMin / 2 < qMin := by dsimp [qMin]; linarith [halphaMin_pos]
              exact lt_of_le_of_lt h1 h2
            exact lt_of_le_of_lt heps_le_eps0 heps0_qMin
          have heps_qMax : eps < 1 / 2 - qMax := by
            have heps0_qMax : eps0 < 1 / 2 - qMax := by
              have h1 : eps0 ≤ (1 / 2 - qMax) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
              have h2 : (1 / 2 - qMax) / 2 < 1 / 2 - qMax := by dsimp [qMax]; linarith [halphaMax_lt_half]
              exact lt_of_le_of_lt h1 h2
            exact lt_of_le_of_lt heps_le_eps0 heps0_qMax
          have hthreshold : K_s7 / eps ^ 8 ≤ (n : ℝ) := by
            dsimp [eps]
            exact r2_effU_threshold_unclamped D.sigma hDsigma_nonneg hK_s7
              (le_trans (le_max_left _ _) hn_small)
          obtain ⟨a, ha⟩ := hS7_bound (r2EffUQData D C).sigma hQsub hQlog
            eps heps_pos heps_qMin heps_qMax n hthreshold S alpha hSnonempty hfat hpinned
          have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSnonempty
          have hScard2 : S.card ≤ 2 ^ n := by
            calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
              _ = 2 ^ n := by
                  rw [Finset.card_univ]
                  exact (Fintype.card_finset).trans (by rw [Fintype.card_fin])
          have hK_bound :
              (K_s7 / eps ^ 8) * (effEnv 10 (r2EffUQData D C).sigma n + 1) ≤
                K * (effEnv 14 D.sigma n + 1) := by
            have hscaled := r2_effU_scaled_mass_bound D hvalidD hC1 hK_s7 n
            have hG_ge : 2 ^ 10 * C + 1 ≤ G := by
              dsimp [G]
              nlinarith [hC1]
            have hM_scaled : K_s7 * (2 ^ 10 * C + 1) ≤ M := by
              dsimp [M]
              exact mul_le_mul_of_nonneg_left hG_ge (by linarith)
            have hM_le_K : M ≤ K := by
              dsimp [K]
              exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
            have hcoef :
                (K_s7 * (2 ^ 10 * C + 1)) * (effEnv 14 D.sigma n + 1) ≤
                  K * (effEnv 14 D.sigma n + 1) :=
              mul_le_mul_of_nonneg_right (le_trans hM_scaled hM_le_K) (by linarith [hE1 n])
            simpa [eps] using le_trans hscaled hcoef
          have h_radius_absorb :
              alpha * (n : ℝ) + 4 * eps * (n : ℝ)
                ≤ (rmin n S.card : ℝ) + K * (effEnv 14 D.sigma n + 1) := by
            have hsizeSlack_nonneg : 0 ≤ cSize * D.sigma n := by
              exact mul_nonneg (by linarith [hcSize]) (hDsigma_nonneg n)
            have halpha_half : alpha ≤ 1 / 2 := by
              exact le_trans hclass.2.2.2.1 (le_of_lt halphaMax_lt_half)
            have hrange0 : alpha + (0 : ℝ) ≤ 1 / 2 - c0 := by
              linarith [hclass.2.2.2.1, hc0_le_gap]
            have hcalc0 := hcalc n S.card 0 alpha 0 (cSize * D.sigma n)
              hclass.2.2.1 halpha_half hsizeSlack_nonneg (by norm_num) hrange0
              hScard1 hScard2 hclass.2.2.2.2.2.1
            have hrmin :
                alpha * (n : ℝ) ≤ (rmin n S.card : ℝ) + B * (effEnv 14 D.sigma n + 1) := by
              have hlow := (abs_le.mp hcalc0.2).1
              have heff := r2_effU_effLog_le_sigma D hvalidD K_IVC hK_IVC n
              have hsig_le : D.sigma n + 1 ≤ effEnv 14 D.sigma n + 1 := by
                have hle := le_effEnv 14 D.sigma n
                linarith
              have hsig_bound : D.sigma n ≤ effEnv 14 D.sigma n + 1 := by
                have hle := le_effEnv 14 D.sigma n
                linarith
              have hslack :
                  C_V * (cSize * D.sigma n) + effLog K_IVC n ≤
                    B * (effEnv 14 D.sigma n + 1) := by
                have hCVc_nonneg : 0 ≤ C_V * cSize := by positivity
                have hCeff_nonneg : 0 ≤ Ceff := by
                  dsimp [Ceff, r2_effU_Ceff]
                  exact le_trans zero_le_one (le_max_left _ _)
                have hterm1 :
                    C_V * (cSize * D.sigma n) ≤
                      (C_V * cSize) * (effEnv 14 D.sigma n + 1) := by
                  calc
                    C_V * (cSize * D.sigma n) = (C_V * cSize) * D.sigma n := by ring
                    _ ≤ (C_V * cSize) * (effEnv 14 D.sigma n + 1) :=
                        mul_le_mul_of_nonneg_left hsig_bound hCVc_nonneg
                have hterm2 :
                    effLog K_IVC n ≤ Ceff * (effEnv 14 D.sigma n + 1) :=
                  le_trans heff (mul_le_mul_of_nonneg_left hsig_le hCeff_nonneg)
                calc
                  C_V * (cSize * D.sigma n) + effLog K_IVC n
                      ≤ C_V * cSize * (effEnv 14 D.sigma n + 1) +
                          Ceff * (effEnv 14 D.sigma n + 1) :=
                        add_le_add hterm1 hterm2
                  _ = B * (effEnv 14 D.sigma n + 1) := by
                        dsimp [B]
                        ring
              linarith
            have hexc : 4 * eps * (n : ℝ) ≤ 4 * effEnv 14 D.sigma n := by
              dsimp [eps]
              exact r2_effU_radius_excess_unclamped D.sigma n
            have hBK : B + 4 ≤ K := by
              have hbig : B + 4 * (G + 1) ≤ K := by
                dsimp [K]
                calc
                  B + 4 * (G + 1)
                      ≤ max (B + 4 * (G + 1)) (Real.log 2 / eps0) := le_max_left _ _
                  _ ≤ max M (max (B + 4 * (G + 1)) (Real.log 2 / eps0)) := le_max_right _ _
                  _ ≤ max ((n0 : ℝ) * Real.log 2)
                        (max M (max (B + 4 * (G + 1)) (Real.log 2 / eps0))) := le_max_right _ _
                  _ ≤ max 1 (max ((n0 : ℝ) * Real.log 2)
                        (max M (max (B + 4 * (G + 1)) (Real.log 2 / eps0)))) := le_max_right _ _
              nlinarith [hbig, hG0]
            have hbudget : (B + 4) * (effEnv 14 D.sigma n + 1) ≤
                K * (effEnv 14 D.sigma n + 1) :=
              mul_le_mul_of_nonneg_right hBK (by linarith [hE1 n])
            nlinarith [hrmin, hexc, hbudget, hE1 n]
          exact r2_effU_s7_output_to_hbl D C n S alpha K_s7 eps a ha
            K hK_bound h_radius_absorb
        · have hbad_ratio :
              eps0 ^ 16 * ((n : ℝ) + 1) ≤ effEnv 10 D.sigma n + 1 := by
            have hlt : eps0 ^ 16 < ratio := lt_of_not_ge hgood
            have hbpos : 0 < (n : ℝ) + 1 := by positivity
            dsimp [ratio] at hlt
            exact le_of_lt ((lt_div_iff₀ hbpos).mp hlt)
          have henv := r2_effU_bad_ratio_env14 (le_of_lt heps0_pos) hbad_ratio
          exact r2_effU_bad_branch_hbl D K eps0 n S hSnonempty heps0_pos henv hK_log
    · rw [Finset.not_nonempty_iff_eq_empty] at hSnonempty
      refine ⟨(∅ : Cube n), ?_⟩
      simp [hSnonempty]

end HarperStability
