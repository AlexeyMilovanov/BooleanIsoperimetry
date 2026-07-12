import HarperStability.Process.Basic
import HarperStability.Interface.Effective

/-!
# Effective S4 (v0.3): the fold field has grade-4 entropy

Target: `S4Eff` — geometric form: for fat+pinned `A` there is an offset
`o ∈ [0, eps/4)` with `uH (binnedFoldField A (eps/4) o) ≤ (K/eps^4) *
(effEnv 4 Q.sigma m + 1)`; v0.3.1: ONE `K` uniform over `eps` (the `∃ K` sits before `∀ eps`) — the `1/eps^2`-type constants of the v0.2 chain fit in `K/eps^4`.

Route: replay the PROVED v0.2 `S4Statement` proof with explicit
parameters instead of the `p → 0` diagonal:
* block regularity from `hR3` (`R3Eff`, grade 2) at the densities the
  v0.2 proof used; the S1/S2 conversions are ALREADY explicit
  (`12*s/eps + 4`, `(s + eps*m + e*log2)/2`) — optimizing the S1
  threshold gives a variance budget of grade 3
  (`effGeo` of grade 2, toolkit `effEnv_comp`);
* the offset-averaged S3 application: choose the window density
  explicitly, `p(m) := sqrt((effEnv 3 Q.sigma m + 1)/((m:ℝ)+1))`
  (clamped to `(0, 1/2]`), so the `2*log2*p*m` term and the
  `budget/p`-terms are both ≤ grade 4; the Chebyshev bad-window mass
  (`s6_badWindow_mass_le`-style) contributes an `m`-free constant;
* absorb small `m` into `K`.
Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

lemma s4_r3_fixedDensity_blockRegular_eff
  (hR3 : R3Eff) (Q : QData) (pLow : ℝ) :
  validQData Q → 0 < pLow → pLow ≤ 1/2 →
  ∃ K, 1 ≤ K ∧ ∀ m A q,
    A.Nonempty → fat Q m A q → pinned Q m A q →
    blockRegular m A q pLow (K * (effEnv 2 Q.sigma m + 1)) := by
  intro hQ hpLow hpLowHalf
  obtain ⟨K3, hK3, hR3_bound⟩ := hR3 Q.qMin Q.qMax Q.s0 Q.mu0 hQ.1 hQ.2.1
    hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1
  refine ⟨K3 / pLow, ?_, fun m A q hA hFat hPinned => ?_⟩
  · rw [le_div_iff₀ hpLow]
    nlinarith
  · exact hR3_bound pLow hpLow hpLowHalf Q.sigma hQ.2.2.2.2.2.2.1
      hQ.2.2.2.2.2.2.2 m A q hA hFat hPinned

lemma s4_eff2_nonneg (σ : ℕ → ℝ) (m : ℕ) : 0 ≤ effEnv 2 σ m := by
  rw [effEnv_succ]; exact effGeo_nonneg _ _

lemma s4_eff3_nonneg (σ : ℕ → ℝ) (m : ℕ) : 0 ≤ effEnv 3 σ m := by
  rw [effEnv_succ]; exact effGeo_nonneg _ _

/-
The grade-3 envelope arithmetic underlying the effective variance budget:
the `S2`-shaped variance value (with the sqrt-optimized threshold `eps`) is
dominated by a single grade-3 envelope constant.
-/
lemma s4_varBudget_env_algebra (K K6 sS eps E2 E3 : ℝ) (m : ℕ)
    (hK : 1 ≤ K) (hK6 : 1 ≤ K6)
    (hE2 : 0 ≤ E2) (hE23 : E2 ≤ E3)
    (hsqrtE3 : Real.sqrt ((E2 + 1) * ((m : ℝ) + 1)) ≤ E3)
    (hsS0 : 0 ≤ sS) (hsSbound : sS ≤ K6 * (E2 + 1) + E2)
    (heps : eps = Real.sqrt ((sS + 1) / ((m : ℝ) + 1))) :
    (K * (E2 + 1) + eps * (m : ℝ) + (12 * sS / eps + 4) * Real.log 2) / 2
      ≤ (30 + K + Real.sqrt (K6 + 2) + 12 * Real.sqrt (K6 + 2) * Real.log 2
          + 4 * Real.log 2) * (E3 + 1) := by
  have h_eps_m_le : eps * (m : ℝ) ≤ Real.sqrt (K6 + 2) * E3 := by
    refine' le_trans _ ( mul_le_mul_of_nonneg_left hsqrtE3 ( Real.sqrt_nonneg _ ) );
    rw [ heps, ← Real.sqrt_mul <| by positivity ] ; refine Real.le_sqrt_of_sq_le ?_ ; ring_nf;
    rw [ Real.sq_sqrt ( by positivity ) ] ; nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) sS, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ];
  have h_sS_eps_le : sS / eps ≤ Real.sqrt (K6 + 2) * E3 := by
    have h_sS_eps_le : sS / eps ≤ Real.sqrt ((sS + 1) * ((m : ℝ) + 1)) := by
      rw [ heps, Real.sqrt_mul ( by positivity ), Real.sqrt_div ( by positivity ) ];
      rw [ div_div_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( sS + 1 ), Real.sqrt_nonneg ( m + 1 ), Real.mul_self_sqrt ( show 0 ≤ sS + 1 by positivity ), Real.mul_self_sqrt ( show 0 ≤ ( m : ℝ ) + 1 by positivity ) ];
    refine le_trans h_sS_eps_le ?_;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left hsqrtE3 <| Real.sqrt_nonneg _ );
    rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.sqrt_le_sqrt <| by nlinarith [ mul_le_mul_of_nonneg_left hK6 <| show 0 ≤ E2 + 1 by positivity ] ;
  ring_nf at *;
  nlinarith [ Real.sqrt_nonneg ( 2 + K6 ), Real.mul_self_sqrt ( show 0 ≤ 2 + K6 by positivity ), Real.log_nonneg one_le_two, mul_le_mul_of_nonneg_left hK ( Real.log_nonneg one_le_two ), mul_le_mul_of_nonneg_left hK6 ( Real.log_nonneg one_le_two ), mul_le_mul_of_nonneg_left hE2 ( Real.log_nonneg one_le_two ), mul_le_mul_of_nonneg_left hE23 ( Real.log_nonneg one_le_two ) ]

lemma s4_fixedDensity_varianceBudget_eff
    (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (pLow : ℝ) :
  validQData Q → 0 < pLow → pLow ≤ 1/2 →
  ∃ C, ∀ m A q, A.Nonempty → fat Q m A q → pinned Q m A q →
    varianceBudgetLE A pLow (C * (effEnv 3 Q.sigma m + 1)) := by
  intro hQ hpLow hpLowHalf
  obtain ⟨K, hK1, hK⟩ := s4_r3_fixedDensity_blockRegular_eff hR3 Q pLow hQ hpLow hpLowHalf
  obtain ⟨K6, hK61, hK6⟩ := s4_r3_fixedDensity_blockRegular_eff hR3 Q (1/6) hQ (by norm_num) (by norm_num);
  use 30 + K + Real.sqrt (K6 + 2) + 12 * Real.sqrt (K6 + 2) * Real.log 2 + 4 * Real.log 2;
  intro m A q hA hfat hpinned W hW1 hW2
  by_cases hm : m < 30;
  · have h_sum_le_m : ∑ t ∈ W, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below W t)) ≤ m := by
      have h_sum_le_m : ∀ t ∈ W, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below W t)) ≤ 1 := by
        intro t ht
        have h_var_le_one : ∀ x ∈ A, (rho A t (proj (below Finset.univ t) x) - uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y))) ^ 2 ≤ 1 := by
          intro x hx
          have h_rho_bounds : 0 ≤ rho A t (proj (below Finset.univ t) x) ∧ rho A t (proj (below Finset.univ t) x) ≤ 1 := by
            exact ⟨ rho_nonneg A t _, rho_le_one A t _ ⟩;
          have h_uE_bounds : 0 ≤ uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y)) ∧ uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y)) ≤ 1 := by
            refine' ⟨ div_nonneg ( Finset.sum_nonneg fun _ _ => _ ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ _ ( Nat.cast_nonneg _ ) ⟩;
            · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
            · exact le_trans ( Finset.sum_le_sum fun _ _ => show rho A t ( proj ( below Finset.univ t ) _ ) ≤ 1 from by
                                                              grind +suggestions ) ( by norm_num );
          nlinarith only [ h_rho_bounds, h_uE_bounds ];
        have h_var_le_one : uE A (fun x => (rho A t (proj (below Finset.univ t) x) - uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y))) ^ 2) ≤ 1 := by
          unfold uE; simp +decide [ * ] ;
          rw [ div_le_iff₀ ( Nat.cast_pos.mpr hA.card_pos ) ];
          convert Finset.sum_le_sum h_var_le_one using 1 ; norm_num [ uE ];
        convert h_var_le_one using 1;
        convert uCondVar_eq_uE_fiber_sq A _ _ using 1;
      exact le_trans ( Finset.sum_le_sum h_sum_le_m ) ( by norm_num; linarith [ show W.card ≤ m from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] );
    refine le_trans h_sum_le_m ?_;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_left <| s4_eff3_nonneg _ _ ) <| by positivity );
    nlinarith only [ show ( m : ℝ ) ≤ 29 by norm_cast; linarith, hK1, hK61, Real.sqrt_nonneg ( K6 + 2 ), Real.log_nonneg one_le_two ];
  · -- Set the constants and apply the lemmas.
    set kappa := H q
    set sS := K6 * (effEnv 2 Q.sigma m + 1) + Q.sigma m
    set epsS := Real.sqrt ((sS + 1) / ((m : ℝ) + 1))
    have hflat : ∀ I : Finset (Fin m), ((m / 5 : ℕ) : ℝ) ≤ I.card → I.card ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ) → uH A (proj I) ≤ kappa * (I.card : ℝ) + sS := by
      intros I hI1 hI2
      have hI_bounds : (1 / 6 : ℝ) * m ≤ I.card ∧ I.card ≤ (1 - 1 / 6 : ℝ) * m := by
        constructor <;> linarith [ show ( m : ℝ ) ≥ 30 by norm_cast; linarith, show ( m / 5 : ℕ ) ≥ ( m : ℝ ) / 6 by exact by rw [ ge_iff_le ] ; rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod m 5, Nat.mod_lt m ( by norm_num : 5 > 0 ) ] ];
      have := hK6 m A q hA hfat hpinned;
      obtain ⟨ hI1, hI2, hI3 ⟩ := this;
      linarith [ abs_le.mp ( hI3 I hI_bounds.1 hI_bounds.2 ), show 0 ≤ Q.sigma m from hQ.2.2.2.2.2.2.1.1 m ];
    have hlow : kappa * (m : ℝ) - sS ≤ uH A (proj Finset.univ) := by
      have hlow : kappa * (m : ℝ) - Q.sigma m ≤ uH A (proj Finset.univ) := by
        have := hfat.2.2.2.2;
        rw [ uH_proj_univ A hA ] ; linarith [ abs_le.mp this ];
      exact le_trans ( by nlinarith [ show 0 ≤ effEnv 2 Q.sigma m from s4_eff2_nonneg Q.sigma m ] ) hlow;
    obtain ⟨count, hcount⟩ : ∃ count : ℝ, 0 ≤ count ∧ ((Finset.univ.filter (fun t => epsS ≤ |hstep A t - kappa|)).card : ℝ) ≤ count ∧ count ≤ 12 * sS / epsS + 4 := by
      refine' ⟨ _, _, le_rfl, _ ⟩;
      · positivity;
      · apply hS1 m A kappa sS epsS hA (by
        exact add_nonneg ( mul_nonneg ( by positivity ) ( add_nonneg ( s4_eff2_nonneg _ _ ) zero_le_one ) ) ( hQ.2.2.2.2.2.2.1.1 _ )) (by
        exact Real.sqrt_pos.mpr ( div_pos ( add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( by positivity ) ( add_nonneg ( s4_eff2_nonneg _ _ ) zero_le_one ) ) ( hQ.2.2.2.2.2.2.1.1 _ ) ) zero_lt_one ) ( by positivity ) )) hflat hlow;
    have := hS2 m A q pLow ( K * ( effEnv 2 Q.sigma m + 1 ) ) epsS count hA hpLow hpLowHalf ( by
      exact mul_nonneg ( by positivity ) ( add_nonneg ( s4_eff2_nonneg _ _ ) zero_le_one ) ) ( by
      exact Real.sqrt_pos.mpr ( div_pos ( add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( by positivity ) ( add_nonneg ( s4_eff2_nonneg _ _ ) zero_le_one ) ) ( hQ.2.2.2.2.2.2.1.1 _ ) ) zero_lt_one ) ( by positivity ) ) ) hcount.1 ( hK m A q hA hfat hpinned ) ( by
      exact hcount.2.1 ) W hW1 hW2;
    refine le_trans ?_ ( s4_varBudget_env_algebra K K6 sS epsS ( effEnv 2 Q.sigma m ) ( effEnv 3 Q.sigma m ) m hK1 hK61 ?_ ?_ ?_ ?_ ?_ rfl );
    any_goals nlinarith [ Real.log_nonneg one_le_two, hQ.2.2.2.2.2.2.1.1 m, le_effEnv 2 Q.sigma m ];
    · exact le_effGeo _ _;
    · rw [ effEnv_succ, effGeo ] ; exact le_max_right _ _

lemma H_le_x_logInv (x : ℝ) : 0 < x → x ≤ 1/2 → H x ≤ x * Real.log (1/x) + x := by
  intro hx hxhalf
  have hone_minus_pos : 0 < 1 - x := by linarith
  have hone_minus_nonneg : 0 ≤ 1 - x := le_of_lt hone_minus_pos
  have hlog : Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := by
    exact Real.log_le_sub_one_of_pos (inv_pos.mpr hone_minus_pos)
  have hterm : (1 - x) * Real.log ((1 - x)⁻¹) ≤ x := by
    have hmul := mul_le_mul_of_nonneg_left hlog hone_minus_nonneg
    have hsimp : (1 - x) * ((1 - x)⁻¹ - 1) = x := by
      field_simp [hone_minus_pos.ne']
      ring
    linarith
  calc
    H x = x * Real.log x⁻¹ + (1 - x) * Real.log (1 - x)⁻¹ := by
      simp [H, Real.binEntropy]
    _ = x * Real.log (1 / x) + (1 - x) * Real.log (1 - x)⁻¹ := by
      rw [one_div]
    _ ≤ x * Real.log (1 / x) + x := by linarith

lemma s4_term_info_le (Q : QData) (m : ℕ) (pUse : ℝ) :
  pUse = Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m:ℝ) + 1)) →
  pUse * (m : ℝ) ≤ effEnv 4 Q.sigma m + 1 := by
  intro hpUse
  subst pUse
  let a : ℝ := effEnv 3 Q.sigma m
  let n : ℝ := (m : ℝ)
  have hn1pos : 0 < n + 1 := by positivity
  have hn1nonneg : 0 ≤ n + 1 := le_of_lt hn1pos
  have heff4 : effEnv 4 Q.sigma m = effGeo (effEnv 3 Q.sigma) m := rfl
  by_cases hb : 0 ≤ a + 1
  · have hsqrt_le : Real.sqrt ((a + 1) / (n + 1)) * n ≤
        Real.sqrt ((a + 1) * (n + 1)) := by
      rw [Real.sqrt_div hb (n + 1)]
      rw [Real.sqrt_mul' (a + 1) hn1nonneg]
      have hsqrtn_pos : 0 < Real.sqrt (n + 1) := by
        rw [Real.sqrt_pos]
        exact hn1pos
      have hn_div_le : n / Real.sqrt (n + 1) ≤ Real.sqrt (n + 1) := by
        rw [div_le_iff₀ hsqrtn_pos]
        have hsq : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 :=
          Real.mul_self_sqrt hn1nonneg
        nlinarith
      calc
        Real.sqrt (a + 1) / Real.sqrt (n + 1) * n
            = Real.sqrt (a + 1) * (n / Real.sqrt (n + 1)) := by ring
        _ ≤ Real.sqrt (a + 1) * Real.sqrt (n + 1) :=
            mul_le_mul_of_nonneg_left hn_div_le (Real.sqrt_nonneg _)
    have hmax : Real.sqrt ((a + 1) * (n + 1)) ≤ effGeo (effEnv 3 Q.sigma) m := by
      dsimp [a, n]
      unfold effGeo
      exact le_max_right _ _
    calc
      Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) * (m : ℝ)
          = Real.sqrt ((a + 1) / (n + 1)) * n := rfl
      _ ≤ Real.sqrt ((a + 1) * (n + 1)) := hsqrt_le
      _ ≤ effGeo (effEnv 3 Q.sigma) m := hmax
      _ ≤ effEnv 4 Q.sigma m + 1 := by rw [heff4]; linarith
  · have hbnonpos : a + 1 ≤ 0 := le_of_not_ge hb
    have hratio_nonpos : (a + 1) / (n + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hbnonpos hn1nonneg
    have hsqrt_zero : Real.sqrt ((a + 1) / (n + 1)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hratio_nonpos
    have hgeo_nonneg : 0 ≤ effGeo (effEnv 3 Q.sigma) m := effGeo_nonneg _ _
    calc
      Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) * (m : ℝ)
          = Real.sqrt ((a + 1) / (n + 1)) * n := rfl
      _ = 0 := by rw [hsqrt_zero, zero_mul]
      _ ≤ effEnv 4 Q.sigma m + 1 := by rw [heff4]; linarith

lemma s4_epsFlat_pos_le (s m : ℝ) :
    0 ≤ s → 0 ≤ m →
    0 ≤ Real.sqrt ((s + 1) / (m + 1)) := by
  intro hs hm
  positivity

lemma s4_term_tail_le_concrete (p : ℝ) (hp : 0 < p) (m : ℕ) :
    2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ 16 / p := by
  let y : ℝ := p * (m : ℝ) / 8
  have hy_le_exp : y ≤ Real.exp y := by
    have h1 : y ≤ y + 1 := by linarith
    exact h1.trans (Real.add_one_le_exp y)
  have hy_exp_le_one : y * Real.exp (-y) ≤ 1 := by
    calc
      y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) := by
        exact mul_le_mul_of_nonneg_right hy_le_exp (Real.exp_pos _).le
      _ = 1 := by
        rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero y)]
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hconst_nonneg : 0 ≤ 16 / p := by positivity
  have hrewrite :
      2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) =
        (16 / p) * (y * Real.exp (-y)) := by
    dsimp [y]
    field_simp [hp_ne]
    ring
  rw [hrewrite]
  calc
    (16 / p) * (y * Real.exp (-y)) ≤ (16 / p) * 1 := by
      exact mul_le_mul_of_nonneg_left hy_exp_le_one hconst_nonneg
    _ = 16 / p := by ring

lemma s4_term_tail_le (p : ℝ) :
    0 < p →
    ∃ C', ∀ m : ℕ,
      2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ C' := by
  intro hp
  exact ⟨16 / p, s4_term_tail_le_concrete p hp⟩

lemma s4_rpow_half_le_sqrt_of_le {x B : ℝ} (hxB : x ≤ B) :
    x ^ (1 / 2 : ℝ) ≤ Real.sqrt B := by
  by_cases hx0 : 0 ≤ x
  · rw [← Real.sqrt_eq_rpow x]
    exact Real.sqrt_le_sqrt hxB
  · have hxneg : x < 0 := lt_of_not_ge hx0
    rw [Real.rpow_def_of_neg hxneg]
    rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring]
    rw [Real.cos_pi_div_two]
    simp [Real.sqrt_nonneg]

lemma s4_errorBound_grade (Q : QData) (C eps p : ℝ) :
    0 < p → 0 < eps →
    ∃ C', ∀ m : ℕ,
      s4_errorBound (eps / 4) (fun _ _ => C * (effEnv 3 Q.sigma m + 1)) p m ≤
        C' * (effEnv 4 Q.sigma m + 1) := by
  intro hp heps
  let Aconst : ℝ := |C| / p + 16 / p ^ 2
  refine ⟨(4 / eps) * (Aconst + 1), ?_⟩
  intro m
  let E3 : ℝ := effEnv 3 Q.sigma m
  let G : ℝ := effEnv 4 Q.sigma m
  let base : ℝ :=
    (C * (E3 + 1) / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) *
      (m : ℝ)
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have heps_ne : eps ≠ 0 := ne_of_gt heps
  have hE3_nonneg : 0 ≤ E3 := by
    change 0 ≤ effEnv 3 Q.sigma m
    exact s4_eff3_nonneg Q.sigma m
  have hG_nonneg : 0 ≤ G := by
    change 0 ≤ effEnv 4 Q.sigma m
    rw [show effEnv 4 Q.sigma = effGeo (effEnv 3 Q.sigma) by rfl]
    exact effGeo_nonneg _ _
  have hsqrtG : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ G := by
    change Real.sqrt ((effEnv 3 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
      effEnv 4 Q.sigma m
    rw [show effEnv 4 Q.sigma = effGeo (effEnv 3 Q.sigma) by rfl]
    unfold effGeo
    exact le_max_right _ _
  have hz_nonneg : 0 ≤ (E3 + 1) * ((m : ℝ) + 1) := by positivity
  have hE3m_le_Gsq : (E3 + 1) * (m : ℝ) ≤ G ^ 2 := by
    have hmle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have h1 : (E3 + 1) * (m : ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hmle (by positivity)
    have h2 : (E3 + 1) * ((m : ℝ) + 1) ≤ G ^ 2 := by
      have hs := Real.sq_sqrt hz_nonneg
      nlinarith [hsqrtG, hG_nonneg, Real.sqrt_nonneg ((E3 + 1) * ((m : ℝ) + 1)),
        hs]
    exact h1.trans h2
  have hm_le_Gsq : (m : ℝ) ≤ G ^ 2 := by
    have h1 : (m : ℝ) ≤ (E3 + 1) * (m : ℝ) := by
      nlinarith
    exact h1.trans hE3m_le_Gsq
  have htail16 :
      2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ 16 / p :=
    s4_term_tail_le_concrete p hp m
  have hCterm : C * (E3 + 1) / p * (m : ℝ) ≤ (|C| / p) * G ^ 2 := by
    have hC_le_abs : C ≤ |C| := le_abs_self C
    have hmul : C * (E3 + 1) ≤ |C| * (E3 + 1) := by
      exact mul_le_mul_of_nonneg_right hC_le_abs (by positivity)
    have hdiv : C * (E3 + 1) / p ≤ |C| * (E3 + 1) / p := by
      exact div_le_div_of_nonneg_right hmul hp_nonneg
    calc
      C * (E3 + 1) / p * (m : ℝ) ≤ (|C| * (E3 + 1) / p) * (m : ℝ) := by
        exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = (|C| / p) * ((E3 + 1) * (m : ℝ)) := by ring
      _ ≤ (|C| / p) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left hE3m_le_Gsq (by positivity)
  have hTailterm :
      (2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ) ≤
        (16 / p ^ 2) * G ^ 2 := by
    calc
      (2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)
          = (2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)) / p * (m : ℝ) := by
              ring
      _ ≤ (16 / p) / p * (m : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right htail16 hp_nonneg) (by positivity)
      _ = (16 / p ^ 2) * (m : ℝ) := by field_simp [hp_ne]
      _ ≤ (16 / p ^ 2) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left hm_le_Gsq (by positivity)
  have hbase_expand :
      base =
        C * (E3 + 1) / p * (m : ℝ) +
          (2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ) := by
    dsimp [base]
    ring
  have hGsq_le : G ^ 2 ≤ (G + 1) ^ 2 := by nlinarith [hG_nonneg]
  have hAconst_nonneg : 0 ≤ Aconst := by
    dsimp [Aconst]
    positivity
  have hbase_le : base ≤ Aconst * (G + 1) ^ 2 := by
    rw [hbase_expand]
    calc
      C * (E3 + 1) / p * (m : ℝ) +
          (2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)
          ≤ (|C| / p) * G ^ 2 + (16 / p ^ 2) * G ^ 2 := add_le_add hCterm hTailterm
      _ = Aconst * G ^ 2 := by
          dsimp [Aconst]
          ring
      _ ≤ Aconst * (G + 1) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hGsq_le hAconst_nonneg
  have hrpow_le : base ^ (1 / 2 : ℝ) ≤ (Aconst + 1) * (G + 1) := by
    have hsqrt_bound :
        Real.sqrt (Aconst * (G + 1) ^ 2) ≤ (Aconst + 1) * (G + 1) := by
      rw [Real.sqrt_le_left]
      · nlinarith [hAconst_nonneg, hG_nonneg]
      · positivity
    exact (s4_rpow_half_le_sqrt_of_le hbase_le).trans hsqrt_bound
  have hden_pos : 0 < eps / 4 := by positivity
  unfold s4_errorBound
  dsimp [E3, G, base] at *
  change
    (((C * (effEnv 3 Q.sigma m + 1) / p +
          2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)) ^
        (1 / 2 : ℝ)) / (eps / 4) ≤
      (4 / eps) * (Aconst + 1) * (effEnv 4 Q.sigma m + 1)
  rw [div_le_iff₀ hden_pos]
  have hmul :
      ((4 / eps) * (Aconst + 1) * (effEnv 4 Q.sigma m + 1)) * (eps / 4) =
        (Aconst + 1) * (effEnv 4 Q.sigma m + 1) := by
    field_simp [heps_ne]
  rw [hmul]
  exact hrpow_le

lemma s4_errorBound_nonneg (w : ℝ) (vFam : ℝ → ℕ → ℝ) (p : ℝ) (m : ℕ)
    (hw : 0 < w) (hp0 : 0 < p) (hv : 0 ≤ vFam (p / 2) m) :
    0 ≤ s4_errorBound w vFam p m := by
  dsimp [s4_errorBound]
  positivity

lemma s4_fixedDensity_entropy_bound_eff (m : ℕ) (A : Finset (Cube m)) (w p : ℝ)
    (hw : 0 < w) (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (vFam : ℝ → ℕ → ℝ)
    (hv_nonneg : 0 ≤ vFam (p / 2) m)
    (hA : A.Nonempty)
    (hvar : varianceBudgetLE A (p / 2) (vFam (p / 2) m))
    (hS3 : S3Statement)
    (sS : ℝ)
    (hsS : 0 ≤ sS)
    (hflat : ∀ I : Finset (Fin m),
      p * (m : ℝ) / 2 ≤ (I.card : ℝ) →
      (I.card : ℝ) ≤ 2 * p * (m : ℝ) →
      uH A (proj I) ≤ Real.log 2 * (I.card : ℝ) + sS) :
    ∃ o : ℝ, 0 ≤ o ∧ o < w ∧
      uH A (binnedFoldField A w o) ≤
        2 * Real.log 2 * p * (m : ℝ) + sS +
        (m : ℝ) * H (min (s4_errorBound w vFam p m / (m : ℝ)) (1 / 2)) +
        s4_errorBound w vFam p m * Real.log (max 1 (1 / w + 2)) +
        2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
  rcases s4_offset_exists m A w p hw hp0 hp1 vFam hv_nonneg hA hvar with ⟨o, ho1, ho2, G, hG_dep, hG_err⟩
  use o
  refine ⟨ho1, ho2, ?_⟩
  let e := s4_errorBound w vFam p m
  let BSize := max 1 (1 / w + 2)
  have h_BSize_ge_1 : 1 ≤ BSize := le_max_left 1 _
  have h_e_nonneg : 0 ≤ e := s4_errorBound_nonneg w vFam p m hw hp0 hv_nonneg
  have h_kappa_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hp_half : p ≤ 1 / 2 := hp1.trans (by norm_num)
  have hbinnedFold_size : ∀ t : Fin m, ((@Finset.image (Cube m) ℤ (fun a b => Classical.propDecidable (a = b)) (fun x => binnedFoldField A w o x t) A).card : ℝ) ≤ BSize := by
    intro t
    have h1 := s4_binnedFoldField_size m A w o hw t
    have h2 : @Finset.image (Cube m) ℤ (fun a b => Classical.propDecidable (a = b)) (fun x => binnedFoldField A w o x t) A = @Finset.image (Cube m) ℤ Int.instDecidableEq (fun x => binnedFoldField A w o x t) A := by
      ext x
      simp
    rw [h2]
    exact h1
  exact hS3 m A (Real.log 2) sS ℤ (binnedFoldField A w o) p e BSize hA h_kappa_nonneg hsS hp0 hp_half h_e_nonneg h_BSize_ge_1 hflat hbinnedFold_size ⟨G, hG_dep, hG_err⟩

lemma s4_log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  by_cases hx4 : x ≤ 4
  · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hsle2 : Real.sqrt x ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · norm_num
        exact hx4
    have hlogs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hspos
    have hlogeq : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (le_of_lt hxpos)]
      ring
    calc
      Real.log x = 2 * Real.log (Real.sqrt x) := hlogeq
      _ ≤ 2 * (Real.sqrt x - 1) := by nlinarith
      _ ≤ Real.sqrt x := by nlinarith
  · have hx_ge4 : 4 ≤ x := le_of_not_ge hx4
    by_cases hxexp : x ≤ Real.exp 2
    · have hlogle2 : Real.log x ≤ 2 := by
        exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hx)).mpr hxexp
      have hsqrtge2 : 2 ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) (le_trans (by norm_num) hx_ge4)]
        norm_num
        exact hx_ge4
      linarith
    · have hx_exp : Real.exp 2 ≤ x := le_of_not_ge hxexp
      have hanti := Real.log_div_sqrt_antitoneOn
        (show Real.exp 2 ∈ {x : ℝ | Real.exp 2 ≤ x} by simp)
        (show x ∈ {x : ℝ | Real.exp 2 ≤ x} by simpa using hx_exp) hx_exp
      have hbase : Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) ≤ 1 := by
        rw [Real.log_exp, ← Real.exp_half]
        norm_num
        have h2le : (2 : ℝ) ≤ Real.exp 1 := by
          simpa using (Real.two_mul_le_exp (x := 1))
        rw [div_le_one (Real.exp_pos 1)]
        exact h2le
      have hratio : Real.log x / Real.sqrt x ≤ 1 := le_trans hanti hbase
      have hspos : 0 < Real.sqrt x :=
        Real.sqrt_pos.mpr (lt_of_lt_of_le (Real.exp_pos 2) hx_exp)
      exact (div_le_one hspos).mp hratio

lemma s4_binEntropy_le_two_mul_sqrt (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
  H y ≤ 2 * Real.sqrt y := by
  by_cases hy0 : y = 0
  · simp [hy0, H]
  by_cases hhalf : y ≤ 1 / 2
  · have hypos : 0 < y := lt_of_le_of_ne h0 (Ne.symm hy0)
    have hone_sub_pos : 0 < 1 - y := by linarith
    have hloginv : Real.log y⁻¹ ≤ Real.sqrt y⁻¹ := by
      apply s4_log_le_sqrt_of_one_le
      rw [one_le_inv₀ hypos]
      exact h1
    have hterm1 : y * Real.log y⁻¹ ≤ Real.sqrt y := by
      calc
        y * Real.log y⁻¹ ≤ y * Real.sqrt y⁻¹ :=
          mul_le_mul_of_nonneg_left hloginv h0
        _ = Real.sqrt y := by
          rw [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]
    have hlog2 : Real.log (1 - y)⁻¹ ≤ (1 - y)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hone_sub_pos)
    have hterm2 : (1 - y) * Real.log (1 - y)⁻¹ ≤ y := by
      calc
        (1 - y) * Real.log (1 - y)⁻¹ ≤ (1 - y) * ((1 - y)⁻¹ - 1) :=
          mul_le_mul_of_nonneg_left hlog2 (by linarith)
        _ = y := by
          field_simp [ne_of_gt hone_sub_pos]
          ring
    have hy_le_sqrt : y ≤ Real.sqrt y := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [h0, h1]
    unfold H Real.binEntropy
    nlinarith
  · have hhalf' : 1 / 2 ≤ y := le_of_not_ge hhalf
    have hHle : H y ≤ Real.log 2 := by
      unfold H
      exact Real.binEntropy_le_log_two
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hsqrtgehalf : (1 / 2 : ℝ) ≤ Real.sqrt y := by
      rw [Real.le_sqrt (by norm_num) h0]
      nlinarith
    nlinarith

/-- v0.3.6: conclusion at grade 5 (was 4 — REFUTED by the E3 Aristotle
pass: `m·H(e/m)` at `e ~ effEnv 4` carries a log factor over grade 4).
Route: `m·H(min(e/m,1/2)) ≤ 2√(e·m) ≤ 2√C·√((E₄+1)(m+1)) ≤ 2√C·(E₅+1)`
via `H x ≤ 2√x` and `effGeo`. -/
lemma s4_fano_term_le (Q : QData) (C : ℝ) :
    ∃ C', ∀ m : ℕ, ∀ e : ℝ,
      0 ≤ e → e ≤ C * (effEnv 4 Q.sigma m + 1) →
      (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) ≤ C' * (effEnv 5 Q.sigma m + 1) := by
  use 2 * Real.sqrt C
  intro m e he0 heC
  let y := min (e / (m : ℝ)) (1 / 2)
  have hy0 : 0 ≤ y := by
    dsimp [y]; apply le_min
    · exact div_nonneg he0 (Nat.cast_nonneg m)
    · norm_num
  have hy1 : y ≤ 1 := by
    dsimp [y]; linarith [min_le_right (e / (m : ℝ)) (1 / 2)]
  have hH : H y ≤ 2 * Real.sqrt y := s4_binEntropy_le_two_mul_sqrt y hy0 hy1
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h_bound1 : (m : ℝ) * H y ≤ (m : ℝ) * (2 * Real.sqrt y) := by
    exact mul_le_mul_of_nonneg_left hH hm0
  have h_bound2 : (m : ℝ) * (2 * Real.sqrt y) = 2 * ((m : ℝ) * Real.sqrt y) := by ring
  have hyle : y ≤ e / (m : ℝ) := min_le_left _ _
  have hsqrt_y_le : Real.sqrt y ≤ Real.sqrt (e / (m : ℝ)) := Real.sqrt_le_sqrt hyle
  have h_bound3 : 2 * ((m : ℝ) * Real.sqrt y) ≤ 2 * ((m : ℝ) * Real.sqrt (e / (m : ℝ))) := by
    gcongr
  by_cases hm0_eq : (m : ℝ) = 0
  · rw [hm0_eq]
    simp
    have heff50 : 0 ≤ effEnv 5 Q.sigma m := by
      rw [effEnv_succ]
      exact effGeo_nonneg _ _
    positivity
  have hmpos : 0 < (m : ℝ) := lt_of_le_of_ne hm0 (Ne.symm hm0_eq)
  have h_sqrt_e_m : (m : ℝ) * Real.sqrt (e / (m : ℝ)) = Real.sqrt (e * (m : ℝ)) := by
    calc (m : ℝ) * Real.sqrt (e / (m : ℝ))
      _ = Real.sqrt ((m : ℝ) ^ 2) * Real.sqrt (e / (m : ℝ)) := by
        rw [Real.sqrt_sq hm0]
      _ = Real.sqrt ((m : ℝ) ^ 2 * (e / (m : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (e * (m : ℝ)) := by
        congr 1
        calc (m : ℝ) ^ 2 * (e / (m : ℝ)) = ((m : ℝ) * (m : ℝ)) * (e / (m : ℝ)) := by ring
          _ = (m : ℝ) * ((m : ℝ) * (e / (m : ℝ))) := by ring
          _ = (m : ℝ) * e := by rw [mul_div_cancel₀ _ hm0_eq]
          _ = e * (m : ℝ) := by ring
  have h_e_m_le : e * (m : ℝ) ≤ (C * (effEnv 4 Q.sigma m + 1)) * ((m : ℝ) + 1) := by
    apply mul_le_mul heC
    · linarith
    · exact hm0
    · exact he0.trans heC
  have h_sqrt_em_le : Real.sqrt (e * (m : ℝ)) ≤ Real.sqrt ((C * (effEnv 4 Q.sigma m + 1)) * ((m : ℝ) + 1)) := by
    exact Real.sqrt_le_sqrt h_e_m_le
  have h_sqrt_split : Real.sqrt ((C * (effEnv 4 Q.sigma m + 1)) * ((m : ℝ) + 1)) = Real.sqrt C * Real.sqrt ((effEnv 4 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
    have hC0 : 0 ≤ C := by
      by_cases hC0' : 0 ≤ C
      · exact hC0'
      · have : C < 0 := lt_of_not_ge hC0'
        have : C * (effEnv 4 Q.sigma m + 1) < 0 := by
          have heff_nonneg : 0 ≤ effEnv 4 Q.sigma m := by
            rw [effEnv_succ]; exact effGeo_nonneg _ _
          nlinarith
        linarith
    rw [mul_assoc, Real.sqrt_mul hC0]
  have h_effGeo : Real.sqrt ((effEnv 4 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤ effGeo (effEnv 4 Q.sigma) m := by
    unfold effGeo
    exact le_max_right _ _
  have h_eff5 : effGeo (effEnv 4 Q.sigma) m = effEnv 5 Q.sigma m := by rfl
  calc (m : ℝ) * H y ≤ 2 * Real.sqrt (e * (m : ℝ)) := by linarith
    _ ≤ 2 * (Real.sqrt C * Real.sqrt ((effEnv 4 Q.sigma m + 1) * ((m : ℝ) + 1))) := by
      rw [← h_sqrt_split]
      gcongr
    _ ≤ 2 * (Real.sqrt C * effGeo (effEnv 4 Q.sigma) m) := by
      have hsqrtC0 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
      gcongr
    _ = 2 * Real.sqrt C * effEnv 5 Q.sigma m := by rw [h_eff5]; ring
    _ ≤ 2 * Real.sqrt C * (effEnv 5 Q.sigma m + 1) := by
      have heff50 : 0 ≤ effEnv 5 Q.sigma m := by
        rw [effEnv_succ]; exact effGeo_nonneg _ _
      have hsqrtC0 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
      nlinarith

noncomputable def s4_eff_p (Q : QData) (m : ℕ) : ℝ :=
  min (Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1))) (1 / 2)

lemma s4_eff_p_bounds (Q : QData) (m : ℕ) (hQ : validQData Q) :
    0 < s4_eff_p Q m ∧ s4_eff_p Q m ≤ 1 / 2 := by
  unfold s4_eff_p
  constructor
  · apply lt_min
    · apply Real.sqrt_pos.mpr
      apply div_pos
      · have henv : 0 ≤ effEnv 3 Q.sigma m :=
          effEnv_nonneg 3 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
        linarith
      · positivity
    · norm_num
  · exact min_le_right _ _

lemma s4_eff_exp_tail (m : ℕ) (p : ℝ) (hp : 0 < p)
    (hpl : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ p) :
    2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ 2048 := by
  set M : ℝ := (m : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  rcases eq_or_lt_of_le hM0 with h0 | hpos
  · rw [← h0]
    simp
  · have hmnat : 0 < m := by
      have h := hpos
      rw [hM] at h
      exact_mod_cast h
    have hM1 : 1 ≤ M := by
      rw [hM]
      exact_mod_cast hmnat
    have hMne : M ≠ 0 := ne_of_gt hpos
    set t : ℝ := p * M / 8 with ht
    have htpos : 0 < t := by
      rw [ht]
      positivity
    have hexp : t ^ 2 / 2 ≤ Real.exp t := by
      have := Real.quadratic_le_exp_of_nonneg (le_of_lt htpos)
      linarith
    have hexpneg : Real.exp (-t) ≤ 2 / t ^ 2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by positivity)]
      have hmm : (2 / t ^ 2) * Real.exp t ≥ (2 / t ^ 2) * (t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have h2 : (2 / t ^ 2) * (t ^ 2 / 2) = 1 := by
        field_simp
      linarith
    have hrw : -p * M / 8 = -t := by
      rw [ht]
      ring
    rw [hrw]
    have h1 : 2 * M * Real.exp (-t) ≤ 2 * M * (2 / t ^ 2) :=
      mul_le_mul_of_nonneg_left hexpneg (by positivity)
    have ht2 : t ^ 2 = p ^ 2 * M ^ 2 / 64 := by
      rw [ht]
      ring
    have hp2 : 1 / (4 * (M + 1)) ≤ p ^ 2 := by
      have hsq : (Real.sqrt (M + 1)) ^ 2 = M + 1 :=
        Real.sq_sqrt (by positivity)
      have hle : (1 / (2 * Real.sqrt (M + 1))) ^ 2 ≤ p ^ 2 := by
        apply sq_le_sq'
        · have : (0 : ℝ) ≤ 1 / (2 * Real.sqrt (M + 1)) := by positivity
          linarith [hpl]
        · exact hpl
      calc
        1 / (4 * (M + 1)) = (1 / (2 * Real.sqrt (M + 1))) ^ 2 := by
          rw [div_pow, one_pow, mul_pow, hsq]
          ring
        _ ≤ p ^ 2 := hle
    have hpM : 1 ≤ 8 * p ^ 2 * M := by
      have hstep := mul_le_mul_of_nonneg_right hp2 (by positivity : (0 : ℝ) ≤ 8 * M)
      have hlhs : 1 / (4 * (M + 1)) * (8 * M) = 2 * M / (M + 1) := by
        field_simp
        ring
      have hge : 1 ≤ 2 * M / (M + 1) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hrhs : p ^ 2 * (8 * M) = 8 * p ^ 2 * M := by ring
      rw [hlhs, hrhs] at hstep
      linarith
    have hfin : 2 * M * (2 / t ^ 2) ≤ 2048 := by
      have hval : 2 * M * (2 / t ^ 2) = 256 / (p ^ 2 * M) := by
        rw [ht2]
        field_simp
        ring
      rw [hval, div_le_iff₀ (by positivity)]
      nlinarith [hpM]
    linarith

lemma s4_eff_exp_remainder (Q : QData) (hQ : validQData Q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℕ, 2 * (m : ℝ) * Real.exp (-s4_eff_p Q m * (m : ℝ) / 8) ≤ C := by
  refine ⟨2048, by norm_num, ?_⟩
  intro m
  have hs : 0 ≤ effEnv 3 Q.sigma m :=
    effEnv_nonneg 3 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  have hp : 0 < s4_eff_p Q m := (s4_eff_p_bounds Q m hQ).1
  have hmc : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hpl : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ s4_eff_p Q m := by
    unfold s4_eff_p
    have hm1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
      calc
        (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
        _ ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hspos : 0 < Real.sqrt ((m : ℝ) + 1) := by
      apply Real.sqrt_pos.mpr
      positivity
    apply le_min
    · have hmono : Real.sqrt (1 / ((m : ℝ) + 1)) ≤
          Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) := by
        apply Real.sqrt_le_sqrt
        gcongr
        linarith
      have heq : Real.sqrt (1 / ((m : ℝ) + 1)) =
          1 / Real.sqrt ((m : ℝ) + 1) := by
        rw [one_div, Real.sqrt_inv, one_div]
      have hstep : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤
          1 / Real.sqrt ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hspos
        linarith
      rw [heq] at hmono
      linarith
    · apply one_div_le_one_div_of_le (by norm_num)
      linarith
  exact s4_eff_exp_tail m (s4_eff_p Q m) hp hpl

/-- One grading step, squared. -/
lemma s4_env_geo_sq (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (k n : ℕ) :
    (effEnv k s n + 1) * ((n : ℝ) + 1) ≤ (effEnv (k + 1) s n + 1) ^ 2 := by
  have hr : Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1)) ≤ effEnv (k + 1) s n := by
    rw [effEnv_succ]; exact le_max_right _ _
  have hrpos : 0 ≤ Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1)) := Real.sqrt_nonneg _
  have hnn : 0 ≤ (effEnv k s n + 1) * ((n : ℝ) + 1) :=
    mul_nonneg (by have := effEnv_nonneg k s hs n; linarith) (by positivity)
  have hsq : (Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1))) ^ 2 =
      (effEnv k s n + 1) * ((n : ℝ) + 1) := Real.sq_sqrt hnn
  nlinarith [hr, hrpos, hsq]

lemma s4_env_mono_grade (s : ℕ → ℝ) (k n : ℕ) :
    effEnv k s n ≤ effEnv (k + 1) s n := by
  rw [effEnv_succ]; exact le_effGeo _ _

/-- `(effEnv 2 + 1)(m+1) ≤ (effEnv 3 + 1)(effEnv 4 + 1)`. -/
lemma s4_env_need1 (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (m : ℕ) :
    (effEnv 2 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 3 s m + 1) * (effEnv 4 s m + 1) := by
  have hgeo : (effEnv 2 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 3 s m + 1) ^ 2 :=
    s4_env_geo_sq s hs 2 m
  have hmono : effEnv 3 s m ≤ effEnv 4 s m := s4_env_mono_grade s 3 m
  have h3 : 0 ≤ effEnv 3 s m := effEnv_nonneg 3 s hs m
  nlinarith [hgeo, hmono, h3]

/-- `(m+1) ≤ (effEnv 3 + 1)(effEnv 4 + 1)`. -/
lemma s4_env_need3 (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (m : ℕ) :
    ((m : ℝ) + 1) ≤ (effEnv 3 s m + 1) * (effEnv 4 s m + 1) := by
  have hgeo : (effEnv 2 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 3 s m + 1) ^ 2 :=
    s4_env_geo_sq s hs 2 m
  have hmono : effEnv 3 s m ≤ effEnv 4 s m := s4_env_mono_grade s 3 m
  have h2 : 0 ≤ effEnv 2 s m := effEnv_nonneg 2 s hs m
  have h3 : 0 ≤ effEnv 3 s m := effEnv_nonneg 3 s hs m
  nlinarith [hgeo, hmono, h2, h3]

/-- Upper bound on `1/p²` for the effective `p = s4_eff_p`. -/
lemma s4_eff_invsq_le (Q : QData) (hQ : validQData Q) (m : ℕ) :
    1 / (s4_eff_p Q m) ^ 2 ≤ ((m : ℝ) + 1) / (effEnv 3 Q.sigma m + 1) + 4 := by
  have hs : 0 ≤ effEnv 3 Q.sigma m :=
    effEnv_nonneg 3 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  unfold s4_eff_p
  set s := effEnv 3 Q.sigma m with hsdef
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  set a := Real.sqrt ((s + 1) / ((m : ℝ) + 1)) with ha
  have ha2 : a ^ 2 = (s + 1) / ((m : ℝ) + 1) := by rw [ha]; exact Real.sq_sqrt (by positivity)
  rcases le_total a (1 / 2) with hle | hge
  · rw [min_eq_left hle, ha2, one_div_div]; linarith
  · rw [min_eq_right hge]; norm_num
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) / (s + 1) := by positivity
    linarith

/-- The clamped schedule density `min (s4_eff_p Q m) (1/3)`. -/
noncomputable def s4_eff_pC (Q : QData) (m : ℕ) : ℝ :=
  min (s4_eff_p Q m) (1 / 3)

lemma s4_eff_pC_bounds (Q : QData) (m : ℕ) (hQ : validQData Q) :
    0 < s4_eff_pC Q m ∧ s4_eff_pC Q m ≤ 1 / 3 := by
  refine ⟨?_, min_le_right _ _⟩
  exact lt_min (s4_eff_p_bounds Q m hQ).1 (by norm_num)

/-- Info-term bound for the clamped schedule: `pC * m ≤ 3 (effEnv 4 + 1)`. -/
lemma s4_eff_pC_mul_le (Q : QData) (m : ℕ) (hQ : validQData Q) :
    s4_eff_pC Q m * (m : ℝ) ≤ 3 * (effEnv 4 Q.sigma m + 1) := by
  have hinfo : Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) * (m : ℝ)
      ≤ effEnv 4 Q.sigma m + 1 := s4_term_info_le Q m _ rfl
  have hpc_le : s4_eff_pC Q m ≤ Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) := by
    unfold s4_eff_pC s4_eff_p
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hpc_nonneg : 0 ≤ s4_eff_pC Q m := le_of_lt (s4_eff_pC_bounds Q m hQ).1
  have hmul : s4_eff_pC Q m * (m : ℝ)
      ≤ Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right hpc_le (Nat.cast_nonneg m)
  have hE4 : 0 ≤ effEnv 4 Q.sigma m :=
    effEnv_nonneg 4 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  linarith [hmul, hinfo]

/-
Tail bound for the clamped schedule: `2 m exp(-pC m /8) ≤ 2048`.
-/
lemma s4_eff_pC_exp_remainder (Q : QData) (m : ℕ) (hQ : validQData Q) :
    2 * (m : ℝ) * Real.exp (-s4_eff_pC Q m * (m : ℝ) / 8) ≤ 2048 := by
  by_cases hm : m ≤ 1;
  · interval_cases m <;> norm_num;
    exact le_trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| by linarith [ show 0 ≤ s4_eff_pC Q 1 by exact le_of_lt <| s4_eff_pC_bounds Q 1 hQ |>.1 ] ) zero_le_two ) ( by norm_num );
  · have h_exp : 1 / (2 * Real.sqrt (m + 1)) ≤ s4_eff_pC Q m := by
      refine' le_min _ _;
      · refine' le_min _ _;
        · refine' Real.le_sqrt_of_sq_le _;
          rw [ div_pow, mul_pow, Real.sq_sqrt <| by positivity ];
          rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast; linarith, show ( effEnv 3 Q.sigma m : ℝ ) ≥ 0 by exact s4_eff3_nonneg _ _ ];
        · exact one_div_le_one_div_of_le ( by positivity ) ( by nlinarith [ Real.sqrt_nonneg ( m + 1 : ℝ ), Real.sq_sqrt ( by positivity : 0 ≤ ( m : ℝ ) + 1 ), show ( m : ℝ ) ≥ 2 by norm_cast; linarith ] );
      · rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( m + 1 : ℝ ), Real.sq_sqrt ( show 0 ≤ ( m : ℝ ) + 1 by positivity ), show ( m : ℝ ) ≥ 2 by norm_cast; linarith ];
    convert s4_eff_exp_tail m ( s4_eff_pC Q m ) ( by linarith [ s4_eff_pC_bounds Q m hQ ] ) h_exp using 1

/-
Pure envelope arithmetic underlying the grade-4 error bound.
-/
lemma s4_error_base_arith (KV E2 E3 E4 mm base : ℝ)
    (hKV : 1 ≤ KV) (hE2 : 0 ≤ E2) (hE23 : E2 ≤ E3) (hE34 : E3 ≤ E4) (hmm : 0 ≤ mm)
    (hgeo2 : (E2 + 1) * (mm + 1) ≤ (E3 + 1) ^ 2)
    (hgeo3 : (E3 + 1) * (mm + 1) ≤ (E4 + 1) ^ 2)
    (hbase : base ≤ (2 * KV * (E2 + 1) + 16) * ((mm + 1) / (E3 + 1) + 13) * mm) :
    base ≤ (28 * KV + 224) * (E4 + 1) ^ 2 := by
  refine le_trans hbase ?_;
  rw [ div_add', mul_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> try nlinarith;
  have h_expand : (2 * KV * (E2 + 1) + 16) * (mm + 1 + 13 * (E3 + 1)) * mm ≤ (2 * KV * (E2 + 1) + 16) * (mm + 1) * (13 * (E3 + 1) + mm) := by
    nlinarith [ mul_nonneg ( show 0 ≤ KV by linarith ) ( show 0 ≤ E2 + 1 by linarith ) ];
  refine le_trans h_expand ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hgeo3 <| by positivity ) <| by linarith );
  have h_expand : (2 * KV * (E2 + 1) + 16) * (13 * (E3 + 1) + mm) ≤ (28 * KV + 224) * (E3 + 1) ^ 2 := by
    nlinarith [ mul_le_mul_of_nonneg_left hE23 ( show 0 ≤ KV by linarith ), mul_le_mul_of_nonneg_left hE34 ( show 0 ≤ KV by linarith ), mul_le_mul_of_nonneg_left hE23 ( show 0 ≤ E3 + 1 by linarith ), mul_le_mul_of_nonneg_left hE34 ( show 0 ≤ E3 + 1 by linarith ) ];
  nlinarith only [ h_expand, hmm, hE2, hE23, hE34, hKV ]

/-
Upper bound on `1/pC²` for the clamped schedule.
-/
lemma s4_eff_pC_invsq_le (Q : QData) (hQ : validQData Q) (m : ℕ) :
    1 / (s4_eff_pC Q m) ^ 2 ≤ ((m : ℝ) + 1) / (effEnv 3 Q.sigma m + 1) + 13 := by
  rw [ s4_eff_pC ];
  cases le_total ( s4_eff_p Q m ) ( 1 / 3 ) <;> simp +decide [ * ];
  · rw [ min_eq_left ] <;> norm_num at *;
    · have := s4_eff_invsq_le Q hQ m;
      norm_num at * ; linarith!;
    · linarith;
  · rw [ min_eq_right ] <;> norm_num;
    · exact le_add_of_nonneg_of_le ( div_nonneg ( by positivity ) ( add_nonneg ( effGeo_nonneg _ _ ) zero_le_one ) ) ( by norm_num );
    · linarith

/-
Grade-4 error bound: with a grade-2 variance family, the S4 canonical
estimator error at the clamped schedule is bounded by `(K_err / w)(effEnv 4 + 1)`.
-/
lemma s4_eff_error_grade4 (Q : QData) (hQ : validQData Q) (K_V : ℝ) (hKV : 1 ≤ K_V) :
    ∃ K_err : ℝ, 1 ≤ K_err ∧
      ∀ (m : ℕ) (w : ℝ), 0 < w → ∀ (vFam : ℝ → ℕ → ℝ),
        (0 ≤ vFam (s4_eff_pC Q m / 2) m) →
        (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 →
          vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1)) →
        s4_errorBound w vFam (s4_eff_pC Q m) m
          ≤ (K_err / w) * (effEnv 4 Q.sigma m + 1) := by
  refine' ⟨ Max.max 1 ( Real.sqrt ( 28 * K_V + 224 ) ), _, _ ⟩ <;> norm_num at *;
  intros m w hw vFam hv_nonneg hv_bound
  set p := s4_eff_pC Q m
  set E2 := effEnv 2 Q.sigma m
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  have hp0 : 0 < p := by
    exact s4_eff_pC_bounds Q m hQ |>.1
  have hp3 : p ≤ 1 / 3 := by
    exact s4_eff_pC_bounds Q m hQ |>.2
  have hE2 : 0 ≤ E2 := by
    exact HarperStability.effEnv_nonneg 2 Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) m
  have hE3 : 0 ≤ E3 := by
    exact HarperStability.effEnv_nonneg 3 Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) m |> fun h => h.trans' ( by norm_num ) ;
  have hE4 : 0 ≤ E4 := by
    exact HarperStability.effEnv_nonneg _ Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) _
  have hE23 : E2 ≤ E3 := by
    exact s4_env_mono_grade Q.sigma 2 m
  have hE34 : E3 ≤ E4 := by
    exact s4_env_mono_grade Q.sigma 3 m
  have hgeo2 : (E2 + 1) * (m + 1) ≤ (E3 + 1) ^ 2 := by
    apply s4_env_geo_sq Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) 2 m
  have hgeo3 : (E3 + 1) * (m + 1) ≤ (E4 + 1) ^ 2 := by
    convert s4_env_geo_sq Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) 3 m using 1
  have hInv : 1 / p ^ 2 ≤ (m + 1) / (E3 + 1) + 13 := by
    convert s4_eff_pC_invsq_le Q hQ m using 1;
  -- Let `base := (V/p + 2*(m:ℝ)/p*Real.exp (-p*(m:ℝ)/8)) * (m:ℝ)`.
  set base := (vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ);
  -- By `s4_error_base_arith`, we have `base ≤ (28*K_V+224)*(E4+1)^2`.
  have hbase : base ≤ (28 * K_V + 224) * (E4 + 1) ^ 2 := by
    apply s4_error_base_arith K_V E2 E3 E4 m base hKV hE2 hE23 hE34 (Nat.cast_nonneg m) hgeo2 hgeo3;
    have hbase : vFam (p / 2) m / p ≤ 2 * K_V * (E2 + 1) * (1 / p ^ 2) := by
      have hbase : vFam (p / 2) m ≤ (2 * K_V / p) * (E2 + 1) := by
        convert hv_bound ( p / 2 ) ( by positivity ) ( by linarith ) using 1 ; ring!;
      convert div_le_div_of_nonneg_right hbase hp0.le using 1 ; ring;
    have htail : 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8) ≤ 16 * (1 / p ^ 2) := by
      have := s4_term_tail_le_concrete p hp0 m;
      convert mul_le_mul_of_nonneg_right this ( show 0 ≤ 1 / p by positivity ) using 1 <;> ring;
    exact mul_le_mul_of_nonneg_right ( by nlinarith [ show 0 ≤ 2 * K_V * ( E2 + 1 ) by positivity ] ) ( Nat.cast_nonneg m );
  -- By `s4_rpow_half_le_sqrt_of_le`, we have `base^(1/2:ℝ) ≤ Real.sqrt ((28*K_V+224)*(E4+1)^2)`.
  have hbase_sqrt : base ^ (1 / 2 : ℝ) ≤ Real.sqrt ((28 * K_V + 224) * (E4 + 1) ^ 2) := by
    rw [ ← Real.sqrt_eq_rpow ] ; exact Real.sqrt_le_sqrt hbase;
  convert div_le_div_of_nonneg_right hbase_sqrt hw.le using 1 ; norm_num [ Real.sqrt_mul ( show 0 ≤ 28 * K_V + 224 by positivity ), Real.sqrt_sq ( show 0 ≤ E4 + 1 by positivity ) ] ; ring!;
  rw [ max_eq_right ( Real.le_sqrt_of_sq_le ( by linarith ) ) ] ; ring!;

/-
For a bin width larger than the range of `fold`, the binned fold field with
offset `0` is constant, hence has zero entropy.
-/
lemma s4_uH_binnedFold_trivial (m : ℕ) (A : Finset (Cube m)) (w : ℝ)
    (hw : 1 / 2 < w) :
    uH A (binnedFoldField A w 0) = 0 := by
  -- Since `w > 1/2`, for any `x : Cube m` and `t : Fin m`, `fold (rho A t (proj (below Finset.univ t) x)) / w < 1`.
  have h_fold_div_w_lt_one (x : Cube m) (t : Fin m) : fold (rho A t (proj (below Finset.univ t) x)) / w < 1 := by
    rw [ div_lt_iff₀ ] <;> linarith [ HarperStability.fold_rho_bounds m A t ( proj ( below Finset.univ t ) x ) ];
  -- Since `fold (rho A t (proj (below Finset.univ t) x)) / w ≥ 0`, we have `Int.floor (fold (rho A t (proj (below Finset.univ t) x)) / w) = 0`.
  have h_floor_zero (x : Cube m) (t : Fin m) : Int.floor (fold (rho A t (proj (below Finset.univ t) x)) / w) = 0 := by
    exact Int.floor_eq_zero_iff.mpr ⟨ div_nonneg ( fold_rho_bounds m A t ( proj ( below Finset.univ t ) x ) |>.1 ) ( by linarith ), h_fold_div_w_lt_one x t ⟩;
  unfold binnedFoldField; simp +decide [ * ] ;
  unfold uH; simp +decide [Real.negMulLog] ;
  rw [ Finset.sum_eq_single ( fun _ => 0 ) ] <;> norm_num [ pOn ]

/-- Integer-power `eps` comparisons on `(0, 4]`. -/
lemma s4_eps_inv_le (eps : ℝ) (heps : 0 < eps) (heps4 : eps ≤ 4) :
    (1 : ℝ) ≤ 256 / eps ^ 4 ∧ 1 / eps ≤ 4 / eps ^ 2 ∧ 1 / eps ^ 2 ≤ 16 / eps ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ heps.le heps4 4]
  · rw [div_le_div_iff₀ heps (by positivity)]
    nlinarith [mul_nonneg heps.le (show (0:ℝ) ≤ 4 - eps by linarith)]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg heps.le heps.le) (show (0:ℝ) ≤ 16 - eps^2 by nlinarith [heps.le, heps4])]

/-- Half-power `eps` comparison on `(0, 4]`: `1/√eps ≤ 128/eps⁴`. -/
lemma s4_eps_sqrt_le (eps : ℝ) (heps : 0 < eps) (heps4 : eps ≤ 4) :
    1 / Real.sqrt eps ≤ 128 / eps ^ 4 := by
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.mpr heps
  have hsq : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have hsge : eps / 2 ≤ Real.sqrt eps := by
    nlinarith [hsq, hs.le, heps.le]
  rw [div_le_div_iff₀ hs (by positivity)]
  have h1 : eps ^ 4 ≤ 64 * eps := by nlinarith [pow_le_pow_left₀ heps.le heps4 3, heps.le]
  nlinarith [hsge, h1, heps.le]

/-
The S3 Fano term, bounded at grade 5 with the explicit `eps⁻⁴` factor.
-/
lemma s4_fano_bound (Kerr eps E4 E5 mm e : ℝ)
    (hKerr : 1 ≤ Kerr) (heps : 0 < eps) (heps4 : eps ≤ 4)
    (hE4 : 0 ≤ E4) (hE45 : E4 ≤ E5) (hmm : 0 ≤ mm)
    (hgeo : (E4 + 1) * (mm + 1) ≤ (E5 + 1) ^ 2)
    (he0 : 0 ≤ e) (he : e ≤ (4 * Kerr / eps) * (E4 + 1)) :
    mm * H (min (e / mm) (1 / 2)) ≤ (512 * Real.sqrt Kerr) / eps ^ 4 * (E5 + 1) := by
  -- Let `y := min (e/mm) (1/2)`. We'll prove the required chain of inequalities by first bounding `mm * Real.sqrt y`.
  set y := min (e / mm) (1 / 2)
  have hy0 : 0 ≤ y := by
    exact le_min ( div_nonneg he0 hmm ) ( by norm_num )
  have hy1 : y ≤ 1 := by
    exact le_trans ( min_le_right _ _ ) ( by norm_num )
  have hyle : y ≤ e / mm := by
    exact min_le_left _ _
  have hH_le : H y ≤ 2 * Real.sqrt y := by
    exact s4_binEntropy_le_two_mul_sqrt y hy0 ( by linarith [ min_le_right ( e / mm ) ( 1 / 2 ) ] );
  -- Now bound `mm * Real.sqrt y`:
  have h_sqrt_step : mm * Real.sqrt y ≤ Real.sqrt (e * mm) := by
    refine Real.le_sqrt_of_sq_le ?_;
    by_cases hmm : mm = 0 <;> simp_all +decide [mul_pow];
    rw [ le_div_iff₀ ( by positivity ) ] at hyle ; nlinarith [ mul_self_pos.mpr hmm ]
  have h_sqrt_bound : Real.sqrt (e * mm) ≤ Real.sqrt (4 * Kerr / eps * (E5 + 1)^2) := by
    exact Real.sqrt_le_sqrt <| by nlinarith [ show 0 ≤ 4 * Kerr / eps by positivity ] ;
  have h_sqrt_final : Real.sqrt (4 * Kerr / eps * (E5 + 1)^2) = 2 * Real.sqrt Kerr / Real.sqrt eps * (E5 + 1) := by
    rw [ Real.sqrt_mul <| by positivity, Real.sqrt_div <| by positivity, Real.sqrt_mul <| by positivity, Real.sqrt_sq <| by linarith ] ; ring
  have h_final : 2 * Real.sqrt Kerr / Real.sqrt eps ≤ 256 * Real.sqrt Kerr / eps^4 := by
    have := s4_eps_sqrt_le eps heps heps4;
    convert mul_le_mul_of_nonneg_left this ( show 0 ≤ 2 * Real.sqrt Kerr by positivity ) using 1 <;> ring;
  ring_nf at *; nlinarith [ show 0 ≤ Real.sqrt Kerr * ( E5 + 1 ) by exact mul_nonneg ( Real.sqrt_nonneg _ ) ( by linarith ) ] ;

/-
The S3 field-entropy term, bounded at grade 5 with the explicit `eps⁻⁴` factor.
-/
lemma s4_errlog_bound (Kerr eps E4 E5 e : ℝ)
    (hKerr : 1 ≤ Kerr) (heps : 0 < eps) (heps4 : eps ≤ 4)
    (hE4 : 0 ≤ E4) (hE45 : E4 ≤ E5)
    (he0 : 0 ≤ e) (he : e ≤ (4 * Kerr / eps) * (E4 + 1)) :
    e * Real.log (max 1 (1 / (eps / 4) + 2)) ≤ (768 * Kerr) / eps ^ 4 * (E5 + 1) := by
  rw [ max_eq_right ];
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by positivity ) ) _;
    refine le_trans ( mul_le_mul_of_nonneg_right he ( by nlinarith [ one_div_mul_cancel ( by positivity : ( eps / 4 ) ≠ 0 ) ] ) ) ?_;
    field_simp;
    nlinarith [ mul_le_mul_of_nonneg_left heps4 ( show 0 ≤ E4 + 1 by linarith ), mul_le_mul_of_nonneg_left heps4 ( show 0 ≤ eps by linarith ), mul_le_mul_of_nonneg_left heps4 ( show 0 ≤ eps ^ 2 by positivity ) ];
  · rw [ div_add', le_div_iff₀ ] <;> nlinarith

set_option maxHeartbeats 1200000 in
lemma s4_rate_gap_certificate (Q : QData) (hQ : validQData Q)
  (hS3 : S3Statement)
  (hVar : ∃ K_V, 1 ≤ K_V ∧ ∀ m A q, A.Nonempty → fat Q m A q →
            pinned Q m A q → ∃ vFam : ℝ → ℕ → ℝ,
              (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
                  varianceBudgetLE A pLow (vFam pLow m)) ∧
              (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
                  vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1))) :
  ∃ K, 1 ≤ K ∧ ∀ eps, 0 < eps → ∀ m A q, A.Nonempty →
    fat Q m A q → pinned Q m A q →
    ∃ o, 0 ≤ o ∧ o < eps/4 ∧
      uH A (binnedFoldField A (eps/4) o) ≤
        (K / eps^4) * (effEnv 5 Q.sigma m + 1) := by
  classical
  obtain ⟨K_V, hKV, hvar_all⟩ := hVar
  obtain ⟨K_err, hKerr, herr⟩ := s4_eff_error_grade4 Q hQ K_V hKV
  have hsig : ∀ n, 0 ≤ Q.sigma n := fun n => hQ.2.2.2.2.2.2.1.1 n
  refine ⟨max 1 (1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288),
    le_max_left _ _, ?_⟩
  intro eps heps m A q hA hfat hpin
  set E4 := effEnv 4 Q.sigma m with hE4def
  set E5 := effEnv 5 Q.sigma m with hE5def
  have hE4nn : 0 ≤ E4 := effEnv_nonneg 4 Q.sigma hsig m
  have hE5nn : 0 ≤ E5 := effEnv_nonneg 5 Q.sigma hsig m
  have hE45 : E4 ≤ E5 := s4_env_mono_grade Q.sigma 4 m
  set K := max 1 (1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288) with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKbound : 1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288 ≤ K :=
    le_max_right _ _
  clear_value K
  have hRHSnn : 0 ≤ (K / eps ^ 4) * (E5 + 1) := by
    have : 0 < eps ^ 4 := by positivity
    have hKnn : 0 ≤ K := by linarith
    positivity
  by_cases hbig : 4 ≤ eps
  · -- large `eps`: one bin, zero entropy
    refine ⟨0, le_refl _, by linarith, ?_⟩
    have hw : 1 / 2 < eps / 4 := by linarith
    rw [s4_uH_binnedFold_trivial m A (eps / 4) hw]
    exact hRHSnn
  · -- small `eps`: run the S3 route at the clamped schedule
    have hsmall : eps < 4 := lt_of_not_ge hbig
    obtain ⟨vFam0, hvb1, hvb2⟩ := hvar_all m A q hA hfat hpin
    set vFam := fun p n => max 0 (vFam0 p n) with hvFdef
    have hvnn : ∀ pLow, 0 ≤ vFam pLow m := fun _ => le_max_left _ _
    have hvar1 : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 →
        varianceBudgetLE A pLow (vFam pLow m) := by
      intro pL h1 h2 W hW1 hW2
      exact le_trans (hvb1 pL h1 h2 W hW1 hW2) (le_max_right _ _)
    have hE2nn : 0 ≤ effEnv 2 Q.sigma m := effEnv_nonneg 2 Q.sigma hsig m
    have hvar2 : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 →
        vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1) := by
      intro pL h1 h2
      refine max_le ?_ (hvb2 pL h1 h2)
      have : 0 ≤ (K_V / pL) * (effEnv 2 Q.sigma m + 1) :=
        mul_nonneg (div_nonneg (by linarith) h1.le) (by linarith)
      exact this
    set pC := s4_eff_pC Q m with hpCdef
    obtain ⟨hpC0, hpC3⟩ := s4_eff_pC_bounds Q m hQ
    have hpChalf : pC ≤ 1 / 2 := le_trans hpC3 (by norm_num)
    have hpC2pos : 0 < pC / 2 := by positivity
    have hpC2half : pC / 2 ≤ 1 / 2 := by linarith
    have hw : 0 < eps / 4 := by linarith
    obtain ⟨o, ho0, how, houH⟩ :=
      s4_fixedDensity_entropy_bound_eff m A (eps / 4) pC hw hpC0 hpC3 vFam
        (hvnn (pC / 2)) hA (hvar1 (pC / 2) hpC2pos hpC2half) hS3 0 le_rfl
        (fun I _ _ => by
          have := uH_proj_le_I_log_two m A hA I; linarith)
    refine ⟨o, ho0, how, ?_⟩
    set e := s4_errorBound (eps / 4) vFam pC m with hedef
    have he0 : 0 ≤ e := s4_errorBound_nonneg (eps / 4) vFam pC m hw hpC0 (hvnn (pC / 2))
    have he : e ≤ (4 * K_err / eps) * (E4 + 1) := by
      have hb := herr m (eps / 4) hw vFam (hvnn (pC / 2)) hvar2
      have hrw : K_err / (eps / 4) = 4 * K_err / eps := by
        rw [div_div_eq_mul_div]; ring
      rw [hrw] at hb
      exact hb
    -- eps arithmetic facts
    obtain ⟨hEps1, hEps2, hEps3⟩ := s4_eps_inv_le eps heps hsmall.le
    -- geo bound for the Fano term
    have hgeo4 : (E4 + 1) * ((m : ℝ) + 1) ≤ (E5 + 1) ^ 2 := s4_env_geo_sq Q.sigma hsig 4 m
    -- term bounds
    have hlog2nn : 0 ≤ Real.log 2 := by positivity
    have hterm1 : 2 * Real.log 2 * pC * (m : ℝ)
        ≤ (1536 * Real.log 2) / eps ^ 4 * (E5 + 1) := by
      have hpm : pC * (m : ℝ) ≤ 3 * (E4 + 1) := s4_eff_pC_mul_le Q m hQ
      have hprod := mul_le_mul_of_nonneg_left hpm (show (0:ℝ) ≤ 2 * Real.log 2 by positivity)
      have hA1 : 2 * Real.log 2 * pC * (m : ℝ) ≤ 6 * Real.log 2 * (E4 + 1) := by
        nlinarith [hprod]
      have hA2 : 6 * Real.log 2 * (E4 + 1) ≤ 6 * Real.log 2 * (E5 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hc : 6 * Real.log 2 ≤ (1536 * Real.log 2) / eps ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [pow_le_pow_left₀ heps.le hsmall.le 4, hlog2nn]
      have hA3 : 6 * Real.log 2 * (E5 + 1) ≤ (1536 * Real.log 2) / eps ^ 4 * (E5 + 1) :=
        mul_le_mul_of_nonneg_right hc (by linarith)
      linarith
    have htermFano : (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
        ≤ (512 * Real.sqrt K_err) / eps ^ 4 * (E5 + 1) :=
      s4_fano_bound K_err eps E4 E5 (m : ℝ) e hKerr heps hsmall.le hE4nn hE45
        (Nat.cast_nonneg m) hgeo4 he0 he
    have htermErr : e * Real.log (max 1 (1 / (eps / 4) + 2))
        ≤ (768 * K_err) / eps ^ 4 * (E5 + 1) :=
      s4_errlog_bound K_err eps E4 E5 e hKerr heps hsmall.le hE4nn hE45 he0 he
    have htermTail : 2 * (m : ℝ) * Real.exp (-pC * (m : ℝ) / 8)
        ≤ (524288) / eps ^ 4 * (E5 + 1) := by
      have ht := s4_eff_pC_exp_remainder Q m hQ
      have hc : (2048 : ℝ) ≤ (524288) / eps ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [pow_le_pow_left₀ heps.le hsmall.le 4]
      have hmul : (524288 : ℝ) / eps ^ 4 * 1 ≤ (524288) / eps ^ 4 * (E5 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hstep : (2048 : ℝ) ≤ (524288) / eps ^ 4 * (E5 + 1) := by
        have h1 : (524288 : ℝ) / eps ^ 4 * 1 = (524288) / eps ^ 4 := by ring
        linarith [hmul, hc, h1]
      linarith
    -- combine
    have hsum : (1536 * Real.log 2) / eps ^ 4 * (E5 + 1)
        + (512 * Real.sqrt K_err) / eps ^ 4 * (E5 + 1)
        + (768 * K_err) / eps ^ 4 * (E5 + 1)
        + (524288) / eps ^ 4 * (E5 + 1)
        ≤ (K / eps ^ 4) * (E5 + 1) := by
      have hcoef : 1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288 ≤ K :=
        hKbound
      have hfac : 0 ≤ (E5 + 1) / eps ^ 4 := by positivity
      have hexpand :
          (1536 * Real.log 2) / eps ^ 4 * (E5 + 1)
          + (512 * Real.sqrt K_err) / eps ^ 4 * (E5 + 1)
          + (768 * K_err) / eps ^ 4 * (E5 + 1)
          + (524288) / eps ^ 4 * (E5 + 1)
          = (1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288)
              * ((E5 + 1) / eps ^ 4) := by ring
      rw [hexpand]
      calc (1536 * Real.log 2 + 512 * Real.sqrt K_err + 768 * K_err + 524288)
              * ((E5 + 1) / eps ^ 4)
          ≤ K * ((E5 + 1) / eps ^ 4) := mul_le_mul_of_nonneg_right hcoef hfac
        _ = (K / eps ^ 4) * (E5 + 1) := by ring
    calc uH A (binnedFoldField A (eps / 4) o)
        ≤ 2 * Real.log 2 * pC * (m : ℝ) + 0
            + (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
            + e * Real.log (max 1 (1 / (eps / 4) + 2))
            + 2 * (m : ℝ) * Real.exp (-pC * (m : ℝ) / 8) := houH
      _ ≤ (1536 * Real.log 2) / eps ^ 4 * (E5 + 1)
            + (512 * Real.sqrt K_err) / eps ^ 4 * (E5 + 1)
            + (768 * K_err) / eps ^ 4 * (E5 + 1)
            + (524288) / eps ^ 4 * (E5 + 1) := by
          linarith [hterm1, htermFano, htermErr, htermTail]
      _ ≤ (K / eps ^ 4) * (E5 + 1) := hsum

/-! ### v0.3.6c — quarter-root schedule route (2026-07-11)

The iter-13 refutation stands: the grade-2/pLow variance family is FALSE
(pLow-free Pinsker term).  Moreover at the OLD √-schedule the honest error is
`⁴√((E₃+1)(m+1)³)`-sized — exactly grade 5 with NO room, so its Fano term
overflows grade 5 by a log.  The repair (hand-verified pointwise, sqrt-only):

* NEW schedule `s4_eff_p2 = min (⁴√((E₃+1)/(m+1))) (1/3)` (the old `s4_eff_p`
  and every lemma about it are kept untouched);
* honest TWO-TERM variance family `(K_V/pLow)·(E₂+1) + K_V·(E₃+1)`;
* the scheduled error is then `≤ (K/eps)·((E₄+1) + ⁸√((E₃+1)³(m+1)⁵))`,
  which sits STRICTLY inside grade 5 with `((m+1)/(E₃+1))^(1/8)` room;
* the Fano term absorbs its log pointwise:
  `log x ≤ 8·⁸√x` and `⁸√((E₃+1)³(m+1)⁵)·⁸√((m+1)/(E₃+1)) = ⁴√((E₃+1)(m+1)³)
  ≤ E₅ + 1`.
-/

/-- Fourth-root density schedule (v0.3.6c).  The `1/3` clamp keeps
`pLow = p/2 ≤ 1/6` inside every band the S1/S2 machinery uses. -/
noncomputable def s4_eff_p2 (Q : QData) (m : ℕ) : ℝ :=
  min (Real.sqrt (Real.sqrt ((effEnv 3 Q.sigma m + 1) / ((m : ℝ) + 1)))) (1 / 3)

lemma s4_eff_p2_bounds (Q : QData) (m : ℕ) :
    0 < s4_eff_p2 Q m ∧ s4_eff_p2 Q m ≤ 1 / 3 := by
  constructor
  · apply lt_min
    · apply Real.sqrt_pos.mpr
      apply Real.sqrt_pos.mpr
      apply div_pos
      · have := s4_eff3_nonneg Q.sigma m
        linarith
      · positivity
    · norm_num
  · exact min_le_right _ _

/-- Schedule–dimension product: `p₂·m ≤ ⁴√((E₃+1)(m+1)³)`. -/
lemma s4_p2_mul_le (Q : QData) (m : ℕ) :
    s4_eff_p2 Q m * (m : ℝ) ≤
      Real.sqrt (Real.sqrt ((effEnv 3 Q.sigma m + 1) * ((m : ℝ) + 1) ^ 3)) := by
  set E3 := effEnv 3 Q.sigma m
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hp2 : s4_eff_p2 Q m ≤ Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) :=
    min_le_left _ _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc4 : Real.sqrt (Real.sqrt ((((m : ℝ) + 1)) ^ 4)) = (m : ℝ) + 1 := by
    rw [show ((((m : ℝ) + 1)) ^ 4) = ((((m : ℝ) + 1)) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  have hmul : Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) * ((m : ℝ) + 1)
      = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1) * (((m : ℝ) + 1)) ^ 4)) := by
    symm
    calc Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1) * (((m : ℝ) + 1)) ^ 4))
        = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1)) *
            Real.sqrt ((((m : ℝ) + 1)) ^ 4)) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (E3 + 1) / ((m : ℝ) + 1))]
      _ = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) *
            Real.sqrt (Real.sqrt ((((m : ℝ) + 1)) ^ 4)) := by
          rw [Real.sqrt_mul (Real.sqrt_nonneg _)]
      _ = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) * ((m : ℝ) + 1) := by
          rw [hc4]
  have harg : (E3 + 1) / ((m : ℝ) + 1) * (((m : ℝ) + 1)) ^ 4
      = (E3 + 1) * ((m : ℝ) + 1) ^ 3 := by
    field_simp
  calc s4_eff_p2 Q m * (m : ℝ)
      ≤ Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) * ((m : ℝ) + 1) := by
        apply mul_le_mul hp2 (by linarith) hm0 (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) := by
        rw [hmul, harg]

/-- The quarter-root error scale is dominated by the grade-5 envelope. -/
lemma s4_quarterroot_le_env5 (Q : QData) (m : ℕ) :
    Real.sqrt (Real.sqrt ((effEnv 3 Q.sigma m + 1) * ((m : ℝ) + 1) ^ 3)) ≤
      effEnv 5 Q.sigma m + 1 := by
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set E5 := effEnv 5 Q.sigma m
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h4 : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := le_max_right _ _
  have h4' : (E3 + 1) * ((m : ℝ) + 1) ≤ (E4 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E3 + 1) * ((m : ℝ) + 1)), h4]
  have h5 : Real.sqrt ((E4 + 1) * ((m : ℝ) + 1)) ≤ E5 := le_max_right _ _
  have hstep1 : (E3 + 1) * ((m : ℝ) + 1) ^ 3 ≤ ((E4 + 1) * ((m : ℝ) + 1)) ^ 2 := by
    have hexp : (E3 + 1) * ((m : ℝ) + 1) ^ 3
        = ((E3 + 1) * ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ 2 := by ring
    rw [hexp, mul_pow]
    exact mul_le_mul_of_nonneg_right h4' (by positivity)
  have hstep2 : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3) ≤ (E4 + 1) * ((m : ℝ) + 1) := by
    calc Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)
        ≤ Real.sqrt (((E4 + 1) * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hstep1
      _ = (E4 + 1) * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)
  calc Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3))
      ≤ Real.sqrt ((E4 + 1) * ((m : ℝ) + 1)) := Real.sqrt_le_sqrt hstep2
    _ ≤ E5 := h5
    _ ≤ E5 + 1 := by linarith

/-- Pointwise logarithm absorption: `log x ≤ 8·⁸√x` for `1 ≤ x`. -/
lemma s4_log_le_eightroot (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hx0)]; ring
  have hs1 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h2 : Real.log (Real.sqrt x) = 2 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (le_of_lt hs1)]; ring
  have hs2 : (0 : ℝ) < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hs1
  have h3 : Real.log (Real.sqrt (Real.sqrt x))
      = 2 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt x))) := by
    rw [Real.log_sqrt (le_of_lt hs2)]; ring
  have hs3 : (0 : ℝ) < Real.sqrt (Real.sqrt (Real.sqrt x)) := Real.sqrt_pos.mpr hs2
  have h4 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt x)))
      ≤ Real.sqrt (Real.sqrt (Real.sqrt x)) - 1 :=
    Real.log_le_sub_one_of_pos hs3
  have h5 : Real.sqrt (Real.sqrt (Real.sqrt x)) - 1
      ≤ Real.sqrt (Real.sqrt (Real.sqrt x)) := by linarith
  calc Real.log x = 8 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt x))) := by
        rw [h1, h2, h3]; ring
    _ ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt x)) := by
        have := h4.trans h5
        linarith

/-- Square comparison. -/
lemma s4_le_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-- Fourth-power comparison. -/
lemma s4_le_of_pow4_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 ≤ b ^ 4) :
    a ≤ b := by
  have h2 : a ^ 2 ≤ b ^ 2 := by
    apply s4_le_of_sq_le (by positivity) (by positivity)
    calc (a ^ 2) ^ 2 = a ^ 4 := by ring
      _ ≤ b ^ 4 := h
      _ = (b ^ 2) ^ 2 := by ring
  exact s4_le_of_sq_le ha hb h2

set_option maxHeartbeats 800000 in
/-- Exponential tail: `y·e^{-y/8} ≤ 3`. -/
lemma s4_texp_le (y : ℝ) (hy : 0 ≤ y) : y * Real.exp (-(y / 8)) ≤ 3 := by
  have h1 : y / 8 ≤ Real.exp (y / 8 - 1) := by
    linarith [Real.add_one_le_exp (y / 8 - 1)]
  have h2 : Real.exp (y / 8 - 1) * Real.exp (-(y / 8)) = Real.exp (-1 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hne : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
  have h4 : Real.exp (-1 : ℝ) ≤ 3 / 8 := by
    nlinarith [h3, mul_le_mul_of_nonneg_left he (le_of_lt hne)]
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(y / 8)) := (Real.exp_pos _).le
  calc y * Real.exp (-(y / 8)) = 8 * ((y / 8) * Real.exp (-(y / 8))) := by ring
    _ ≤ 8 * (Real.exp (y / 8 - 1) * Real.exp (-(y / 8))) := by
        have := mul_le_mul_of_nonneg_right h1 hexp_nonneg
        linarith
    _ = 8 * Real.exp (-1 : ℝ) := by rw [h2]
    _ ≤ 8 * (3 / 8) := by linarith
    _ = 3 := by norm_num

set_option maxHeartbeats 1600000 in
/-- Honest uniform variance family (two-term; v0.3.6c).  Mirror the PROVED
`s4_fixedDensity_varianceBudget_eff` above with the `R3Eff` constant hoisted
out of the `pLow`-quantifier: obtain `K₃` from `hR3` ONCE, run the identical
S1/S2 argument with `K := K₃/pLow` and `K6 := 6·K₃`, and keep the
`pLow`-scaled block-regularity slack separate from the pLow-FREE
Pinsker/threshold terms (`epsS·m + count·log 2 ≤ c(K₃)·(E₃+1)` via
`√((sS+1)(m+1)) ≤ √(c)·(E₃+1)`). -/
lemma s4_eff_variance_twoterm (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) :
    ∃ K_V, 1 ≤ K_V ∧ ∀ m A q, A.Nonempty → fat Q m A q →
      pinned Q m A q → ∃ vFam : ℝ → ℕ → ℝ,
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 → 0 ≤ vFam pLow m) ∧
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
            varianceBudgetLE A pLow (vFam pLow m)) ∧
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
            vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1)
              + K_V * (effEnv 3 Q.sigma m + 1)) := by
  obtain ⟨K3, hK31, hR3b⟩ := hR3 Q.qMin Q.qMax Q.s0 Q.mu0 hQ.1 hQ.2.1 hQ.2.2.1
    hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1
  set K_V := 30 + K3 + 13 * Real.sqrt (6 * K3 + 1) with hKVdef
  have hsq0 : 0 ≤ Real.sqrt (6 * K3 + 1) := Real.sqrt_nonneg _
  have hKV1 : 1 ≤ K_V := by rw [hKVdef]; linarith
  refine ⟨K_V, hKV1, ?_⟩
  intro m A q hA hfat hpinned
  have hsig_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
  have hE2 : 0 ≤ effEnv 2 Q.sigma m := s4_eff2_nonneg Q.sigma m
  have hE3 : 0 ≤ effEnv 3 Q.sigma m := s4_eff3_nonneg Q.sigma m
  by_cases hm : m < 30
  · refine ⟨fun _ _ => (m : ℝ), ?_, ?_, ?_⟩
    · intro pLow hp1 hp2
      exact Nat.cast_nonneg m
    · intro pLow hp1 hp2 W hW1 hW2
      have h_sum_le_m : ∑ t ∈ W, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below W t)) ≤ m := by
        have h_sum_le_m : ∀ t ∈ W, uCondVar A (fun x => rho A t (proj (below Finset.univ t) x)) (proj (below W t)) ≤ 1 := by
          intro t ht
          have h_var_le_one : ∀ x ∈ A, (rho A t (proj (below Finset.univ t) x) - uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y))) ^ 2 ≤ 1 := by
            intro x hx
            have h_rho_bounds : 0 ≤ rho A t (proj (below Finset.univ t) x) ∧ rho A t (proj (below Finset.univ t) x) ≤ 1 := by
              exact ⟨ rho_nonneg A t _, rho_le_one A t _ ⟩;
            have h_uE_bounds : 0 ≤ uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y)) ∧ uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y)) ≤ 1 := by
              refine' ⟨ div_nonneg ( Finset.sum_nonneg fun _ _ => _ ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ _ ( Nat.cast_nonneg _ ) ⟩;
              · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
              · exact le_trans ( Finset.sum_le_sum fun _ _ => show rho A t ( proj ( below Finset.univ t ) _ ) ≤ 1 from by
                                                                grind +suggestions ) ( by norm_num );
            nlinarith only [ h_rho_bounds, h_uE_bounds ];
          have h_var_le_one : uE A (fun x => (rho A t (proj (below Finset.univ t) x) - uE (A.filter fun y => proj (below W t) y = proj (below W t) x) (fun y => rho A t (proj (below Finset.univ t) y))) ^ 2) ≤ 1 := by
            unfold uE; simp +decide [ * ] ;
            rw [ div_le_iff₀ ( Nat.cast_pos.mpr hA.card_pos ) ];
            convert Finset.sum_le_sum h_var_le_one using 1 ; norm_num [ uE ];
          convert h_var_le_one using 1;
          convert uCondVar_eq_uE_fiber_sq A _ _ using 1;
        exact le_trans ( Finset.sum_le_sum h_sum_le_m ) ( by norm_num; linarith [ show W.card ≤ m from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] );
      exact h_sum_le_m
    · intro pLow hp1 hp2
      have hm29 : (m : ℝ) ≤ 29 := by norm_cast; linarith
      have hfirst : 0 ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1) := by positivity
      have hsecond : 30 ≤ K_V * (effEnv 3 Q.sigma m + 1) := by
        have h1 : (30 : ℝ) ≤ K_V := by rw [hKVdef]; linarith
        nlinarith [hE3, hKV1]
      linarith
  · -- main branch: mirror of the fixed-density proof with the R3 constant hoisted
    set kappa := H q with hkappadef
    set sS := K3 / (1/6 : ℝ) * (effEnv 2 Q.sigma m + 1) + Q.sigma m with hsSdef
    set epsS := Real.sqrt ((sS + 1) / ((m : ℝ) + 1)) with hepsSdef
    have hsS_nonneg : 0 ≤ sS := by
      rw [hsSdef]
      have : 0 ≤ K3 / (1/6 : ℝ) := by positivity
      positivity
    have hepsS_pos : 0 < epsS := by
      rw [hepsSdef]
      apply Real.sqrt_pos.mpr
      positivity
    have hesq : epsS ^ 2 = (sS + 1) / ((m : ℝ) + 1) := by
      rw [hepsSdef, sq]
      exact Real.mul_self_sqrt (by positivity)
    have h_m30 : 30 ≤ m := not_lt.mp hm
    have h_m30_real : (30 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h_m30
    have hflat : ∀ I : Finset (Fin m), ((m / 5 : ℕ) : ℝ) ≤ I.card → I.card ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ) → uH A (proj I) ≤ kappa * (I.card : ℝ) + sS := by
      intros I hI1 hI2
      have hI_bounds : (1 / 6 : ℝ) * m ≤ I.card ∧ I.card ≤ (1 - 1 / 6 : ℝ) * m := by
        constructor <;> linarith [ show ( m : ℝ ) ≥ 30 by exact_mod_cast h_m30, show ( m / 5 : ℕ ) ≥ ( m : ℝ ) / 6 by exact by rw [ ge_iff_le ] ; rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod m 5, Nat.mod_lt m ( by norm_num : 5 > 0 ) ] ];
      have hbr := hR3b (1/6 : ℝ) (by norm_num) (by norm_num) Q.sigma
        hQ.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2 m A q hA hfat hpinned
      obtain ⟨ hI1', hI2', hI3 ⟩ := hbr
      linarith [ abs_le.mp ( hI3 I hI_bounds.1 hI_bounds.2 ), hsig_nonneg ]
    have hlow : kappa * (m : ℝ) - sS ≤ uH A (proj Finset.univ) := by
      have hlow0 : kappa * (m : ℝ) - Q.sigma m ≤ uH A (proj Finset.univ) := by
        have hfa := hfat.2.2.2.2
        rw [ uH_proj_univ A hA ]
        linarith [ abs_le.mp hfa ]
      have hK6E : 0 ≤ K3 / (1/6 : ℝ) * (effEnv 2 Q.sigma m + 1) := by positivity
      rw [hsSdef]
      linarith
    obtain ⟨count, hcount⟩ : ∃ count : ℝ, 0 ≤ count ∧ ((Finset.univ.filter (fun t => epsS ≤ |hstep A t - kappa|)).card : ℝ) ≤ count ∧ count ≤ 12 * sS / epsS + 4 := by
      refine' ⟨ _, _, le_rfl, _ ⟩
      · positivity
      · exact hS1 m A kappa sS epsS hA hsS_nonneg hepsS_pos hflat hlow
    refine ⟨fun pl _ => (K3 / pl * (effEnv 2 Q.sigma m + 1) + epsS * (m : ℝ) + count * Real.log 2) / 2, ?_, ?_, ?_⟩
    · intro pLow hp1 hp2
      have h1 : 0 ≤ K3 / pLow * (effEnv 2 Q.sigma m + 1) := by positivity
      have h2 : 0 ≤ epsS * (m : ℝ) := by positivity
      have h3 : 0 ≤ count * Real.log 2 :=
        mul_nonneg hcount.1 (Real.log_nonneg one_le_two)
      linarith
    · intro pLow hp1 hp2
      exact hS2 m A q pLow (K3 / pLow * (effEnv 2 Q.sigma m + 1)) epsS count hA hp1 hp2
        (by positivity) hepsS_pos hcount.1
        (hR3b pLow hp1 hp2 Q.sigma hQ.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2 m A q hA hfat hpinned)
        hcount.2.1
    · intro pLow hp1 hp2
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      have hlog2n : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
      have hm1p : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hsS1p : (0 : ℝ) < sS + 1 := by linarith
      -- epsS * m ≤ √((sS+1)(m+1))
      have hepsm : epsS * (m : ℝ) ≤ Real.sqrt ((sS + 1) * ((m : ℝ) + 1)) := by
        have hc2 : Real.sqrt (((m : ℝ) + 1) ^ 2) = (m : ℝ) + 1 :=
          Real.sqrt_sq (by positivity)
        have hstep : Real.sqrt ((sS + 1) / ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ 2)
            = epsS * ((m : ℝ) + 1) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (sS + 1) / ((m : ℝ) + 1)), hc2,
            hepsSdef]
        have harg : (sS + 1) / ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ 2
            = (sS + 1) * ((m : ℝ) + 1) := by
          field_simp
        have hmono : epsS * (m : ℝ) ≤ epsS * ((m : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hepsS_pos)
        rw [← hstep, harg] at hmono
        exact hmono
      -- sS / epsS ≤ √((sS+1)(m+1))
      have hsSeps : sS / epsS ≤ Real.sqrt ((sS + 1) * ((m : ℝ) + 1)) := by
        apply s4_le_of_sq_le (by positivity) (Real.sqrt_nonneg _)
        have hL : (sS / epsS) ^ 2 = sS ^ 2 / ((sS + 1) / ((m : ℝ) + 1)) := by
          rw [div_pow, hesq]
        have hRw : (Real.sqrt ((sS + 1) * ((m : ℝ) + 1))) ^ 2
            = (sS + 1) * ((m : ℝ) + 1) := by
          rw [sq]
          exact Real.mul_self_sqrt (by positivity)
        rw [hL, hRw, div_div_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < sS + 1)]
        nlinarith [hsS_nonneg, hm1p, sq_nonneg sS]
      -- √((sS+1)(m+1)) ≤ √(6K3+1)·(E3+1)
      have hkey : Real.sqrt ((sS + 1) * ((m : ℝ) + 1))
          ≤ Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1) := by
        have hsig_le : Q.sigma m ≤ effEnv 2 Q.sigma m := le_effEnv 2 Q.sigma m
        have hK6eq : K3 / (1/6 : ℝ) = 6 * K3 := by
          field_simp
        have hsS1 : sS + 1 ≤ (6 * K3 + 1) * (effEnv 2 Q.sigma m + 1) := by
          rw [hsSdef, hK6eq]
          nlinarith [hE2, hsig_le, hK31]
        have hmul : (sS + 1) * ((m : ℝ) + 1)
            ≤ (6 * K3 + 1) * ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
          nlinarith [mul_le_mul_of_nonneg_right hsS1 (le_of_lt hm1p)]
        have h3g : Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1))
            ≤ effEnv 3 Q.sigma m := le_max_right _ _
        calc Real.sqrt ((sS + 1) * ((m : ℝ) + 1))
            ≤ Real.sqrt ((6 * K3 + 1) * ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1))) :=
              Real.sqrt_le_sqrt hmul
          _ = Real.sqrt (6 * K3 + 1) *
              Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
              rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ 6 * K3 + 1)]
          _ ≤ Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1) := by
              apply mul_le_mul_of_nonneg_left (by linarith [h3g]) hsq0
      -- first term: (K3/pl)(E2+1)/2 ≤ (K_V/pl)(E2+1)
      have hfirst : K3 / pLow * (effEnv 2 Q.sigma m + 1) / 2
          ≤ K_V / pLow * (effEnv 2 Q.sigma m + 1) := by
        have hd : K3 / pLow ≤ K_V / pLow :=
          (div_le_div_iff_of_pos_right hp1).mpr (by rw [hKVdef]; linarith)
        have hprod := mul_le_mul_of_nonneg_right hd (by linarith : (0:ℝ) ≤ effEnv 2 Q.sigma m + 1)
        have hnn : 0 ≤ K3 / pLow * (effEnv 2 Q.sigma m + 1) := by positivity
        linarith
      -- second: (epsS·m + count·log2)/2 ≤ K_V(E3+1)
      have hsecond : (epsS * (m : ℝ) + count * Real.log 2) / 2
          ≤ K_V * (effEnv 3 Q.sigma m + 1) := by
        have hc1 : count * Real.log 2 ≤ (12 * sS / epsS + 4) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hcount.2.2 hlog2n
        have hc2 : (12 * sS / epsS + 4) * Real.log 2 ≤ 12 * (sS / epsS) + 4 := by
          have hd0 : 0 ≤ sS / epsS := div_nonneg hsS_nonneg (le_of_lt hepsS_pos)
          have hprod := mul_le_mul_of_nonneg_left hlog2 hd0
          have heq : 12 * sS / epsS = 12 * (sS / epsS) := by ring
          nlinarith [hprod, hd0, hlog2, hlog2n, heq]
        have hS := Real.sqrt_nonneg ((sS + 1) * ((m : ℝ) + 1))
        have hE31 : (1 : ℝ) ≤ effEnv 3 Q.sigma m + 1 := by linarith
        have hKV30 : (30 : ℝ) ≤ K_V := by rw [hKVdef]; linarith
        have h13 : 13 * Real.sqrt (6 * K3 + 1) ≤ K_V := by rw [hKVdef]; linarith
        have hkey13 : 13 * Real.sqrt ((sS + 1) * ((m : ℝ) + 1))
            ≤ 13 * Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1) := by
          calc 13 * Real.sqrt ((sS + 1) * ((m : ℝ) + 1))
              ≤ 13 * (Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1)) := by
                linarith [hkey]
            _ = 13 * Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1) := by ring
        have hKVE : 13 * Real.sqrt (6 * K3 + 1) * (effEnv 3 Q.sigma m + 1) + 4
            ≤ K_V * (effEnv 3 Q.sigma m + 1) + 4 := by
          have := mul_le_mul_of_nonneg_right h13 (by linarith : (0:ℝ) ≤ effEnv 3 Q.sigma m + 1)
          linarith
        -- total: epsS·m + count·log2 ≤ 13√ + 4 ≤ K_V(E3+1) + 4; and 4 ≤ ... absorb
        have habs : (4 : ℝ) ≤ K_V * (effEnv 3 Q.sigma m + 1) := by
          nlinarith [hKV30, hE31]
        nlinarith [hepsm, hc1, hc2, hsSeps, hkey13, hKVE, habs, hS]
      linarith [hfirst, hsecond]


set_option maxHeartbeats 1000000 in
/-- Pure-arithmetic core of the two-term error bound. -/
lemma s4_error_core (K_V E2 E3 E4 R Q2 Q4 ip mR X : ℝ)
    (hKV : 1 ≤ K_V) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3) (hE4 : 0 ≤ E4) (hR0 : 0 ≤ R)
    (hQ20 : 0 ≤ Q2) (hQ40 : 0 ≤ Q4) (hm0 : 0 ≤ mR) (hip0 : 0 < ip)
    (hip_le : ip ≤ Q4 + 3) (hip2_le : ip ^ 2 ≤ Q2 + 9)
    (hTA : (E2 + 1) * mR * Q2 ≤ (E4 + 1) ^ 2)
    (hTB : (E3 + 1) * mR * Q4 ≤ R ^ 2)
    (hMcap : mR ≤ (E4 + 1) ^ 2)
    (hE2m : (E2 + 1) * mR ≤ (E4 + 1) ^ 2)
    (hE3m : (E3 + 1) * mR ≤ (E4 + 1) ^ 2)
    (hmQ2 : mR * Q2 ≤ (E4 + 1) ^ 2)
    (hX : X ≤ 2 * K_V * (E2 + 1) * ip ^ 2 + K_V * (E3 + 1) * ip + 6 * ip ^ 2) :
    X * mR ≤ 83 * K_V * ((E4 + 1) + R) ^ 2 := by
  have hKV0 : (0 : ℝ) ≤ K_V := by linarith
  have t1 : (E2 + 1) * ip ^ 2 * mR ≤ 10 * (E4 + 1) ^ 2 := by
    have a1 := mul_le_mul_of_nonneg_left hip2_le
      (mul_nonneg (by linarith : (0:ℝ) ≤ E2 + 1) hm0)
    nlinarith [a1, hTA, hE2m]
  have t2 : (E3 + 1) * ip * mR ≤ R ^ 2 + 3 * (E4 + 1) ^ 2 := by
    have a2 := mul_le_mul_of_nonneg_left hip_le
      (mul_nonneg (by linarith : (0:ℝ) ≤ E3 + 1) hm0)
    nlinarith [a2, hTB, hE3m]
  have t3 : ip ^ 2 * mR ≤ 10 * (E4 + 1) ^ 2 := by
    have a3 := mul_le_mul_of_nonneg_left hip2_le hm0
    nlinarith [a3, hmQ2, hMcap]
  have hXm := mul_le_mul_of_nonneg_right hX hm0
  have u1 := mul_le_mul_of_nonneg_left t1
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hKV0)
  have u2 := mul_le_mul_of_nonneg_left t2 hKV0
  have u3 := mul_le_mul_of_nonneg_left t3 (by norm_num : (0:ℝ) ≤ 6)
  nlinarith [hXm, u1, u2, u3, hKV, hE4, hR0,
    mul_nonneg (mul_nonneg hKV0 (by linarith : (0:ℝ) ≤ E4 + 1)) hR0,
    sq_nonneg (E4 + 1), sq_nonneg R, mul_nonneg hE4 hR0]

set_option maxHeartbeats 2000000 in
lemma s4_eff_error_twoterm (Q : QData) (hQ : validQData Q)
    (K_V : ℝ) (hKV : 1 ≤ K_V) :
    ∃ K_err : ℝ, 1 ≤ K_err ∧
      ∀ m : ℕ, ∀ (vFam : ℝ → ℕ → ℝ),
        (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → 0 ≤ vFam pLow m) →
        (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 →
            vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1)
              + K_V * (effEnv 3 Q.sigma m + 1)) →
        ∀ eps > 0,
        s4_errorBound (eps / 4) vFam (s4_eff_p2 Q m) m ≤
          (K_err / eps) * ((effEnv 4 Q.sigma m + 1) +
            Real.sqrt (Real.sqrt (Real.sqrt
              ((effEnv 3 Q.sigma m + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)))) := by
  refine ⟨4 * Real.sqrt (83 * K_V), ?_, ?_⟩
  · have h81 : (81 : ℝ) ≤ 83 * K_V := by nlinarith
    have h9 : (9 : ℝ) ≤ Real.sqrt (83 * K_V) := by
      have h9' : (9 : ℝ) = Real.sqrt 81 := by
        rw [show (81 : ℝ) = 9 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9)]
      rw [h9']
      exact Real.sqrt_le_sqrt h81
    linarith
  intro m vFam hv0 hvle eps heps
  obtain ⟨hp0, hp13⟩ := s4_eff_p2_bounds Q m
  set p := s4_eff_p2 Q m with hpdef
  set E2 := effEnv 2 Q.sigma m
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set R := Real.sqrt (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)))
    with hRdef
  have hE2 : 0 ≤ E2 := s4_eff2_nonneg Q.sigma m
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have h34 : E3 ≤ E4 := le_effGeo (effEnv 3 Q.sigma) m
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hE3p : (0 : ℝ) < E3 + 1 := by linarith
  have hm1p : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hKV0 : (0 : ℝ) ≤ K_V := by linarith
  have hphalf_pos : 0 < p / 2 := by linarith
  have hphalf_le : p / 2 ≤ 1 / 2 := by linarith
  have hvS := hvle (p / 2) hphalf_pos hphalf_le
  have hv0S := hv0 (p / 2) hphalf_pos hphalf_le
  have h3g : Real.sqrt ((E2 + 1) * ((m : ℝ) + 1)) ≤ E3 := le_max_right _ _
  have h3sq : (E2 + 1) * ((m : ℝ) + 1) ≤ (E3 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E2 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E2 + 1) * ((m : ℝ) + 1)), h3g]
  have h4g : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := le_max_right _ _
  have h4sq : (E3 + 1) * ((m : ℝ) + 1) ≤ (E4 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E3 + 1) * ((m : ℝ) + 1)), h4g]
  have hE34 : (E3 + 1) ^ 3 * ((m : ℝ) + 1) ≤ (E4 + 1) ^ 4 := by
    rcases le_total (E3 + 1) ((m : ℝ) + 1) with hc | hc
    · nlinarith [pow_le_pow_left₀
        (by positivity : (0:ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1)) h4sq 2,
        hc, hE3, hm1p]
    · have h44 : (E3 + 1) ^ 4 ≤ (E4 + 1) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have hmc := mul_le_mul_of_nonneg_left hc
        (pow_nonneg (by linarith : (0:ℝ) ≤ E3 + 1) 3)
      nlinarith [h44, hmc, hE3, hm1p]
  set ratio := ((m : ℝ) + 1) / (E3 + 1) with hratiodef
  have hratio0 : (0 : ℝ) < ratio := by positivity
  set Q2 := Real.sqrt ratio with hQ2def
  set Q4 := Real.sqrt (Real.sqrt ratio) with hQ4def
  have hQ20 : 0 ≤ Q2 := Real.sqrt_nonneg _
  have hQ40 : 0 ≤ Q4 := Real.sqrt_nonneg _
  have hQ4sq : Q4 ^ 2 = Q2 := by
    rw [hQ4def, hQ2def, sq]
    exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hQ2sq : Q2 ^ 2 = ratio := by
    rw [hQ2def, sq]
    exact Real.mul_self_sqrt (le_of_lt hratio0)
  set ip := 1 / p with hipdef
  have hip0 : 0 < ip := by rw [hipdef]; positivity
  -- schedule inverse: ip = Q4 or ip = 3
  have hip_cases : ip = Q4 ∨ ip = 3 := by
    have hAinv : Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) * Q4 = 1 := by
      rw [hQ4def, hratiodef,
        ← Real.sqrt_mul (Real.sqrt_nonneg _),
        ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (E3 + 1) / ((m : ℝ) + 1))]
      rw [show (E3 + 1) / ((m : ℝ) + 1) * (((m : ℝ) + 1) / (E3 + 1)) = 1 by
        field_simp]
      simp
    have hpmin : p = min (Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1)))) ((1:ℝ)/3) :=
      rfl
    rcases min_cases (Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1)))) ((1:ℝ)/3) with
      ⟨hmin, _⟩ | ⟨hmin, _⟩
    · left
      have hp_eq : p = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) :=
        hpmin.trans hmin
      have hppos : 0 < Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) := by
        rw [← hp_eq]
        exact hp0
      rw [hipdef, hp_eq]
      rw [eq_comm, eq_div_iff (ne_of_gt hppos), mul_comm]
      exact hAinv
    · right
      have hp_eq : p = (1:ℝ)/3 := hpmin.trans hmin
      rw [hipdef, hp_eq]
      norm_num
  have hip_le : ip ≤ Q4 + 3 := by
    rcases hip_cases with h | h <;> rw [h] <;> linarith
  have hip2_le : ip ^ 2 ≤ Q2 + 9 := by
    rcases hip_cases with h | h
    · rw [h, hQ4sq]; linarith
    · rw [h]; norm_num; linarith
  -- tail
  have hpip : p * ip = 1 := by
    rw [hipdef]
    field_simp
  have htail : 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8) ≤ 6 * ip ^ 2 := by
    have hy : 0 ≤ p * (m : ℝ) := mul_nonneg (le_of_lt hp0) hm0
    have hexp := s4_texp_le (p * (m : ℝ)) hy
    have hexp_pos : 0 ≤ Real.exp (-(p * (m : ℝ) / 8)) := le_of_lt (Real.exp_pos _)
    have harg : -p * (m : ℝ) / 8 = -(p * (m : ℝ) / 8) := by ring
    have hdiv : 2 * (m : ℝ) / p = 2 * ((m : ℝ) * ip) := by
      rw [hipdef]; field_simp
    have hmip : (m : ℝ) * ip = p * (m : ℝ) * ip ^ 2 := by
      calc (m : ℝ) * ip = (p * ip) * ((m : ℝ) * ip) := by rw [hpip]; ring
        _ = p * (m : ℝ) * ip ^ 2 := by ring
    rw [harg, hdiv, hmip]
    calc 2 * (p * (m : ℝ) * ip ^ 2) * Real.exp (-(p * (m : ℝ) / 8))
        = 2 * ip ^ 2 * (p * (m : ℝ) * Real.exp (-(p * (m : ℝ) / 8))) := by ring
      _ ≤ 2 * ip ^ 2 * 3 :=
          mul_le_mul_of_nonneg_left hexp
            (by positivity : (0:ℝ) ≤ 2 * ip ^ 2)
      _ = 6 * ip ^ 2 := by ring
  -- vFam part
  have hvpart : vFam (p / 2) m / p ≤
      2 * K_V * (E2 + 1) * ip ^ 2 + K_V * (E3 + 1) * ip := by
    have h1 : K_V / (p / 2) = 2 * K_V * ip := by
      rw [hipdef]
      field_simp
    have h2 : vFam (p / 2) m / p = vFam (p / 2) m * ip := by
      rw [hipdef, mul_one_div]
    have h3 : vFam (p / 2) m ≤ 2 * K_V * ip * (E2 + 1) + K_V * (E3 + 1) := by
      have := hvS
      rw [h1] at this
      linarith
    rw [h2]
    calc vFam (p / 2) m * ip
        ≤ (2 * K_V * ip * (E2 + 1) + K_V * (E3 + 1)) * ip :=
          mul_le_mul_of_nonneg_right h3 (le_of_lt hip0)
      _ = 2 * K_V * (E2 + 1) * ip ^ 2 + K_V * (E3 + 1) * ip := by ring
  -- structural facts about R, then make the envelope variables opaque
  have hR2 : R ^ 2 = Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)) := by
    rw [hRdef, sq]
    exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hR24 : (R ^ 2) ^ 4 = (E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5 := by
    rw [hR2]
    rw [show (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) ^ 4
        = ((Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) ^ 2) ^ 2 by ring]
    rw [sq (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))),
      Real.mul_self_sqrt (Real.sqrt_nonneg _)]
    rw [sq (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)),
      Real.mul_self_sqrt (by positivity)]
  clear_value E2 E3 E4 R Q2 Q4 ratio ip p
  -- key envelope bounds
  have hTA : (E2 + 1) * (m : ℝ) * Q2 ≤ (E4 + 1) ^ 2 := by
    apply s4_le_of_sq_le (by positivity) (by positivity)
    have hexpand : ((E2 + 1) * (m : ℝ) * Q2) ^ 2
        = (E2 + 1) ^ 2 * (m : ℝ) ^ 2 * ratio := by
      rw [mul_pow, mul_pow, hQ2sq]
    rw [hexpand, hratiodef,
      show (E2 + 1) ^ 2 * (m : ℝ) ^ 2 * (((m : ℝ) + 1) / (E3 + 1))
        = ((E2 + 1) ^ 2 * (m : ℝ) ^ 2 * ((m : ℝ) + 1)) / (E3 + 1) by ring,
      div_le_iff₀ hE3p]
    have hh1 : ((E2 + 1) * ((m : ℝ) + 1)) ^ 2 ≤ ((E3 + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3sq 2
    have hmsq : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [hm0]
    have s1 : (E2 + 1) ^ 2 * (m : ℝ) ^ 2 * ((m : ℝ) + 1)
        ≤ (E2 + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hmsq
        (mul_nonneg (sq_nonneg (E2 + 1)) (le_of_lt hm1p))]
    have s2 : (E2 + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1)
        ≤ (E3 + 1) ^ 4 * ((m : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hh1 (le_of_lt hm1p)]
    have s3 : (E3 + 1) ^ 4 * ((m : ℝ) + 1) ≤ (E4 + 1) ^ 4 * (E3 + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hE34 (le_of_lt hE3p)]
    calc (E2 + 1) ^ 2 * (m : ℝ) ^ 2 * ((m : ℝ) + 1)
        ≤ (E3 + 1) ^ 4 * ((m : ℝ) + 1) := le_trans s1 s2
      _ ≤ (E4 + 1) ^ 4 * (E3 + 1) := s3
      _ = ((E4 + 1) ^ 2) ^ 2 * (E3 + 1) := by ring
  have hTB : (E3 + 1) * (m : ℝ) * Q4 ≤ R ^ 2 := by
    apply s4_le_of_pow4_le (by positivity) (by positivity)
    have hQ44 : Q4 ^ 4 = ratio := by
      rw [show Q4 ^ 4 = (Q4 ^ 2) ^ 2 by ring, hQ4sq, hQ2sq]
    have hL4 : ((E3 + 1) * (m : ℝ) * Q4) ^ 4
        = (E3 + 1) ^ 4 * (m : ℝ) ^ 4 * ratio := by
      rw [mul_pow, mul_pow, hQ44]
    rw [hL4, hR24, hratiodef,
      show (E3 + 1) ^ 4 * (m : ℝ) ^ 4 * (((m : ℝ) + 1) / (E3 + 1))
        = ((E3 + 1) ^ 4 * (m : ℝ) ^ 4 * ((m : ℝ) + 1)) / (E3 + 1) by ring,
      div_le_iff₀ hE3p]
    have hm4 : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 :=
      pow_le_pow_left₀ hm0 (by linarith) 4
    have hmul4 := mul_le_mul_of_nonneg_left hm4
      (pow_nonneg (le_of_lt hE3p) 4)
    nlinarith [hmul4, hm1p, pow_nonneg (le_of_lt hE3p) 4,
      pow_nonneg (le_of_lt hm1p) 4]
  -- caps
  -- deterministic caps
  have hMcap : (m : ℝ) ≤ (E4 + 1) ^ 2 := by
    have c1 : ((m : ℝ) + 1) ≤ (E3 + 1) * ((m : ℝ) + 1) :=
      le_mul_of_one_le_left (le_of_lt hm1p) (by linarith)
    linarith [h4sq]
  have hE2m : (E2 + 1) * (m : ℝ) ≤ (E4 + 1) ^ 2 := by
    have c1 : (E2 + 1) * (m : ℝ) ≤ (E2 + 1) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have c2 : (E3 + 1) ^ 2 ≤ (E4 + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith [h3sq]
  have hE3m : (E3 + 1) * (m : ℝ) ≤ (E4 + 1) ^ 2 := by
    have c1 : (E3 + 1) * (m : ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith [h4sq]
  have hmQ2 : (m : ℝ) * Q2 ≤ (E4 + 1) ^ 2 := by
    have c1 : (m : ℝ) * Q2 ≤ (E2 + 1) * ((m : ℝ) * Q2) :=
      le_mul_of_one_le_left (mul_nonneg hm0 hQ20) (by linarith)
    have c2 : (E2 + 1) * ((m : ℝ) * Q2) = (E2 + 1) * (m : ℝ) * Q2 := by ring
    linarith [hTA, c2 ▸ c1]
  -- slim the context for the final arithmetic
  clear hvS hv0S hpip hpdef hipdef hRdef hratiodef hQ2def hQ4def
  clear hQ2sq hQ4sq hR2 hR24 hip_cases h3g h4g
  -- assemble the inside of the root via the pure core
  have hb : vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)
      ≤ 2 * K_V * (E2 + 1) * ip ^ 2 + K_V * (E3 + 1) * ip + 6 * ip ^ 2 := by
    linarith [hvpart, htail]
  have hINS : (vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ)
      ≤ 83 * K_V * ((E4 + 1) + R) ^ 2 :=
    s4_error_core K_V E2 E3 E4 R Q2 Q4 ip (m : ℝ) _
      hKV hE2 hE3 hE4 hR0 hQ20 hQ40 hm0 hip0
      hip_le hip2_le hTA hTB hMcap hE2m hE3m hmQ2 hb
  -- descend through the square root
  have hnum := s4_rpow_half_le_sqrt_of_le hINS
  have hsqrtmul : Real.sqrt (83 * K_V * ((E4 + 1) + R) ^ 2)
      = Real.sqrt (83 * K_V) * ((E4 + 1) + R) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 83 * K_V),
      Real.sqrt_sq (by positivity)]
  show ((vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ))
        ^ ((1:ℝ)/2) / (eps / 4)
      ≤ 4 * Real.sqrt (83 * K_V) / eps * ((E4 + 1) + R)
  calc ((vFam (p / 2) m / p + 2 * (m : ℝ) / p * Real.exp (-p * (m : ℝ) / 8)) * (m : ℝ))
        ^ ((1:ℝ)/2) / (eps / 4)
      ≤ (Real.sqrt (83 * K_V) * ((E4 + 1) + R)) / (eps / 4) :=
        (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < eps / 4)).mpr
          (hnum.trans (le_of_eq hsqrtmul))
    _ = 4 * Real.sqrt (83 * K_V) / eps * ((E4 + 1) + R) := by
        field_simp

/-- Eighth roots multiply. -/
lemma s4_root8_mul (a b : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (Real.sqrt (Real.sqrt (a * b)))
      = Real.sqrt (Real.sqrt (Real.sqrt a)) *
        Real.sqrt (Real.sqrt (Real.sqrt b)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg a),
    Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- The eighth-root error scale is dominated by the grade-5 envelope. -/
lemma s4_eightroot_le_env5 (Q : QData) (m : ℕ) :
    Real.sqrt (Real.sqrt (Real.sqrt
      ((effEnv 3 Q.sigma m + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) ≤
      effEnv 5 Q.sigma m + 1 := by
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set E5 := effEnv 5 Q.sigma m
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have hE5 : 0 ≤ E5 := effGeo_nonneg _ _
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h45 : E4 ≤ E5 := le_effGeo (effEnv 4 Q.sigma) m
  have h4 : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := le_max_right _ _
  have h4' : (E3 + 1) * ((m : ℝ) + 1) ≤ (E4 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E3 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E3 + 1) * ((m : ℝ) + 1)), h4]
  have h5 : Real.sqrt ((E4 + 1) * ((m : ℝ) + 1)) ≤ E5 := le_max_right _ _
  have h5' : (E4 + 1) * ((m : ℝ) + 1) ≤ (E5 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E4 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E4 + 1) * ((m : ℝ) + 1)), h5]
  have h8 : (E3 + 1) * ((m : ℝ) + 1) ^ 3 ≤ (E5 + 1) ^ 4 := by
    have hsq5 : ((E4 + 1) * ((m : ℝ) + 1)) ^ 2 ≤ ((E5 + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5' 2
    nlinarith [hsq5,
      mul_le_mul_of_nonneg_right h4' (by positivity : (0:ℝ) ≤ ((m : ℝ) + 1) ^ 2)]
  have hW : (E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5 ≤ ((E5 + 1) ^ 4) ^ 2 := by
    rcases le_total (E3 + 1) ((m : ℝ) + 1) with hc | hc
    · have hsq : ((E3 + 1) * ((m : ℝ) + 1) ^ 3) ^ 2 ≤ ((E5 + 1) ^ 4) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h8 2
      nlinarith [hsq, hc, hE3, hm1,
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ E3 + 1)
          (by positivity : (0:ℝ) ≤ ((m:ℝ)+1)^3)) hm1]
    · have h44 : ((E3 + 1) * ((m : ℝ) + 1)) ^ 4 ≤ ((E4 + 1) ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h4' 4
      have h58 : ((E4 + 1) ^ 2) ^ 4 ≤ ((E5 + 1) ^ 2) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [h45, hE4, hE5]
      nlinarith [h44, h58, hc, hE3, hm1,
        mul_nonneg (by positivity : (0:ℝ) ≤ (E3+1)^3)
          (by positivity : (0:ℝ) ≤ ((m:ℝ)+1)^4)]
  have hd1 : Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5) ≤ (E5 + 1) ^ 4 := by
    calc Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)
        ≤ Real.sqrt (((E5 + 1) ^ 4) ^ 2) := Real.sqrt_le_sqrt hW
      _ = (E5 + 1) ^ 4 := Real.sqrt_sq (by positivity)
  have hd2 : Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)) ≤ (E5 + 1) ^ 2 := by
    calc Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))
        ≤ Real.sqrt (((E5 + 1) ^ 2) ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5) ≤ (E5 + 1) ^ 4 := hd1
            _ = ((E5 + 1) ^ 2) ^ 2 := by ring
      _ = (E5 + 1) ^ 2 := Real.sqrt_sq (by positivity)
  calc Real.sqrt (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)))
      ≤ Real.sqrt ((E5 + 1) ^ 2) := Real.sqrt_le_sqrt hd2
    _ = E5 + 1 := Real.sqrt_sq (by positivity)

/-- Fano bound for the quarter-root error grade.  The input may reach
`⁸√((E₃+1)³(m+1)⁵)`, strictly inside grade 5.  Route: split on
`e ≤ 2C(E₄+1)` (then the PROVED `s4_fano_term_le` applies) versus
`e ≤ 2C·R` with `R := ⁸√((E₃+1)³(m+1)⁵)`; in the second branch
`m·H(min(e/m,1/2)) ≤ e·log(m/e) + e` (`H_le_x_logInv`), the clamp branch
`e ≥ m/2` uses `m ≤ 4CR ≤ 4C(E₅+1)`, and for the log:
`e ≥ 2C(E₄+1)` with `(E₄+1)² ≥ (E₃+1)(m+1)` gives
`log(m/e) ≤ (1/2)·log₊((m+1)/(E₃+1)) + 1`, and
`R·log₊((m+1)/(E₃+1)) ≤ 8·R·⁸√((m+1)/(E₃+1)) = 8·⁴√((E₃+1)(m+1)³)
≤ 8·(E₅+1)` (`s4_log_le_eightroot`, `Real.sqrt_mul` ×3,
`s4_quarterroot_le_env5`). -/
lemma s4_fano_twoterm (Q : QData) (C : ℝ) (hC : 0 ≤ C) :
    ∃ C', 0 ≤ C' ∧ ∀ m : ℕ, ∀ e : ℝ,
      0 ≤ e →
      e ≤ C * ((effEnv 4 Q.sigma m + 1) +
        Real.sqrt (Real.sqrt (Real.sqrt
          ((effEnv 3 Q.sigma m + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)))) →
      (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) ≤ C' * (effEnv 5 Q.sigma m + 1) := by
  set C1 := C + 1 with hC1def
  have hC1 : 1 ≤ C1 := by dsimp [C1]; linarith
  have hC1pos : 0 < C1 := by linarith
  obtain ⟨C1', hC1'⟩ := s4_fano_term_le Q (2 * C1)
  refine ⟨|C1'| + 10 * C1, by positivity, ?_⟩
  intro m e he0 heC
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set E5 := effEnv 5 Q.sigma m
  set R := Real.sqrt (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) with hRdef
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have hE5 : 0 ≤ E5 := effGeo_nonneg _ _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRE5 : R ≤ E5 + 1 := s4_eightroot_le_env5 Q m
  have heC1 : e ≤ C1 * ((E4 + 1) + R) := by
    refine heC.trans ?_
    apply mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith) (by positivity)
  have hHcap : ∀ x : ℝ, H (min x (1 / 2)) ≤ Real.log 2 := by
    intro x
    have := Real.binEntropy_le_log_two (p := min x (1 / 2))
    simpa [H] using this
  by_cases hbr : e ≤ 2 * C1 * (E4 + 1)
  · have hb1 := hC1' m e he0 hbr
    calc (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) ≤ C1' * (E5 + 1) := hb1
      _ ≤ |C1'| * (E5 + 1) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ (|C1'| + 10 * C1) * (E5 + 1) := by nlinarith [abs_nonneg C1', hE5, hC1pos]
  · push_neg at hbr
    have heR : e ≤ 2 * C1 * R := by nlinarith [heC1, hbr]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, zero_mul]
      positivity
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    by_cases hclamp : ((m : ℝ) / 2) ≤ e
    · have hm4 : (m : ℝ) ≤ 4 * C1 * R := by nlinarith [heR]
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      calc (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
          ≤ (m : ℝ) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_left (hHcap _) (le_of_lt hmR)
        _ ≤ (4 * C1 * R) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right hm4 (Real.log_nonneg one_le_two)
        _ ≤ 4 * C1 * (E5 + 1) := by
            nlinarith [Real.log_nonneg (one_le_two), hRE5, hR0, hC1pos, hE5, hlog2]
        _ ≤ (|C1'| + 10 * C1) * (E5 + 1) := by nlinarith [abs_nonneg C1', hE5, hC1pos]
    · push_neg at hclamp
      rcases eq_or_lt_of_le he0 with he0' | hepos
      · rw [← he0']
        have hmin0 : min ((0:ℝ) / (m : ℝ)) (1 / 2) = 0 := by
          rw [zero_div]
          exact min_eq_left (by norm_num)
        rw [hmin0]
        have hH0 : H 0 = 0 := by simp [H]
        rw [hH0, mul_zero]
        positivity
      have hxlt : e / (m : ℝ) < 1 / 2 := by
        rw [div_lt_iff₀ hmR]; linarith
      have hmin : min (e / (m : ℝ)) (1 / 2) = e / (m : ℝ) :=
        min_eq_left (le_of_lt hxlt)
      rw [hmin]
      have hxpos : 0 < e / (m : ℝ) := div_pos hepos hmR
      have hHx := H_le_x_logInv (e / (m : ℝ)) hxpos (le_of_lt hxlt)
      have hstep : (m : ℝ) * H (e / (m : ℝ)) ≤ e * Real.log ((m : ℝ) / e) + e := by
        have hmul := mul_le_mul_of_nonneg_left hHx (le_of_lt hmR)
        have hlog_eq : Real.log (1 / (e / (m : ℝ))) = Real.log ((m : ℝ) / e) := by
          congr 1
          field_simp
        calc (m : ℝ) * H (e / (m : ℝ))
            ≤ (m : ℝ) * (e / (m : ℝ) * Real.log (1 / (e / (m : ℝ))) + e / (m : ℝ)) := hmul
          _ = e * Real.log (1 / (e / (m : ℝ))) + e := by
              field_simp
          _ = e * Real.log ((m : ℝ) / e) + e := by rw [hlog_eq]
      refine hstep.trans ?_
      have heE5 : e ≤ 2 * C1 * (E5 + 1) := by
        refine heR.trans ?_
        apply mul_le_mul_of_nonneg_left hRE5 (by positivity)
      have hlogterm : e * Real.log ((m : ℝ) / e) ≤ 8 * C1 * (E5 + 1) := by
        by_cases hme : ((m : ℝ) / e) ≤ 1
        · have hlognp : Real.log ((m : ℝ) / e) ≤ 0 := Real.log_nonpos (by positivity) hme
          nlinarith [mul_nonpos_of_nonneg_of_nonpos he0 hlognp, hC1pos, hE5]
        · push_neg at hme
          have h4r : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := le_max_right _ _
          have hsqrt_le_e : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ e := by
            calc Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := h4r
              _ ≤ 2 * C1 * (E4 + 1) := by nlinarith [hE4, hC1pos]
              _ ≤ e := le_of_lt hbr
          set S := Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) with hSdef
          have hSpos : 0 < S := by
            rw [hSdef]
            apply Real.sqrt_pos.mpr
            positivity
          set ratio := ((m : ℝ) + 1) / (E3 + 1) with hratiodef
          have hratio0 : 0 < ratio := by positivity
          have hqS : Real.sqrt ratio * S = (m : ℝ) + 1 := by
            rw [hratiodef, hSdef,
              ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((m:ℝ)+1)/(E3+1))]
            rw [show ((m:ℝ)+1)/(E3+1) * ((E3+1) * ((m:ℝ)+1)) = ((m:ℝ)+1)^2 by
              field_simp]
            exact Real.sqrt_sq (by positivity)
          have hme_le : (m : ℝ) / e ≤ Real.sqrt ratio := by
            rw [div_le_iff₀ hepos]
            nlinarith [mul_le_mul_of_nonneg_left hsqrt_le_e (Real.sqrt_nonneg ratio), hqS]
          have hratio1 : 1 ≤ ratio := by
            by_cases hr : ratio ≤ 1
            · have := Real.sqrt_le_one.mpr hr
              linarith [hme_le]
            · push_neg at hr
              linarith
          have hlogme : Real.log ((m : ℝ) / e) ≤ Real.log (Real.sqrt ratio) :=
            Real.log_le_log (by positivity) hme_le
          have hlogsqrt : Real.log (Real.sqrt ratio) = Real.log ratio / 2 :=
            Real.log_sqrt (le_of_lt hratio0)
          have hlog8 : Real.log ratio ≤
              8 * Real.sqrt (Real.sqrt (Real.sqrt ratio)) :=
            s4_log_le_eightroot ratio hratio1
          have hprod : R * Real.sqrt (Real.sqrt (Real.sqrt ratio))
              = Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) := by
            rw [hRdef, ← s4_root8_mul _ _ (by positivity)]
            rw [show (E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5 * ratio
                = ((E3 + 1) * ((m : ℝ) + 1) ^ 3) ^ 2 by
              rw [hratiodef]; field_simp]
            rw [Real.sqrt_sq (by positivity)]
          have hquarter : Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) ≤ E5 + 1 :=
            s4_quarterroot_le_env5 Q m
          have hlogpos : 0 ≤ Real.log ((m : ℝ) / e) :=
            Real.log_nonneg (le_of_lt hme)
          have hroot0 : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt ratio)) :=
            Real.sqrt_nonneg _
          calc e * Real.log ((m : ℝ) / e)
              ≤ (2 * C1 * R) * Real.log ((m : ℝ) / e) := by
                apply mul_le_mul_of_nonneg_right heR hlogpos
            _ ≤ (2 * C1 * R) * (Real.log ratio / 2) := by
                apply mul_le_mul_of_nonneg_left (hlogme.trans (le_of_eq hlogsqrt))
                positivity
            _ ≤ (2 * C1 * R) * (8 * Real.sqrt (Real.sqrt (Real.sqrt ratio)) / 2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith
            _ = 8 * C1 * (R * Real.sqrt (Real.sqrt (Real.sqrt ratio))) := by ring
            _ = 8 * C1 * Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) := by
                rw [hprod]
            _ ≤ 8 * C1 * (E5 + 1) := by
                apply mul_le_mul_of_nonneg_left hquarter (by positivity)
      calc e * Real.log ((m : ℝ) / e) + e
          ≤ 8 * C1 * (E5 + 1) + 2 * C1 * (E5 + 1) := by linarith [heE5, hlogterm]
        _ = 10 * C1 * (E5 + 1) := by ring
        _ ≤ (|C1'| + 10 * C1) * (E5 + 1) := by nlinarith [abs_nonneg C1', hE5]

/-- `√x ≤ (x+1)/2`. -/
lemma s4_sqrt_le_half_add (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ (x + 1) / 2 := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

set_option maxHeartbeats 1600000 in
/-- Explicit-constant Fano bound for the quarter-root error grade
(mirrors the proved `s4_fano_twoterm` with the constant surfaced, so that
the certificate can absorb its `eps`-dependence; the small-`e` branch is
the `H ≤ 2√·` route of `s4_fano_term_le` inlined). -/
lemma s4_fano_twoterm_explicit (Q : QData) (C : ℝ) (hC : 0 ≤ C) (m : ℕ) (e : ℝ)
    (he0 : 0 ≤ e)
    (heC : e ≤ C * ((effEnv 4 Q.sigma m + 1) +
      Real.sqrt (Real.sqrt (Real.sqrt
        ((effEnv 3 Q.sigma m + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))))) :
    (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
      ≤ (12 * (C + 1) + 3) * (effEnv 5 Q.sigma m + 1) := by
  set C1 := C + 1 with hC1def
  have hC1 : 1 ≤ C1 := by dsimp [C1]; linarith
  have hC1pos : 0 < C1 := by linarith
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set E5 := effEnv 5 Q.sigma m
  set R := Real.sqrt (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) with hRdef
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have hE5 : 0 ≤ E5 := effGeo_nonneg _ _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRE5 : R ≤ E5 + 1 := s4_eightroot_le_env5 Q m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have heC1 : e ≤ C1 * ((E4 + 1) + R) := by
    refine heC.trans ?_
    apply mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith) (by positivity)
  have h5g : Real.sqrt ((E4 + 1) * ((m : ℝ) + 1)) ≤ E5 := le_max_right _ _
  have h5sq : (E4 + 1) * ((m : ℝ) + 1) ≤ (E5 + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E4 + 1) * ((m : ℝ) + 1) by positivity),
      Real.sqrt_nonneg ((E4 + 1) * ((m : ℝ) + 1)), h5g]
  have hHcap : ∀ x : ℝ, H (min x (1 / 2)) ≤ Real.log 2 := by
    intro x
    have := Real.binEntropy_le_log_two (p := min x (1 / 2))
    simpa [H] using this
  by_cases hbr : e ≤ 2 * C1 * (E4 + 1)
  · -- small-e branch: H ≤ 2√ route, explicit
    rcases Nat.eq_zero_or_pos m with hm00 | hmpos
    · subst hm00
      simp only [Nat.cast_zero, zero_mul]
      positivity
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    set y := min (e / (m : ℝ)) (1 / 2) with hydef
    have hy0 : 0 ≤ y := by
      rw [hydef]
      apply le_min (div_nonneg he0 hm0) (by norm_num)
    have hy1 : y ≤ 1 := by
      rw [hydef]
      have := min_le_right (e / (m : ℝ)) (1 / 2)
      linarith
    have hH2 : H y ≤ 2 * Real.sqrt y := s4_binEntropy_le_two_mul_sqrt y hy0 hy1
    have hyle : y ≤ e / (m : ℝ) := by rw [hydef]; exact min_le_left _ _
    have hstep1 : (m : ℝ) * H y ≤ 2 * ((m : ℝ) * Real.sqrt (e / (m : ℝ))) := by
      have h1 := mul_le_mul_of_nonneg_left hH2 hm0
      have h2 : Real.sqrt y ≤ Real.sqrt (e / (m : ℝ)) := Real.sqrt_le_sqrt hyle
      nlinarith [mul_le_mul_of_nonneg_left h2 hm0]
    have hsqem : (m : ℝ) * Real.sqrt (e / (m : ℝ)) = Real.sqrt (e * (m : ℝ)) := by
      rw [show (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) from (Real.sqrt_sq hm0).symm]
      rw [← Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hm0]
      congr 1
      field_simp
    have hem : e * (m : ℝ) ≤ 2 * C1 * ((E5 + 1) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_right hbr hm0
      have h2 : 2 * C1 * (E4 + 1) * (m : ℝ) ≤ 2 * C1 * ((E4 + 1) * ((m : ℝ) + 1)) := by
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC1pos.le)
          (by linarith : (0:ℝ) ≤ E4 + 1)]
      have h3 := mul_le_mul_of_nonneg_left h5sq
        (by positivity : (0:ℝ) ≤ 2 * C1)
      linarith
    have hsq2 : Real.sqrt (e * (m : ℝ)) ≤ Real.sqrt (2 * C1) * (E5 + 1) := by
      calc Real.sqrt (e * (m : ℝ)) ≤ Real.sqrt (2 * C1 * ((E5 + 1) ^ 2)) :=
            Real.sqrt_le_sqrt hem
        _ = Real.sqrt (2 * C1) * (E5 + 1) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hconst : 2 * Real.sqrt (2 * C1) ≤ 2 * C1 + 3 := by
      have := s4_sqrt_le_half_add (2 * C1) (by positivity)
      linarith
    calc (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
        ≤ 2 * ((m : ℝ) * Real.sqrt (e / (m : ℝ))) := hstep1
      _ = 2 * Real.sqrt (e * (m : ℝ)) := by rw [hsqem]
      _ ≤ 2 * (Real.sqrt (2 * C1) * (E5 + 1)) := by linarith [hsq2]
      _ = (2 * Real.sqrt (2 * C1)) * (E5 + 1) := by ring
      _ ≤ (2 * C1 + 3) * (E5 + 1) := by
          apply mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ (12 * C1 + 3) * (E5 + 1) := by nlinarith [hC1pos, hE5]
  · -- large-e branch: e ≤ 2·C1·R, e·log(m/e) route (as in s4_fano_twoterm)
    push_neg at hbr
    have heR : e ≤ 2 * C1 * R := by nlinarith [heC1, hbr]
    rcases Nat.eq_zero_or_pos m with hm00 | hmpos
    · subst hm00
      simp only [Nat.cast_zero, zero_mul]
      positivity
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    by_cases hclamp : ((m : ℝ) / 2) ≤ e
    · have hm4 : (m : ℝ) ≤ 4 * C1 * R := by nlinarith [heR]
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      calc (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
          ≤ (m : ℝ) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_left (hHcap _) (le_of_lt hmR)
        _ ≤ (4 * C1 * R) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right hm4 (Real.log_nonneg one_le_two)
        _ ≤ 4 * C1 * (E5 + 1) := by
            nlinarith [Real.log_nonneg (one_le_two), hRE5, hR0, hC1pos, hE5, hlog2]
        _ ≤ (12 * C1 + 3) * (E5 + 1) := by nlinarith [hC1pos, hE5]
    · push_neg at hclamp
      rcases eq_or_lt_of_le he0 with he0' | hepos
      · rw [← he0']
        have hmin0 : min ((0:ℝ) / (m : ℝ)) (1 / 2) = 0 := by
          rw [zero_div]
          exact min_eq_left (by norm_num)
        rw [hmin0]
        have hH0 : H 0 = 0 := by simp [H]
        rw [hH0, mul_zero]
        positivity
      have hxlt : e / (m : ℝ) < 1 / 2 := by
        rw [div_lt_iff₀ hmR]; linarith
      have hmin : min (e / (m : ℝ)) (1 / 2) = e / (m : ℝ) :=
        min_eq_left (le_of_lt hxlt)
      rw [hmin]
      have hxpos : 0 < e / (m : ℝ) := div_pos hepos hmR
      have hHx := H_le_x_logInv (e / (m : ℝ)) hxpos (le_of_lt hxlt)
      have hstep : (m : ℝ) * H (e / (m : ℝ)) ≤ e * Real.log ((m : ℝ) / e) + e := by
        have hmul := mul_le_mul_of_nonneg_left hHx (le_of_lt hmR)
        have hlog_eq : Real.log (1 / (e / (m : ℝ))) = Real.log ((m : ℝ) / e) := by
          congr 1
          field_simp
        calc (m : ℝ) * H (e / (m : ℝ))
            ≤ (m : ℝ) * (e / (m : ℝ) * Real.log (1 / (e / (m : ℝ))) + e / (m : ℝ)) := hmul
          _ = e * Real.log (1 / (e / (m : ℝ))) + e := by
              field_simp
          _ = e * Real.log ((m : ℝ) / e) + e := by rw [hlog_eq]
      refine hstep.trans ?_
      have heE5 : e ≤ 2 * C1 * (E5 + 1) := by
        refine heR.trans ?_
        apply mul_le_mul_of_nonneg_left hRE5 (by positivity)
      have hlogterm : e * Real.log ((m : ℝ) / e) ≤ 8 * C1 * (E5 + 1) := by
        by_cases hme : ((m : ℝ) / e) ≤ 1
        · have hlognp : Real.log ((m : ℝ) / e) ≤ 0 := Real.log_nonpos (by positivity) hme
          nlinarith [mul_nonpos_of_nonneg_of_nonpos he0 hlognp, hC1pos, hE5]
        · push_neg at hme
          have h4r : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := le_max_right _ _
          have hsqrt_le_e : Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ e := by
            calc Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) ≤ E4 := h4r
              _ ≤ 2 * C1 * (E4 + 1) := by nlinarith [hE4, hC1pos]
              _ ≤ e := le_of_lt hbr
          set S := Real.sqrt ((E3 + 1) * ((m : ℝ) + 1)) with hSdef
          have hSpos : 0 < S := by
            rw [hSdef]
            apply Real.sqrt_pos.mpr
            positivity
          set ratio := ((m : ℝ) + 1) / (E3 + 1) with hratiodef
          have hratio0 : 0 < ratio := by positivity
          have hqS : Real.sqrt ratio * S = (m : ℝ) + 1 := by
            rw [hratiodef, hSdef,
              ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((m:ℝ)+1)/(E3+1))]
            rw [show ((m:ℝ)+1)/(E3+1) * ((E3+1) * ((m:ℝ)+1)) = ((m:ℝ)+1)^2 by
              field_simp]
            exact Real.sqrt_sq (by positivity)
          have hme_le : (m : ℝ) / e ≤ Real.sqrt ratio := by
            rw [div_le_iff₀ hepos]
            nlinarith [mul_le_mul_of_nonneg_left hsqrt_le_e (Real.sqrt_nonneg ratio), hqS]
          have hratio1 : 1 ≤ ratio := by
            by_cases hr : ratio ≤ 1
            · have := Real.sqrt_le_one.mpr hr
              linarith [hme_le]
            · push_neg at hr
              linarith
          have hlogme : Real.log ((m : ℝ) / e) ≤ Real.log (Real.sqrt ratio) :=
            Real.log_le_log (by positivity) hme_le
          have hlogsqrt : Real.log (Real.sqrt ratio) = Real.log ratio / 2 :=
            Real.log_sqrt (le_of_lt hratio0)
          have hlog8 : Real.log ratio ≤
              8 * Real.sqrt (Real.sqrt (Real.sqrt ratio)) :=
            s4_log_le_eightroot ratio hratio1
          have hprod : R * Real.sqrt (Real.sqrt (Real.sqrt ratio))
              = Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) := by
            rw [hRdef, ← s4_root8_mul _ _ (by positivity)]
            rw [show (E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5 * ratio
                = ((E3 + 1) * ((m : ℝ) + 1) ^ 3) ^ 2 by
              rw [hratiodef]; field_simp]
            rw [Real.sqrt_sq (by positivity)]
          have hquarter : Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) ≤ E5 + 1 :=
            s4_quarterroot_le_env5 Q m
          have hlogpos : 0 ≤ Real.log ((m : ℝ) / e) :=
            Real.log_nonneg (le_of_lt hme)
          have hroot0 : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt ratio)) :=
            Real.sqrt_nonneg _
          calc e * Real.log ((m : ℝ) / e)
              ≤ (2 * C1 * R) * Real.log ((m : ℝ) / e) := by
                apply mul_le_mul_of_nonneg_right heR hlogpos
            _ ≤ (2 * C1 * R) * (Real.log ratio / 2) := by
                apply mul_le_mul_of_nonneg_left (hlogme.trans (le_of_eq hlogsqrt))
                positivity
            _ ≤ (2 * C1 * R) * (8 * Real.sqrt (Real.sqrt (Real.sqrt ratio)) / 2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith
            _ = 8 * C1 * (R * Real.sqrt (Real.sqrt (Real.sqrt ratio))) := by ring
            _ = 8 * C1 * Real.sqrt (Real.sqrt ((E3 + 1) * ((m : ℝ) + 1) ^ 3)) := by
                rw [hprod]
            _ ≤ 8 * C1 * (E5 + 1) := by
                apply mul_le_mul_of_nonneg_left hquarter (by positivity)
      calc e * Real.log ((m : ℝ) / e) + e
          ≤ 8 * C1 * (E5 + 1) + 2 * C1 * (E5 + 1) := by linarith [heE5, hlogterm]
        _ = 10 * C1 * (E5 + 1) := by ring
        _ ≤ (12 * C1 + 3) * (E5 + 1) := by nlinarith [hC1pos, hE5]

set_option maxHeartbeats 2000000 in
/-- v2 certificate at the quarter-root schedule.  Assemble exactly as the
proved `s4_rate_gap_certificate` does, with `p := s4_eff_p2` throughout:
the `2 < eps` branch is `s4_binnedFoldField_zero_of_two_lt_eps` +
`s4_uH_const`; otherwise feed `s4_fixedDensity_entropy_bound_eff` with the
two-term `vFam`, `sS := K_V·(effEnv 2 Q.sigma m + 1) + Q.sigma m`, and the
trivial cap `hflat` from `uH_proj_le_I_log_two`; bound the five budget terms:
`2log2·p₂·m ≤ 2log2·(E₅+1)` (`s4_p2_mul_le` + `s4_quarterroot_le_env5`);
`sS ≤ (K_V+1)·(E₅+1)`; the Fano term by `s4_fano_twoterm`;
`e·log(max 1 (4/eps+2)) ≤ (2K_err/eps)·(E₅+1)·(4/eps+1)` since
`e ≤ (K_err/eps)·((E₄+1)+R) ≤ (2K_err/eps)·(E₅+1)`
(`R ≤ E₅+1` by the two-case `(E₃+1) ≶ (m+1)` comparison) and
`log x ≤ x − 1`; the exp remainder by `2m·exp(−p₂m/8) ≤ 6/p₂ ≤
6·(⁴√((m+1)/(E₃+1)) + 3) ≤ 6·((m+1)^{1/4} + 3) ≤ 24·(E₅+1)`;
absorb `1/eps`-powers with `eps ≤ 2` as in the proved `s4_cert_combine`. -/
lemma s4_rate_gap_certificate_v2 (Q : QData) (hQ : validQData Q)
    (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (hS3 : S3Statement) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (eps : ℝ), 0 < eps →
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty → fat Q m A q → pinned Q m A q →
          ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
            uH A (binnedFoldField A (eps / 4) o) ≤
              (K / eps ^ 4) * (effEnv 5 Q.sigma m + 1) := by
  obtain ⟨K_V, hKV1, hKV⟩ := s4_eff_variance_twoterm hR3 hS1 hS2 Q hQ
  obtain ⟨K_err, hKerr1, hKerr⟩ := s4_eff_error_twoterm Q hQ K_V hKV1
  refine ⟨1024 * K_err + 16384, by linarith, ?_⟩
  intro eps heps m A q hA hfat hpin
  have hE5nn : 0 ≤ effEnv 5 Q.sigma m := effGeo_nonneg _ _
  have hE51 : (0:ℝ) ≤ effEnv 5 Q.sigma m + 1 := by linarith
  have hKnn : (0:ℝ) < 1024 * K_err + 16384 := by linarith
  have hRHSnn : 0 ≤ ((1024 * K_err + 16384) / eps ^ 4) * (effEnv 5 Q.sigma m + 1) := by
    have h4 : (0:ℝ) < eps ^ 4 := by positivity
    positivity
  by_cases hbig : 4 ≤ eps
  · refine ⟨0, le_refl _, by linarith, ?_⟩
    have hwbig : 1 / 2 < eps / 4 := by linarith
    rw [s4_uH_binnedFold_trivial m A (eps / 4) hwbig]
    exact hRHSnn
  push_neg at hbig
  obtain ⟨hp0, hp13⟩ := s4_eff_p2_bounds Q m
  obtain ⟨vFam, hv0, hv1, hv2⟩ := hKV m A q hA hfat hpin
  have hw : 0 < eps / 4 := by linarith
  have hp2pos : 0 < s4_eff_p2 Q m / 2 := by linarith
  have hp2half : s4_eff_p2 Q m / 2 ≤ 1 / 2 := by linarith
  obtain ⟨o, ho0, how, houH⟩ :=
    s4_fixedDensity_entropy_bound_eff m A (eps / 4) (s4_eff_p2 Q m) hw hp0 hp13 vFam
      (hv0 _ hp2pos hp2half) hA (hv1 _ hp2pos hp2half) hS3 0 le_rfl
      (fun I _ _ => by have := uH_proj_le_I_log_two m A hA I; linarith)
  refine ⟨o, ho0, how, ?_⟩
  set p := s4_eff_p2 Q m with hpdef
  set e := s4_errorBound (eps / 4) vFam p m with hedef
  set E3 := effEnv 3 Q.sigma m
  set E4 := effEnv 4 Q.sigma m
  set E5 := effEnv 5 Q.sigma m
  set R := Real.sqrt (Real.sqrt (Real.sqrt ((E3 + 1) ^ 3 * ((m : ℝ) + 1) ^ 5))) with hRdef
  have hE3 : 0 ≤ E3 := s4_eff3_nonneg Q.sigma m
  have hE4 : 0 ≤ E4 := effGeo_nonneg _ _
  have hE45 : E4 ≤ E5 := le_effGeo (effEnv 4 Q.sigma) m
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRE5 : R ≤ E5 + 1 := s4_eightroot_le_env5 Q m
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm1p : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hE3p : (0:ℝ) < E3 + 1 := by linarith
  -- eps power facts (0 < eps < 4)
  have heps4 : (0:ℝ) < eps ^ 4 := by positivity
  have heps_sq : eps ^ 2 ≤ 16 := by
    have h1 : eps ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ heps.le hbig.le 2
    norm_num at h1
    linarith
  have heps_cb : eps ^ 3 ≤ 64 := by
    have h1 : eps ^ 3 ≤ 4 ^ 3 := pow_le_pow_left₀ heps.le hbig.le 3
    norm_num at h1
    linarith
  have heps_qt : eps ^ 4 ≤ 256 := by
    have h1 : eps ^ 4 ≤ 4 ^ 4 := pow_le_pow_left₀ heps.le hbig.le 4
    norm_num at h1
    linarith
  -- error bound
  have he0 : 0 ≤ e :=
    s4_errorBound_nonneg (eps / 4) vFam p m hw hp0 (hv0 _ hp2pos hp2half)
  have he : e ≤ (K_err / eps) * ((E4 + 1) + R) := hKerr m vFam hv0 hv2 eps heps
  have heE5 : e ≤ (2 * K_err / eps) * (E5 + 1) := by
    have hsum : (E4 + 1) + R ≤ 2 * (E5 + 1) := by linarith [hE45, hRE5]
    have := mul_le_mul_of_nonneg_left hsum
      (by positivity : (0:ℝ) ≤ K_err / eps)
    calc e ≤ (K_err / eps) * ((E4 + 1) + R) := he
      _ ≤ (K_err / eps) * (2 * (E5 + 1)) := this
      _ = (2 * K_err / eps) * (E5 + 1) := by ring
  -- T1: schedule-dimension term
  have hT1 : 2 * Real.log 2 * p * (m : ℝ) ≤ (512 / eps ^ 4) * (E5 + 1) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    have hlog2n : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    have hpm : p * (m : ℝ) ≤ E5 + 1 :=
      (s4_p2_mul_le Q m).trans (s4_quarterroot_le_env5 Q m)
    have h1 : 2 * Real.log 2 * p * (m : ℝ) ≤ 2 * (E5 + 1) := by
      nlinarith [hpm, mul_nonneg (le_of_lt hp0) hm0]
    have h2 : (2:ℝ) ≤ 512 / eps ^ 4 := by
      rw [le_div_iff₀ heps4]
      linarith [heps_qt]
    nlinarith [mul_le_mul_of_nonneg_right h2 hE51, hE51]
  -- T3: Fano term via the explicit lemma
  have hT3 : (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
      ≤ ((768 * K_err + 3840) / eps ^ 4) * (E5 + 1) := by
    have hfx := s4_fano_twoterm_explicit Q (K_err / eps) (by positivity) m e he0 he
    have hCabs : 12 * (K_err / eps + 1) + 3 ≤ (768 * K_err + 3840) / eps ^ 4 := by
      rw [le_div_iff₀ heps4]
      have hexp : (12 * (K_err / eps + 1) + 3) * eps ^ 4
          = 12 * K_err * eps ^ 3 + 15 * eps ^ 4 := by
        field_simp
        ring
      rw [hexp]
      have hb1 : 12 * K_err * eps ^ 3 ≤ 12 * K_err * 64 := by
        apply mul_le_mul_of_nonneg_left heps_cb (by linarith)
      linarith [heps_qt, hb1]
    calc (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
        ≤ (12 * (K_err / eps + 1) + 3) * (E5 + 1) := hfx
      _ ≤ ((768 * K_err + 3840) / eps ^ 4) * (E5 + 1) := by
          apply mul_le_mul_of_nonneg_right hCabs hE51
  -- T4: error·log term
  have hT4 : e * Real.log (max 1 (1 / (eps / 4) + 2))
      ≤ (256 * K_err / eps ^ 4) * (E5 + 1) := by
    have hval : (1:ℝ) ≤ 1 / (eps / 4) + 2 := by
      have : 0 < 1 / (eps / 4) := by positivity
      linarith
    have hmax : max (1:ℝ) (1 / (eps / 4) + 2) = 1 / (eps / 4) + 2 := max_eq_right hval
    have hlogle : Real.log (1 / (eps / 4) + 2) ≤ 1 / (eps / 4) + 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (eps / 4) + 2 by positivity)
      linarith
    have hrw : 1 / (eps / 4) = 4 / eps := by
      field_simp
    have hlognn : 0 ≤ Real.log (max 1 (1 / (eps / 4) + 2)) :=
      Real.log_nonneg (le_max_left _ _)
    have hstep : e * Real.log (max 1 (1 / (eps / 4) + 2))
        ≤ ((2 * K_err / eps) * (E5 + 1)) * (4 / eps + 1) := by
      have h1 := mul_le_mul_of_nonneg_right heE5 hlognn
      have h2 : Real.log (max 1 (1 / (eps / 4) + 2)) ≤ 4 / eps + 1 := by
        rw [hmax, hrw] at *
        linarith [hlogle]
      have h3 : 0 ≤ (2 * K_err / eps) * (E5 + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 h3]
    refine hstep.trans ?_
    have hcoef : (2 * K_err / eps) * (4 / eps + 1) ≤ 256 * K_err / eps ^ 4 := by
      rw [le_div_iff₀ heps4]
      have hexp : (2 * K_err / eps) * (4 / eps + 1) * eps ^ 4
          = 8 * K_err * eps ^ 2 + 2 * K_err * eps ^ 3 := by
        field_simp
        ring
      rw [hexp]
      have hb1 : 8 * K_err * eps ^ 2 ≤ 8 * K_err * 16 := by
        apply mul_le_mul_of_nonneg_left heps_sq (by linarith)
      have hb2 : 2 * K_err * eps ^ 3 ≤ 2 * K_err * 64 := by
        apply mul_le_mul_of_nonneg_left heps_cb (by linarith)
      linarith
    calc ((2 * K_err / eps) * (E5 + 1)) * (4 / eps + 1)
        = ((2 * K_err / eps) * (4 / eps + 1)) * (E5 + 1) := by ring
      _ ≤ (256 * K_err / eps ^ 4) * (E5 + 1) := by
          apply mul_le_mul_of_nonneg_right hcoef hE51
  -- T5: exponential remainder at the quarter-root schedule
  have hT5 : 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ (6144 / eps ^ 4) * (E5 + 1) := by
    have htexp := s4_texp_le (p * (m : ℝ)) (by positivity)
    have harg : -p * (m : ℝ) / 8 = -((p * (m : ℝ)) / 8) := by ring
    have hip : 2 * (m : ℝ) * Real.exp (-((p * (m : ℝ)) / 8)) ≤ 6 * (1 / p) := by
      have hexp0 : 0 ≤ Real.exp (-((p * (m : ℝ)) / 8)) := (Real.exp_pos _).le
      calc 2 * (m : ℝ) * Real.exp (-((p * (m : ℝ)) / 8))
          = 2 * (1 / p) * ((p * (m : ℝ)) * Real.exp (-((p * (m : ℝ)) / 8))) := by
            field_simp
        _ ≤ 2 * (1 / p) * 3 := by
            apply mul_le_mul_of_nonneg_left htexp (by positivity)
        _ = 6 * (1 / p) := by ring
    have hipQ : 1 / p ≤ Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1))) + 3 := by
      have hAinv : Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) *
          Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1))) = 1 := by
        rw [← Real.sqrt_mul (Real.sqrt_nonneg _),
          ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (E3 + 1) / ((m : ℝ) + 1))]
        rw [show (E3 + 1) / ((m : ℝ) + 1) * (((m : ℝ) + 1) / (E3 + 1)) = 1 by
          field_simp]
        simp
      have hpmin : p = min (Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1)))) ((1:ℝ)/3) :=
        rfl
      rcases min_cases (Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1)))) ((1:ℝ)/3) with
        ⟨hmin, _⟩ | ⟨hmin, _⟩
      · have hp_eq : p = Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) :=
          hpmin.trans hmin
        have hppos : 0 < Real.sqrt (Real.sqrt ((E3 + 1) / ((m : ℝ) + 1))) := by
          rw [← hp_eq]; exact hp0
        have : 1 / p = Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1))) := by
          rw [hp_eq, eq_comm, eq_div_iff (ne_of_gt hppos), mul_comm]
          exact hAinv
        linarith [Real.sqrt_nonneg (Real.sqrt (((m : ℝ) + 1) / (E3 + 1)))]
      · have hp_eq : p = (1:ℝ)/3 := hpmin.trans hmin
        have : 1 / p = 3 := by rw [hp_eq]; norm_num
        linarith [Real.sqrt_nonneg (Real.sqrt (((m : ℝ) + 1) / (E3 + 1)))]
    have hQ4cap : Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1))) ≤ E5 + 1 := by
      have hr1 : ((m : ℝ) + 1) / (E3 + 1) ≤ (m : ℝ) + 1 := by
        rw [div_le_iff₀ hE3p]
        nlinarith [hm1p, hE3]
      have hr2 : Real.sqrt (((m : ℝ) + 1) / (E3 + 1)) ≤ Real.sqrt ((m : ℝ) + 1) :=
        Real.sqrt_le_sqrt hr1
      have hr3 : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
        apply s4_le_of_sq_le (Real.sqrt_nonneg _) (by positivity)
        rw [sq, Real.mul_self_sqrt (by positivity)]
        nlinarith [hm1p]
      have hr4 : Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1)))
          ≤ Real.sqrt ((m : ℝ) + 1) := by
        calc Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1)))
            ≤ Real.sqrt (Real.sqrt ((m : ℝ) + 1)) := Real.sqrt_le_sqrt hr2
          _ ≤ Real.sqrt ((m : ℝ) + 1) := by
              apply s4_le_of_sq_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
              rw [sq, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
              nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (m:ℝ)+1 by positivity),
                Real.sqrt_nonneg ((m:ℝ)+1), hr3]
      have hr5 : Real.sqrt ((m : ℝ) + 1) ≤ E5 + 1 := by
        apply s4_le_of_sq_le (Real.sqrt_nonneg _) (by linarith)
        rw [sq, Real.mul_self_sqrt (by positivity)]
        have h5g : Real.sqrt ((E4 + 1) * ((m : ℝ) + 1)) ≤ E5 := le_max_right _ _
        have h5sq : (E4 + 1) * ((m : ℝ) + 1) ≤ (E5 + 1) ^ 2 := by
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (E4 + 1) * ((m : ℝ) + 1) by positivity),
            Real.sqrt_nonneg ((E4 + 1) * ((m : ℝ) + 1)), h5g]
        nlinarith [h5sq, hm1p, hE4]
      linarith [hr4, hr5]
    have hfinal : 2 * (m : ℝ) * Real.exp (-((p * (m : ℝ)) / 8)) ≤ 24 * (E5 + 1) := by
      have h1 : 6 * (1 / p) ≤ 6 * ((E5 + 1) + 3) := by
        have := hipQ.trans (by linarith [hQ4cap] : Real.sqrt (Real.sqrt (((m : ℝ) + 1) / (E3 + 1))) + 3 ≤ (E5 + 1) + 3)
        linarith
      have h2 : (6:ℝ) * ((E5 + 1) + 3) ≤ 24 * (E5 + 1) := by nlinarith [hE5nn]
      linarith [hip]
    have h24 : (24:ℝ) ≤ 6144 / eps ^ 4 := by
      rw [le_div_iff₀ heps4]
      linarith [heps_qt]
    calc 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)
        = 2 * (m : ℝ) * Real.exp (-((p * (m : ℝ)) / 8)) := by rw [harg]
      _ ≤ 24 * (E5 + 1) := hfinal
      _ ≤ (6144 / eps ^ 4) * (E5 + 1) := by
          apply mul_le_mul_of_nonneg_right h24 hE51
  -- combine
  have hsum := houH
  have hzero : (2:ℝ) * Real.log 2 * p * (m:ℝ) + 0
      + (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
      + e * Real.log (max 1 (1 / (eps / 4) + 2))
      + 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)
      ≤ ((1024 * K_err + 16384) / eps ^ 4) * (E5 + 1) := by
    have hcollect : (512 / eps ^ 4) * (E5 + 1)
        + ((768 * K_err + 3840) / eps ^ 4) * (E5 + 1)
        + (256 * K_err / eps ^ 4) * (E5 + 1)
        + (6144 / eps ^ 4) * (E5 + 1)
        ≤ ((1024 * K_err + 16384) / eps ^ 4) * (E5 + 1) := by
      have hcoef : (512:ℝ) / eps ^ 4 + (768 * K_err + 3840) / eps ^ 4
          + 256 * K_err / eps ^ 4 + 6144 / eps ^ 4
          ≤ (1024 * K_err + 16384) / eps ^ 4 := by
        rw [div_add_div_same, div_add_div_same, div_add_div_same]
        exact (div_le_div_iff_of_pos_right heps4).mpr (by linarith)
      have hprod := mul_le_mul_of_nonneg_right hcoef hE51
      nlinarith [hprod]
    linarith [hT1, hT3, hT4, hT5]
  exact hsum.trans hzero

theorem s4_eff (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (hS3 : S3Statement) : S4Eff := by
  intro Q hQ
  exact s4_rate_gap_certificate_v2 Q hQ hR3 hS1 hS2 hS3

end HarperStability
