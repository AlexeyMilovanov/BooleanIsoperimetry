import HarperStability.Core.S6
import HarperStability.Core.S5Transfer
import HarperStability.Interface.Effective

namespace HarperStability

lemma s6_eff_variance_grade5 (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) :
    ∃ K_V : ℝ, 1 ≤ K_V ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        ∃ vFam : ℝ → ℕ → ℝ,
          (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → varianceBudgetLE A pLow (vFam pLow m)) ∧
          (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 →
            vFam pLow m ≤ (K_V / pLow) * (effEnv 5 Q.sigma m + 1)) := by
  obtain ⟨K3, hK3, hR3_bound⟩ := hR3 Q.qMin Q.qMax Q.s0 Q.mu0 hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1
  let K_V : ℝ := max (K3 * 100 + 100) 30
  have hKV : 1 ≤ K_V := le_max_of_le_right (by norm_num)
  refine ⟨K_V, hKV, ?_⟩
  intro m A q hA hFat hPinned
  by_cases hm : m < 30
  · refine ⟨fun pLow m => m, ?_, ?_⟩
    · intro pLow hpLow1 hpLow2
      exact core_varianceBudgetLE_dim A pLow
    · intro pLow hpLow1 hpLow2
      have hm30 : (m : ℝ) ≤ 30 := by exact_mod_cast le_of_lt hm
      have hpLow_inv : 2 ≤ 1 / pLow := by
        rw [le_div_iff₀ hpLow1]
        linarith
      have henv : 1 ≤ effEnv 5 Q.sigma m + 1 := by
        have : 0 ≤ effEnv 5 Q.sigma m := effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 m
        linarith
      calc (m : ℝ) ≤ 30 := hm30
        _ ≤ K_V := le_max_right _ _
        _ = K_V * 1 := by ring
        _ ≤ K_V * (effEnv 5 Q.sigma m + 1) := mul_le_mul_of_nonneg_left henv (by positivity)
        _ ≤ 2 * (K_V * (effEnv 5 Q.sigma m + 1)) := by linarith [mul_nonneg (by positivity : 0 ≤ K_V) (by positivity : 0 ≤ effEnv 5 Q.sigma m + 1)]
        _ ≤ (1 / pLow) * (K_V * (effEnv 5 Q.sigma m + 1)) := mul_le_mul_of_nonneg_right hpLow_inv (by positivity)
        _ = (K_V / pLow) * (effEnv 5 Q.sigma m + 1) := by ring
  · let s1 := (K3 / (1 / 6)) * (effEnv 2 Q.sigma m + 1)
    let eps1 := Real.sqrt ((s1 + 1) / ((m : ℝ) + 1))
    let e := 12 * s1 / eps1 + 4
    let vFam := fun pLow m => ((K3 / pLow) * (effEnv 2 Q.sigma m + 1) + eps1 * (m : ℝ) + e * Real.log 2) / 2
    refine ⟨vFam, ?_, ?_⟩
    · intro pLow hpLow1 hpLow2
      have hreg_16 : blockRegular m A q (1 / 6) s1 := by
        apply hR3_bound (1 / 6) (by norm_num) (by norm_num) Q.sigma hQ.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2 m A q hA hFat hPinned
      have hs1_nonneg : 0 ≤ s1 := by
        dsimp [s1]
        have h1 : 0 ≤ K3 := by linarith
        have h2 : 0 ≤ effEnv 2 Q.sigma m + 1 := by
          have : 0 ≤ effEnv 2 Q.sigma m := effEnv_nonneg 2 Q.sigma hQ.2.2.2.2.2.2.1.1 m
          linarith
        positivity
      have heps1_pos : 0 < eps1 := by
        dsimp [eps1]
        apply Real.sqrt_pos.mpr
        positivity
      have h_m30 : 30 ≤ m := not_lt.mp hm
      have h_m30_real : 30 ≤ (m : ℝ) := by exact_mod_cast h_m30
      have h_m56 : (1 / 6 : ℝ) * (m : ℝ) ≤ ((m / 5 : ℕ) : ℝ) := by
        have hdiv : (m : ℝ) ≤ 5 * ((m / 5 : ℕ) : ℝ) + 4 := by
          have : m ≤ 5 * (m / 5) + 4 := by omega
          exact_mod_cast this
        linarith
      have h_m56_ub : (m : ℝ) - ((m / 5 : ℕ) : ℝ) ≤ (1 - 1 / 6 : ℝ) * (m : ℝ) := by
        have hdiv : 5 * ((m / 5 : ℕ) : ℝ) + 4 ≥ (m : ℝ) := by
          have : 5 * (m / 5) + 4 ≥ m := by omega
          exact_mod_cast this
        linarith
      have hS1_apply : (((Finset.univ : Finset (Fin m)).filter (fun t => eps1 ≤ |hstep A t - H q|)).card : ℝ) ≤ e := by
        apply hS1 m A (H q) s1 eps1 hA hs1_nonneg heps1_pos
        · intro I hI_lb hI_ub
          have h1 : (1 / 6 : ℝ) * (m : ℝ) ≤ (I.card : ℝ) := le_trans h_m56 hI_lb
          have h2 : (I.card : ℝ) ≤ (1 - 1 / 6 : ℝ) * (m : ℝ) := le_trans hI_ub h_m56_ub
          have h3 := hreg_16.2.2 I h1 h2
          linarith [le_of_abs_le h3]
        · have h_fat_bound := hFat.2.2.2.2
          have h_univ : uH A (proj (Finset.univ : Finset (Fin m))) = Real.log (A.card : ℝ) := by
            apply uH_proj_univ A hA
          have h_sigma : Q.sigma m ≤ s1 := by
            have h01 : effEnv 0 Q.sigma m ≤ effEnv 1 Q.sigma m := le_max_left _ _
            have h12 : effEnv 1 Q.sigma m ≤ effEnv 2 Q.sigma m := le_max_left _ _
            have h1 : Q.sigma m ≤ effEnv 2 Q.sigma m := le_trans h01 h12
            have h3 : 1 ≤ K3 / (1 / 6) := by linarith
            have hE2_nonneg : 0 ≤ effEnv 2 Q.sigma m := effEnv_nonneg 2 Q.sigma hQ.2.2.2.2.2.2.1.1 m
            have he1 : Q.sigma m ≤ effEnv 2 Q.sigma m + 1 := by linarith
            have he2 : 1 * (effEnv 2 Q.sigma m + 1) ≤ (K3 / (1 / 6)) * (effEnv 2 Q.sigma m + 1) := mul_le_mul_of_nonneg_right h3 (by linarith)
            have hs1_def : s1 = (K3 / (1 / 6)) * (effEnv 2 Q.sigma m + 1) := rfl
            linarith [hs1_def]
          rw [h_univ]
          have h_abs := h_fat_bound
          linarith [neg_le_of_abs_le h_abs]
      have hreg_pLow : blockRegular m A q pLow ((K3 / pLow) * (effEnv 2 Q.sigma m + 1)) := by
        apply hR3_bound pLow hpLow1 hpLow2 Q.sigma hQ.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2 m A q hA hFat hPinned
      apply hS2 m A q pLow ((K3 / pLow) * (effEnv 2 Q.sigma m + 1)) eps1 e hA hpLow1 hpLow2
      · have : 0 ≤ effEnv 2 Q.sigma m := effEnv_nonneg 2 Q.sigma hQ.2.2.2.2.2.2.1.1 m
        positivity
      · exact heps1_pos
      · dsimp [e]; positivity
      · exact hreg_pLow
      · exact hS1_apply
    · intro pLow hpLow1 hpLow2
      have hsig_nonneg : ∀ n : ℕ, 0 ≤ Q.sigma n :=
        hQ.2.2.2.2.2.2.1.1
      have hK3_nonneg : 0 ≤ K3 := by linarith
      have hE2_nonneg : 0 ≤ effEnv 2 Q.sigma m :=
        effEnv_nonneg 2 Q.sigma hsig_nonneg m
      have hE5_nonneg : 0 ≤ effEnv 5 Q.sigma m :=
        effEnv_nonneg 5 Q.sigma hsig_nonneg m
      have hE2_le_E5 : effEnv 2 Q.sigma m ≤ effEnv 5 Q.sigma m := by
        have h23 : effEnv 2 Q.sigma m ≤ effEnv 3 Q.sigma m := by
          change effEnv 2 Q.sigma m ≤ effGeo (effEnv 2 Q.sigma) m
          exact le_effGeo _ _
        have h34 : effEnv 3 Q.sigma m ≤ effEnv 4 Q.sigma m := by
          change effEnv 3 Q.sigma m ≤ effGeo (effEnv 3 Q.sigma) m
          exact le_effGeo _ _
        have h45 : effEnv 4 Q.sigma m ≤ effEnv 5 Q.sigma m := by
          change effEnv 4 Q.sigma m ≤ effGeo (effEnv 4 Q.sigma) m
          exact le_effGeo _ _
        exact h23.trans (h34.trans h45)
      have hE2p_le_E5p :
          effEnv 2 Q.sigma m + 1 ≤ effEnv 5 Q.sigma m + 1 := by
        linarith
      have hE5p_nonneg : 0 ≤ effEnv 5 Q.sigma m + 1 := by
        linarith
      have hGeom_le_E5p :
          Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
            effEnv 5 Q.sigma m + 1 := by
        have hGeom_le_E3 :
            Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
              effEnv 3 Q.sigma m := by
          change Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
            effGeo (effEnv 2 Q.sigma) m
          exact le_max_right _ _
        have h35 : effEnv 3 Q.sigma m ≤ effEnv 5 Q.sigma m := by
          have h34 : effEnv 3 Q.sigma m ≤ effEnv 4 Q.sigma m := by
            change effEnv 3 Q.sigma m ≤ effGeo (effEnv 3 Q.sigma) m
            exact le_effGeo _ _
          have h45 : effEnv 4 Q.sigma m ≤ effEnv 5 Q.sigma m := by
            change effEnv 4 Q.sigma m ≤ effGeo (effEnv 4 Q.sigma) m
            exact le_effGeo _ _
          exact h34.trans h45
        linarith
      have hs1_nonneg : 0 ≤ s1 := by
        have hcoef : 0 ≤ K3 / (1 / 6 : ℝ) :=
          div_nonneg hK3_nonneg (by norm_num)
        have henv : 0 ≤ effEnv 2 Q.sigma m + 1 := by linarith
        exact mul_nonneg hcoef henv
      have hC0 : 0 ≤ 7 * K3 := by nlinarith
      have hC1 : 1 ≤ 7 * K3 := by nlinarith [hK3]
      have hs1p_le : s1 + 1 ≤ (7 * K3) * (effEnv 2 Q.sigma m + 1) := by
        have henv : 1 ≤ effEnv 2 Q.sigma m + 1 := by linarith
        calc
          s1 + 1 = (6 * K3) * (effEnv 2 Q.sigma m + 1) + 1 := by
            dsimp [s1]
            ring
          _ ≤ (7 * K3) * (effEnv 2 Q.sigma m + 1) := by
            nlinarith [hK3, henv]
      have hsqrtC_le_C : Real.sqrt (7 * K3) ≤ 7 * K3 := by
        rw [Real.sqrt_le_iff]
        constructor
        · exact hC0
        · nlinarith [hC1]
      have hsqrt_s1_le :
          Real.sqrt ((s1 + 1) * ((m : ℝ) + 1)) ≤
            (7 * K3) * (effEnv 5 Q.sigma m + 1) := by
        have harg :
            (s1 + 1) * ((m : ℝ) + 1) ≤
              (7 * K3) * ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
          calc
            (s1 + 1) * ((m : ℝ) + 1)
                ≤ ((7 * K3) * (effEnv 2 Q.sigma m + 1)) * ((m : ℝ) + 1) :=
                  mul_le_mul_of_nonneg_right hs1p_le (by positivity)
            _ = (7 * K3) * ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
                  ring
        calc
          Real.sqrt ((s1 + 1) * ((m : ℝ) + 1))
              ≤ Real.sqrt ((7 * K3) *
                  ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1))) :=
                Real.sqrt_le_sqrt harg
          _ = Real.sqrt (7 * K3) *
                Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
                rw [Real.sqrt_mul hC0]
          _ ≤ (7 * K3) *
                Real.sqrt ((effEnv 2 Q.sigma m + 1) * ((m : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_right hsqrtC_le_C (Real.sqrt_nonneg _)
          _ ≤ (7 * K3) * (effEnv 5 Q.sigma m + 1) :=
                mul_le_mul_of_nonneg_left hGeom_le_E5p hC0
      have heps_mul_le :
          eps1 * (m : ℝ) ≤ (7 * K3) * (effEnv 5 Q.sigma m + 1) := by
        dsimp [eps1]
        exact (core_geomMean_mul_le s1 hs1_nonneg m).trans hsqrt_s1_le
      have hs1_div_eps_le :
          s1 / eps1 ≤ (7 * K3) * (effEnv 5 Q.sigma m + 1) := by
        dsimp [eps1]
        exact (core_div_geomMean_le s1 hs1_nonneg m).trans hsqrt_s1_le
      have hpLow_inv_one : 1 ≤ 1 / pLow := by
        rw [le_div_iff₀ hpLow1]
        linarith [hpLow2]
      have hbase :
          (K3 / pLow) * (effEnv 2 Q.sigma m + 1) ≤
            (K3 / pLow) * (effEnv 5 Q.sigma m + 1) := by
        exact mul_le_mul_of_nonneg_left hE2p_le_E5p
          (div_nonneg hK3_nonneg (le_of_lt hpLow1))
      have heps_as_p :
          eps1 * (m : ℝ) ≤
            ((7 * K3) / pLow) * (effEnv 5 Q.sigma m + 1) := by
        calc
          eps1 * (m : ℝ) ≤ (7 * K3) * (effEnv 5 Q.sigma m + 1) := heps_mul_le
          _ ≤ (1 / pLow) * ((7 * K3) * (effEnv 5 Q.sigma m + 1)) := by
                simpa [one_mul] using
                  mul_le_mul_of_nonneg_right hpLow_inv_one
                    (mul_nonneg hC0 hE5p_nonneg)
          _ = ((7 * K3) / pLow) * (effEnv 5 Q.sigma m + 1) := by ring
      have hlog_nonneg : 0 ≤ Real.log 2 := by positivity
      have hlog_le_one : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have he_le_plain :
          e * Real.log 2 ≤ (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by
        have he_inner : e ≤ (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by
          have hfour : 4 ≤ 4 * (effEnv 5 Q.sigma m + 1) := by nlinarith
          calc
            e = 12 * (s1 / eps1) + 4 := by
              dsimp [e]
              ring
            _ ≤ 12 * ((7 * K3) * (effEnv 5 Q.sigma m + 1)) +
                  4 * (effEnv 5 Q.sigma m + 1) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hs1_div_eps_le (by norm_num))
                  hfour
            _ = (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by ring
        have hcoef_nonneg : 0 ≤ (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by
          positivity
        calc
          e * Real.log 2
              ≤ ((84 * K3 + 4) * (effEnv 5 Q.sigma m + 1)) * Real.log 2 :=
                mul_le_mul_of_nonneg_right he_inner hlog_nonneg
          _ ≤ ((84 * K3 + 4) * (effEnv 5 Q.sigma m + 1)) * 1 :=
                mul_le_mul_of_nonneg_left hlog_le_one hcoef_nonneg
          _ = (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by ring
      have hlog_as_p :
          e * Real.log 2 ≤
            ((84 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1) := by
        have hcoef_nonneg : 0 ≤ (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := by
          positivity
        calc
          e * Real.log 2 ≤ (84 * K3 + 4) * (effEnv 5 Q.sigma m + 1) := he_le_plain
          _ ≤ (1 / pLow) * ((84 * K3 + 4) * (effEnv 5 Q.sigma m + 1)) := by
                simpa [one_mul] using
                  mul_le_mul_of_nonneg_right hpLow_inv_one hcoef_nonneg
          _ = ((84 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1) := by ring
      have hsum :
          (K3 / pLow) * (effEnv 2 Q.sigma m + 1) + eps1 * (m : ℝ) +
              e * Real.log 2 ≤
            ((92 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1) := by
        calc
          (K3 / pLow) * (effEnv 2 Q.sigma m + 1) + eps1 * (m : ℝ) +
              e * Real.log 2
              ≤ (K3 / pLow) * (effEnv 5 Q.sigma m + 1) +
                  ((7 * K3) / pLow) * (effEnv 5 Q.sigma m + 1) +
                  ((84 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1) :=
                add_le_add (add_le_add hbase heps_as_p) hlog_as_p
          _ = ((92 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1) := by ring
      have hcoef : (92 * K3 + 4) / 2 ≤ K_V := by
        have hleft : (92 * K3 + 4) / 2 ≤ K3 * 100 + 100 := by
          nlinarith [hK3]
        exact hleft.trans (le_max_left _ _)
      dsimp [vFam]
      calc
        (((K3 / pLow) * (effEnv 2 Q.sigma m + 1) + eps1 * (m : ℝ) +
              e * Real.log 2) / 2)
            ≤ (((92 * K3 + 4) / pLow) * (effEnv 5 Q.sigma m + 1)) / 2 :=
              div_le_div_of_nonneg_right hsum (by norm_num)
        _ = (((92 * K3 + 4) / 2) / pLow) * (effEnv 5 Q.sigma m + 1) := by ring
        _ ≤ (K_V / pLow) * (effEnv 5 Q.sigma m + 1) := by
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hcoef (le_of_lt hpLow1))
            hE5p_nonneg

noncomputable def s6_eff_p (Q : QData) (m : ℕ) : ℝ :=
  min (Real.sqrt ((effEnv 8 Q.sigma m + 1) / ((m : ℝ) + 1))) (1 / 2)

lemma s6_eff_p_bounds (Q : QData) (m : ℕ) (hQ : validQData Q) :
    0 < s6_eff_p Q m ∧ s6_eff_p Q m ≤ 1 / 2 := by
  unfold s6_eff_p
  constructor
  · apply lt_min
    · apply Real.sqrt_pos.mpr
      apply div_pos
      · have henv : 0 ≤ effEnv 8 Q.sigma m :=
          effEnv_nonneg 8 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
        linarith
      · positivity
    · norm_num
  · exact min_le_right _ _

lemma s6_eff_p_mul_le_effEnv8 (Q : QData) (m : ℕ) (hQ : validQData Q) :
    s6_eff_p Q m * (m : ℝ) ≤ effEnv 9 Q.sigma m := by
  let s := effEnv 8 Q.sigma m
  let M := (m : ℝ) + 1
  have hs : 0 ≤ s := by
    dsimp [s]
    exact effEnv_nonneg 8 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  have hs1 : 0 ≤ s + 1 := by linarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hsqrt_eq :
      Real.sqrt ((s + 1) / M) * M = Real.sqrt ((s + 1) * M) := by
    rw [Real.sqrt_div hs1 M, Real.sqrt_mul hs1 M]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hMpos)]
    rw [Real.sq_sqrt hM0]
  unfold s6_eff_p
  rw [show effEnv 9 Q.sigma m = effGeo (effEnv 8 Q.sigma) m by rfl]
  unfold effGeo
  dsimp [s, M]
  calc
    min (Real.sqrt ((effEnv 8 Q.sigma m + 1) / ((m : ℝ) + 1))) (1 / 2) *
          (m : ℝ)
        ≤ Real.sqrt ((effEnv 8 Q.sigma m + 1) / ((m : ℝ) + 1)) *
            (m : ℝ) := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg m)
    _ ≤ Real.sqrt ((effEnv 8 Q.sigma m + 1) / ((m : ℝ) + 1)) *
          ((m : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((effEnv 8 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
          simpa [s, M] using hsqrt_eq
    _ ≤ max (effEnv 8 Q.sigma m)
          (Real.sqrt ((effEnv 8 Q.sigma m + 1) * ((m : ℝ) + 1))) :=
          le_max_right _ _

/-- One grading step, squared: `(effEnv k s n + 1)(n+1) ≤ (effEnv (k+1) s n + 1)²`.
This is the defining geometric-mean lower bound for the envelope. -/
lemma s6_env_geo_sq (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (k n : ℕ) :
    (effEnv k s n + 1) * ((n : ℝ) + 1) ≤ (effEnv (k + 1) s n + 1) ^ 2 := by
  have hr : Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1)) ≤ effEnv (k + 1) s n := by
    rw [effEnv_succ]; exact le_max_right _ _
  have hrpos : 0 ≤ Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1)) := Real.sqrt_nonneg _
  have hnn : 0 ≤ (effEnv k s n + 1) * ((n : ℝ) + 1) :=
    mul_nonneg (by have := effEnv_nonneg k s hs n; linarith) (by positivity)
  have hsq : (Real.sqrt ((effEnv k s n + 1) * ((n : ℝ) + 1))) ^ 2 =
      (effEnv k s n + 1) * ((n : ℝ) + 1) := Real.sq_sqrt hnn
  nlinarith [hr, hrpos, hsq]

/-- The envelope is monotone in the grading level. -/
lemma s6_env_mono_grade (s : ℕ → ℝ) (k n : ℕ) :
    effEnv k s n ≤ effEnv (k + 1) s n := by
  rw [effEnv_succ]; exact le_effGeo _ _

/-- Cross bound at grades `5,7,8`: `(effEnv 5 + 1)(m+1) ≤ (effEnv 8 + 1)(effEnv 9 + 1)`. -/
lemma s6_env_need1 (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (m : ℕ) :
    (effEnv 5 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 8 s m + 1) * (effEnv 9 s m + 1) := by
  have g5 : (effEnv 5 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 6 s m + 1) ^ 2 :=
    s6_env_geo_sq s hs 5 m
  have g6 : (effEnv 6 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 8 s m + 1) ^ 2 := by
    nlinarith [s6_env_geo_sq s hs 6 m, s6_env_mono_grade s 7 m,
      effEnv_nonneg 7 s hs m, effEnv_nonneg 8 s hs m]
  have g7 : (effEnv 8 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 9 s m + 1) ^ 2 :=
    s6_env_geo_sq s hs 8 m
  have m56 : effEnv 5 s m ≤ effEnv 6 s m := s6_env_mono_grade s 5 m
  have m67 : effEnv 6 s m ≤ effEnv 8 s m :=
    le_trans (s6_env_mono_grade s 6 m) (s6_env_mono_grade s 7 m)
  have e5 := effEnv_nonneg 5 s hs m
  have hbN : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  set b5 := effEnv 5 s m + 1 with hb5d
  set b6 := effEnv 6 s m + 1 with hb6d
  set b7 := effEnv 8 s m + 1 with hb7d
  set b8 := effEnv 9 s m + 1 with hb8d
  set N := (m : ℝ) + 1 with hNd
  have hb5 : 0 ≤ b5 := by rw [hb5d]; linarith
  have hb7 : 0 ≤ b7 := by rw [hb7d]; linarith [effEnv_nonneg 8 s hs m]
  have hb8 : 0 ≤ b8 := by rw [hb8d]; linarith [effEnv_nonneg 9 s hs m]
  have h56 : b5 ≤ b6 := by rw [hb5d, hb6d]; linarith
  have h67 : b6 ≤ b7 := by rw [hb6d, hb7d]; linarith
  have step1 : (b6 * N) * (b7 * N) ≤ b7 ^ 2 * b8 ^ 2 :=
    mul_le_mul g6 g7 (by positivity) (by positivity)
  have hb5sq : b5 ^ 2 ≤ b6 * b7 := by nlinarith [h56, h67, hb5]
  have step2 : b5 ^ 2 * N ^ 2 ≤ (b6 * N) * (b7 * N) := by nlinarith [mul_nonneg hbN hbN, hb5sq]
  have key : (b5 * N) ^ 2 ≤ (b7 * b8) ^ 2 := by nlinarith [step1, step2]
  nlinarith [key, mul_nonneg hb7 hb8, mul_nonneg hb5 hbN]

/-- Cross bound at grades `7,8`: `(m+1) ≤ (effEnv 8 + 1)(effEnv 9 + 1)`. -/
lemma s6_env_need3 (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (m : ℕ) :
    ((m : ℝ) + 1) ≤ (effEnv 8 s m + 1) * (effEnv 9 s m + 1) := by
  have g6 : (effEnv 6 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 8 s m + 1) ^ 2 := by
    nlinarith [s6_env_geo_sq s hs 6 m, s6_env_mono_grade s 7 m,
      effEnv_nonneg 7 s hs m, effEnv_nonneg 8 s hs m]
  have g7 : (effEnv 8 s m + 1) * ((m : ℝ) + 1) ≤ (effEnv 9 s m + 1) ^ 2 :=
    s6_env_geo_sq s hs 8 m
  have e6 := effEnv_nonneg 7 s hs m
  have e7 := effEnv_nonneg 8 s hs m
  have e8 := effEnv_nonneg 9 s hs m
  set b7 := effEnv 8 s m + 1 with hb7d
  set b8 := effEnv 9 s m + 1 with hb8d
  set N := (m : ℝ) + 1 with hNd
  have hb7 : 0 ≤ b7 := by rw [hb7d]; linarith
  have hb8 : 0 ≤ b8 := by rw [hb8d]; linarith
  have hNb7 : N ≤ b7 ^ 2 := by
    have hb6 : (1 : ℝ) ≤ effEnv 6 s m + 1 := by
      linarith [effEnv_nonneg 6 s hs m]
    nlinarith [g6, hb6]
  have key : N ^ 2 ≤ (b7 * b8) ^ 2 := by nlinarith [g7, hNb7, mul_nonneg hb7 hb8]
  nlinarith [key, mul_nonneg hb7 hb8]

/-- Upper bound on `1/p²` for the effective `p = s6_eff_p`. -/
lemma s6_eff_invsq_le (Q : QData) (hQ : validQData Q) (m : ℕ) :
    1 / (s6_eff_p Q m) ^ 2 ≤ ((m : ℝ) + 1) / (effEnv 8 Q.sigma m + 1) + 4 := by
  have hs : 0 ≤ effEnv 8 Q.sigma m :=
    effEnv_nonneg 8 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  unfold s6_eff_p
  set s := effEnv 8 Q.sigma m with hsdef
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  set a := Real.sqrt ((s + 1) / ((m : ℝ) + 1)) with ha
  have ha2 : a ^ 2 = (s + 1) / ((m : ℝ) + 1) := by rw [ha]; exact Real.sq_sqrt (by positivity)
  rcases le_total a (1 / 2) with hle | hge
  · rw [min_eq_left hle, ha2, one_div_div]; linarith
  · rw [min_eq_right hge]; norm_num
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) / (s + 1) := by positivity
    linarith

/-- Upper bound on `(effEnv 8 + 1)/p` for the effective `p = s6_eff_p`. -/
lemma s6_eff_term2_le (Q : QData) (hQ : validQData Q) (m : ℕ) :
    (effEnv 8 Q.sigma m + 1) / (s6_eff_p Q m) ≤ 3 * (effEnv 9 Q.sigma m + 1) := by
  have hsig : ∀ n, 0 ≤ Q.sigma n := fun n => hQ.2.2.2.2.2.2.1.1 n
  have hs : 0 ≤ effEnv 8 Q.sigma m := effEnv_nonneg 8 Q.sigma hsig m
  have hE8 : 0 ≤ effEnv 9 Q.sigma m := effEnv_nonneg 9 Q.sigma hsig m
  have hgeo : (effEnv 8 Q.sigma m + 1) * ((m : ℝ) + 1) ≤ (effEnv 9 Q.sigma m + 1) ^ 2 :=
    s6_env_geo_sq Q.sigma hsig 8 m
  have hmono : effEnv 8 Q.sigma m ≤ effEnv 9 Q.sigma m := s6_env_mono_grade Q.sigma 8 m
  have hE8sqrt : Real.sqrt ((effEnv 8 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
      effEnv 9 Q.sigma m + 1 := by
    rw [show effEnv 9 Q.sigma m + 1 = Real.sqrt ((effEnv 9 Q.sigma m + 1) ^ 2) by
        rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hgeo
  unfold s6_eff_p
  set s := effEnv 8 Q.sigma m with hsdef
  set E8p := effEnv 9 Q.sigma m + 1 with hE8def
  have hsE8 : s + 1 ≤ E8p := by rw [hE8def]; linarith
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set a := Real.sqrt ((s + 1) / ((m : ℝ) + 1)) with ha
  have hapos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = (s + 1) / ((m : ℝ) + 1) := by rw [ha]; exact Real.sq_sqrt (by positivity)
  have hE8pos : 0 ≤ E8p := by rw [hE8def]; linarith
  rcases le_total a (1 / 2) with hle | hge
  · rw [min_eq_left hle]
    have hkey : (s + 1) / a = Real.sqrt ((s + 1) * ((m : ℝ) + 1)) := by
      have h1 : ((s + 1) / a) ^ 2 = (s + 1) * ((m : ℝ) + 1) := by rw [div_pow, ha2]; field_simp
      have h2 : 0 ≤ (s + 1) / a := by positivity
      rw [← h1, Real.sqrt_sq h2]
    rw [hkey]; linarith
  · rw [min_eq_right hge]
    have hhalf : (s + 1) / (1 / 2 : ℝ) = 2 * (s + 1) := by ring
    rw [hhalf]; linarith

lemma s6_eff_error_grade9 (Q : QData) (hQ : validQData Q)
    (K_V K_S5 : ℝ) (hKV : 1 ≤ K_V) (hKS5 : 1 ≤ K_S5) :
    ∃ K_err : ℝ, 1 ≤ K_err ∧
      ∀ m : ℕ, ∀ (vFam : ℝ → ℕ → ℝ) (bSlack : ℕ → ℝ),
        (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → vFam pLow m ≤ (K_V / pLow) * (effEnv 5 Q.sigma m + 1)) →
        bSlack m ≤ (K_S5 / (min Q.qMin Q.s0 / 2) ^ 4) * (effEnv 8 Q.sigma m + 1) →
        s6_errorBound (Q.mu0 / 2) vFam bSlack (s6_eff_p Q m) (s6_eff_p Q m / 2) m ≤
          K_err * (effEnv 9 Q.sigma m + 1) := by
  refine' ⟨ 40 * K_V / ( Q.mu0 / 2 ) ^ 2 + 6 * K_S5 / ( min Q.qMin Q.s0 / 2 ) ^ 4 + 80 / ( Q.mu0 / 2 ) ^ 2 + 1, _, _ ⟩;
  · exact le_add_of_nonneg_left ( add_nonneg ( add_nonneg ( div_nonneg ( by positivity ) ( sq_nonneg _ ) ) ( div_nonneg ( by positivity ) ( by positivity ) ) ) ( div_nonneg ( by positivity ) ( sq_nonneg _ ) ) );
  · intro m vFam bSlack hvf hbs
    set gap := Q.mu0 / 2
    set eps4 := (min Q.qMin Q.s0 / 2) ^ 4
    set p := s6_eff_p Q m
    set E5 := effEnv 5 Q.sigma m
    set E7 := effEnv 8 Q.sigma m
    set E8 := effEnv 9 Q.sigma m
    have hp_bounds : 0 < p ∧ p ≤ 1 / 2 := by
      exact s6_eff_p_bounds Q m hQ
    have hE5_le_E8 : E5 ≤ E8 := by
      exact le_trans (le_trans ( s6_env_mono_grade _ _ _ ) ( s6_env_mono_grade _ _ _ ))
        (le_trans ( s6_env_mono_grade _ _ _ ) ( s6_env_mono_grade _ _ _ ))
    have hE7_le_E8 : E7 ≤ E8 := by
      exact s6_env_mono_grade _ _ _
    have hE8_plus_one : 0 < E8 + 1 := by
      exact add_pos_of_nonneg_of_pos ( effEnv_nonneg _ _ ( fun n => hQ.2.2.2.2.2.2.1.1 n ) _ ) zero_lt_one
    have hE7_plus_one : 0 < E7 + 1 := by
      exact add_pos_of_nonneg_of_pos ( effEnv_nonneg _ _ ( fun n => hQ.2.2.2.2.2.2.1.1 n ) _ ) zero_lt_one
    have hE5_plus_one : 0 < E5 + 1 := by
      exact add_pos_of_nonneg_of_pos ( effEnv_nonneg _ _ ( fun n => hQ.2.2.2.2.2.2.1.1 n ) _ ) zero_lt_one
    generalize_proofs at *;
    have hT1 : (4 / gap ^ 2) * (vFam (p / 2) m / p) ≤ (40 * K_V / gap ^ 2) * (E8 + 1) := by
      have hT1 : vFam (p / 2) m / p ≤ 2 * K_V * (E5 + 1) / p^2 := by
        convert div_le_div_of_nonneg_right ( hvf ( p / 2 ) ( by linarith ) ( by linarith ) ) hp_bounds.1.le using 1 ; ring;
      have hT1_bound : (E5 + 1) / p^2 ≤ 5 * (E8 + 1) := by
        have hT1_bound : (E5 + 1) / p^2 ≤ (E5 + 1) * ((m + 1) / (E7 + 1) + 4) := by
          have := s6_eff_invsq_le Q hQ m; ring_nf at *; nlinarith;
        generalize_proofs at *;
        have hT1_bound : (E5 + 1) * (m + 1) / (E7 + 1) ≤ E8 + 1 := by
          have := s6_env_need1 Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) m; rw [ div_le_iff₀ ] <;> nlinarith;
        generalize_proofs at *;
        ring_nf at *; linarith;
      generalize_proofs at *;
      convert mul_le_mul_of_nonneg_left ( hT1.trans <| show 2 * K_V * ( E5 + 1 ) / p ^ 2 ≤ 10 * K_V * ( E8 + 1 ) by convert mul_le_mul_of_nonneg_left hT1_bound ( show 0 ≤ 2 * K_V by positivity ) using 1 <;> ring ) ( show 0 ≤ 4 / gap ^ 2 by positivity ) using 1 ; ring
    have hT2 : 2 * (bSlack m / p) ≤ (6 * K_S5 / eps4) * (E8 + 1) := by
      have hT2 : bSlack m / p ≤ (K_S5 / eps4) * (3 * (E8 + 1)) := by
        have hT2 : (E7 + 1) / p ≤ 3 * (E8 + 1) := by
          convert s6_eff_term2_le Q hQ m using 1;
        exact le_trans ( div_le_div_of_nonneg_right hbs hp_bounds.1.le ) ( by convert mul_le_mul_of_nonneg_left hT2 ( show 0 ≤ K_S5 / eps4 by exact div_nonneg ( by positivity ) ( by positivity ) ) using 1 ; ring );
      convert mul_le_mul_of_nonneg_left hT2 zero_le_two using 1 ; ring
    have hT3 : (4 / gap ^ 2) * (((m : ℝ) / p) * (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => ¬(p / 2 * (m : ℝ) ≤ J.card ∧ J.card ≤ (1 - p / 2) * (m : ℝ))), windowProb J p)) ≤ (80 / gap ^ 2) * (E8 + 1) := by
      have hT3 : (m : ℝ) / p * (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => ¬(p / 2 * (m : ℝ) ≤ J.card ∧ J.card ≤ (1 - p / 2) * (m : ℝ))), windowProb J p) ≤ 4 / p^2 := by
        have hT3 : (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => ¬(p / 2 * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - p / 2) * (m : ℝ))), windowProb J p) ≤ p / ((p - p / 2) ^ 2 * (m : ℝ)) := by
          convert s6_badWindow_mass_le m p ( p / 2 ) ( by linarith ) ( by linarith ) ( by linarith ) using 1
        generalize_proofs at *;
        refine le_trans ( mul_le_mul_of_nonneg_left hT3 <| div_nonneg ( Nat.cast_nonneg _ ) hp_bounds.1.le ) ?_ ; ring_nf ; norm_num [ hp_bounds.1.ne' ];
        by_cases hm : m = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        · positivity;
        · exact le_of_eq ( by rw [ ← div_eq_mul_inv ] ; rw [ inv_eq_one_div, div_eq_div_iff ] <;> ring_nf <;> nlinarith [ pow_pos hp_bounds.1 3 ] );
      have hT3 : 4 / p^2 ≤ 4 * ((m + 1) / (E7 + 1) + 4) := by
        have := s6_eff_invsq_le Q hQ m; ring_nf at *; linarith;
      generalize_proofs at *;
      have hT3 : (m + 1) / (E7 + 1) + 4 ≤ 5 * (E8 + 1) := by
        have hT3 : (m + 1) ≤ (E7 + 1) * (E8 + 1) := by
          exact s6_env_need3 Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) m |> le_trans ( by norm_num ) |> le_trans <| by nlinarith;
        generalize_proofs at *; (
        rw [ div_add', div_le_iff₀ ] <;> nlinarith only [ hT3, hE7_plus_one, hE8_plus_one, show ( effEnv 9 Q.sigma m : ℝ ) ≥ 0 from effEnv_nonneg 9 Q.sigma ( fun n => hQ.2.2.2.2.2.2.1.1 n ) m ] ;)
      generalize_proofs at *; (
      refine le_trans ( mul_le_mul_of_nonneg_left ‹_› <| by positivity ) ?_;
      convert mul_le_mul_of_nonneg_left ( show 4 / p ^ 2 ≤ 20 * ( E8 + 1 ) by linarith ) ( show 0 ≤ 4 / gap ^ 2 by positivity ) using 1 ; ring)
    generalize_proofs at *;
    unfold s6_errorBound; linarith;

/-- Fano entropy term at grade 10 (v0.3.4; the grade-9 form was REFUTED
by the E5 Aristotle pass: `m·H(e/m) ≈ e·log(m/e)` has an unavoidable
logarithmic loss over `e ~ effEnv 9` when `sigma = log`).

Route (easy at grade 10): `H y ≤ 2·√y` on `[0,1]` (as in
`Core/S5Transfer.lean`), so
`m·H(min(e/m,1/2)) ≤ 2·√(e·m) ≤ 2·√(K_err·(effEnv 9 σ m + 1)·(m+1))
  ≤ 2·√K_err·√((effEnv 9 σ m + 1)·((m:ℝ)+1)) ≤ 2·√K_err·(effEnv 10 σ m + 1)`
(the last step is `le_max_right` into the `effGeo` defining grade 10),
so `K_H := 2·√K_err + 1` works; handle `m = 0` separately
(`(0:ℝ)·H(…) = 0`). -/
lemma s6_eff_entropy_term_grade10 (Q : QData) (hQ : validQData Q)
    (K_err : ℝ) :
    ∃ K_H : ℝ, 1 ≤ K_H ∧
      ∀ m : ℕ, ∀ e : ℝ, 0 ≤ e →
        e ≤ K_err * (effEnv 9 Q.sigma m + 1) →
        (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) ≤ K_H * (effEnv 10 Q.sigma m + 1) := by
  let Kp : ℝ := max K_err 0
  refine ⟨2 * Real.sqrt Kp + 1, ?_, ?_⟩
  · have hKp0 : 0 ≤ Kp := by dsimp [Kp]; exact le_max_right _ _
    nlinarith [Real.sqrt_nonneg Kp]
  intro m e he0 he_bound
  have hsig : ∀ n, 0 ≤ Q.sigma n := fun n => hQ.2.2.2.2.2.2.1.1 n
  have hE8_nonneg : 0 ≤ effEnv 9 Q.sigma m := effEnv_nonneg 9 Q.sigma hsig m
  have hE9_nonneg : 0 ≤ effEnv 10 Q.sigma m := effEnv_nonneg 10 Q.sigma hsig m
  have hE8p_nonneg : 0 ≤ effEnv 9 Q.sigma m + 1 := by linarith
  have hKp0 : 0 ≤ Kp := by dsimp [Kp]; exact le_max_right _ _
  have he_bound_Kp : e ≤ Kp * (effEnv 9 Q.sigma m + 1) := by
    have hKle : K_err ≤ Kp := by dsimp [Kp]; exact le_max_left _ _
    exact he_bound.trans (mul_le_mul_of_nonneg_right hKle hE8p_nonneg)
  have hgeo : Real.sqrt ((effEnv 9 Q.sigma m + 1) * ((m : ℝ) + 1)) ≤
      effEnv 10 Q.sigma m := by
    rw [show effEnv 10 Q.sigma m = effGeo (effEnv 9 Q.sigma) m by rfl]
    exact le_max_right _ _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hright : 0 ≤ (2 * Real.sqrt Kp + 1) * (effEnv 10 Q.sigma 0 + 1) := by
      positivity
    simpa using hright
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hm_pos
  let y : ℝ := min (e / (m : ℝ)) (1 / 2)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact le_min (div_nonneg he0 hm_nonneg) (by norm_num)
  have hy1 : y ≤ 1 := by
    dsimp [y]
    exact (min_le_right _ _).trans (by norm_num)
  have hy_le : y ≤ e / (m : ℝ) := by
    dsimp [y]
    exact min_le_left _ _
  have hHsqrt : H y ≤ 2 * Real.sqrt y :=
    s5_binEntropy_le_two_mul_sqrt y hy0 hy1
  have h_sqrt_step :
      (m : ℝ) * Real.sqrt y ≤ Real.sqrt (e * (m : ℝ)) := by
    have hsq_nonneg : 0 ≤ e * (m : ℝ) := mul_nonneg he0 hm_nonneg
    refine Real.le_sqrt_of_sq_le ?_
    have hleft_sq :
        ((m : ℝ) * Real.sqrt y) ^ 2 = (m : ℝ) ^ 2 * y := by
      rw [mul_pow, Real.sq_sqrt hy0]
    have hsq_le : (m : ℝ) ^ 2 * y ≤ e * (m : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hy_le (sq_nonneg (m : ℝ))
      have hrewrite : (m : ℝ) ^ 2 * (e / (m : ℝ)) = e * (m : ℝ) := by
        field_simp [ne_of_gt hm_pos]
      simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [hleft_sq] using hsq_le
  have h_em_le :
      e * (m : ℝ) ≤ Kp * ((effEnv 9 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
    calc
      e * (m : ℝ) ≤ (Kp * (effEnv 9 Q.sigma m + 1)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right he_bound_Kp hm_nonneg
      _ ≤ (Kp * (effEnv 9 Q.sigma m + 1)) * ((m : ℝ) + 1) := by
        have hcoef : 0 ≤ Kp * (effEnv 9 Q.sigma m + 1) :=
          mul_nonneg hKp0 hE8p_nonneg
        exact mul_le_mul_of_nonneg_left (by linarith) hcoef
      _ = Kp * ((effEnv 9 Q.sigma m + 1) * ((m : ℝ) + 1)) := by ring
  have h_sqrt_env :
      Real.sqrt (e * (m : ℝ)) ≤ Real.sqrt Kp * (effEnv 10 Q.sigma m) := by
    calc
      Real.sqrt (e * (m : ℝ))
          ≤ Real.sqrt (Kp * ((effEnv 9 Q.sigma m + 1) * ((m : ℝ) + 1))) :=
            Real.sqrt_le_sqrt h_em_le
      _ = Real.sqrt Kp *
            Real.sqrt ((effEnv 9 Q.sigma m + 1) * ((m : ℝ) + 1)) := by
            rw [Real.sqrt_mul hKp0]
      _ ≤ Real.sqrt Kp * effEnv 10 Q.sigma m :=
            mul_le_mul_of_nonneg_left hgeo (Real.sqrt_nonneg _)
  calc
    (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2))
        = (m : ℝ) * H y := by rfl
    _ ≤ (m : ℝ) * (2 * Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hHsqrt hm_nonneg
    _ = 2 * ((m : ℝ) * Real.sqrt y) := by ring
    _ ≤ 2 * Real.sqrt (e * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left h_sqrt_step (by norm_num)
    _ ≤ 2 * (Real.sqrt Kp * effEnv 10 Q.sigma m) :=
        mul_le_mul_of_nonneg_left h_sqrt_env (by norm_num)
    _ ≤ (2 * Real.sqrt Kp + 1) * (effEnv 10 Q.sigma m + 1) := by
        nlinarith [Real.sqrt_nonneg Kp, hE9_nonneg]

/-- Analytic tail bound: whenever `p ≥ 1/(2√(m+1))` and `p > 0`, the
Hoeffding-like term `2·m·exp(-p·m/8)` is bounded by the absolute constant
`2048`, uniformly in `m`.  This uses `exp t ≥ t²/2` to get
`exp(-t) ≤ 2/t²`, then the lower bound on `p`. -/
lemma s6_eff_exp_tail (m : ℕ) (p : ℝ) (hp : 0 < p)
    (hpl : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ p) :
    2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ 2048 := by
  set M : ℝ := (m : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  rcases eq_or_lt_of_le hM0 with h0 | hpos
  · rw [← h0]; simp
  · have hmnat : 0 < m := by have h := hpos; rw [hM] at h; exact_mod_cast h
    have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast hmnat
    have hMne : M ≠ 0 := ne_of_gt hpos
    set t : ℝ := p * M / 8 with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have hexp : t ^ 2 / 2 ≤ Real.exp t := by
      have := Real.quadratic_le_exp_of_nonneg (le_of_lt htpos); linarith
    have hexpneg : Real.exp (-t) ≤ 2 / t ^ 2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by positivity)]
      have hmm : (2 / t ^ 2) * Real.exp t ≥ (2 / t ^ 2) * (t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have h2 : (2 / t ^ 2) * (t ^ 2 / 2) = 1 := by field_simp
      linarith
    have hrw : -p * M / 8 = -t := by rw [ht]; ring
    rw [hrw]
    have h1 : 2 * M * Real.exp (-t) ≤ 2 * M * (2 / t ^ 2) :=
      mul_le_mul_of_nonneg_left hexpneg (by positivity)
    have ht2 : t ^ 2 = p ^ 2 * M ^ 2 / 64 := by rw [ht]; ring
    have hp2 : 1 / (4 * (M + 1)) ≤ p ^ 2 := by
      have hsq : (Real.sqrt (M + 1)) ^ 2 = M + 1 := Real.sq_sqrt (by positivity)
      have hle : (1 / (2 * Real.sqrt (M + 1))) ^ 2 ≤ p ^ 2 := by
        apply sq_le_sq' _ hpl
        have : (0 : ℝ) ≤ 1 / (2 * Real.sqrt (M + 1)) := by positivity
        linarith [hpl]
      calc 1 / (4 * (M + 1)) = (1 / (2 * Real.sqrt (M + 1))) ^ 2 := by
            rw [div_pow, one_pow, mul_pow, hsq]; ring
        _ ≤ p ^ 2 := hle
    have hpM : 1 ≤ 8 * p ^ 2 * M := by
      have hstep := mul_le_mul_of_nonneg_right hp2 (by positivity : (0 : ℝ) ≤ 8 * M)
      have hlhs : 1 / (4 * (M + 1)) * (8 * M) = 2 * M / (M + 1) := by field_simp; ring
      have hge : 1 ≤ 2 * M / (M + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
      have hrhs : p ^ 2 * (8 * M) = 8 * p ^ 2 * M := by ring
      rw [hlhs, hrhs] at hstep
      linarith
    have hfin : 2 * M * (2 / t ^ 2) ≤ 2048 := by
      have hval : 2 * M * (2 / t ^ 2) = 256 / (p ^ 2 * M) := by
        rw [ht2]; field_simp; ring
      rw [hval, div_le_iff₀ (by positivity)]
      nlinarith [hpM]
    linarith

lemma s6_eff_exp_remainder (Q : QData) (hQ : validQData Q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℕ, 2 * (m : ℝ) * Real.exp (-s6_eff_p Q m * (m : ℝ) / 8) ≤ C := by
  refine ⟨2048, by norm_num, ?_⟩
  intro m
  have hs : 0 ≤ effEnv 8 Q.sigma m :=
    effEnv_nonneg 8 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
  have hp : 0 < s6_eff_p Q m := (s6_eff_p_bounds Q m hQ).1
  have hmc : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hpl : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ s6_eff_p Q m := by
    unfold s6_eff_p
    have hm1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
      calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
        _ ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hspos : 0 < Real.sqrt ((m : ℝ) + 1) := by apply Real.sqrt_pos.mpr; positivity
    apply le_min
    · have hmono : Real.sqrt (1 / ((m : ℝ) + 1)) ≤
          Real.sqrt ((effEnv 8 Q.sigma m + 1) / ((m : ℝ) + 1)) := by
        apply Real.sqrt_le_sqrt; gcongr; linarith
      have heq : Real.sqrt (1 / ((m : ℝ) + 1)) = 1 / Real.sqrt ((m : ℝ) + 1) := by
        rw [one_div, Real.sqrt_inv, one_div]
      have hstep : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hspos; linarith
      rw [heq] at hmono; linarith
    · apply one_div_le_one_div_of_le (by norm_num); linarith
  exact s6_eff_exp_tail m (s6_eff_p Q m) hp hpl

lemma s6_eff_apply_s3 (_hS3 : S3Statement)
    (m : ℕ) (A : Finset (Cube m)) (q qMax eps gap : ℝ)
    (hq_le : q ≤ qMax) (hqMax : qMax < 1 / 2)
    (heps : 0 < eps) (hgap : 0 < gap) (hgap_le : qMax + eps ≤ 1 / 2 - gap)
    (vFam : ℝ → ℕ → ℝ) (bSlack : ℕ → ℝ)
    (hA : A.Nonempty)
    (h_var : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → varianceBudgetLE A pLow (vFam pLow m))
    (h_bad : averageBadStepsLE A q eps (bSlack m))
    (hv_nonneg : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → 0 ≤ vFam pLow m)
    (hb_nonneg : 0 ≤ bSlack m)
    (p pLow : ℝ) (hpLow_pos : 0 < pLow) (hpLow_le : pLow ≤ p) (hp : p ≤ 1 / 2) :
    uH A (fun x t => coord t (predictableCenter A x)) ≤
      2 * Real.log 2 * p * (m : ℝ) +
      (m : ℝ) *
        H (min (s6_errorBound gap vFam bSlack p pLow m / (m : ℝ)) (1 / 2)) +
      s6_errorBound gap vFam bSlack p pLow m * Real.log 2 +
      2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
  classical
  have hpLow_half : pLow ≤ 1 / 2 := hpLow_le.trans hp
  have hp_pos : 0 < p := hpLow_pos.trans_le hpLow_le
  have hp_one : p ≤ 1 := hp.trans (by norm_num)
  let e : ℝ := s6_errorBound gap vFam bSlack p pLow m
  have hv_nonneg_val : 0 ≤ vFam pLow m := hv_nonneg pLow hpLow_pos hpLow_half
  have hsum_nonneg :=
    s6_badWindow_sum_nonneg m p pLow (le_of_lt hp_pos) hp_one
  have he_nonneg : 0 ≤ e := by
    dsimp [e, s6_errorBound]
    have h1 : (0 : ℝ) ≤ (4 / gap ^ 2) * (vFam pLow m / p) :=
      mul_nonneg (by positivity) (div_nonneg hv_nonneg_val (le_of_lt hp_pos))
    have h2 : (0 : ℝ) ≤ 2 * (bSlack m / p) :=
      mul_nonneg (by norm_num) (div_nonneg hb_nonneg (le_of_lt hp_pos))
    have h3 : (0 : ℝ) ≤ (4 / gap ^ 2) * (((m : ℝ) / p) *
        ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
          ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧
            (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
          windowProb J p) := by
      have hm : (0 : ℝ) ≤ (m : ℝ) / p := by positivity
      have h4 : (0 : ℝ) ≤ 4 / gap ^ 2 := by positivity
      exact mul_nonneg h4 (mul_nonneg hm hsum_nonneg)
    linarith
  have hErr :
      expectedEstimatorError A
        (fun x t => coord t (predictableCenter A x))
        (centerMajorityEstimator A) p ≤ e := by
    dsimp [e, s6_errorBound]
    exact s6_expectedEstimatorError_le A q qMax eps gap p pLow (vFam pLow m)
      (bSlack m) hA hv_nonneg_val hb_nonneg hq_le hqMax heps hgap hgap_le
      hpLow_pos hpLow_le hp
      (h_var pLow hpLow_pos hpLow_half) h_bad
  have hS3_apply := _hS3 m A (Real.log 2) 0 Bool
    (fun x t => coord t (predictableCenter A x)) p e 2
    hA (by positivity) (by norm_num) hp_pos hp he_nonneg (by norm_num)
    (by
      intro I _ _
      have hproj := s6_uH_proj_le_log_two_mul A hA I
      linarith)
    (by
      intro t
      have hcard :
          (@Finset.image (Cube m) Bool
            (fun a b => Classical.propDecidable (a = b))
            (fun x => (fun x t => coord t (predictableCenter A x)) x t) A).card ≤ 2 := by
        simpa using
          (Finset.card_le_univ
            (s := @Finset.image (Cube m) Bool
              (fun a b => Classical.propDecidable (a = b))
              (fun x => (fun x t => coord t (predictableCenter A x)) x t) A))
      exact_mod_cast hcard)
    ⟨centerMajorityEstimator A, center_majority_estimator_dependsOnWindow A, hErr⟩
  simpa [e, zero_add, s6_errorBound] using hS3_apply

theorem s6_eff_grade10_from_current_route (hR3 : R3Eff) (_hS4 : S4Eff) (hS5 : S5Eff)
    (hS1 : S1Statement) (hS2 : S2Statement) (hS3 : S3Statement) :
    ∀ (Q : QData), validQData Q →
      ∃ K : ℝ, 1 ≤ K ∧
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty → fat Q m A q → pinned Q m A q →
          uH A (predictableCenter A) ≤ K * (effEnv 10 Q.sigma m + 1) := by
  intro Q hQ
  obtain ⟨K_V, hK_V, hvFam⟩ := s6_eff_variance_grade5 hR3 hS1 hS2 Q hQ
  obtain ⟨K_S5, hK_S5, hbSlack⟩ := hS5 Q hQ
  obtain ⟨K_err, hK_err, herr_bound⟩ := s6_eff_error_grade9 Q hQ K_V K_S5 hK_V hK_S5
  obtain ⟨K_H, hK_H, hH_bound⟩ := s6_eff_entropy_term_grade10 Q hQ K_err
  obtain ⟨C, hC, hC_bound⟩ := s6_eff_exp_remainder Q hQ
  let K := 2 * Real.log 2 + K_H + K_err * Real.log 2 + C
  have hK : 1 ≤ K := by
    dsimp [K]
    have h1 : 0 ≤ 2 * Real.log 2 := by positivity
    have h2 : 0 ≤ K_err * Real.log 2 := by positivity
    linarith
  refine ⟨K, hK, ?_⟩
  intro m A q hA hFat hPinned
  have h_vFam := hvFam m A q hA hFat hPinned
  obtain ⟨vFam', hvFam_bound1', hvFam_bound2'⟩ := h_vFam
  let vFam := fun p m => max 0 (vFam' p m)
  have hvFam_bound1 : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → varianceBudgetLE A pLow (vFam pLow m) := by
    intro pL hpL1 hpL2
    unfold varianceBudgetLE
    intro W hW1 hW2
    exact le_trans (hvFam_bound1' pL hpL1 hpL2 W hW1 hW2) (le_max_right _ _)
  have hvFam_bound2 : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → vFam pLow m ≤ (K_V / pLow) * (effEnv 5 Q.sigma m + 1) := by
    intro pL hpL1 hpL2
    have h1 : 0 ≤ K_V := by linarith [hK_V]
    have h2 : 0 ≤ effEnv 5 Q.sigma m + 1 := by
      have : 0 ≤ effEnv 5 Q.sigma m := effEnv_nonneg 5 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
      linarith
    have h3 : 0 ≤ (K_V / pL) * (effEnv 5 Q.sigma m + 1) := mul_nonneg (div_nonneg h1 (le_of_lt hpL1)) h2
    exact max_le h3 (hvFam_bound2' pL hpL1 hpL2)
  let eps := min Q.qMin Q.s0 / 2
  have heps : 0 < eps := by
    dsimp [eps]
    have h1 : 0 < Q.qMin := hQ.1
    have h2 : 0 < Q.s0 := hQ.2.2.2.1
    exact half_pos (lt_min h1 h2)
  have heps_lt : eps < Q.qMin := by
    dsimp [eps]
    have h1 : 0 < Q.qMin := hQ.1
    have h2 : min Q.qMin Q.s0 ≤ Q.qMin := min_le_left _ _
    calc min Q.qMin Q.s0 / 2
      ≤ Q.qMin / 2 := by linarith
      _ < Q.qMin := by linarith
  have hbSlack_bound := hbSlack eps heps heps_lt m A q hA hFat hPinned
  let bSlack := fun m => (K_S5 / eps ^ 4) * (effEnv 8 Q.sigma m + 1)
  have h_bad : averageBadStepsLE A q eps (bSlack m) := hbSlack_bound
  let p := s6_eff_p Q m
  let pLow := p / 2
  have hp_bounds := s6_eff_p_bounds Q m hQ
  have hpLow_pos : 0 < pLow := half_pos hp_bounds.1
  have hpLow_le : pLow ≤ p := by
    dsimp [pLow]
    have h1 : 0 < p := hp_bounds.1
    linarith
  have hpLow_half : pLow ≤ 1 / 2 := by linarith [hp_bounds.2]
  have h_var : varianceBudgetLE A pLow (vFam pLow m) := hvFam_bound1 pLow hpLow_pos hpLow_half
  have hv_nonneg : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → 0 ≤ vFam pLow m := fun _ _ _ => le_max_left _ _
  have hb_nonneg : 0 ≤ bSlack m := by
    dsimp [bSlack]
    have h_env : 0 ≤ effEnv 8 Q.sigma m + 1 := by
      exact add_nonneg (effEnv_nonneg 8 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m) zero_le_one
    positivity
  let gap := Q.mu0 / 2
  have hgap : 0 < gap := half_pos hQ.2.2.2.2.1
  have hgap_le : Q.qMax + eps ≤ 1 / 2 - gap := by
    dsimp [eps, gap]
    have h1 : Q.qMax + Q.s0 ≤ 1 / 2 - Q.mu0 := hQ.2.2.2.2.2.1
    have h2 : min Q.qMin Q.s0 ≤ Q.s0 := min_le_right _ _
    have h3 : 0 ≤ Q.s0 := by linarith [hQ.2.2.2.1]
    have h4 : 0 ≤ Q.mu0 := by linarith [hQ.2.2.2.2.1]
    linarith
  have hq_le : q ≤ Q.qMax := hFat.2.2.2.1
  have hqMax : Q.qMax < 1 / 2 := hQ.2.2.1
  have h_apply := s6_eff_apply_s3 hS3 m A q Q.qMax eps gap hq_le hqMax heps hgap hgap_le vFam bSlack hA hvFam_bound1 h_bad hv_nonneg hb_nonneg p pLow hpLow_pos hpLow_le hp_bounds.2
  have h_center := uH_predictableCenter_le_coordField A
  have h_err_bound := herr_bound m vFam bSlack hvFam_bound2 (le_refl _)
  have he_nonneg : 0 ≤ s6_errorBound gap vFam bSlack p pLow m := by
    dsimp [s6_errorBound]
    have hsum_nonneg := s6_badWindow_sum_nonneg m p pLow (le_of_lt hp_bounds.1) (hp_bounds.2.trans (by norm_num))
    have h1 : 0 ≤ (4 / gap ^ 2) * (vFam pLow m / p) := mul_nonneg (by positivity) (div_nonneg (hv_nonneg pLow hpLow_pos hpLow_half) (le_of_lt hp_bounds.1))
    have h2 : 0 ≤ 2 * (bSlack m / p) := mul_nonneg (by norm_num) (div_nonneg hb_nonneg (le_of_lt hp_bounds.1))
    have h3 : 0 ≤ (4 / gap ^ 2) * (((m : ℝ) / p) * ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))), windowProb J p) := mul_nonneg (by positivity) (mul_nonneg (div_nonneg (Nat.cast_nonneg m) (le_of_lt hp_bounds.1)) hsum_nonneg)
    linarith
  have hH := hH_bound m (s6_errorBound gap vFam bSlack p pLow m) he_nonneg h_err_bound
  have h_term1 : 2 * Real.log 2 * p * (m : ℝ) ≤ (2 * Real.log 2) * (effEnv 9 Q.sigma m + 1) := by
    have h_pm : p * (m : ℝ) ≤ effEnv 9 Q.sigma m := s6_eff_p_mul_le_effEnv8 Q m hQ
    have h_log : 0 ≤ 2 * Real.log 2 := by positivity
    calc 2 * Real.log 2 * p * (m : ℝ) = (2 * Real.log 2) * (p * (m : ℝ)) := by ring
      _ ≤ (2 * Real.log 2) * (effEnv 9 Q.sigma m) := mul_le_mul_of_nonneg_left h_pm h_log
      _ ≤ (2 * Real.log 2) * (effEnv 9 Q.sigma m + 1) := by linarith
  have h_term3 : s6_errorBound gap vFam bSlack p pLow m * Real.log 2 ≤ (K_err * Real.log 2) * (effEnv 9 Q.sigma m + 1) := by
    have h_log : 0 ≤ Real.log 2 := by positivity
    calc s6_errorBound gap vFam bSlack p pLow m * Real.log 2
      ≤ (K_err * (effEnv 9 Q.sigma m + 1)) * Real.log 2 := mul_le_mul_of_nonneg_right h_err_bound h_log
      _ = (K_err * Real.log 2) * (effEnv 9 Q.sigma m + 1) := by ring
  have h_term4 : 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ C * (effEnv 9 Q.sigma m + 1) := by
    have h_C := hC_bound m
    have h_env : 1 ≤ effEnv 9 Q.sigma m + 1 := by
      have : 0 ≤ effEnv 9 Q.sigma m := effEnv_nonneg 9 Q.sigma (fun n => hQ.2.2.2.2.2.2.1.1 n) m
      linarith
    calc 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)
      ≤ C := h_C
      _ = C * 1 := by ring
      _ ≤ C * (effEnv 9 Q.sigma m + 1) := mul_le_mul_of_nonneg_left h_env hC
  have h8le9 : effEnv 9 Q.sigma m + 1 ≤ effEnv 10 Q.sigma m + 1 := by
    have := s6_env_mono_grade Q.sigma 9 m
    linarith
  have h_term1_9 : 2 * Real.log 2 * p * (m : ℝ) ≤ (2 * Real.log 2) * (effEnv 10 Q.sigma m + 1) :=
    le_trans h_term1 (mul_le_mul_of_nonneg_left h8le9 (by positivity))
  have h_term3_9 : s6_errorBound gap vFam bSlack p pLow m * Real.log 2 ≤ (K_err * Real.log 2) * (effEnv 10 Q.sigma m + 1) := by
    refine le_trans h_term3 (mul_le_mul_of_nonneg_left h8le9 ?_)
    have h_log : 0 ≤ Real.log 2 := by positivity
    have : 0 ≤ K_err := by linarith [hK_err]
    positivity
  have h_term4_9 : 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) ≤ C * (effEnv 10 Q.sigma m + 1) :=
    le_trans h_term4 (mul_le_mul_of_nonneg_left h8le9 hC)
  have h_bound : uH A (fun x t => coord t (predictableCenter A x)) ≤ K * (effEnv 10 Q.sigma m + 1) := by
    dsimp [K]
    calc uH A (fun x t => coord t (predictableCenter A x))
      ≤ 2 * Real.log 2 * p * (m : ℝ) + (m : ℝ) * H (min (s6_errorBound gap vFam bSlack p pLow m / (m : ℝ)) (1 / 2)) + s6_errorBound gap vFam bSlack p pLow m * Real.log 2 + 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := h_apply
      _ ≤ (2 * Real.log 2) * (effEnv 10 Q.sigma m + 1) + K_H * (effEnv 10 Q.sigma m + 1) + (K_err * Real.log 2) * (effEnv 10 Q.sigma m + 1) + C * (effEnv 10 Q.sigma m + 1) := add_le_add (add_le_add (add_le_add h_term1_9 hH) h_term3_9) h_term4_9
      _ = (2 * Real.log 2 + K_H + K_err * Real.log 2 + C) * (effEnv 10 Q.sigma m + 1) := by ring
  exact h_center.trans h_bound

theorem s6_eff (hR3 : R3Eff) (hS4 : S4Eff) (hS5 : S5Eff)
    (hS1 : S1Statement) (hS2 : S2Statement) (hS3 : S3Statement) :
    S6Eff :=
  s6_eff_grade10_from_current_route hR3 hS4 hS5 hS1 hS2 hS3

end HarperStability
