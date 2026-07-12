import HarperStability.Process.EffectiveS4
import HarperStability.Interface.EffectiveUniform

/-!
# Uniform S4 (v0.4)
-/

namespace HarperStability

set_option maxHeartbeats 10000000 in
theorem s4_effU (hR3 : R3Eff) (hS1 : S1Statement) (hS2 : S2Statement)
    (hS3 : S3Statement) : S4EffU := by
  intro qMin qMax s0 mu0 hqMin hqMax1 hqMax2 hs0 hmu0 hqMax3
  have h_ex_K3 := hR3 qMin qMax s0 mu0 hqMin hqMax1 hqMax2 hs0 hmu0 hqMax3
  -- We use obtain instead of Classical.choose as S4EffU is a Prop
  obtain ⟨K3, hK31, hR3b⟩ := h_ex_K3
  obtain ⟨K_V, hKVdef⟩ : ∃ K, K = 30 + K3 + 13 * Real.sqrt (6 * K3 + 1) := ⟨_, rfl⟩
  obtain ⟨K_err, hKerrdef⟩ : ∃ K, K = 4 * Real.sqrt (83 * K_V) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 1024 * K_err + 16384 := ⟨_, rfl⟩
  have hsq0 : 0 ≤ Real.sqrt (6 * K3 + 1) := Real.sqrt_nonneg _
  have hKV1 : 1 ≤ K_V := by
    rw [hKVdef]; linarith
  have hKV : 1 ≤ K_V := hKV1
  have hKV83 : 1 ≤ 83 * K_V := by linarith
  have hsq1 : 1 ≤ Real.sqrt (83 * K_V) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hKV83
  have hKerr1 : 1 ≤ K_err := by
    rw [hKerrdef]; linarith
  refine ⟨K, ?_, ?_⟩
  · rw [hKdef]
    linarith
  · intro sigma hSub hLog eps heps m A q hA hfat hpinned
    have h_ex_Q : ∃ Q : QData, sigma = Q.sigma ∧ validQData Q := by
      use ⟨qMin, qMax, s0, mu0, sigma⟩
      refine ⟨rfl, ?_⟩
      exact ⟨hqMin, hqMax1, hqMax2, hs0, hmu0, hqMax3, hSub, hLog⟩
    obtain ⟨Q, hQsigma, hQ⟩ := h_ex_Q
    subst hQsigma
    have h_ex_vFam : ∃ vFam : ℝ → ℕ → ℝ,
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 → 0 ≤ vFam pLow m) ∧
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
            varianceBudgetLE A pLow (vFam pLow m)) ∧
        (∀ pLow, 0 < pLow → pLow ≤ 1/2 →
            vFam pLow m ≤ (K_V / pLow) * (effEnv 2 Q.sigma m + 1)
              + K_V * (effEnv 3 Q.sigma m + 1)) := by
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
    obtain ⟨vFam, hv0, hv1, hv2⟩ := h_ex_vFam
    have hKerr : s4_errorBound (eps / 4) vFam (s4_eff_p2 Q m) m ≤
          (K_err / eps) * ((effEnv 4 Q.sigma m + 1) +
            Real.sqrt (Real.sqrt (Real.sqrt
              ((effEnv 3 Q.sigma m + 1) ^ 3 * ((m : ℝ) + 1) ^ 5)))) := by
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
      have hvS := hv2 (p / 2) hphalf_pos hphalf_le
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
        apply s4_le_of_sq_le (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (sq_nonneg _)
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
      rw [hKerrdef]
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

    have hpin := hpinned
    rw [hKdef]
    have hE5nn : 0 ≤ effEnv 5 Q.sigma m := effGeo_nonneg _ _
    have hE51 : (0:ℝ) ≤ effEnv 5 Q.sigma m + 1 := by linarith
    have hKnn : (0:ℝ) < 1024 * K_err + 16384 := by linarith
    have hRHSnn : 0 ≤ ((1024 * K_err + 16384) / eps ^ 4) * (effEnv 5 Q.sigma m + 1) := by
      have h4 : (0:ℝ) < eps ^ 4 := pow_pos heps 4
      exact mul_nonneg (div_nonneg (by linarith) h4.le) (by linarith)
    by_cases hbig : 4 ≤ eps
    · refine ⟨0, le_refl _, by linarith, ?_⟩
      have hwbig : 1 / 2 < eps / 4 := by linarith
      rw [s4_uH_binnedFold_trivial m A (eps / 4) hwbig]
      exact hRHSnn
    push_neg at hbig
    obtain ⟨hp0, hp13⟩ := s4_eff_p2_bounds Q m
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
    have he : e ≤ (K_err / eps) * ((E4 + 1) + R) := hKerr
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
          rw [← add_div, ← add_div, ← add_div]
          exact (div_le_div_iff_of_pos_right heps4).mpr (by linarith)
        have hprod := mul_le_mul_of_nonneg_right hcoef hE51
        nlinarith [hprod]
      linarith [hT1, hT3, hT4, hT5]
    exact hsum.trans hzero
end HarperStability
