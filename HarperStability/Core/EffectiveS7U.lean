import HarperStability.Core.EffectiveS7
import HarperStability.Interface.EffectiveUniform

/-!
# Uniform S7 (v0.4)

Target: `S7EffU` — the grade-10 heavy ball with class-only `K`.

Route: binder reshuffle of the CLOSED `s7_eff` in `Core/EffectiveS7.lean`:
its `K` collects `K₅` (from `hS5U`), `K₆` (from `hS6U`) and absolute
constants — obtain both BEFORE introducing `sigma`; the
`massSlack`/`s8`/`s9` ladder is `sigma`-pointwise.  The `K/eps^8`
threshold and the `exp`-mass shape are verbatim.  Do NOT modify the
frozen interfaces.
-/

namespace HarperStability

theorem s7_effU (_hR3 : R3Eff) (hS5U : S5EffU) (hS6U : S6EffU) : S7EffU := by
  intro qMin qMax s0 mu0 hqMin_pos hqMin_le_qMax hqMax_lt_half hs0_pos hmu0_pos hqMax_add_s0_le
  rcases hS5U qMin qMax s0 mu0 hqMin_pos hqMin_le_qMax hqMax_lt_half hs0_pos hmu0_pos hqMax_add_s0_le with ⟨K5, hK5, hS5_eps⟩
  rcases hS6U qMin qMax s0 mu0 hqMin_pos hqMin_le_qMax hqMax_lt_half hs0_pos hmu0_pos hqMax_add_s0_le with ⟨K6, hK6, hS6_eps⟩
  let K := max (K5 * Real.log 2) ((5 / 2) * K6 + 2)
  have hK_ge1 : 1 ≤ K := by
    have h1 : 1 ≤ (5 / 2 : ℝ) * K6 + 2 := by linarith
    exact le_trans h1 (le_max_right _ _)
  refine ⟨K, hK_ge1, ?_⟩
  intro sigma hSublinear hlog eps heps heps_qMin heps_qMax m hm A q hA hfat hpinned
  have heps_half : eps ≤ 1 / 2 := by
    linarith [heps_qMax, hqMax_lt_half]
  have hq_nonneg : 0 ≤ q := by
    exact (le_of_lt hqMin_pos).trans hfat.2.2.1
  have hqeps : q + eps ≤ 1 / 2 := by
    linarith [hfat.2.2.2.1, heps_qMax]
  let massSlack := (K5 / eps ^ 4) * (effEnv 8 sigma m + 1)
  have hPF : averageBadStepsLE A q eps massSlack :=
    hS5_eps sigma hSublinear hlog eps heps heps_qMin m A q hA hfat hpinned
  have hCenterBound : uH A (predictableCenter A) ≤ K6 * (effEnv 10 sigma m + 1) :=
    hS6_eps sigma hSublinear hlog m A q hA hfat hpinned
  have h_m_pos : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h_m_strict_pos : 0 < (m : ℝ) := by
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK_ge1
    exact lt_of_lt_of_le (div_pos hK_pos (pow_pos heps 8)) hm
  let s7 := effEnv 8 sigma m
  let s8 := effEnv 10 sigma m
  let s9 := effEnv 10 sigma m
  have hSigma_nonneg : ∀ n, 0 ≤ sigma n := hSublinear.1
  have hs9_nonneg : 0 ≤ s9 := by
    simpa [s9] using effEnv_nonneg 10 sigma hSigma_nonneg m
  have hs8_lower : Real.sqrt ((s7 + 1) * (m + 1)) ≤ s9 := by
    calc Real.sqrt ((s7 + 1) * (m + 1)) ≤ effEnv 9 sigma m := le_max_right _ _
      _ ≤ s9 := le_max_left _ _
  have hs9_lower : s8 ≤ s9 := le_refl _
  have hlog_nonneg : 0 ≤ Real.log 2 := by positivity
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
      s7_eff_math_large heps heps_half hK5 (le_max_left _ _) h_m_pos hs8_lower h_mass hlog_nonneg
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
