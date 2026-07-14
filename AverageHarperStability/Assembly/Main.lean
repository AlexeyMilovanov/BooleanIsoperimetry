import AverageHarperStability.Distribution.Main
import AverageHarperStability.Sets.Cover

open Filter Set
open scoped Topology

namespace AverageHarperStability

lemma isLaw_uniformMass {n : ℕ} {A : Finset (Cube n)} (hA : A.Nonempty) :
    IsLaw (uniformMass A) := by
  classical
  constructor
  · intro x
    simp only [uniformMass]
    split <;> positivity
  · simp [uniformMass, hA.card_ne_zero]

lemma entropyRate_uniformMass {n : ℕ} {A : Finset (Cube n)} (hA : A.Nonempty) :
    entropyRate n (uniformMass A) = setEntropyRate n A := by
  classical
  have hcard : (A.card : ℝ) ≠ 0 := by positivity
  have hentropy : entropy (uniformMass A) = Real.log (A.card : ℝ) := by
    rw [entropy]
    calc
      ∑ x, Real.negMulLog (uniformMass A x) =
          ∑ x ∈ A, Real.negMulLog (1 / (A.card : ℝ)) := by
            simp only [uniformMass, apply_ite, Real.negMulLog_zero]
            rw [Finset.sum_ite]
            simp
      _ = Real.log (A.card : ℝ) := by
        simp [Real.negMulLog, Real.log_inv, hcard]
  unfold entropyRate setEntropyRate
  rw [hentropy]

lemma tendsto_assemblyErr2 {err : ℝ → ℝ} (h : Tendsto err (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    Tendsto (fun delta ↦ Real.sqrt (err delta) + 2 * err delta + delta)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hsqrt : Tendsto (fun delta ↦ Real.sqrt (err delta))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp h
  have hid : Tendsto (fun delta : ℝ ↦ delta)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := tendsto_id.mono_left inf_le_left
  simpa only [add_assoc, mul_zero, add_zero] using hsqrt.add ((h.const_mul 2).add hid)

lemma assemblyErr2_pos {err : ℝ → ℝ} {delta : ℝ} (h_pos : 0 < err delta) (hd : 0 < delta) :
    0 < Real.sqrt (err delta) + 2 * err delta + delta := by
  positivity

lemma coverConclusion_mono {n : ℕ} {A : Finset (Cube n)} {eps1 eps2 r1 r2 : ℝ}
    (heps : eps1 ≤ eps2) (hr : r1 ≤ r2) (h : coverConclusion A eps1 r1) :
    coverConclusion A eps2 r2 := by
  classical
  rcases h with ⟨centers, hcenters, hmiss⟩
  refine ⟨centers, ?_, ?_⟩
  · exact hcenters.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg n)))
  · calc
      ((A \ coveredByBalls A centers r2).card : ℝ) ≤
          ((A \ coveredByBalls A centers r1).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (by
              intro x hx
              rw [Finset.mem_sdiff] at hx ⊢
              refine ⟨hx.1, ?_⟩
              intro hxcover
              apply hx.2
              simp only [coveredByBalls, Finset.mem_filter] at hxcover ⊢
              rcases hxcover with ⟨hxA, c, hc, hdist⟩
              exact ⟨hxA, c, hc, hdist.trans hr⟩)
      _ ≤ eps1 * (A.card : ℝ) := hmiss
      _ ≤ eps2 * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg A.card)

lemma large_n_bound (delta : ℝ) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → 1 / (n : ℝ) ≤ delta := by
  have ht : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < delta :=
    (tendsto_order.1 ht).2 delta hdelta
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  exact (hN n (le_trans (le_max_right _ _) hn)).le

/-- Formal combinatorial average-Harper stability theorem. -/
theorem average_harper_set_stability : AverageHarperSetStabilityStatement := by
  intro tau zeta htau1 htau2 hzeta1 hzeta2
  rcases distribution_average_harper_stability tau zeta htau1 htau2 hzeta1 hzeta2 with ⟨delta0, hdelta0_pos, err, herr_tendsto, herr_pos, H_dist⟩
  use delta0, hdelta0_pos
  let err2 : ℝ → ℝ := fun delta ↦ Real.sqrt (err delta) + 2 * err delta + delta
  use err2
  refine ⟨tendsto_assemblyErr2 herr_tendsto, ?_, ?_⟩
  · intro delta hd hd0
    exact assemblyErr2_pos (herr_pos delta hd hd0) hd
  · intro delta hd hd0
    rcases large_n_bound delta hd with ⟨n0, hn0_1, hn0_bound⟩
    use n0, hn0_1
    intro n A hn0 hnA
    dsimp only
    intro h_zeta_p1 h_zeta_p2 h_entropy
    have hn1 : 1 ≤ n := hn0_1.trans hn0
    have H_dist_A :=
      H_dist n (uniformMass A) delta hn1 (isLaw_uniformMass hnA) hd hd0
    rw [entropyRate_uniformMass hnA] at H_dist_A
    have hdist := H_dist_A h_zeta_p1 h_zeta_p2 h_entropy
    rcases hdist with ⟨D, hlabel, htail⟩
    let radius1 :=
      ((hbInv (setEntropyRate n A) + err delta +
        Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ))
    have hcover := entropy_labels_to_cover n A D (err delta)
      (err delta + 1 / (n : ℝ)) radius1 hn1 hnA (herr_pos delta hd hd0)
      (add_nonneg (herr_pos delta hd hd0).le (one_div_nonneg.mpr (Nat.cast_nonneg n)))
      hlabel (by simpa [radius1, entropyRate_uniformMass hnA] using htail)
    apply coverConclusion_mono (h := hcover)
    · dsimp [err2]
      have hnrecip := hn0_bound n hn0
      linarith
    · dsimp [radius1, err2]
      gcongr
      nlinarith [Real.sqrt_nonneg (err delta), herr_pos delta hd hd0]

end AverageHarperStability
