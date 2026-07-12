import HarperStability.Interface
import HarperStability.Volume
import HarperStability.Entropy
import HarperStability.Reductions
import HarperStability.Process
import HarperStability.Core

namespace HarperStability

/-!
Assembly layer.

Besides the root aggregator, this is the only proof-layer module that imports
all worker modules.  The monorepo policy is: `Volume` and `Entropy` are
upstream toolkit libraries; cross-worker theorem dependencies are still passed
explicitly as statement hypotheses.  The import DAG is enforced by
`scripts/audit.sh`.
-/

theorem q_from_s7_skeleton : QFromS7Statement := by
  intro hS7 Q hQ delta eta hdelta heta
  let eps : ℝ := min (delta / 8) (min (Q.qMin / 2) ((1 / 2 - Q.qMax) / 2))
  have hqMin_pos : 0 < Q.qMin := hQ.1
  have hqMax_lt : Q.qMax < 1 / 2 := hQ.2.2.1
  have hgap_pos : 0 < 1 / 2 - Q.qMax := by linarith
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have heps_lt_qMin : eps < Q.qMin := by
    have heps_le : eps ≤ Q.qMin / 2 := by
      dsimp [eps]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have heps_lt_gap : eps < 1 / 2 - Q.qMax := by
    have heps_le : eps ≤ (1 / 2 - Q.qMax) / 2 := by
      dsimp [eps]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  rcases hS7 Q hQ eps heps_pos heps_lt_qMin heps_lt_gap with
    ⟨env, henv, m1, hm1⟩
  rcases henv with ⟨_henv_nonneg, henv_sublinear⟩
  rcases henv_sublinear (eta / 2) (by linarith) with ⟨N, hN⟩
  refine ⟨max m1 (max N 1), ?_⟩
  intro m hm A q hWitness
  rcases hWitness with ⟨hFat, hPinned, hBad⟩
  have hm_m1 : m ≥ m1 :=
    le_trans (Nat.le_max_left m1 (max N 1)) hm
  have hm_N : m ≥ N :=
    le_trans (le_trans (Nat.le_max_left N 1) (Nat.le_max_right m1 (max N 1))) hm
  have hm_one : m ≥ 1 :=
    le_trans (le_trans (Nat.le_max_right N 1) (Nat.le_max_right m1 (max N 1))) hm
  have hA_nonempty : A.Nonempty := hFat.1
  rcases hm1 m hm_m1 A q hA_nonempty hFat hPinned with ⟨a, hHeavy⟩
  have henv_le_half : env m ≤ (eta / 2) * (m : ℝ) := hN m hm_N
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_one
  have henv_lt_eta : env m < eta * (m : ℝ) := by nlinarith
  have hexp_lt : Real.exp (-eta * (m : ℝ)) < Real.exp (-(env m)) := by
    rw [Real.exp_lt_exp]
    linarith
  have hA_card_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hA_nonempty)
  have hmass_lt :
      Real.exp (-eta * (m : ℝ)) * (A.card : ℝ) <
        Real.exp (-(env m)) * (A.card : ℝ) :=
    mul_lt_mul_of_pos_right hexp_lt hA_card_pos
  have heps_le_delta : 4 * eps ≤ delta := by
    have heps_le : eps ≤ delta / 8 := by
      dsimp [eps]
      exact min_le_left _ _
    nlinarith
  have hceil_le :
      Nat.ceil ((q + 4 * eps) * (m : ℝ)) ≤
        Nat.ceil ((q + delta) * (m : ℝ)) := by
    apply Nat.ceil_mono
    nlinarith [show 0 ≤ (m : ℝ) by exact_mod_cast Nat.zero_le m]
  have hfilter_le :
      (((A.filter fun x =>
        hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))).card : ℕ) : ℝ) ≤
        (((A.filter fun x =>
          hDist x a ≤ Nat.ceil ((q + delta) * (m : ℝ))).card : ℕ) : ℝ) := by
    exact_mod_cast
      (Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 hceil_le⟩))
  have hbad_a :
      (((A.filter fun x =>
        hDist x a ≤ Nat.ceil ((q + delta) * (m : ℝ))).card : ℕ) : ℝ) ≤
        Real.exp (-eta * (m : ℝ)) * (A.card : ℝ) :=
    hBad a
  have hcontr :
      Real.exp (-(env m)) * (A.card : ℝ) ≤
        Real.exp (-eta * (m : ℝ)) * (A.card : ℝ) :=
    le_trans hHeavy (le_trans hfilter_le hbad_a)
  exact (not_lt_of_ge hcontr) hmass_lt

theorem component_package_skeleton : A0Statement := by
  let hBV := ball_volume_two_sided_skeleton
  let hVP := vplus_skeleton
  let hVC := interior_volume_calculus_skeleton
  let hR3 : R3Statement := R3_skeleton hBV hVP hVC
  let hS2 : S2Statement := S2_skeleton
  let hS3 : S3Statement := S3_skeleton
  let hS4 : S4Statement := S4_skeleton hS3
  let hS5 : S5Statement := S5_skeleton hR3 S1_skeleton hS2 hS4
  let hS6 : S6Statement := S6_skeleton hS3
  let hS7 : S7Statement := S7_skeleton hR3 S1_skeleton hS2 hS5 hS6
  exact ⟨hBV, hVP, interior_v_skeleton, hVC,
    R1a_skeleton hBV hVP hVC, R1b_skeleton, R2_skeleton hBV hVP hVC, hR3,
    S1_skeleton, hS2, hS3, hS4, hS5, hS6, hS7, q_from_s7_skeleton⟩

theorem main_from_components (h : A0Statement) : MainFiniteStatement := by
  -- R2 gives Q/HBL; QFromS7 supplies Q from S7; R1a upgrades HBL to cover.
  rcases h with
    ⟨_hBallVolume, _hVPlus, _hInteriorV, _hInteriorCalc,
      hR1a, _hR1b, hR2, _hR3,
      _hS1, _hS2, _hS3, _hS4, _hS5, _hS6, hS7, hQFromS7⟩
  intro Din epsCover hDin heps
  exact hR1a Din epsCover hDin heps
    (fun D hD => hR2 (hQFromS7 hS7) D hD)

theorem main_finite_skeleton : MainFiniteStatement := by
  exact main_from_components component_package_skeleton

end HarperStability
