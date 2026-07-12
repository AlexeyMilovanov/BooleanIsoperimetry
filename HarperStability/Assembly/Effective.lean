import HarperStability.Interface.Effective
import HarperStability.Core.Basic
import HarperStability.Assembly.Basic
import HarperStability.Volume.Effective
import HarperStability.Reductions.EffectiveR3
import HarperStability.Reductions.EffectiveR2
import HarperStability.Reductions.EffectiveR1
import HarperStability.Process.EffectiveS4
import HarperStability.Core.EffectiveS5
import HarperStability.Core.EffectiveS6
import HarperStability.Core.EffectiveS7

/-!
# Effective assembly (v0.3)

Proved here, once and for all:

* `effGeo_sublinear` / `effEnv_sublinear` — graded envelopes of a
  sublinear slack are sublinear;
* `effDegrade_degraded` — the effective degradation is a legal
  `degradedData` step;
* `mainFinite_of_effective` — **the o(n) main theorem
  (`MainFiniteStatement`, frozen v0.2) is a corollary of the effective
  statement at ANY grade** — this is the bridge the v0.3 program exists
  for.

Left as the assembly target (`main_finite_effective`): compose the
effective components.  Recipe:

1. `hHBL : ∀ D, validData D → ∃ K ≥ 1, HBLFor D (effDegrade D K 14)`
   from `r2_eff` applied to `s7_eff` (which consumes `r3_eff`,
   `s5_eff`, `s6_eff`, which consume `s4_eff`, ...), with the v0.2
   inputs discharged by the PROVED skeletons: `VPlusStatement`,
   `InteriorVStatement`, `S1Statement`, `S2Statement`, `S3Statement`
   are all available from `component_package_skeleton`
   (`Assembly/Basic.lean`); the effective volume statements come from
   `ball_volume_two_sided_eff` / `interior_volume_calculus_eff`.
2. `r1a_eff ... hHBL` gives the grade-14 cover.
3. Pair with `effDegrade_degraded Din hDin hK 13` to produce
   `MainFiniteEffectiveAt 13 = MainFiniteEffectiveStatement`.

No new mathematics: this is constant-plumbing over proved components.
-/

namespace HarperStability

lemma effGeo_sublinear {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effGeo s) := by
  refine core_Sublinear_of_le (fun n => effGeo_nonneg s n) (fun n => ?_)
    (core_Sublinear_add hs (core_Sublinear_geomMean hs))
  exact max_le_add_of_nonneg (hs.1 n) (Real.sqrt_nonneg _)

lemma effEnv_sublinear (k : ℕ) {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effEnv k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact effGeo_sublinear ih

/-- The effective degradation is a legal degradation step. -/
theorem effDegrade_degraded (D : StabilityData) (hD : validData D)
    {K : ℝ} (hK : 1 ≤ K) (k : ℕ) :
    degradedData D (effDegrade D K k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hD
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hsig_nonneg : ∀ n, 0 ≤ D.sigma n := h8.1
  have hle : ∀ n, D.sigma n ≤ K * (effEnv k D.sigma n + 1) := by
    intro n
    have h1' := le_effEnv k D.sigma n
    have h2' := effEnv_nonneg k D.sigma hsig_nonneg n
    nlinarith
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩,
    rfl, rfl, le_refl _, rfl, rfl, hle⟩
  · have hE : Sublinear (effEnv k D.sigma) := effEnv_sublinear k h8
    have hE1 : Sublinear (fun n => effEnv k D.sigma n + 1) :=
      core_Sublinear_add hE
        (core_Sublinear_const (show (0 : ℝ) ≤ 1 by norm_num))
    exact core_Sublinear_smul hK0 hE1
  · intro n hn
    exact (h9 n hn).trans (hle n)

/-- **The bridge**: the frozen o(n) main theorem is a corollary of the
effective statement at any grade. -/
theorem mainFinite_of_effective (k : ℕ) (h : MainFiniteEffectiveAt k) :
    MainFiniteStatement := by
  intro Din epsCover hDin heps
  obtain ⟨K, _hK, hdeg, hcov⟩ := h Din epsCover hDin heps
  exact ⟨effDegrade Din K k, hdeg, hcov⟩

/-- The effective main theorem (assembly target; see the module
docstring for the recipe). -/
theorem main_finite_effective : MainFiniteEffectiveStatement := by
  let hBV := ball_volume_two_sided_eff
  let hIVC := interior_volume_calculus_eff
  let hVP := vplus_skeleton
  let hIV := interior_v_skeleton
  let hS1 := S1_skeleton
  let hS2 := S2_skeleton
  let hS3 := S3_skeleton

  let hR3 := r3_eff hBV hVP hIVC
  let hS4 := s4_eff hR3 hS1 hS2 hS3
  let hS5 := s5_eff hR3 hS4 hS1 hS2
  let hS6 := s6_eff hR3 hS4 hS5 hS1 hS2 hS3
  let hS7 := s7_eff hR3 hS5 hS6
  let hR2 := r2_eff hS7 hBV hVP hIVC
  let hR1a := r1a_eff hBV hVP hIV hIVC

  let hHBL := hR2
  let hCover := hR1a hHBL
  intro Din epsCover hDin heps
  rcases hCover Din epsCover hDin heps with ⟨K, hK, hCoverK⟩
  have hDegrade := effDegrade_degraded Din hDin hK effMainGrade
  exact ⟨K, hK, hDegrade, hCoverK⟩

/-- Sanity: the v0.2 main theorem re-derived through the effective
route (the original `main_finite_skeleton` remains the canonical
fully verified proof; this corollary certifies the bridge). -/
theorem main_finite_via_effective : MainFiniteStatement :=
  mainFinite_of_effective effMainGrade main_finite_effective

end HarperStability
