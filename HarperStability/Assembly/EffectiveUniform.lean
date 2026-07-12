import HarperStability.Assembly.Effective
import HarperStability.Interface.EffectiveUniform
import HarperStability.Process.EffectiveS4U
import HarperStability.Core.EffectiveS5U
import HarperStability.Core.EffectiveS6U
import HarperStability.Core.EffectiveS7U
import HarperStability.Reductions.EffectiveR2U
import HarperStability.Reductions.EffectiveR1U

/-!
# Uniform effective assembly (v0.4): the ideal formulation

Target: `main_finite_effective_uniform : MainFiniteEffectiveUniformStatement`
— compose `r3_eff → s4_effU → s5_effU → s6_effU → s7_effU → r2_effU →
r1a_effU` exactly as `main_finite_effective` does, keeping every constant
extraction BEFORE the `∀ sigma` introduction, and package `degradedData`
via `effDegrade_degraded` at `effMainGrade`.

Also derive the sanity corollary
`main_finite_effective_of_uniform : MainFiniteEffectiveUniformStatement →
MainFiniteEffectiveStatement` (destructure `validData D`, apply the
uniform statement at `D.rho, …, D.alphaMax, epsCover`, then at `D.sigma`;
`⟨D.rho, D.deltaCap, D.cSize, D.alphaMin, D.alphaMax, D.sigma⟩ ≡ D` by
structure eta).  Do NOT modify the frozen interfaces.
-/

namespace HarperStability

theorem main_finite_effective_uniform : MainFiniteEffectiveUniformStatement := by
  let hBV := ball_volume_two_sided_eff
  let hIVC := interior_volume_calculus_eff
  let hVP := vplus_skeleton
  let hIV := interior_v_skeleton
  let hS1 := S1_skeleton
  let hS2 := S2_skeleton
  let hS3 := S3_skeleton

  let hR3 := r3_eff hBV hVP hIVC
  let hS4 := s4_effU hR3 hS1 hS2 hS3
  let hS5 := s5_effU hR3 hS4 hS1 hS2
  let hS6 := s6_effU hR3 hS4 hS5 hS1 hS2 hS3
  let hS7 := s7_effU hR3 hS5 hS6
  let hR2 := r2_effU hS7 hBV hVP hIVC
  let hR1a := r1a_effU hBV hVP hIV hIVC

  let hHBL := hR2
  let hCover := hR1a hHBL

  intro rho deltaCap cSize alphaMin alphaMax epsCover hrho hdeltaCap hdeltaCap1 hcSize halphaMin halphaMax halphaMaxHalf hepsCover
  rcases hCover rho deltaCap cSize alphaMin alphaMax epsCover hrho hdeltaCap hdeltaCap1 hcSize halphaMin halphaMax halphaMaxHalf hepsCover with ⟨K, hK, hCoverK⟩
  use K, hK
  intro sigma hsublin hlog
  have hvalid : validData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ :=
    ⟨hrho, hdeltaCap, hdeltaCap1, hcSize, halphaMin, halphaMax, halphaMaxHalf, hsublin, hlog⟩
  have hDegrade := effDegrade_degraded ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ hvalid hK effMainGrade
  exact ⟨hDegrade, hCoverK sigma hsublin hlog⟩

theorem main_finite_effective_of_uniform : MainFiniteEffectiveUniformStatement → MainFiniteEffectiveStatement := by
  intro hU Din epsCover hDin heps
  rcases hDin with ⟨hrho, hdeltaCap, hdeltaCap1, hcSize, halphaMin, halphaMax, halphaMaxHalf, hsublin, hlog⟩
  rcases hU Din.rho Din.deltaCap Din.cSize Din.alphaMin Din.alphaMax epsCover hrho hdeltaCap hdeltaCap1 hcSize halphaMin halphaMax halphaMaxHalf heps with ⟨K, hK, hCoverK⟩
  use K, hK
  have ⟨hdeg, hcov⟩ := hCoverK Din.sigma hsublin hlog
  have heta : (StabilityData.mk Din.rho Din.deltaCap Din.cSize Din.alphaMin Din.alphaMax Din.sigma) = Din := by
    cases Din
    rfl
  rw [heta] at hdeg hcov
  exact ⟨hdeg, hcov⟩

end HarperStability
