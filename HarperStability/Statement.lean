import HarperStability.Assembly
import HarperStability.Assembly.EffectiveUniform

/-!
# Statement guard

Each `example` below re-states a headline theorem's type **without naming the
`...Statement` abbreviation**, and discharges it with the proved theorem.
If the top-level shape of any statement ever changes, the corresponding
`example` stops type-checking and the build (hence CI) fails.

Together with the frozen `.interface.sha256` — which pins the inner definitions
(`validData`, `degradedData`, `CoverFor`, `classMember`, `effDegrade`, …) — and
the `#print axioms` audit (`scripts/audit_axioms.lean`), this pins the entire
human-trusted surface. Plain-English walkthrough:
`docs/STABILITY_HARPER_STATEMENT.md`.

`effMainGrade` is spelled out as the literal `14` on purpose: if the certified
grade ever changes, these guards fail loudly.
-/

namespace HarperStability

/-- Coarse `o(n)` version: some sublinear output slack. -/
example :
    ∀ (Din : StabilityData) (epsCover : ℝ),
      validData Din → 0 < epsCover →
      ∃ Dout : StabilityData, degradedData Din Dout ∧ CoverFor Din Dout epsCover :=
  main_finite_skeleton

/-- Effective version: explicit envelope `σ_out = K·(effEnv 14 σ n + 1)`,
`K` allowed to depend on `σ`. -/
example :
    ∀ (Din : StabilityData) (epsCover : ℝ),
      validData Din → 0 < epsCover →
      ∃ K : ℝ, 1 ≤ K ∧
        degradedData Din (effDegrade Din K 14) ∧
        CoverFor Din (effDegrade Din K 14) epsCover :=
  main_finite_effective

/-- Uniform version (the ideal form): a single `K` depending only on the class
reals `(rho, deltaCap, cSize, alphaMin, alphaMax)` and `epsCover`, quantified
BEFORE `σ`. -/
example :
    ∀ (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ),
      0 < rho → 0 < deltaCap → deltaCap < 1 → 1 ≤ cSize →
      0 < alphaMin → alphaMin ≤ alphaMax → alphaMax < 1 / 2 → 0 < epsCover →
      ∃ K : ℝ, 1 ≤ K ∧
        ∀ (sigma : ℕ → ℝ), Sublinear sigma →
          (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
          degradedData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
              (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K 14) ∧
            CoverFor ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
              (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K 14)
              epsCover :=
  main_finite_effective_uniform

/-- Consistency: the uniform statement implies the effective one. -/
example : MainFiniteEffectiveUniformStatement → MainFiniteEffectiveStatement :=
  main_finite_effective_of_uniform

/-- Consistency: the effective route re-derives the coarse `o(n)` statement. -/
example :
    ∀ (Din : StabilityData) (epsCover : ℝ),
      validData Din → 0 < epsCover →
      ∃ Dout : StabilityData, degradedData Din Dout ∧ CoverFor Din Dout epsCover :=
  main_finite_via_effective

end HarperStability
