import AverageHarperStability.Interface.Definitions

open scoped Topology
open Filter Set

/-!
# Frozen theorem statements

These declarations are the trust boundary. Proof workers may not edit them.
The headline theorem is exactly the combinatorial (set/minimizer) form: a
near-minimizer of noisy entropy is covered, up to vanishing relative mass,
by exponentially few Hamming balls of asymptotically optimal radius.
-/

namespace AverageHarperStability

/-- Distribution-level stability, including the corrected finite-n tail. -/
def DistributionStabilityStatement : Prop :=
  ∀ tau zeta : ℝ,
    0 < tau → tau < 1 / 2 → 0 < zeta → zeta ≤ 1 / 4 →
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∃ err : ℝ → ℝ,
      Tendsto err (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      (∀ delta, 0 < delta → delta ≤ delta0 → 0 < err delta) ∧
      ∀ (n : ℕ) (mu : Cube n → ℝ) (delta : ℝ),
        1 ≤ n → IsLaw mu → 0 < delta → delta ≤ delta0 →
        let u := entropyRate n mu
        let p := hbInv u
        zeta ≤ p → p ≤ 1 / 2 - zeta →
        entropy (noiseMass tau mu) ≤
          (n : ℝ) * mglCurve tau u + delta * (n : ℝ) →
        distributionStabilityConclusion (err delta) mu

/-- Generic entropy-pigeonhole bridge used to pass from a low-entropy label
and a global distance tail to a union of few balls. -/
def EntropyLabelsToCoverStatement : Prop :=
  ∀ (n : ℕ) (A : Finset (Cube n)) (D : Cube n → Cube n)
      (a b radius : ℝ),
    1 ≤ n → A.Nonempty → 0 < a → 0 ≤ b →
    entropy (mapMass (uniformMass A) D) ≤ a * (n : ℝ) →
    eventMass (uniformMass A)
      (fun x => radius < (hDist x (D x) : ℝ)) ≤ b →
    coverConclusion A (Real.sqrt a + a + b) radius

/-- Headline combinatorial average-Harper stability theorem. -/
def AverageHarperSetStabilityStatement : Prop :=
  ∀ tau zeta : ℝ,
    0 < tau → tau < 1 / 2 → 0 < zeta → zeta ≤ 1 / 4 →
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∃ err2 : ℝ → ℝ,
      Tendsto err2 (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      (∀ delta, 0 < delta → delta ≤ delta0 → 0 < err2 delta) ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ (n : ℕ) (A : Finset (Cube n)),
        n0 ≤ n → A.Nonempty →
        let u := setEntropyRate n A
        let p := hbInv u
        zeta ≤ p → p ≤ 1 / 2 - zeta →
        entropy (noiseMass tau (uniformMass A)) ≤
          (n : ℝ) * mglCurve tau u + delta * (n : ℝ) →
        coverConclusion A (err2 delta)
          ((p + err2 delta +
              Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ))

end AverageHarperStability
