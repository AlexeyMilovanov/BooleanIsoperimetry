# The average-Harper statement (for a reviewer)

This document isolates the theorem proved by the `AverageHarperStability`
library. The Lean kernel checks the proof; a human reviewer only needs to check
that the frozen statement below expresses the intended combinatorial theorem.

## Scope

This is the **combinatorial/set (minimizer) form** of average-Harper stability.
It does not claim the Kolmogorov-complexity form and does not include the
online-enumeration Step 6 needed for that separate application.

## Plain-English statement

Fix noise `tau` strictly between `0` and `1/2`, and keep the entropy density a
fixed distance `zeta` from both endpoints `0` and `1/2`. Then there is a
positive near-minimality threshold `delta0` and an error function tending to
zero with `delta` such that, for every sufficiently large dimension, every
nonempty set `A` whose noisy entropy is within `delta * n` of the MGL minimum
is covered, apart from an `err2(delta)` fraction of its points, by at most
`exp (err2(delta) * n)` Hamming balls. Their radius is

```text
(hbInv(setEntropyRate n A) + err2(delta)
  + sqrt(2 * log n / n)) * n.
```

Thus the number of centers is subexponential and the radius excess over the
entropy-optimal radius is `o(n)` as `delta -> 0` and `n -> infinity`.

## Frozen Lean statement

```lean
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
```

The theorem inhabiting it is:

```lean
theorem AverageHarperStability.average_harper_set_stability :
  AverageHarperStability.AverageHarperSetStabilityStatement
```

The exact source of the frozen contract is
`AverageHarperStability/Interface/Statements.lean`; its hash, together with
the definitions it uses, is protected by `.interface.sha256`.

## Trust and reproducibility

The strict audit rejects `sorry`, project-defined `axiom`, `admit`, `unsafe`,
`implemented_by`, `native_decide`, and disabled heartbeat limits. It builds
both libraries and checks the headline theorem's axioms. The expected result
is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Reproduce it with:

```bash
export PATH="$HOME/.elan/bin:$PATH"
STRICT_NO_SORRY=1 STRICT_AXIOMS=1 bash scripts/audit.sh
```
