# Harper and average-Harper stability formalizations

This repository contains two complete Lean 4 / Mathlib developments on the
Hamming cube:

- `HarperStability`: a **stability version of Harper's vertex-isoperimetric
  inequality**. If a set has near-minimal boundary, then all but an
  `ε`-fraction of it is covered by few Hamming balls of near-optimal radius.
- `AverageHarperStability`: the **combinatorial/set form of average-Harper
  stability**. A finite set whose noisy entropy is nearly MGL-minimal is
  covered, up to vanishing relative mass, by exponentially few Hamming balls
  of asymptotically optimal radius.

**Status: fully proved. Zero `sorry`.** The main theorems depend only on the
standard axioms `[propext, Classical.choice, Quot.sound]`.

Six interface files contain the frozen trusted statements and definitions;
their hashes are recorded in `.interface.sha256` and checked by the audit.

## Reviewing the result

The accompanying paper proof is available as
**[Robust Harper Stability at the Exponential Scale](docs/robust-harper-stability-at-the-exponential-scale.pdf)**.

If you only care about *what is proved* (not the proof or the constants), start
with **[`docs/STABILITY_HARPER_STATEMENT.md`](docs/STABILITY_HARPER_STATEMENT.md)**.
It explains the main theorem and every definition it depends on.  The core
executable statement surface is **[`Challenge.lean`](Challenge.lean)**: it
imports only Mathlib and is checked against the proved theorem by
[`leanprover/comparator`](https://github.com/leanprover/comparator).  See the
**[Comparator certificate](comparator/README.md)** and the transparent project
metadata in **[`formalization.yaml`](formalization.yaml)**.  Comparator's trust
base also includes the small Lake configuration, the dependency lockfile, and
the pinned checking tools described by the certificate.

For the average-Harper theorem, see
**[`docs/AVERAGE_HARPER_STATEMENT.md`](docs/AVERAGE_HARPER_STATEMENT.md)**.

## Average-Harper theorem

The frozen headline is:

```lean
theorem AverageHarperStability.average_harper_set_stability :
  AverageHarperStability.AverageHarperSetStabilityStatement
```

It is the minimizer/set side only. Kolmogorov complexity and the separate
online-enumeration Step 6 are deliberately outside this theorem's scope.

The proof is exposed through three independently reviewable entry points:

```text
distribution_average_harper_stability
  → entropy_labels_to_cover
  → average_harper_set_stability
```

They implement, respectively, distribution-level stability, the
entropy-labels-to-cover bridge, and the final set theorem. Their contracts are
the frozen `DistributionStabilityStatement`,
`EntropyLabelsToCoverStatement`, and `AverageHarperSetStabilityStatement`.

## Harper-stability variants

The same theorem is proved at three levels of precision, connected by
machine-checked consistency bridges:

| Theorem | Output slack `σ_out(n)` |
| --- | --- |
| `main_finite_skeleton` | *some* sublinear `σ_out ≥ σ` (the coarse `o(n)` form) |
| `main_finite_effective` | explicit `K·(effEnv 14 σ n + 1) ≈ K·σ^(1/16384)·n^(16383/16384)`, `K` may depend on `σ` |
| `main_finite_effective_uniform` | same envelope, single `K` depending only on the class reals + `epsCover`, **not** on `σ` |

Bridges: `main_finite_via_effective` (effective ⟹ coarse) and
`main_finite_effective_of_uniform` (uniform ⟹ effective).

## Layout

- `HarperStability.Interface`: the **trusted surface** — definitions and
  statement contracts (`Definitions`, `Statements`, and the effective/uniform
  contract layers `Effective`, `EffectiveUniform`). Frozen via
  `.interface.sha256`.
- `HarperStability.Volume`: volume/radius calculus, bridge to
  `BooleanIsoperimetry`.
- `HarperStability.Entropy`: finite entropy toolkit.
- `HarperStability.Reductions`: R1–R3 (peeling, heavy-ball, block-regularity).
- `HarperStability.Process`: S1–S4.
- `HarperStability.Core`: S5–S7 (the heavy-ball heart).
- `HarperStability.Assembly`: A0 and the final finite theorems.
- `AverageHarperStability.Interface`: frozen definitions and theorem contracts.
- `AverageHarperStability.Probability` / `.MGL` / `.Distribution`: finite
  probability, MGL, flatness, tracking and Wyner--Ziv components.
- `AverageHarperStability.Sets` / `.Assembly`: the entropy-to-cover bridge and
  the final combinatorial theorem.
- `Challenge.lean`, `Solution.lean`, and `comparator/config.json`: the
  Mathlib-only trusted statement and its machine-checked bridge to
  `HarperStability.main_finite_skeleton`.

The external Harper theorem dependency is
[`AlexeyMilovanov/BooleanIsoperimetry`](https://github.com/AlexeyMilovanov/BooleanIsoperimetry),
pinned at `v4.28.0`.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake update
lake build HarperStability AverageHarperStability
```

## Audit

```bash
./scripts/audit.sh
```

The audit checks both libraries' import boundaries and frozen interface hashes,
and verifies that no `sorry`, `axiom`, `admit`, `unsafe`, or heartbeat-disabling
option remains in the proved formalization.  The separate `Challenge.lean`
contains one intentional `sorry`: it is the statement hole that Comparator
requires, not part of the proof.

The only known build diagnostics are three linter warnings in the frozen
`HarperStability/Interface/Effective.lean` statement layer. They are retained
to keep the reviewed interface hash unchanged; all non-frozen modules build
without warnings.

## Verify the axioms directly

```bash
lake env lean --stdin <<'EOF'
import HarperStability.Assembly
import AverageHarperStability
#print axioms HarperStability.main_finite_skeleton
#print axioms HarperStability.main_finite_effective_uniform
#print axioms AverageHarperStability.average_harper_set_stability
EOF
```
