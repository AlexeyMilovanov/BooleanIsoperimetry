# HarperStabilityLean

A complete Lean 4 / Mathlib formalization of a **stability version of Harper's
vertex-isoperimetric inequality** on the Hamming cube: if a set has a
near-minimal boundary, then all but an `ε`-fraction of it is covered by few
Hamming balls of near-optimal radius.

**Status: fully proved. Zero `sorry`.** The main theorems depend only on the
standard axioms `[propext, Classical.choice, Quot.sound]`.

## Reviewing the result

If you only care about *what is proved* (not the proof or the constants), read
**[`docs/STATEMENT.md`](docs/STATEMENT.md)**. It isolates the main theorem and
every definition it depends on (~15 short definitions), gives a plain-English
statement, and shows the `#print axioms` output. That document is the entire
human-trusted surface.

## The three theorems

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

The external Harper theorem dependency is
[`AlexeyMilovanov/BooleanIsoperimetry`](https://github.com/AlexeyMilovanov/BooleanIsoperimetry),
pinned at `v4.28.0`.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake update
lake build
```

## Audit

```bash
./scripts/audit.sh
```

The audit checks import boundaries, the frozen interface hashes, and that no
`sorry`, `axiom`, `admit`, `unsafe`, or heartbeat-disabling option remains.

## Verify the axioms directly

```bash
lake env lean <<'EOF'
import HarperStability.Assembly
#print axioms HarperStability.main_finite_skeleton
#print axioms HarperStability.main_finite_effective_uniform
EOF
```
