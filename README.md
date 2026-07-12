# HarperStabilityLean

Lean 4 skeleton for the robust Harper stability proof candidate.

This repository is intentionally a single monorepo with seven logical
components:

- `HarperStability.Interface`: shared definitions and statement contracts.
- `HarperStability.Volume`: volume estimates and the bridge to
  `BooleanIsoperimetry`.
- `HarperStability.Entropy`: finite entropy toolkit.
- `HarperStability.Reductions`: R1--R3.
- `HarperStability.Process`: S1--S4.
- `HarperStability.Core`: S5--S7.
- `HarperStability.Assembly`: A0 and the final finite theorem.

The external Harper theorem dependency is
[`AlexeyMilovanov/BooleanIsoperimetry`](https://github.com/AlexeyMilovanov/BooleanIsoperimetry),
pinned at `v4.28.0`.

Current status: statement/skeleton stage. Many theorem bodies contain
`sorry` deliberately. The next milestone is semantic review of the Lean
statements against `paper/harper-stability.tex` and `writeup/`.

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

At the skeleton stage the audit is expected to report `sorry`. In proof
stage, `sorry`, `axiom`, `admit`, `unsafe`, and heartbeat-disabling options
must disappear.
