# Prior Aristotle / Agent Artifacts

This note records the status of early proof-loop artifacts from 2026-07-08.

## Old Aristotle archives

The first proof-loop launch produced Aristotle submissions for at least:

- `P3_reductions`
- `P4_process_s1_s4`
- `P6_assembly`

Those artifacts were produced before ordinary iterations were changed from
planning-only to implementation mode.  The original `proof_loop_runs/` copies
were later lost during an earlier sync/delete incident, but the user recovered
the three Aristotle tarballs into local WSL on 2026-07-08:

```text
/home/lesha/ff32e5e8-a3cc-4df0-81d7-35a68af4e8c4-aristotle.tar.gz  # P6
/home/lesha/ac222075-86ea-4257-a33f-b9bf2184e701-aristotle.tar.gz  # P3
/home/lesha/1bb67992-8ce1-4bdd-bee0-6bdafe7abccf-aristotle.tar.gz  # P4
```

They were unpacked for inspection at:

```text
/home/lesha/harper_aristotle_downloads_20260708T1433/
```

Do not spend agent time trying to open the old run paths:

```text
proof_loop_runs/20260708T123455Z-all-sections-proof-loop/...
```

They no longer exist in the VM checkout.

What was observed before deletion:

- `P3` Aristotle read `Reductions/Basic.lean` and the interface, and built.
- `P4` Aristotle read `Process/Basic.lean`, `Entropy/Basic.lean`, and the
  interface, but mostly diagnosed the project as a large skeleton.
- `P6` Aristotle focused on `Assembly/Basic.lean` and the helper shape for
  composing `S7Statement` into `QFromS7Statement`.

Treat this as historical context only, not as recoverable Lean code.

## Recovered useful progress

A later isolated Codex run recovered and verified the main low-level progress
that overlapped with the old Aristotle direction.  The following patches have
been copied into the main repository after successful worktree build/audit:

- `HarperStability/Volume/Basic.lean`:
  `vplus_skeleton : VPlusStatement` and
  `interior_v_skeleton : InteriorVStatement` are proved.
- `HarperStability/Entropy/Basic.lean`:
  basic finite-probability leaves are proved, including `pOn_le_one`,
  `uH_nonneg`, `rho_nonneg`, `rho_le_one`, `windowProb_nonneg`,
  `sum_windowProb_eq_one`, and `windowProb_split_below`.
- `HarperStability/Assembly/Basic.lean`:
  `q_from_s7_skeleton : QFromS7Statement` is proved.
- `HarperStability/Reductions/Basic.lean`:
  `R1b_skeleton : R1bStatement` is proved.
- `HarperStability/Process/Basic.lean`:
  `S2_skeleton : S2Statement` is proved.
- `HarperStability/Core/Basic.lean`:
  helper lemmas `predictableCenter_mem_iff` and
  `averageBadStepsLE_mono_slack` are proved.

Future proof loops should not target those declarations unless a later audit
finds a real problem.

## Recovered Aristotle-specific content

The recovered Aristotle archives were inspected after the Codex recovery pass:

- `P6` (`ff32...`) proves the same `q_from_s7_skeleton` bridge, but decomposes
  it into leaf lemmas `q_from_s7_eps_choice`,
  `s7_ball_card_le_bad_ball_card`, and `sublinear_exp_mass_contradiction`.
  The current baseline keeps the already-audited Codex proof; these leaf names
  are useful if the proof is later refactored for readability.
- `P3` (`ac222...`) proves the same `R1b_skeleton`, with helper lemmas
  `coveredByBalls_card_le_sum`, `real_exists_ge_of_sum_ge`,
  `real_half_le_of_sub_le`, and `r1b_exp_mass_eq`.  The current baseline keeps
  the already-audited Codex proof; these lemmas are useful refactoring targets.
- `P4` (`1bb...`) contributed two process helpers.  The small algebra lemma
  `variance_budget_algebra` has been copied into
  `HarperStability/Process/Basic.lean` and audited.  The larger
  `diagonal_sublinear_envelope` is mathematically relevant to S4
  uniformization, but its archived Lean code did not transfer cleanly into the
  current baseline; keep it as a candidate leaf, not as accepted code.

## Remaining high-value sections

After the recovered progress, the main open targets are:

- `P1_geometry_volume`: `ball_volume_two_sided_skeleton` and
  `interior_volume_calculus_skeleton`.
- `P2_entropy_probability`: the remaining finite entropy toolkit leaves:
  support-size entropy, projection entropy, chain rules, conditioning
  monotonicity, Jensen gap, observer surplus, and finite Fano.
- `P3_reductions`: `R1a_skeleton`, `R2_skeleton`, `R3_skeleton`.
- `P4_process_s1_s4`: `S1_skeleton`, `S3_skeleton`, `S4_skeleton`.
- `P5_core_s5_s7`: `S5_skeleton`, `S6_skeleton`, `S7_skeleton`.

`P6_assembly` currently has no local assembly-layer sorry except packaging
upstream worker proofs.
