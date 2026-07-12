# Harper Stability Lean Proof Loop

This directory prepares the proof-planning loop for the frozen Harper stability
Lean interface.

The intended per-section ordinary iteration is:

1. Gemini proposes a concrete Lean proof move.
2. Codex checks Gemini's edits, keeps what is sound, repairs what is broken,
   and tries to close or reconstruct more sorries.
3. Gemini continues from Codex's reviewed worktree.
4. Codex makes the final verification/implementation pass.
5. Aristotle receives a leaf-proof packet.

Ordinary iterations are write-enabled. Each section works in its own isolated
`_worktree` under the run directory, so sections can run in parallel without
editing the same repository copy.

Every fifth iteration is strategic: all four LLM stages plus Aristotle write a
plan for the next four proof iterations in that section.

The runner is:

```bash
python3 scripts/run_proof_section_loop.py --help
```

Useful commands:

```bash
# See available sections.
python3 scripts/run_proof_section_loop.py --list-sections

# Prepare prompt files only; do not call models.
python3 scripts/run_proof_section_loop.py --section P1_geometry_volume --iterations 1 --dry-run

# Later, run one section for four proof iterations plus one strategy iteration.
python3 scripts/run_proof_section_loop.py --section P1_geometry_volume --iterations 5

# Later, run all sections in parallel.
python3 scripts/run_proof_section_loop.py --section all --iterations 5 --jobs 6
```

By default Aristotle is not submitted automatically. Each iteration, including
strategic iterations, writes `aristotle_prompt.md` and `submit_aristotle.py`
under the iteration directory. Add `--submit-aristotle` only when we explicitly
want automatic submission.

After an ordinary iteration, the serial merge-gate tests section worktree
changes and automatically merges accepted patches into the main repository.
The gate holds `proof_loop/MERGE_GATE.lock`, checks the frozen interface hash,
rejects forbidden tokens through `scripts/audit.sh`, bounds `sorry` increase,
and reverts the main repository if the gate rejects a patch.

The section worktree is still preserved for audit/debugging:

```text
proof_loop_runs/<run>/<section>/_worktree/
```

Checkpointing is inherited from `harper_pipeline.call_agent_safe`: each model is
told to write a checkpoint every about 10 minutes if it has filesystem access.

Stop file:

```bash
touch proof_loop/PAUSE
```

This is the global pause: every section sees it.  The runner checks it between
stages and between iterations, so a currently running model is allowed to finish
its current stage and then the loop stops softly.

Per-section pause files are also supported:

```bash
touch proof_loop/PAUSE.P4_process_s1_s4
touch proof_loop/PAUSE.P5_core_s5_s7
```

The convention is `PAUSE.<section_id>`, using the ids printed by
`--list-sections`.  A section pause affects only that section; other sections
continue unless the global `proof_loop/PAUSE` exists.  To resume, remove the
corresponding file:

```bash
rm proof_loop/PAUSE
rm proof_loop/PAUSE.P4_process_s1_s4
```
