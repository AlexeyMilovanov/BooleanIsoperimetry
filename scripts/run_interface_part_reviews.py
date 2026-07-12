#!/usr/bin/env python3
"""Run six-part semantic reviews for the Harper stability Lean interface.

For each part:
1. Gemini reviews, Codex checks.
2. Codex reviews, Gemini checks.
3. Codex writes the final verdict.

This is statement audit only.  Agents must not edit files or try to prove the
theorems; they compare Lean contracts against the proof paper/status.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import datetime as dt
import json
import os
from pathlib import Path
import sys
import traceback
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
STABILITY_LAB_ROOT = Path(os.environ.get("HARPER_STABILITY_LAB_ROOT", "/home/lesha/harper-stability-lab"))

# Reuse the robust model-call wrapper, but make the Lean repo the call root so
# prompt paths and outputs live under this project.
os.environ.setdefault("HARPER_LAB_ROOT", str(ROOT))
sys.path.insert(0, str(STABILITY_LAB_ROOT / "scripts"))

from harper_pipeline import call_agent_safe, write_json, write_text  # noqa: E402


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def read_if_exists(path: Path, max_chars: int | None = None) -> str:
    if not path.exists():
        return f"[missing: {path}]\n"
    text = path.read_text(encoding="utf-8", errors="replace")
    if max_chars is not None and len(text) > max_chars:
        return text[:max_chars] + f"\n\n[TRUNCATED at {max_chars} chars from {path}]\n"
    return text


def file_block(paths: list[Path], max_each: int | None = None) -> str:
    chunks: list[str] = []
    for path in paths:
        chunks.append(f"\n\n# FILE: {path}\n\n```lean\n")
        chunks.append(read_if_exists(path, max_each).strip())
        chunks.append("\n```\n")
    return "".join(chunks)


BASE_FILES = [
    ROOT / "STATUS.md",
    ROOT / "README.md",
    ROOT / "lakefile.lean",
    ROOT / "lean-toolchain",
    ROOT / "HarperStability.lean",
    ROOT / "HarperStability" / "Interface.lean",
    ROOT / "HarperStability" / "Interface" / "Definitions.lean",
    ROOT / "HarperStability" / "Interface" / "Statements.lean",
]


PARTS: list[dict[str, Any]] = [
    {
        "id": "P1_geometry_volume",
        "title": "Geometry / BooleanIsoperimetry / Volume Bridge",
        "focus": (
            "Cube/hDist/neighborhood usage, local ball/V/rmin/coveredByBalls, "
            "BallVolumeTwoSidedStatement, VPlusStatement, InteriorVStatement, "
            "compatibility with BooleanIsoperimetry and harper_vertex_iso."
        ),
        "files": [
            ROOT / "HarperStability" / "Volume.lean",
            ROOT / "HarperStability" / "Volume" / "Basic.lean",
        ],
        "paper_hint": "Preliminaries, volume calculus, R1/R2 bridge to Harper.",
    },
    {
        "id": "P2_entropy_probability",
        "title": "Finite Probability / Entropy Toolkit",
        "focus": (
            "pOn/uE/varOn/uH/uCondH/uCondVar, Sublinear, proj/rho/hstep, "
            "windowProb, expectedEstimatorError, varianceBudgetLE, nats-vs-bits."
        ),
        "files": [
            ROOT / "HarperStability" / "Entropy.lean",
            ROOT / "HarperStability" / "Entropy" / "Basic.lean",
        ],
        "paper_hint": "Entropy toolkit used by S1-S7, especially S2/S3.",
    },
    {
        "id": "P3_stability_q_reductions",
        "title": "Stability / Q / Reductions Interface",
        "focus": (
            "StabilityData, validData, degradedData, classMember, size/near/cap "
            "hypotheses, QData, fat/pinned/bad/QuestionQ, R1a/R1b/R2/R3, "
            "MainFiniteStatement and slack typing."
        ),
        "files": [
            ROOT / "HarperStability" / "Reductions.lean",
            ROOT / "HarperStability" / "Reductions" / "Basic.lean",
        ],
        "paper_hint": "R1-R3 and A0 reduction layer.",
    },
    {
        "id": "P4_process_s1_s4",
        "title": "Process Layer S1-S4",
        "focus": (
            "blockRegular/blockRegularFamily, S1, S2, S3, S4, randomized windows, "
            "binnedFoldField, offset averaging, entropy-layer purity."
        ),
        "files": [
            ROOT / "HarperStability" / "Process.lean",
            ROOT / "HarperStability" / "Process" / "Basic.lean",
        ],
        "paper_hint": "S1-S4 process/entropy layer.",
    },
    {
        "id": "P5_core_s5_s7",
        "title": "Core Layer S5-S7",
        "focus": (
            "averageBadStepsLE, predictableCenter, S5, S6, S7, QFromS7, "
            "heavy-ball output versus not-bad corollary, PF and center entropy."
        ),
        "files": [
            ROOT / "HarperStability" / "Core.lean",
            ROOT / "HarperStability" / "Core" / "Basic.lean",
        ],
        "paper_hint": "S5-S7 and Q-from-heavy-ball assembly.",
    },
    {
        "id": "P6_assembly_ci",
        "title": "Assembly / Dependency Graph / CI Readiness",
        "focus": (
            "worker imports, statement-hypothesis pattern, A0Statement package, "
            "component_package_skeleton, main theorem assembly, build/audit readiness."
        ),
        "files": [
            ROOT / "HarperStability" / "Assembly.lean",
            ROOT / "HarperStability" / "Assembly" / "Basic.lean",
            ROOT / "scripts" / "audit.sh",
        ],
        "paper_hint": "A0 assembly, final theorem, proof dependency graph.",
    },
]


def paper_context() -> str:
    paper = read_if_exists(STABILITY_LAB_ROOT / "paper" / "harper-stability.tex", 90000)
    plan = read_if_exists(STABILITY_LAB_ROOT / "writeup-lean" / "01-FORMALIZATION-PLAN.md", 30000)
    return f"""
# PAPER / PLAN CONTEXT

The full proof paper is truncated if needed, but enough is included for semantic
comparison.

```tex
{paper}
```

```markdown
{plan}
```
"""


def part_context(part: dict[str, Any]) -> str:
    all_paths = BASE_FILES + part["files"]
    return f"""
# PART

- id: `{part['id']}`
- title: {part['title']}
- focus: {part['focus']}
- paper hint: {part['paper_hint']}

# CURRENT LEAN FILES
{file_block(all_paths, 60000)}
"""


def review_prompt(model: str, part: dict[str, Any], previous: str = "") -> str:
    prev = ""
    if previous.strip():
        prev = f"""
# PREVIOUS REPORTS FOR THIS PART

Do not merely repeat these. Confirm, refute, sharpen, or find new issues.

```markdown
{previous.strip()}
```
"""
    return f"""You are {model}, doing hostile semantic review of one part of a Lean formalization interface.

This is NOT proof search. Do not edit files. Your job is to compare the Lean
definitions/statements against the paper and formalization plan, looking for
wrong theorem statements, wrong quantifier order, missing hypotheses, too-strong
or too-weak conclusions, wrong dependency boundaries, scale/slack errors, and
Lean API mismatches.

Required output:

STATUS: ACCEPT / ACCEPT_WITH_MINOR_EDITS / REPAIR_INTERFACE / MAJOR_REWRITE_NEEDED

## Executive Summary

## Mismatch Table
Columns: Lean item | intended object | issue | severity | exact proposed fix.

## Confirmed Good Choices

## Missing Statements Or Definitions

## Dependency Boundary Review

## Exact Next Edits

## Questions For Human Mathematician

{prev}

{part_context(part)}

{paper_context()}
"""


def check_prompt(checker: str, finder: str, part: dict[str, Any], report: str) -> str:
    return f"""You are {checker}, checking a semantic-review report by {finder}.

Target part: `{part['id']}` / {part['title']}.

For every alleged problem: confirm, refine, or refute it. If the report is too
vague, make it concrete. If the issue is false, explain exactly why.

Required output:

STATUS: ALL_REFUTED / SOME_CONFIRMED / MAJOR_CONFIRMED / INCONCLUSIVE

## Verdict Summary

## Issue-By-Issue Review

## Additional Issues You Notice

## Minimal Repair Set

Finder report:

```markdown
{report.strip()}
```

{part_context(part)}
"""


def final_prompt(part: dict[str, Any], reports: str) -> str:
    return f"""You are Codex, writing the final verdict for one part of the Lean interface semantic review.

Target part: `{part['id']}` / {part['title']}.

You have:
1. Gemini review + Codex check.
2. Codex review + Gemini check.

Write a compact but precise final verdict that a human can use to edit the
interface. Distinguish real blockers from stylistic concerns.

Required output:

STATUS: ACCEPT / ACCEPT_WITH_MINOR_EDITS / REPAIR_INTERFACE / BLOCKED

## Final Verdict

## Repairs Required Before Statement Freeze

## Optional Improvements

## Refuted Objections

## Exact Patch Plan

## Safe To Send To Aristotle?
Answer yes/no, and for which leaf lemmas if any.

All reports:

```markdown
{reports.strip()}
```

{part_context(part)}
"""


def call(kind: str, agent_id: str, prompt: str, out_dir: Path, timeout: int) -> str:
    ok, text = call_agent_safe(kind, agent_id, prompt, out_dir, timeout)
    if not ok:
        write_text(out_dir / f"{agent_id}.FAILED.md", text + "\n")
        return text
    return text


def run_part(part: dict[str, Any], run_root: Path, timeout: int) -> dict[str, Any]:
    part_dir = run_root / part["id"]
    part_dir.mkdir(parents=True, exist_ok=True)
    manifest: dict[str, Any] = {"part": part["id"], "status": "RUNNING", "title": part["title"]}
    write_json(part_dir / "manifest.json", manifest)
    reports: list[str] = []
    try:
        g_review = call("gemini", f"{part['id']}_gemini_review", review_prompt("Gemini", part), part_dir, timeout)
        reports.append(f"# Gemini review\n\n{g_review}")

        c_check = call("codex", f"{part['id']}_codex_checks_gemini", check_prompt("Codex", "Gemini", part, g_review), part_dir, timeout)
        reports.append(f"# Codex checks Gemini\n\n{c_check}")

        c_review = call("codex", f"{part['id']}_codex_review", review_prompt("Codex", part, "\n\n".join(reports)), part_dir, timeout)
        reports.append(f"# Codex independent review\n\n{c_review}")

        g_check = call("gemini", f"{part['id']}_gemini_checks_codex", check_prompt("Gemini", "Codex", part, c_review), part_dir, timeout)
        reports.append(f"# Gemini checks Codex\n\n{g_check}")

        all_reports = "\n\n".join(reports)
        write_text(part_dir / "ALL_REPORTS.md", all_reports + "\n")

        final = call("codex", f"{part['id']}_codex_final", final_prompt(part, all_reports), part_dir, timeout)
        write_text(part_dir / "FINAL.md", final.strip() + "\n")

        manifest.update({"status": "COMPLETED", "final": str(part_dir / "FINAL.md")})
    except Exception as exc:
        err = "".join(traceback.format_exception(exc))
        write_text(part_dir / "EXCEPTION.txt", err)
        manifest.update({"status": "FAILED", "error": repr(exc)})
    write_json(part_dir / "manifest.json", manifest)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", action="append", default=[], help="Part id to run; repeatable.")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=int(os.environ.get("HARPER_LEAN_REVIEW_TIMEOUT", "3600")))
    args = parser.parse_args()

    selected = PARTS
    if args.part:
      allowed = set(args.part)
      selected = [p for p in PARTS if p["id"] in allowed]
      missing = allowed - {p["id"] for p in selected}
      if missing:
        raise SystemExit(f"unknown part ids: {sorted(missing)}")

    run_root = ROOT / "interface_part_reviews" / f"{utc_stamp()}-six-part-review"
    run_root.mkdir(parents=True, exist_ok=False)
    write_json(run_root / "manifest.json", {
        "status": "RUNNING",
        "parts": [p["id"] for p in selected],
        "jobs": args.jobs,
        "timeout": args.timeout,
    })

    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as executor:
        futures = {executor.submit(run_part, part, run_root, args.timeout): part for part in selected}
        for future in as_completed(futures):
            results.append(future.result())

    status = "COMPLETED" if all(r.get("status") == "COMPLETED" for r in results) else "PARTIAL_FAILURE"
    write_json(run_root / "manifest.json", {"status": status, "results": sorted(results, key=lambda r: r["part"])})
    lines = ["# Interface Part Review Summary\n"]
    for result in sorted(results, key=lambda r: r["part"]):
        lines.append(f"- `{result['part']}`: {result.get('status')} -> `{result.get('final', '')}`")
    write_text(run_root / "SUMMARY.md", "\n".join(lines).strip() + "\n")
    print(run_root)
    return 0 if status == "COMPLETED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
