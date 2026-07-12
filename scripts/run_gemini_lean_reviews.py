#!/usr/bin/env python3
"""Run two Gemini reviews for the Harper stability Lean formalization.

The two tasks are intentionally independent:

1. semantic_review: compare the current Lean interface/skeleton against the
   prose proof and the Lean formalization plan.
2. library_survey: search for existing Lean libraries/formalizations that could
   be useful, including Lean versions and dependency recommendations.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import datetime as dt
import json
import os
from pathlib import Path
import sys
import traceback
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
STABILITY_LAB_ROOT = Path(os.environ.get("HARPER_STABILITY_LAB_ROOT", "/home/lesha/harper-stability-lab"))

# `harper_pipeline` uses HARPER_LAB_ROOT both as the model cwd and as the root
# for relative prompt paths. For these Lean reviews, the output root is the Lean
# repo, while the pipeline implementation is borrowed from the stability lab.
os.environ.setdefault("HARPER_LAB_ROOT", str(ROOT))
sys.path.insert(0, str(STABILITY_LAB_ROOT / "scripts"))

from harper_pipeline import call_agent_safe, write_text, write_json  # noqa: E402


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def read_if_exists(path: Path, max_chars: int | None = None) -> str:
    if not path.exists():
        return f"[missing: {path}]\n"
    text = path.read_text(encoding="utf-8", errors="replace")
    if max_chars is not None and len(text) > max_chars:
        return text[:max_chars] + f"\n\n[TRUNCATED at {max_chars} chars from {path}]\n"
    return text


def collect_files(paths: list[Path], title: str, max_each: int | None = None) -> str:
    chunks = [f"\n\n# {title}\n"]
    for path in paths:
        chunks.append(f"\n\n## FILE: {path}\n\n")
        chunks.append(read_if_exists(path, max_each).strip())
        chunks.append("\n")
    return "".join(chunks)


def lean_files() -> list[Path]:
    files = [ROOT / "lakefile.lean", ROOT / "lean-toolchain", ROOT / "lake-manifest.json"]
    files.extend(sorted((ROOT / "HarperStability").rglob("*.lean")))
    files.extend([ROOT / "README.md", ROOT / "STATUS.md"])
    return [p for p in files if p.exists()]


def plan_files() -> list[Path]:
    base = STABILITY_LAB_ROOT / "writeup-lean"
    return [
        base / "00-DEFINITIONS.md",
        base / "01-FORMALIZATION-PLAN.md",
        base / "S1-quantitative.md",
        base / "S1Skeleton.lean",
    ]


def semantic_review_prompt() -> str:
    paper = read_if_exists(STABILITY_LAB_ROOT / "paper" / "harper-stability.tex", 90000)
    context = (
        collect_files(plan_files(), "Lean formalization plan files", 50000)
        + collect_files(lean_files(), "Current Lean repository files", 50000)
    )
    return f"""You are Gemini, doing a semantic review of a Lean formalization interface.

Goal: check whether the current Lean skeleton in `/home/lesha/harper-stability-lean`
faithfully represents the proof candidate in
`/home/lesha/harper-stability-lab/paper/harper-stability.tex` and the formalization
plan in `writeup-lean/`.

This is NOT a proof search. Ignore `sorry`s. Your job is statement audit:
definitions, theorem contracts, dependency boundaries, quantifiers, slack
parameters, and whether the proposed module split really lets independent teams
work on Volume / Entropy / Reductions / Process / Core / Assembly.

Look especially for:
- Lean definitions that do not match the prose object (cube, Hamming ball,
  neighborhood, V/V+, r_min, cover conclusions, Q-data, fat/pinned/bad).
- Prop-level theorem statements that are too weak to imply the next step, too
  strong compared to the paper, circular, or missing hypotheses.
- Missing objects needed by the paper but absent from the interface.
- Places where using `Finset (Fin n)` creates type/semantic mismatch with the
  imported BooleanIsoperimetry Harper theorem.
- Whether Core should be stated conditionally on R3/S1/S4 etc. rather than as
  direct standalone statements.

Required output:

STATUS: ACCEPT_INTERFACE / REPAIR_INTERFACE / MAJOR_REWRITE_NEEDED

## Executive Summary

## Mismatch Table
Columns: Lean name/file | intended prose object | issue | severity | proposed fix.

## Missing Statements Or Definitions

## Dependency Split Review

## Exact Next Edits
Give a concrete ordered edit list for Codex.

## High-Risk Semantic Questions For Human Mathematician

Paper proof candidate follows.

```tex
{paper}
```

Formalization context follows.

{context}
"""


def library_survey_prompt() -> str:
    manifest = read_if_exists(ROOT / "lake-manifest.json", 20000)
    toolchain = read_if_exists(ROOT / "lean-toolchain", 2000)
    lakefile = read_if_exists(ROOT / "lakefile.lean", 5000)
    return f"""You are Gemini, doing a Lean ecosystem/library survey for a formalization project.

Project: robust Harper stability formalization in Lean 4. Current dependency
plan is Mathlib + AlexeyMilovanov/BooleanIsoperimetry only. The current toolchain
is pinned below.

Your task: search for existing Lean formalizations or libraries that may already
contain useful results for this project, and report their Lean versions. Include
Mathlib modules and external repos. In particular, check:
- Kruskal-Katona / Lovasz-KK / shadows / colex / simplicial order.
- Harper theorem / Boolean cube / Hamming balls / isoperimetry.
- finite entropy, Shannon entropy, KL divergence, Pinsker, Fano, chain rule.
- finite probability / counting probability / concentration: Hoeffding, Azuma,
  Chernoff, martingales.
- Stirling, binomial entropy asymptotics, binomial estimates.
- Johnson graphs / layer shadows / LYM-type inequalities.
- any Terry Tao-related Lean projects or other combinatorics formalizations that
  might be relevant, and whether they are actually useful here.

If you have live web/search access, use it and cite URLs. If you do not, say so
explicitly and mark memory-based claims as such. Do not recommend adding a
dependency unless it is likely compatible with Lean 4.28.0 or easy to port.

Required output:

STATUS: KEEP_DEPS / ADD_DEPENDENCY_NOW / INVESTIGATE_BEFORE_ADDING

## Current Pins

## Library Table
Columns: source/repo/module | useful content | Lean/toolchain version | compatibility
with Lean 4.28.0 | recommendation | URL/evidence.

## Mathlib Modules To Import First

## External Repos Not To Depend On Yet

## Version Risks

## Exact Recommendation For lakefile.lean

Current `lean-toolchain`:

```text
{toolchain}
```

Current `lakefile.lean`:

```lean
{lakefile}
```

Current `lake-manifest.json`:

```json
{manifest}
```
"""


TASKS = {
    "semantic_review": semantic_review_prompt,
    "library_survey": library_survey_prompt,
}


def run_task(name: str, out_root: Path, timeout: int) -> dict[str, Any]:
    out_dir = out_root / name
    out_dir.mkdir(parents=True, exist_ok=True)
    prompt = TASKS[name]()
    write_text(out_dir / f"{name}.prompt.md", prompt)
    ok, text = call_agent_safe("gemini", f"gemini_{name}", prompt, out_dir, timeout)
    if not ok:
        write_text(out_dir / f"{name}.FAILED.md", text + "\n")
        return {"task": name, "ok": False, "output": str(out_dir / f"{name}.FAILED.md")}
    write_text(out_dir / f"{name}.md", text.strip() + "\n")
    return {"task": name, "ok": True, "output": str(out_dir / f"{name}.md")}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--task",
        action="append",
        choices=sorted(TASKS),
        default=[],
        help="Task to run. Repeatable. Defaults to all tasks.",
    )
    args = parser.parse_args()

    timeout = int(os.environ.get("HARPER_LEAN_GEMINI_TIMEOUT", "3600"))
    run_id = f"{utc_stamp()}-gemini-lean-reviews"
    out_root = ROOT / "reviews" / run_id
    out_root.mkdir(parents=True, exist_ok=False)
    selected = args.task or list(TASKS)
    write_json(out_root / "manifest.json", {"status": "RUNNING", "tasks": selected, "timeout": timeout})

    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = {executor.submit(run_task, name, out_root, timeout): name for name in selected}
        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as exc:
                name = futures[future]
                err = "".join(traceback.format_exception(exc))
                write_text(out_root / f"{name}.EXCEPTION.txt", err)
                results.append({"task": name, "ok": False, "output": str(out_root / f"{name}.EXCEPTION.txt")})

    status = "COMPLETED" if all(r["ok"] for r in results) else "PARTIAL_FAILURE"
    write_json(out_root / "manifest.json", {"status": status, "results": sorted(results, key=lambda r: r["task"])})
    lines = ["# Gemini Lean Reviews\n"]
    for result in sorted(results, key=lambda r: r["task"]):
        lines.append(f"- `{result['task']}`: {'OK' if result['ok'] else 'FAILED'} -> `{result['output']}`")
    write_text(out_root / "SUMMARY.md", "\n".join(lines).strip() + "\n")
    print(out_root)
    return 0 if status == "COMPLETED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
