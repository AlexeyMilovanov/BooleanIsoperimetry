#!/usr/bin/env python3
"""Ask Gemini to audit whether the proof section loop is ready to launch."""

from __future__ import annotations

import argparse
import datetime as dt
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
STABILITY_LAB_ROOT = Path(os.environ.get("HARPER_STABILITY_LAB_ROOT", "/home/lesha/harper-stability-lab"))

os.environ.setdefault("HARPER_LAB_ROOT", str(ROOT))
sys.path.insert(0, str(STABILITY_LAB_ROOT / "scripts"))

from harper_pipeline import call_agent_safe, write_text  # noqa: E402


def stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def read(path: Path, limit: int | None = None) -> str:
    if not path.exists():
        return f"[missing: {path}]\n"
    text = path.read_text(encoding="utf-8", errors="replace")
    if limit is not None and len(text) > limit:
        return text[:limit] + f"\n\n[TRUNCATED at {limit} chars from {path}]\n"
    return text


def command_output(argv: list[str], timeout: int = 120) -> str:
    try:
        cp = subprocess.run(
            argv,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        return cp.stdout + f"\n[returncode={cp.returncode}]\n"
    except Exception as exc:
        return f"[command failed: {type(exc).__name__}: {exc}]\n"


def latest_summary() -> str:
    root = ROOT / "interface_part_reviews"
    summaries = sorted(root.glob("*/SUMMARY.md"), key=lambda p: p.stat().st_mtime if p.exists() else 0)
    if not summaries:
        return "[no interface_part_reviews summary found]\n"
    return read(summaries[-1], 40000)


def build_prompt() -> str:
    audit_output = command_output(["bash", "scripts/audit.sh"], timeout=1800)
    list_sections = command_output(["python3", "scripts/run_proof_section_loop.py", "--list-sections"])
    dry_run_output = command_output(
        [
            "python3",
            "scripts/run_proof_section_loop.py",
            "--section",
            "P1_geometry_volume",
            "--iterations",
            "1",
            "--dry-run",
            "--run-dir",
            "proof_loop_runs/readiness-dry-run",
        ]
    )
    # Clean the readiness dry-run if it was created.
    dry_run_dir = ROOT / "proof_loop_runs" / "readiness-dry-run"
    if dry_run_dir.exists():
        import shutil

        shutil.rmtree(dry_run_dir)

    return f"""You are Gemini, auditing launch readiness for the Harper stability Lean proof loop.

Goal: decide whether the loop is ready to run proof-planning/proof-attempt
iterations by section. The intended chain is:

Gemini -> Codex -> Gemini -> Codex -> Aristotle

Every fifth iteration is strategic, and Aristotle participates in strategy too.

Required verdict:

STATUS: READY_TO_LAUNCH / READY_WITH_MINOR_FIXES / DO_NOT_LAUNCH

Please check:
1. Are all six sections present and coherent?
2. Do agents receive enough mathematical and Lean context to close sorries?
3. Does the runner preserve the frozen interface and module boundaries?
4. Does PAUSE stop after the current agent call, not after the whole iteration?
5. Does strategic iteration include Aristotle?
6. Are outputs/checkpoints/Aristotle packets saved in useful locations?
7. Are there obvious operational hazards before launching all sections?

If fixes are needed, give exact file/line-level edits.

# Command checks

## audit.sh

```text
{audit_output}
```

## --list-sections

```text
{list_sections}
```

## dry-run

```text
{dry_run_output}
```

# Files

## proof_loop/README.md

```markdown
{read(ROOT / "proof_loop" / "README.md", 30000)}
```

## proof_loop/sections.json

```json
{read(ROOT / "proof_loop" / "sections.json", 40000)}
```

## scripts/run_proof_section_loop.py

```python
{read(ROOT / "scripts" / "run_proof_section_loop.py", 80000)}
```

## STATUS.md

```markdown
{read(ROOT / "STATUS.md", 30000)}
```

## Latest six-part review summary

```markdown
{latest_summary()}
```

## Fable semantic audit

```markdown
{read(ROOT / "reviews" / "20260708T-fable-semantic-audit" / "AUDIT.md", 40000)}
```
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--out-dir", type=Path, default=None)
    args = parser.parse_args()

    out_dir = args.out_dir or (ROOT / "proof_loop_readiness" / f"{stamp()}-gemini")
    out_dir.mkdir(parents=True, exist_ok=True)
    prompt = build_prompt()
    write_text(out_dir / "readiness.prompt.md", prompt)
    ok, text = call_agent_safe("gemini", "gemini_readiness", prompt, out_dir, args.timeout_seconds)
    write_text(out_dir / "SUMMARY.md", text.strip() + "\n")
    print(out_dir)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
