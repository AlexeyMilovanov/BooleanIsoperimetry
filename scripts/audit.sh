#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== escape hatch grep =="
if grep -RInE --include='*.lean' '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option maxHeartbeats 0' HarperStability *.lean 2>/dev/null; then
  echo "ERROR: hard escape hatch found"
  exit 1
fi

if grep -RInE --include='*.lean' '\bsorry\b' HarperStability *.lean 2>/dev/null; then
  if [[ "${STRICT_NO_SORRY:-0}" == "1" ]]; then
    echo "ERROR: sorry found in strict proof-stage mode"
    exit 1
  fi
  echo "NOTE: sorry found (expected during skeleton stage; forbidden after proof stage)"
else
  echo "No sorry found."
fi

echo "== import boundary grep =="
check_allowed_imports() {
  local path="$1"
  local allowed="$2"
  local bad
  bad="$(grep -RInE '^import HarperStability\.' "$path" 2>/dev/null \
    | grep -vE "import HarperStability\.(${allowed})(\.|$)" || true)"
  if [[ -n "$bad" ]]; then
    echo "$bad"
    echo "ERROR: $path imports outside allowlist: ${allowed}"
    exit 1
  fi
}

check_no_external_imports() {
  local path="$1"
  local bad
  bad="$(grep -RInE '^import ' "$path" 2>/dev/null \
    | grep -vE ':import HarperStability(\.|$)' || true)"
  if [[ -n "$bad" ]]; then
    echo "$bad"
    echo "ERROR: $path imports external modules directly; only Interface may do that"
    exit 1
  fi
}

check_allowed_imports HarperStability.lean 'Interface|Volume|Entropy|Reductions|Process|Core|Assembly|Statement'
check_allowed_imports HarperStability/Interface.lean 'Interface'
check_allowed_imports HarperStability/Volume.lean 'Volume'
check_allowed_imports HarperStability/Entropy.lean 'Entropy'
check_allowed_imports HarperStability/Reductions.lean 'Reductions'
check_allowed_imports HarperStability/Process.lean 'Process'
check_allowed_imports HarperStability/Core.lean 'Core'
check_allowed_imports HarperStability/Assembly.lean 'Assembly'
check_allowed_imports HarperStability/Interface 'Interface'
check_allowed_imports HarperStability/Volume 'Interface|Volume'
check_allowed_imports HarperStability/Entropy 'Interface|Entropy'
check_allowed_imports HarperStability/Reductions 'Interface|Volume|Entropy|Reductions'
check_allowed_imports HarperStability/Process 'Interface|Entropy|Process'
check_allowed_imports HarperStability/Core 'Interface|Entropy|Core'
check_allowed_imports HarperStability/Assembly 'Interface|Volume|Entropy|Reductions|Process|Core|Assembly'
check_no_external_imports HarperStability.lean
check_no_external_imports HarperStability/Volume.lean
check_no_external_imports HarperStability/Entropy.lean
check_no_external_imports HarperStability/Reductions.lean
check_no_external_imports HarperStability/Process.lean
check_no_external_imports HarperStability/Core.lean
check_no_external_imports HarperStability/Assembly.lean
check_no_external_imports HarperStability/Volume
check_no_external_imports HarperStability/Entropy
check_no_external_imports HarperStability/Reductions
check_no_external_imports HarperStability/Process
check_no_external_imports HarperStability/Core
check_no_external_imports HarperStability/Assembly
echo "Import boundaries look clean."

echo "== interface hash =="
if [[ -f .interface.sha256 ]]; then
  sha256sum --check .interface.sha256
else
  echo "ERROR: .interface.sha256 is required"
  exit 1
fi

echo "== lake build =="
export PATH="$HOME/.elan/bin:$PATH"
lake build HarperStability

echo "== theorem axiom audit =="
axiom_output="$(lake env lean scripts/audit_axioms.lean 2>&1)"
echo "$axiom_output"
AXIOM_OUTPUT="$axiom_output" CHECK_ALL_AXIOMS="${STRICT_AXIOMS:-0}${STRICT_NO_SORRY:-0}" python3 - <<'PY'
import os
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = []
main_seen = False
for line in os.environ["AXIOM_OUTPUT"].splitlines():
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    if not m:
        continue
    is_main = "HarperStability.main_from_components" in line
    if is_main:
        main_seen = True
    axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
    extra = sorted(axioms - allowed)
    if extra and (is_main or os.environ.get("CHECK_ALL_AXIOMS") != "00"):
        bad.append((line.strip(), extra))

if not main_seen:
    bad.append(("HarperStability.main_from_components axiom line missing", ["missing-audit-line"]))

if bad:
    print("ERROR: non-whitelisted axioms found in axiom audit")
    for line, extra in bad:
        print(line)
        print("  extra:", ", ".join(extra))
    raise SystemExit(1)
PY
