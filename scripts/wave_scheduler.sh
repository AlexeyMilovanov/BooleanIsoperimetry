#!/usr/bin/env bash
# Wave scheduler: keep at most MAXLOCAL effective sections with ACTIVE
# LOCAL work (lean/lake/agy/codex); resume paused sections in priority
# order as slots free up. Sections whose target file has no sorry left
# are skipped. Exits when the queue is empty.
set -u
ROOT=/home/lesha/harper-stability-lean
RUN=$ROOT/proof_loop_runs/20260708T201217Z-proof-section-loop
MAXLOCAL=3
QUEUE=(U1_s4_uniform U2_s5s6_uniform U3_s7r2_uniform U4_assembly_uniform)
declare -A OWNED=(
  [E3_s4_eff]=HarperStability/Process/EffectiveS4.lean
  [E4_s5_eff]=HarperStability/Core/EffectiveS5.lean
  [E5_s6_eff]=HarperStability/Core/EffectiveS6.lean
  [E6_s7_eff]=HarperStability/Core/EffectiveS7.lean
  [E8_r1a_eff]=HarperStability/Reductions/EffectiveR1.lean
  [E9_assembly_eff]=HarperStability/Assembly/Effective.lean
  [U1_s4_uniform]=HarperStability/Process/EffectiveS4U.lean
  [U2_s5s6_uniform]=HarperStability/Core/EffectiveS6U.lean
  [U3_s7r2_uniform]=HarperStability/Reductions/EffectiveR2U.lean
  [U4_assembly_uniform]=HarperStability/Assembly/EffectiveUniform.lean
)
log() { echo "[$(date -u +%H:%M:%S)] $*"; }
while true; do
  # count sections with active local compute (any stage process alive)
  active=0
  for s in U1_s4_uniform U2_s5s6_uniform U3_s7r2_uniform U4_assembly_uniform; do
    if pgrep -f "bin/lean .*${s}/_worktree" >/dev/null 2>&1 \
       || pgrep -f "ag[y].*${s}/" >/dev/null 2>&1 \
       || pgrep -f "claud[e].*${s}/" >/dev/null 2>&1 \
       || pgrep -f "code[x].*${s}/" >/dev/null 2>&1; then
      active=$((active+1))
    fi
  done
  # rebuild remaining queue
  remaining=()
  for s in "${QUEUE[@]}"; do
    f=$ROOT/${OWNED[$s]}
    if [ -f "$f" ] && grep -q "sorry" "$f"; then
      if ! pgrep -f "section ${s}" >/dev/null 2>&1; then
        remaining+=("$s")
      fi
    fi
  done
  if [ ${#remaining[@]} -eq 0 ]; then log "queue empty - scheduler done"; exit 0; fi
  while [ $active -lt $MAXLOCAL ] && [ ${#remaining[@]} -gt 0 ]; do
    s=${remaining[0]}; remaining=("${remaining[@]:1}")
    rm -f $ROOT/proof_loop/PAUSE.$s
    it=$(ls -d $RUN/$s/iter_* 2>/dev/null | grep -oE "iter_0*[0-9]+" | grep -oE "[0-9]+$" | sort -n | tail -1)
    it=$(( 10#${it:-0} + 1 ))
    cd $ROOT && nohup python3 scripts/run_proof_section_loop.py --section $s --run-dir $RUN --start-iteration $it --until-zero-sorries --jobs 1 --submit-aristotle --aristotle-timeout-seconds 86400 --max-sorry-increase-per-merge 1000000000 > $RUN/${s}_wave_$(date -u +%Y%m%dT%H%M%SZ).log 2>&1 &
    log "resumed $s at iteration $it"
    active=$((active+1))
    sleep 20
  done
  sleep 180
done
