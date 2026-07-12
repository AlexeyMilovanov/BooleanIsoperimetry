#!/usr/bin/env bash
set -euo pipefail

VM=${VM:-lesha@157.90.241.208}
DEST=${DEST:-/home/lesha/harper-stability-lean/}

cd "$(dirname "$0")/.."

rsync -az \
  --exclude '.lake/' \
  --exclude 'proof_loop_runs/' \
  --exclude 'proof_loop_readiness/' \
  --exclude 'lake-manifest.json' \
  --delete \
  ./ "$VM:$DEST"
