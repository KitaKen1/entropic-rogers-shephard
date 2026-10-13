#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../build-receipt
set +e
timeout --kill-after=120 300m lake build FCSolution EntropicRogersShephard.Audit 2>&1 | tee ../build-receipt/build.log
ERS_PIPE=("${PIPESTATUS[@]}")
set -e
test "${ERS_PIPE[1]}" -eq 0
if [[ "${ERS_PIPE[0]}" -eq 0 ]]; then
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "${ERS_PIPE[0]}" -eq 124 || "${ERS_PIPE[0]}" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun same commit to resume cached build\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "${ERS_PIPE[0]}" > ../build-receipt/status.txt
  exit "${ERS_PIPE[0]}"
fi
