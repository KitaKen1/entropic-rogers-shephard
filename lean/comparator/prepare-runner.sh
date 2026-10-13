#!/usr/bin/env bash
set -euo pipefail
sudo apt-get update -qq
sudo apt-get install -y -q time > /dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/elan-init.sh"
sh "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain none > /dev/null
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
{ nproc; free -h; df -h / /mnt 2>/dev/null || true; } | tee "$RUNNER_TEMP/runner.txt"
