#!/usr/bin/env bash
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
# Run the unmodified, pinned upstream Comparator with its real Linux sandbox.
set -euo pipefail
cd "$(dirname "$0")"
comparator_nanoda=false
if [[ "${1:-}" == --help ]]; then
  printf '%s\n' 'Usage: ./check_comparator.sh [--nanoda] [ComparatorChallenges/NAME.json ...]' \
    'The --nanoda option additionally requires the pinned real nanoda_bin on PATH.'
  exit 0
fi
if [[ "${1:-}" == --nanoda ]]; then
  comparator_nanoda=true
  shift
fi
if [[ "$(uname -s)" != Linux ]]; then
  printf '%s\n' 'Comparator sandbox not run: real Landrun requires Linux.' >&2
  exit 2
fi
if [[ "$(id -u)" == 0 ]]; then
  printf '%s\n' 'Run Comparator as an unprivileged user, as required by upstream.' >&2
  exit 2
fi
command -v landrun >/dev/null || {
  printf '%s\n' 'Missing landrun. See ComparatorChallenges/README.md for the pinned source build.' >&2
  exit 2
}
# The pinned Landrun requests its full filesystem/network/IPC feature set.
# Do not add --best-effort: fail before Comparator on an incapable kernel.
if ! landrun --ro / --ldd --add-exec /usr/bin/true; then
  printf '%s\n' \
    'Comparator not run: strict Landrun capability preflight failed.' \
    'The pinned Landrun requires full Landlock ABI 9 support (Linux 7.1 or newer).' >&2
  exit 2
fi
printf '%s\n' 'Strict Landrun capability preflight passed.'
if [[ "$comparator_nanoda" == true ]]; then
  command -v nanoda_bin >/dev/null || {
    printf '%s\n' 'Missing nanoda_bin. Build the pinned source described in ComparatorChallenges/README.md.' >&2
    exit 2
  }
  printf '%s\n' 'Nanoda enabled explicitly, in addition to Lean kernel replay.'
fi
lake build comparator lean4export
export PATH="$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"
if [[ $# == 0 ]]; then
  set -- ComparatorChallenges/Theorem1Achievability.json \
    ComparatorChallenges/Theorem1Converse.json ComparatorChallenges/Theorem2Choi.json
fi
comparator_temp=$(mktemp -d)
trap 'rm -rf "$comparator_temp"' EXIT
comparator_index=0
for comparator_config in "$@"; do
  if [[ "$comparator_nanoda" == true ]]; then
    comparator_index=$((comparator_index + 1))
    comparator_generated="$comparator_temp/nanoda-$comparator_index.json"
    python3 - "$comparator_config" "$comparator_generated" <<'PY'
import json
from pathlib import Path
import sys
config = json.loads(Path(sys.argv[1]).read_text())
config["enable_nanoda"] = True
Path(sys.argv[2]).write_text(json.dumps(config, indent=2) + "\n")
PY
    lake exe comparator "$comparator_generated"
  else
    lake exe comparator "$comparator_config"
  fi
done
