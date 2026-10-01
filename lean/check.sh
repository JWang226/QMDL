#!/usr/bin/env bash
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
set -euo pipefail
cd -- "$(dirname -- "$0")"
if ! command -v lake >/dev/null 2>&1; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
mkdir -p verification
python3 audit.py --generate
lake build All 2>&1 | tee verification/build.txt
lake env lean Audit.lean 2>&1 | tee verification/axioms.txt
python3 audit.py
