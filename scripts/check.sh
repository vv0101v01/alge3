#!/usr/bin/env bash
# Full local gate -- mirrors .github/workflows/ci.yml exactly.
set -euo pipefail
export PATH="$HOME/.moon/bin:$PATH"
if ! command -v moon >/dev/null 2>&1; then
  curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
  export PATH="$HOME/.moon/bin:$PATH"
fi
cd "$(dirname "$0")/.."
moon version --all
moon fmt --check
moon check --target wasm --deny-warn
moon check --target native --deny-warn
moon test --target wasm
moon test --target native
moon run --target native bench
