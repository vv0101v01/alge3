#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.moon/bin:$PATH"
if ! command -v moon >/dev/null 2>&1; then
  curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
fi
cd "$(dirname "$0")/.."
moon test --target wasm
moon test --target native
moon run --target native bench
