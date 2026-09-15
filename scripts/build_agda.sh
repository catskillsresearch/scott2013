#!/usr/bin/env bash
# Typecheck the Scott2013 library with Agda --safe.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if ! command -v agda >/dev/null 2>&1; then
  echo "error: agda not on PATH" >&2
  exit 1
fi

echo "$(agda --version)"
exec agda --safe --no-libraries -i src src/Scott2013.agda
