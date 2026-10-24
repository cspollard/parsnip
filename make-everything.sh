#!/usr/bin/env bash
# Typecheck every module of the library on its own (no GeoAgda on the path).
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p test
{
  echo "module Everything where"; echo
  find src -type f -name "*.agda" | sort | sed -e 's|^src/||' -e 's|\.agda$||' -e 's|/|.|g' -e 's/^/import /'
} > test/Everything.agda
agda -i src -i test test/Everything.agda
