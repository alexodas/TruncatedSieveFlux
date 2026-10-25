#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for command in python3 bwrap lake lean; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "Required command not found: $command" >&2
    exit 1
  fi
done

lake exe cache get
lake build Challenge Solution

prefix=$(lean --print-prefix)
for executable in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$executable" ]; then
    echo "Toolchain does not provide $executable" >&2
    exit 1
  fi
done

config=$(mktemp "${TMPDIR:-/tmp}/truncated-sieve-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT

python3 - "$prefix" "$config" <<'PY'
import json
import pathlib
import sys
prefix, destination = sys.argv[1:]
config = json.loads(pathlib.Path('comparator.json').read_text())
config['external_kernels'] = {
    'nanoda': [str(pathlib.Path(prefix) / 'bin' / 'nanoda_bin')],
    'con-ron': [str(pathlib.Path(prefix) / 'bin' / 'con-ron')],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY

lake comparator --config "$config"
