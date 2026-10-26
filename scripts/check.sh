#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for command in python3 bwrap lake lean; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "Required command not found: $command" >&2
    exit 1
  fi
done

config_source=${1:-comparator.json}

lake exe cache get

case "$config_source" in
  comparator.json)
    lake build Challenge Solution
    ;;
  comparator-covariance.json)
    lake build CovarianceChallenge CovarianceSolution
    ;;
  *)
    echo "Unsupported Comparator config: $config_source" >&2
    exit 1
    ;;
esac

prefix=$(lean --print-prefix)
for executable in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$executable" ]; then
    echo "Toolchain does not provide $executable" >&2
    exit 1
  fi
done

config=$(mktemp "${TMPDIR:-/tmp}/truncated-sieve-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT

python3 - "$prefix" "$config" "$config_source" <<'PY'
import json
import pathlib
import sys
prefix, destination, source = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text())
config['external_kernels'] = {
    'nanoda': [str(pathlib.Path(prefix) / 'bin' / 'nanoda_bin')],
    'con-ron': [str(pathlib.Path(prefix) / 'bin' / 'con-ron')],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY

lake comparator --config "$config"
