#!/usr/bin/env bash
# Compare the independent statement with the proved solution, using the pinned
# toolchain's Lean kernel and bundled NanoDa and con-ron checkers.
set -euo pipefail
cd "$(dirname "$0")/.."
palomar_prefix=$(lean --print-prefix)
palomar_config=$(mktemp)
trap 'rm -f "$palomar_config"' EXIT
python3 - "$palomar_prefix" "$palomar_config" <<'PY'
import json
import sys
from pathlib import Path

prefix, destination = map(Path, sys.argv[1:])
config = json.loads(Path('comparator.json').read_text())
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(prefix / 'bin/nanoda_bin')],
    'con-ron': [str(prefix / 'bin/con-ron')],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
lake comparator --config "$palomar_config"
