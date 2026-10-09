#!/usr/bin/env python3
"""Read-only build-host source-manifest audit, run from the repository root."""
import hashlib
import json
from pathlib import Path

out = Path('results/r0-opening-20261009')
manifest = json.loads((out / 'source-manifest.json').read_text())
mismatches = [path for path, digest in manifest['files'].items()
              if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest]
result = dict(source_revision=manifest['source_revision'], inputs=len(manifest['files']),
              mismatches=mismatches, exit_status=int(bool(mismatches)))
(out / 'source-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
raise SystemExit(result['exit_status'])
