#!/usr/bin/env python3
"""Collect source-only native step packets and preserve excluded predecessors."""
from pathlib import Path
import hashlib
import json
import shutil

R = Path(__file__).resolve().parents[2]
E = R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O = E/'s6-bump-step-terminal-v1'
O.mkdir(exist_ok=True)
for version in [1,2,3,4,5]:
    source = Path('/tmp/s6-bump-step-20261026-v'+str(version)).resolve()
    destination = O/('source-v'+str(version))
    destination.mkdir(exist_ok=True)
    for path in source.rglob('*'):
        if not path.is_file() or 'target' in path.relative_to(source).parts:
            continue
        assert path.suffix in {'.rs','.toml','.lock','.json','.py'}, path
        target = destination/path.relative_to(source)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
manifest = {
    'schema': 'focused-extractor-proof-packet-v1',
    'positive': 's6-bump-step-positive-local-v4',
    'negative': 's6-bump-step-negative-local-v4',
    'source_workspace': 'source-v5',
    'positive_predecessor_262144_bytes': 's6-bump-step-positive-local-v3',
    'negative_predecessor_262144_bytes': 's6-bump-step-negative-local-v3',
    'positive_predecessor_8192_bytes': 's6-bump-step-positive-local-v1',
    'excluded_stack_arena_timeout': 's6-bump-step-positive-local-v2',
    'scope': 'Actual copied SDK allocator one-step and dealloc, successful Kani arena allocation, aarch64/darwin,262144-byte arena, arbitrary initial cursor/request, align1/2/4/8; reference floor division. No whole caller/native-global-allocator/SBF or native-to-Lean reference extraction claim.',
    'whole_s6_closed': False, 'enclosing_premises_removed': 0,
}
manifest['source_files'] = {str(path.relative_to(O)): hashlib.sha256(path.read_bytes()).hexdigest()
                            for path in sorted(O.rglob('*')) if path.is_file() and path != O/'manifest.json'}
(O/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'exported_source_files': len(manifest['source_files'])}))
