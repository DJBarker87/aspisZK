#!/usr/bin/env python3
"""Recreate only the pinned private namespace symlinks; never build objects."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT / 'docs/research/100bit-spend-path-20261013/evidence/join-split-draft-20261021'
OBJECTS = Path('/tmp/codex-cx-join-split-draft-20261021-objects')
for record in json.loads((EVIDENCE / 'cache-overlay.json').read_text())['objects']:
    source, target = Path(record['source_object']), Path(record['selected_object'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sha256']
    assert source.stat().st_size == record['bytes']
    assert target.is_relative_to(OBJECTS)
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists():
        target.symlink_to(source)
    assert target.is_symlink() and target.resolve() == source.resolve()
print('Pinned private cache symlinks validated; shared caches unchanged')
