#!/usr/bin/env python3
"""Pin a private namespace union, or recreate its hash-checked symlinks."""
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
EVIDENCE=ROOT/'docs/research/100bit-spend-path-20261013/evidence/s7-join-20261021'
OBJECTS=Path('/tmp/codex-cx-s7-join-20261021-objects')
overlay=EVIDENCE/'cache-overlay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)>1:
    namespace=sys.argv[2] if len(sys.argv)>2 else 'AspisV8R19'
    command=json.loads(Path(sys.argv[1]).read_text())
    selected={}
    for entry in command['lean_path'].split(':'):
        base=Path(entry)
        if base==OBJECTS:continue
        directory=base/namespace
        if directory.is_dir():
            for source in sorted(directory.rglob('*')):
                if source.is_file() and any(source.name.endswith(suffix) for suffix in
                    ['.olean','.olean.server','.olean.private','.ir']):
                    relative=source.relative_to(base)
                    selected.setdefault(str(relative),source)
    records=[{'source_object':str(source),'selected_object':str(OBJECTS/relative),
              'sha256':sha(source),'bytes':source.stat().st_size}
             for relative,source in sorted(selected.items())]
    previous=json.loads(overlay.read_text())['objects'] if overlay.exists() else []
    assert not ({r['selected_object'] for r in previous}&{r['selected_object'] for r in records}), 'Refusing to replace pinned namespace'
    records=previous+records
    overlay.write_text(json.dumps({'schema':'private-cache-namespace-union-v1',
        'reason':'RowsTrace imports expose partial AspisV8R19 and AspisR72Sampler namespaces; union preserves first existing module per ordered LEAN_PATH',
        'source_command':str(Path(sys.argv[1]).relative_to(ROOT)),
        'objects':records},indent=2)+'\n')
for row in json.loads(overlay.read_text())['objects']:
    source,target=Path(row['source_object']),Path(row['selected_object'])
    assert sha(source)==row['sha256'] and source.stat().st_size==row['bytes']
    assert target.is_relative_to(OBJECTS)
    target.parent.mkdir(parents=True,exist_ok=True)
    if not target.exists():target.symlink_to(source)
    assert target.is_symlink() and target.resolve()==source.resolve()
print('Validated private namespace union; shared caches unchanged')
