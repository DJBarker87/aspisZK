#!/usr/bin/env python3
"""Stage only the exact dependency cone from the accepted current snapshot."""
from pathlib import Path
import hashlib
import json
import re
import shutil

W = Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
snapshot = W / 'sampler-current-object-pins.json'
assert sha(snapshot) == 'edba3d88f67b83a1355f85ce4f8365c32f4dddc3908d27ffae8ae52b5eafdde5'
modules = json.loads(snapshot.read_text())['modules']
libraries = {'backend', 'runtime', 'mathlib', 'aesop', 'batteries', 'Qq',
             'proofwidgets', 'plausible', 'LeanSearchClient', 'importGraph'}
seen = {}


def visit(name):
    if name in seen:
        return
    if name not in modules:
        assert name.startswith(('Init', 'Lean', 'Std', 'Lake')), name
        return
    meta = modules[name]
    seen[name] = meta
    if meta.get('root') in libraries:
        return
    source = Path(meta['source'])
    assert sha(source) == meta['source_sha256'], name
    inputs = [('.lean', source, W / 'sources')]
    for suffix, obj in meta['objects'].items():
        path = Path(obj['path'])
        assert sha(path) == obj['sha256'], (name, suffix)
        inputs.append((suffix, path, W / 'objects'))
    for suffix, path, root in inputs:
        target = root / (name.replace('.', '/') + suffix)
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert sha(target) == sha(path), (name, suffix, 'incompatible universe')
        else:
            shutil.copyfile(path, target)
    if 'build_receipt' in meta:
        receipt = meta['build_receipt']
        assert sha(Path(receipt['path'])) == receipt['sha256'], name
    for child in meta['imports']:
        visit(child)


for module in ['ExtractedSourceDigestAddresses', 'ExtractedSourceCircleFrameBound']:
    source = W / 'sources' / (module + '.lean')
    for name in re.findall(r'^import ([\w.]+)', source.read_text(), re.M):
        visit(name)
manifest = W / 'input-manifest.json'
data = json.loads(manifest.read_text())
data['address_leaf_current_import_closure'] = seen
data['sources'] = {str(p.relative_to(W / 'sources')): sha(p)
                   for p in (W / 'sources').rglob('*.lean')}
manifest.write_text(json.dumps(data, indent=2) + '\n')
print('Address leaf dependencies pinned:', len(seen), '; no Lean launched')
