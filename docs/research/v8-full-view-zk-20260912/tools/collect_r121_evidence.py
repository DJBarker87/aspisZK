#!/usr/bin/env python3
"""Collect public logs and pins only; exclude keys, fixtures and objects."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
out = args.output
assert not out.exists()
out.mkdir(parents=True)
base = Path('/home/dombarker/project-offloads')
cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1].lstrip('/')
resources = {n: (cg / n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']}
assert resources == {'memory.high': str(2**30), 'memory.max': str(2*2**30), 'memory.swap.max': '0', 'pids.max': '128'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob(path):
    h = sha(path)
    destination = out / 'blobs' / h
    destination.parent.mkdir(exist_ok=True)
    if not destination.exists():
        shutil.copy2(path, destination)
    assert sha(destination) == h
    return h


control = base / 'aspis-r20-r117-primal-20260930-a'
manifest = control / 'r18-stage.json'
assert sha(manifest) == '26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6'
source_pins = json.loads(manifest.read_text())['files']
for name, h in source_pins.items():
    assert sha(control / name) == h, name
formal = {}
stages = ['table-a', 'table-b', 'table-c', 'weights-a', 'weights-b', 'g-a',
          'fixed-a', 'fixed-b', 'model-a', 'source-a', 'source-b',
          'minor-a', 'minor-b', 'minor-c', 'minor-d', 'release-a']
for short in stages:
    component, attempt = short.rsplit('-', 1)
    name = f'aspis-r121-{component}-20260930-{attempt}'
    stage = base / name
    assert stage.is_dir(), stage
    artifacts = {path.name: blob(path) for path in sorted(stage.iterdir())
                 if path.is_file() and path.suffix in ['.json', '.log']}
    formal[name] = {'stage': str(stage), 'artifacts': artifacts}
(out / 'formal.json').write_text(json.dumps(formal, indent=2) + '\n')
(out / 'collection.json').write_text(json.dumps({
    'resources': resources, 'selected_native_manifest_sha256': sha(manifest),
    'selected_native_files_verified': len(source_pins),
    'all_selected_native_source_pins_verified': True,
    'private_fixtures_collected': False, 'compiled_objects_collected': False,
    'wallet_keys_collected': False, 'verifier_changed': False,
}, indent=2) + '\n')
print(json.dumps({'stages': len(stages), 'public_files': sum(p.is_file() for p in out.rglob('*'))}))
