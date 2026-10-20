#!/usr/bin/env python3
"""Focused additive local compile. Never rebuild or overwrite shared objects."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
OBJECTS = Path('/tmp/codex-cx-r4-transport2-20261021-objects')
LOCK = Path('/tmp/aspis-local-lean.lock.d')
LEAN = '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def lean_processes():
    rows = subprocess.check_output(['ps', '-axo', 'pid=,comm=,args='], text=True)
    return [r for r in rows.splitlines()
            if len(r.split()) > 2 and Path(r.split()[2]).name == 'lean']


module = sys.argv[1]
source = PACKET / 'lean' / (module + '.lean')
baseline = json.loads((PACKET / 'evidence/headline-20261021/R1FinalSoundnessHeadline-2/command.json').read_text())
path = str(OBJECTS) + ':' + baseline['lean_path']
overlay = Path('/tmp/codex-cx-r4-transport-20261021-imports')
(overlay / 'AspisR1PublicPreparation').mkdir(parents=True, exist_ok=True)
for filename in ['Types.olean', 'Funs.olean']:
    link = overlay / 'AspisR1PublicPreparation' / filename
    target = Path('/tmp/prepared-local-warm-cache-20261020/AspisR1PublicPreparation') / filename
    if not link.exists():
        link.symlink_to(target)
path = ':'.join([str(OBJECTS), '/tmp/codex-cx-r4-transport-20261021-objects', str(overlay), '/tmp/codex-cx-r4-row31-20261021-objects',
    '/tmp/codex-cx-sampler-20261020-objects', baseline['lean_path'],
    '/tmp/codex-cx-r14-finish-20261020-objects'])

imports = []
for name in re.findall(r'^import (\S+)', source.read_text(), re.M):
    obj = next((Path(p) / (name.replace('.', '/') + '.olean')
                for p in path.split(':')
                if (Path(p) / (name.replace('.', '/') + '.olean')).exists()), None)
    if obj is None:
        raise SystemExit('Missing cached import: ' + name)
    imports.append({'module': name, 'path': str(obj), 'sha256': sha(obj)})
overlay_sha = sha(PACKET / 'evidence/r4-transport-20261021/import-overlay-v5.json')
fp = hashlib.sha256(json.dumps({'imports':imports,'lean_path':path,'overlay_sha256':overlay_sha}, sort_keys=True).encode()).hexdigest()
manifest = HERE / 'manifest.json'
data = json.loads(manifest.read_text()) if manifest.exists() else {
    'schema': 'focused-extractor-proof-packet-v1', 'attempts': [],
    'status': 'focused model packet; coherent frozen release replay remains separate'}
if any(a['source_sha256'] == sha(source) and a['deps_fingerprint'] == fp
       for a in data['attempts']):
    raise SystemExit('Refused unchanged source/dependency retry')
n = 1 + max([int(p.name.rsplit('-', 1)[1]) for p in HERE.glob(module + '-*') if p.is_dir()] or [0])
out = HERE / (module + '-' + str(n))
out.mkdir()
(out / 'source.lean.txt').write_text(source.read_text())
OBJECTS.mkdir(exist_ok=True)
argv = [LEAN, '-j1', '-M4400', '-DElab.async=false', '-R', str(PACKET / 'lean'),
        '-o', str(OBJECTS / (module + '.olean')), str(source)]
receipt = {'module': module, 'attempt': n, 'argv': argv, 'lean_path': path,
           'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
           'source_sha256': sha(source), 'overlay_manifest_sha256':overlay_sha, 'direct_imports': imports, 'deps_fingerprint': fp,
           'nominal_owner_objects': {str(p):sha(p) for p in (overlay / 'AspisR1PublicPreparation').glob('*.olean')}}
(out / 'command.json').write_text(json.dumps(receipt, indent=2) + '\n')
while True:
    try:
        LOCK.mkdir()
    except FileExistsError:
        if time.time() - LOCK.stat().st_mtime > 1800 and not lean_processes():
            LOCK.rmdir()
        else:
            print('Waiting for shared mkdir lock', flush=True)
            time.sleep(15)
        continue
    if lean_processes():
        LOCK.rmdir()
        print('Waiting for active Lean process', flush=True)
        time.sleep(60)
        continue
    break
try:
    if sha(source) != receipt['source_sha256']:
        raise RuntimeError('Source changed while waiting for lock')
    start = time.monotonic()
    with (out / 'lean.log').open('w') as log, (out / 'time.log').open('w') as timing:
        result = subprocess.run(['/usr/bin/time', '-l', *argv],
                                env={**os.environ, 'LEAN_PATH': path}, stdout=log, stderr=timing)
    receipt.update(exit=result.returncode, wall_seconds=time.monotonic() - start)
finally:
    LOCK.rmdir()
timing = (out / 'time.log').read_text()
log = (out / 'lean.log').read_text()
receipt.update(peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size', timing)[1]),
               swaps=int(re.search(r'(\d+)\s+swaps', timing)[1]),
               axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log),
               log=str((out / 'lean.log').relative_to(ROOT)),
               time=str((out / 'time.log').relative_to(ROOT)),
               final_current=result.returncode == 0)
if result.returncode == 0:
    obj = OBJECTS / (module + '.olean')
    receipt.update(object_sha256=sha(obj), object_size=obj.stat().st_size)
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
data = json.loads(manifest.read_text()) if manifest.exists() else data
for a in data['attempts']:
    if a['module'] == module:
        a['final_current'] = False
data['attempts'].append(receipt)
manifest.write_text(json.dumps(data, indent=2) + '\n')
print(log)
print(json.dumps({k: receipt[k] for k in ['module', 'attempt', 'exit', 'wall_seconds',
                                        'peak_rss_bytes', 'swaps']}))
sys.exit(result.returncode)
