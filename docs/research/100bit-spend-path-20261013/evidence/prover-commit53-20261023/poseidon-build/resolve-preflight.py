#!/usr/bin/env python3
"""Resolve omitted evidence roots without choosing between different bodies.

Runs read-only host --check; no compiler is invoked. Run from worktree root.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

W = Path(__file__).resolve().parent
HOST = 'dombarker@100.108.41.90'
REMOTE = '/home/dombarker/project-offloads/codex-cx-prover-commit53-20261023/poseidon-build'
files = subprocess.check_output(['rg', '--files', 'docs/research'], text=True).splitlines()
files = [Path(f) for f in files if f.endswith('.lean')]
manifest = W / 'preflight-expanded.json'
receipts = []
for step in range(100):
    subprocess.run(['scp', '-q', str(manifest), HOST + ':' + REMOTE + '/'], check=True)
    check = subprocess.run(['ssh', HOST, 'cd ' + REMOTE + ' && python3 cold-build.py --check'],
                           text=True, capture_output=True)
    if check.returncode == 0:
        print(check.stdout)
        break
    missing = re.search(r'unresolved uncached import: ([\w.]+)', check.stderr)
    if not missing:
        raise RuntimeError(check.stderr)
    m = missing[1]
    suffix = '/' + m.replace('.', '/') + '.lean'
    matches = [p for p in files if ('/' + str(p)).endswith(suffix)
               and not any(x in str(p).lower() for x in ['rejected', '/failed', '/attempts/'])]
    groups = {}
    for p in matches:
        groups.setdefault(hashlib.sha256(p.read_bytes()).hexdigest(), []).append(str(p))
    receipts.append({'module': m, 'candidates_by_sha256': groups})
    (W / 'resolution.json').write_text(json.dumps(receipts, indent=2) + '\n')
    if len(groups) != 1:
        print('STOP: unresolved or differing source bodies', m, json.dumps(groups, indent=2))
        break
    digest, candidates = next(iter(groups.items()))
    chosen = min(candidates, key=len)
    root = chosen[:-len(m.replace('.', '/') + '.lean')].rstrip('/')
    imports = []
    for line in Path(chosen).read_text().splitlines():
        hit = re.match(r'^\s*import\s+(.+)', line)
        if hit:
            imports.extend(hit[1].split('--')[0].split())
    d = json.loads(manifest.read_text())
    if root not in d['resolution_roots']:
        d['resolution_roots'].append(root)
    d['resolved_sources'][m] = {'path': chosen, 'sha256': digest, 'imports': imports}
    manifest.write_text(json.dumps(d, indent=2) + '\n')
    subprocess.run(['rsync', '-aR', chosen, HOST + ':' + REMOTE + '/pinned/'], check=True)
    print('resolved', m, chosen, flush=True)
