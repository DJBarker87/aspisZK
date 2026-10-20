#!/usr/bin/env python3
"""Read-only focused receipts/source audit, including failed drafts."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest = json.loads((HERE / 'manifest.json').read_text())
results = []
for a in manifest['attempts']:
    folder = HERE / (a['module'] + '-' + str(a['attempt']))
    assert sha(folder / 'source.lean.txt') == a['source_sha256']
    assert a['swaps'] == 0
    assert all(k in a for k in ['argv', 'source_revision', 'deps_fingerprint',
                               'exit', 'wall_seconds', 'peak_rss_bytes', 'axioms'])
    if not a['final_current']:
        continue
    module = a['module']
    assert a['exit'] == 0
    source = PACKET / 'lean' / (module + '.lean')
    assert sha(source) == a['source_sha256']
    assert all(sha(i['path']) == i['sha256'] for i in a['direct_imports'])
    assert sha(Path('/tmp/codex-cx-r16-decision-20261021-objects') /
               (module + '.olean')) == a['object_sha256']
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option max(RecDepth|Heartbeats)', text)
    names = re.findall(r'^theorem (\w+)', text, re.M)
    assert all('#print axioms ' + n in text for n in names)
    assert len(names) == len(a['axioms'])
    for line in a['axioms']:
        used = re.search(r'\[([\s\S]*?)\]', line)
        if used:
            assert set(re.findall(r'[\w.]+', used[1])) <= {'propext', 'Classical.choice', 'Quot.sound'}
    results.append({'module': module, 'theorems': len(names), 'exit': a['exit'],
                    'peak_rss_bytes': a['peak_rss_bytes']})
changes = subprocess.check_output(['git', 'diff', '--name-status', '418a4c9ea', '--'],
                                  cwd=ROOT, text=True)
assert all(line.startswith('A\t') for line in changes.splitlines()), changes
print(json.dumps({'status': 'passed', 'modules': results}, indent=2))
