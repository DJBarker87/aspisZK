#!/usr/bin/env python3
"""Read-only final source/import/axiom audit; no Lean replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

here = Path(__file__).resolve().parent
packet = here.parent.parent
manifest = json.loads((here / 'manifest.json').read_text())
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
checked = []
for receipt in manifest['attempts']:
    if not receipt['final_current']:
        continue
    source = packet / 'lean' / (receipt['module'] + '.lean')
    assert receipt['exit'] == 0
    assert sha(source) == receipt['source_sha256']
    assert all(sha(i['path']) == i['sha256'] for i in receipt['direct_imports'])
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b', text)
    names = re.findall(r'^theorem (\w+)', text, re.M)
    assert len(names) == len(receipt['axioms'])
    for name, line in zip(names, receipt['axioms']):
        assert '.' + name + "'" in line
        if 'depends on axioms:' in line:
            axioms = set(re.search(r'\[([^]]*)\]', line)[1].split(', '))
            assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
    checked.append({'module': receipt['module'], 'theorems': names})
changes = subprocess.check_output(['git', 'diff', '--name-status', '339907977'], text=True)
assert all(row.startswith('A\t') for row in changes.splitlines()), changes
print(json.dumps({'status': 'pass', 'accepted_targets': checked}, indent=2))
