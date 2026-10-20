#!/usr/bin/env python3
"""Read-only validation of focused R15 sources, receipts and signatures."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
data = json.loads((HERE / 'manifest.json').read_text())
results = []
for module in ['R15WriterModel', 'R1FinalSoundnessBinPerQueryR15']:
    a = next(a for a in data['attempts'] if a['module'] == module and a['final_current'])
    source = PACKET / 'lean' / (module + '.lean')
    assert a['exit'] == 0 and sha(source) == a['source_sha256']
    assert a['swaps'] == 0
    assert all(sha(i['path']) == i['sha256'] for i in a['direct_imports'])
    obj = Path('/tmp/codex-cx-r15-writer-20261021-objects') / (module + '.olean')
    assert sha(obj) == a['object_sha256']
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option max(RecDepth|Heartbeats)', text)
    theorems = re.findall(r'^theorem (\w+)', text, re.M)
    assert all('#print axioms ' + n in text for n in theorems)
    assert len(a['axioms']) == len(theorems)
    for line in a['axioms']:
        names = re.search(r'\[(.*?)\]', line)
        if names:
            assert set(names[1].split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}
    results.append({'module': module, 'theorems': len(theorems), 'source_sha256': sha(source)})
before = (PACKET / 'lean/R1FinalSoundnessBinPerQueryR18.lean').read_text()
after = (PACKET / 'lean/R1FinalSoundnessBinPerQueryR15.lean').read_text()
def signature(s):
    start = s.index('theorem final_soundness')
    return s[start:s.index(' := by', start)] + '\n'
assert signature(before) == signature(after)
assert signature(before) == (HERE / 'signature-before.lean.txt').read_text()
assert signature(after) == (HERE / 'signature-after.lean.txt').read_text()
assert (HERE / 'signature.diff').read_text() == ''
changes = subprocess.check_output(['git', 'diff', '--name-status', '15470cfc5', '--'], cwd=ROOT, text=True)
assert all(line.startswith('A\t') for line in changes.splitlines()), changes
print(json.dumps({'status': 'passed', 'modules': results, 'signature_change': 'none; R15 retained'}, indent=2))
