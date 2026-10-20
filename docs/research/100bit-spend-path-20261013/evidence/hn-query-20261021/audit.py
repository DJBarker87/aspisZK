#!/usr/bin/env python3
"""Audit receipts without re-running Lean or changing any object cache."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '12d15d245'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

manifest = json.loads((HERE / 'manifest.json').read_text())
accepted = [a for a in manifest['attempts'] if a['final_current']]
assert {a['module'] for a in accepted} == {
    'DecoderQueryAccounting','BinHonestStartFrames','BinHonestQueryBudget',
    'BinPerQueryNumeric','BinInitialQueryAccounting','R1FinalSoundnessBinPerQuery',
    'DecoderFiniteStartSupport'}
summary = []
for a in accepted:
    module = a['module']
    src = PACKET / 'lean' / (module + '.lean')
    assert a['exit'] == 0 and a['swaps'] == 0
    assert sha(src) == a['source_sha256'], module
    assert sha(Path(a['argv'][a['argv'].index('-o')+1])) == a['object_sha256']
    for imp in a['direct_imports']:
        assert sha(imp['path']) == imp['sha256'], (module, imp['module'])
    assert hashlib.sha256(json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest() == a['deps_fingerprint']
    decls = re.findall(r'^(?:private )?theorem (\w+)', src.read_text(), re.M)
    prints = re.findall(r'^#print axioms (\w+)', src.read_text(), re.M)
    assert sorted(decls) == sorted(prints), (module, decls, prints)
    assert len(a['axioms']) == len(decls), module
    for ax in a['axioms']:
        if 'depends on axioms:' in ax:
            names = re.search(r'\[([\s\S]*?)\]', ax)[1]
            assert set(re.findall(r'\w+(?:\.\w+)*', names)) <= {'propext','Classical.choice','Quot.sound'}, ax
    assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b', src.read_text()), module
    summary.append({k:a[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','deps_fingerprint']})
changed = subprocess.check_output(['git','diff','--name-status',BASE],cwd=ROOT,text=True).splitlines()
assert all(line.startswith('A\t') for line in changed), changed
for label, module in [('before','R1FinalSoundnessBinFirstReadBudget'),('after','R1FinalSoundnessBinPerQuery')]:
    source = (PACKET/'lean'/(module+'.lean')).read_text()
    sig = source[source.index('theorem final_soundness'):source.index(' := by',source.index('theorem final_soundness'))]
    assert (HERE/(label+'-statement.lean.txt')).read_text() == sig+'\n'
    assert sig in (PACKET/'design/HN-QUERY-20261021.md').read_text()
result = {'schema':'hn-query-focused-receipt-audit-v1','base':BASE,'accepted':summary,
          'attempt_count':len(manifest['attempts']),
          'theorem_count':sum(len(a['axioms']) for a in accepted),
          'standard_axioms_only':True,'additions_only':True}
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
