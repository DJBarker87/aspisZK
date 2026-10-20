#!/usr/bin/env python3
"""Audit focused receipts, every new theorem, and the sole signature deletion."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '15470cfc5'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def signature(s):
    a = s.index('theorem final_soundness')
    return s[a:s.index(' := by', a)]

before = signature((PACKET/'lean/R1FinalSoundnessBinPerQueryR18.lean').read_text())
after = signature((PACKET/'lean/R1FinalSoundnessBinPerQueryR19.lean').read_text())
a = before.index('    /- R19 with R10:')
b = before.index('    /- R-wire:', a)
assert after == before[:a] + before[b:]
for name, s in [('before', before), ('after', after)]:
    assert (HERE/(name+'-statement.lean.txt')).read_text() == s+'\n'
    assert s in (PACKET/'design/R19-BUDGET-20261021.md').read_text()
assert (HERE/'signature.diff').read_text() == ''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True),
    fromfile='R18.final_soundness', tofile='R19.final_soundness'))
manifest = json.loads((HERE/'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
accepted = [a for a in manifest['attempts'] if a['final_current']]
assert len(accepted) == 3
reports = 0
for a in manifest['attempts']:
    folder = HERE/(a['module']+'-'+str(a['attempt']))
    assert a == json.loads((folder/'receipt.json').read_text())
    assert all(a[k] == v for k,v in json.loads((folder/'command.json').read_text()).items())
    assert a['source_sha256'] == sha(folder/'source.lean.txt')
    assert a['deps_fingerprint'] == hashlib.sha256(json.dumps(a['direct_imports'],sort_keys=True).encode()).hexdigest()
    assert a['swaps'] == 0
    for key in ['source_revision','exit','wall_seconds','peak_rss_bytes','axioms','errors']:
        assert key in a
    if not a['final_current']:
        continue
    assert a['exit'] == 0 and not a['errors']
    src = PACKET/'lean'/(a['module']+'.lean')
    assert sha(src) == a['source_sha256']
    code = src.read_text()
    names = re.findall(r'^theorem (\w+)',code,re.M)
    assert names == re.findall(r'^#print axioms (\w+)',code,re.M)
    assert len(names) == len(a['axioms'])
    for name,line in zip(names,a['axioms']):
        assert a['module']+'.'+name+"'" in line
        assert line in (folder/'lean.log').read_text()
        assert set(re.findall(r'[\w.]+',line.split('[',1)[1])) <= ALLOWED
        reports += 1
    stripped = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', stripped)
    for dep in a['direct_imports']:
        assert sha(dep['path']) == dep['sha256']
        candidates = [Path(p)/(dep['module'].replace('.','/')+'.olean') for p in a['lean_path'].split(':')]
        assert next(str(p) for p in candidates if p.exists()) == dep['path']
    obj = Path(a['argv'][a['argv'].index('-o')+1])
    assert sha(obj) == a['object_sha256'] and obj.stat().st_size == a['object_size']
    assert a['argv'][1:4] == ['-j1','-M4400','-DElab.async=false']
    assert a['lean_path'].split(':')[0] == str(obj.parent)
changes = subprocess.check_output(['git','diff',BASE,'--name-status'],cwd=ROOT,text=True).splitlines()
assert all(s.startswith('A\t') for s in changes), changes
assert not any(s.endswith(('.olean','.tar','.gz','.elf')) for s in changes)
result = dict(status='PASS', base=BASE, scope='Focused cached-object evidence; no coherent frozen release replay',
              accepted_modules=len(accepted), axiom_reports=reports, total_attempts=len(manifest['attempts']),
              endpoint_only_removes_h_R19=True, replacement_premises=[], existing_files_unchanged=True,
              peak_rss_bytes=max(a['peak_rss_bytes'] for a in manifest['attempts']),
              swaps=sum(a['swaps'] for a in manifest['attempts']))
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
