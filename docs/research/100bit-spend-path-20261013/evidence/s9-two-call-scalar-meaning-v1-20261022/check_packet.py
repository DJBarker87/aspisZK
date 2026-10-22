#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
src=root/m['source']; prof=root/m['profile']; rec=json.loads((root/m['launch_receipt']).read_text()); close=json.loads((root/m['closure_preflight']).read_text()); pre=json.loads((root/m['preflight']).read_text())
assert sha(src)==m['source_sha256']==rec['source_sha256']
assert sha(prof)==m['profile_sha256']==pre['profile_sha256']
assert rec['exit_status']==0 and rec['object_sha256']==m['external_object_sha256']
assert not close['missing'] and len(close['owners'])==m['closure']['modules']
log=(root/m['lean_raw_log']).read_text()
for decl, axioms in m['theorems'].items():
    match=re.search(re.escape("'"+decl+"' depends on axioms:")+r'([^\n]*(?:\n\s+[^\n]*){0,3})',log)
    assert match, f'missing named axiom report for {decl}'
    assert all(a in match.group(1) for a in axioms), f'unexpected axiom report for {decl}: {match.group(1)}'
    assert 'sorryAx' not in match.group(1), f'sorryAx in {decl}'
assert not list(root.rglob('*.olean')), 'packet must remain source-only'
print('PASS source-only proof packet; import closure complete; four named theorem reports present')
