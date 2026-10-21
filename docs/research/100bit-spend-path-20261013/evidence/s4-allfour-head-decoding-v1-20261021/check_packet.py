from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
r=json.loads((D/'evidence/receipt.json').read_text());c=json.loads((D/'evidence/command.json').read_text())
assert r['exit_status']==0
assert sha(D/m['target_source'])==r['source_sha256_at_launch']==c['source_sha256_at_launch']==m['target_source_sha256']
assert r['source_revision_at_launch']==m['source_revision']
assert '-j1' in c['argv'] and '-M4400' in c['argv']
l=(D/'evidence/lean.log').read_text();assert 'error:' not in l and 'sorryAx' not in l
reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',l);assert len(reports)==1
for a in reports:assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\b(sorry|axiom|native_decide)\b',(D/m['target_source']).read_text())
assert m['result']['swap_count']==0
assert not any(p.suffix in ['.olean','.ilean','.ir','.o'] for p in D.rglob('*') if p.is_file())
print('PASS paired all-four head witnesses; deterministic alignment and final functional remain open')
