from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
for x in m['modules']:
 r=json.loads((D/x['receipt']).read_text());assert r['exit_status']==0 and r['swap_bytes']==0
 assert sha(D/x['source'])==r['source_sha256']==x['source_sha256'];assert r['object_sha256']==x['object_sha256']
 assert 'source_revision_observed_after_compile' in r and 'source_revision_at_launch' not in r
 s=(D/'evidence/lean.log').read_text();assert 'sorryAx' not in s and 'core.fmt.Formatter' not in s and 'error:' not in s
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',s):assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
assert not any(f.suffix in ['.olean','.ir','.ilean','.o'] for f in D.rglob('*') if f.is_file())
print('PASS: checked model totality/projection; launch-provenance and option gaps explicitly retained')
