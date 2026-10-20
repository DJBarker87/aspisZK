from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
for x in m['modules']:
 rc=json.loads((D/x['receipt']).read_text());pf=json.loads((D/x['preflight']).read_text())
 assert rc['exit_status']==0 and rc['swap_bytes']==0 and rc['peak_rss_bytes']<8*2**30
 assert sha(D/x['source'])==rc['source_sha256']==pf['source_sha256']==x['source_sha256']
 assert rc['object_sha256']==x['object_sha256'] and pf['git_head_before_popen']==rc['git_head_before_popen']==x['source_revision']
 assert '-j1' in pf['argv'] and '-M4400' in pf['argv'] and not any(s.startswith('-D') for s in pf['argv'])
 s=(D/'evidence/lean.log').read_text();assert 'sorryAx' not in s and 'error:' not in s and 'core.fmt.Formatter' not in s
 reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',s);assert reports
 for a in reports:assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
for n,o in m['direct_import_source_map'].items():assert sha(D/o['source_path'])==o['source_sha256']
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc'] for f in D.rglob('*') if f.is_file())
print('PASS: total and canonical sixteen-entry source-cut model; exact launch evidence; enclosing caller/Std open')
