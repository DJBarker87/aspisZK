from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
for x in m['modules']:
 rc=json.loads((D/x['receipt']).read_text());cmd=json.loads((D/x['command']).read_text());s=(D/x['log']).read_text()
 assert rc['exit_status']==0 and rc['source_sha256']==x['source_sha256']==sha(D/x['source']) and rc['object_sha256']==x['object_sha256']
 assert rc['git_head_at_launch']==x['source_revision'] and '-j1' in rc['argv'] and '-M4400' in rc['argv']
 assert int(re.search(r'(\d+)\s+maximum resident set size',s)[1])==x['peak_rss_bytes']<8*2**30
 assert re.search(r'0\s+swaps',s) and 'sorryAx' not in s and 'error:' not in s and 'core.fmt.Formatter' not in s
 reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',s);assert len(reports)==4
 for a in reports:assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
for n,x in m['supporting_selected_modules'].items():
 rc=json.loads((D/x['receipt']).read_text());assert rc['exit_status']==0 and rc['source_sha256']==sha(D/x['source'])==x['source_sha256'] and rc['object_sha256']==x['object_sha256']
for n,x in m['direct_import_source_map'].items():assert sha(D/x['source'])==x['source_sha256'],n
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc'] for f in D.rglob('*') if f.is_file())
print('PASS: original serializer -> strict extracted parser -> same eight coordinates; standard axioms; P6/Std boundary explicit')
