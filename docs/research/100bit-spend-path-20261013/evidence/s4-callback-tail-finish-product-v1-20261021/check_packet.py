from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']: assert sha(D/f['path'])==f['sha256'],f['path']
for x in m['modules']:
 r=json.loads((D/x['receipt']).read_text()); p=json.loads((D/x['preflight']).read_text())
 assert r['exit_status']==0 and r['watchdog_abort'] is None and r['process_swaps']==0
 assert sha(D/x['source'])==r['source_sha256']==p['source_sha256']==x['source_sha256']
 assert r['object_sha256']==x['object_sha256'] and p['source_revision']==x['source_revision']
 assert r['peak_aggregate_rss_bytes']<8*2**30
 for n,v in p['direct_imports'].items(): assert m['direct_import_source_map'][n]['object_sha256']==v['sha256'],n
 text=(D/x['source']).read_text(); log=(D/Path(x['receipt']).parent/'lean.log').read_text()
 assert not re.search(r'\b(sorry|axiom|native_decide)\b',text)
 assert 'sorryAx' not in log and 'error:' not in log and 'core.fmt.Formatter' not in log
 reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log); assert reports
 for a in reports: assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
assert not any(p.suffix in ['.olean','.ilean','.ir','.o','.llbc'] for p in D.rglob('*') if p.is_file())
print('PASS',m['packet'])
