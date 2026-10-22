from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for x in m['files']:assert sha(D/x['path'])==x['sha256'],x['path']
for x in m['modules']:
 rc=json.loads((D/x['receipt']).read_text());pf=json.loads((D/x['preflight']).read_text());cmd=json.loads((D/x['command']).read_text())
 assert rc['exit_status']==0 and rc['watchdog_abort'] is None and rc['process_swaps']==0
 assert sha(D/x['source'])==rc['source_sha256']==pf['source_sha256']==x['source_sha256']
 assert rc['object_sha256']==x['object_sha256'] and pf['source_revision']==x['source_revision']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 assert rc['peak_aggregate_rss_bytes']<8*2**30
 for n,pin in pf['direct_imports'].items():assert m['direct_import_source_map'][n]['object_sha256']==pin['sha256']
 s=(D/'evidence/lean.log').read_text();assert 'sorryAx' not in s and 'error:' not in s and 'core.fmt.Formatter' not in s
 reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',s);assert len(reports)==2
 for a in reports:assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide)\b',(D/x['source']).read_text())
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc'] for f in D.rglob('*') if f.is_file())
print('PASS: s4-tx1-concrete-ten-field-results-root-v4-20261021; actual source operation installation remains open')
