"""Offline receipts, source archive and matched-configuration audit."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
PATCH='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67';STUB='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9';LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
receipts=[];archive={}
for p in sorted(E.glob('KNA_*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert r['kmx_patch_sha256']==PATCH and r['kmx_stub_file_sha256']==STUB
 ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 if r['kind'] in ['kani','rust']:
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['allowed'] and g['unchanged'] and g['lock_before']==g['lock_after']==LOCK
  assert r['source_hashes']['KMX_stubs.rs']==STUB and r['source_hashes']['KMY_src/Cargo.lock']==LOCK
  if r['kind']=='kani':
   src=E/'sources'/(r['source_hashes']['KNA_windows.rs']+'.rs');assert src.exists()
   assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_hashes']['KNA_windows.rs']
   archive[a]={'KNA_windows.rs':str(src.relative_to(E))}
 else:
  source=E/r['sources'][0];assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_hashes'][source.name]
  if r['exit_status']==0:assert not any('sorryAx' in x for x in r['print_axioms'])
  archive[a]={source.name:source.name}
 c=p.parent/'classification.json'
 result=json.loads(c.read_text())['result'] if c.exists() else ('PASS' if r['exit_status']==0 else 'ERROR')
 receipts.append(dict(attempt=a,kind=r['kind'],result=result,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps']),source_revision=r['source_revision']))
for pair in json.loads((E/'KNA_PAIRS.json').read_text()):
 pos=json.loads((E/pair['positive_id']/'receipt.json').read_text());neg=json.loads((E/pair['control_id']/'receipt.json').read_text())
 for key in ['env','command','timeout']:
  x=pos[key];y=neg[key]
  if key=='command':x=x[:2]+['ATTEMPT']+x[3:];y=y[:2]+['ATTEMPT']+y[3:]
  assert x==y,(pair,key)
 for key in pos['source_hashes']:
  if key!='KNA_windows.rs':assert pos['source_hashes'][key]==neg['source_hashes'][key],(pair,key)
 p=(E/archive[pos['attempt']]['KNA_windows.rs']).read_text();n=(E/archive[neg['attempt']]['KNA_windows.rs']).read_text();assert p.replace('^0u8','^1u8').replace('^ 0u8','^ 1u8')==n,pair['name']
(E/'KNA_RUNS.json').write_text(json.dumps(receipts,indent=2)+'\n');(E/'KNA_SOURCE_ARCHIVE.json').write_text(json.dumps(archive,indent=2)+'\n')
print(json.dumps({'attempts':len(receipts),'kani':sum(r['kind']=='kani' for r in receipts),'lean':sum(r['kind']=='lean' for r in receipts),'rust':sum(r['kind']=='rust' for r in receipts),'max_rss_kib':max(r['peak_rss_kib'] for r in receipts)}))
