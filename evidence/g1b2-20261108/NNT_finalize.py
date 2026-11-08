"""Summarise retained receipts, standard axioms and live-object pin consistency."""
from pathlib import Path
import json,hashlib,csv,re
E=Path(__file__).resolve().parent
rows=[];objects={};changed=[];last_lean={}
for p in sorted(E.glob('NNT_L[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());a=x['attempt']
 if x['kind']=='lean' and x['exit_status']==0:last_lean[x['module']]=x
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for key,v in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/NNH_' in key or '/Aeneas' in key:
   if key in objects and objects[key]!=v['sha256']:changed.append(dict(attempt=a,path=key,old=objects[key],new=v['sha256']))
   objects[key]=v['sha256']
 if x['exit_status']==0 and x['kind']=='lean':
  assert not any('sorryAx' in l for l in x.get('print_axioms',[]))
  for l in x.get('print_axioms',[]):
   if 'depends on axioms:' in l:
    axioms=set(l.split('[',1)[1].split(']',1)[0].split(', '));assert axioms<={'propext','Classical.choice','Quot.sound'},l
 rows.append(dict(attempt=a,target=x['module'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],revision=x['source_revision'],source_hashes=json.dumps(x['source_hashes'],sort_keys=True),deps_receipt=str(p.relative_to(E)),axioms=' | '.join(x.get('print_axioms',[]))))
with (E/'NNT_COMPILE.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t');w.writeheader();w.writerows(rows)
(E/'NNT_PIN_CONSISTENCY.json').write_text(json.dumps(dict(selected_NNH_Aeneas_files=len(objects),changed=changed),indent=2)+'\n')
assert not changed,changed
attempts=[json.loads(l) for l in (E/'NNT_ATTEMPTS.jsonl').read_text().splitlines()]
for row in rows:
 checks=[x for x in attempts if x['attempt']==row['attempt'] and x.get('event')=='share_check']
 assert checks and checks[-1]['host']['count']<6
 disks=[json.loads(p.read_text()) for p in E.glob(row['attempt']+'-disk-*.json')]
 assert disks and disks[-1]['free']>=40_000_000_000

sources=[]
for p in E.glob('NNT_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s)
 assert 'maxHeartbeats' not in s and 'maxRecDepth' not in s
 assert p.stem in last_lean,p.stem
 assert hashlib.sha256(p.read_bytes()).hexdigest()==last_lean[p.stem]['source_hashes']['NNT_generated/'+p.name],p.name
 sources.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
(E/'NNT_SOURCE_HASHES.json').write_text(json.dumps(sources,indent=2)+'\n')
print(json.dumps(dict(scopes=len(rows),pass_count=sum(r['exit']==0 for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),selected_pins=len(objects),changed=len(changed))))
