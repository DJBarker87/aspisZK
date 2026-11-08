"""Validate Run6 evidence without replaying a prover or scanning shared caches."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
rows=[]; allowed={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('NNH_L9[0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());n=int(r['attempt'][-3:])
 if n<907:continue
 assert n<=946
 assert r['source_revision'] and r['wall_seconds']>=0
 assert int(r['peak_rss_kib'])>0 and int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and r['timeout']==180
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 disk=json.loads((E/(r['attempt']+'-disk-0.json')).read_text());assert disk['free']>=40_000_000_000
 for rel,sha in r['source_hashes'].items():assert hashlib.sha256((p.parent/'sources'/rel).read_bytes()).hexdigest()==sha
 assert r['deps_fingerprint']['selected_objects']
 assert any('Aeneas' in x for x in r['deps_fingerprint']['selected_objects'])
 if r['exit_status']==0:
  for line in r['print_axioms']:
   found=re.search(r'axioms: \[(.*)\]',line)
   if found:assert {re.sub(r'\.\{[^{}]*\}$','',x) for x in found[1].split(', ')}<=allowed,line
 rows.append(r)
assert len(rows)<=40
shares=[json.loads(l) for l in (E/'NNH_ATTEMPTS.jsonl').read_text().splitlines()]
for r in rows:
 assert any(x.get('attempt')==r['attempt'] and x.get('event')=='share_check' and x['host']['count']<6 for x in shares)
products={}
for name in ['NNH_Run6_OBJECTS_before_final.json','NNH_Run6_OBJECTS_final.json']:
 for value in json.loads((E/name).read_text()).values():products[value['attempt']]=value
for r in rows:
 if r['exit_status']==0:
  assert r['attempt'] in products, 'Missing output hash for '+r['attempt']
  assert products[r['attempt']]['source_hashes']==r['source_hashes']
  assert products[r['attempt']]['objects']
pins={}
for r in rows:
 for key,v in r['deps_fingerprint']['selected_objects'].items():pins.setdefault(key,set()).add(v['sha256'])
assert not [k for k,v in pins.items() if len(v)>1], 'Changed selected dependency object'
(E/'NNH_Run6_PIN_CONSISTENCY.json').write_text(json.dumps({'selected_object_paths':len(pins),'variants':sum(len(v) for v in pins.values()),'changed_paths':[],'own_products':len(products)},indent=2)+'\n')
sources=sorted(E.glob('NNH_Run6*.lean'))+[E/'NNH_DeployedOuter.lean',E/'TAS_FinalB.lean']
accepted=[]
for p in sources:
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r for r in rows if r['exit_status']==0 and sha in r['source_hashes'].values()]
 assert matches,'No passing exact source: '+p.name
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b',p.read_text(),re.M),p.name
 accepted.append({'module':p.stem,'source_sha256':sha,'attempt':matches[-1]['attempt'],'axioms':matches[-1]['print_axioms']})
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
summary={'status':'CONDITIONAL; no credit','condition4':'NOT PROVED','scopes':len(rows),'pass':sum(r['exit_status']==0 for r in rows),'fail':sum(r['exit_status']!=0 for r in rows),'wall_seconds':sum(r['wall_seconds'] for r in rows),'max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in rows),'swaps':0,'sources':accepted,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'final_gate_run':False,'16GiB_used':False,'Kani':0,'extraction':0}
(E/'NNH_Run6_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
with (E/'NNH_Run6_COMPILE.tsv').open('w') as f:
 f.write('attempt\tmodule\texit\twall_seconds\tpeak_rss_kib\tswaps\tsource_revision\tprinted_axioms\n')
 for r in rows:f.write('\t'.join(str(r[k]) for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision'])+'\t'+' | '.join(r['print_axioms'])+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='sources'}))
