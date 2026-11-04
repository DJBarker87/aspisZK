"""Artifact validation only: no compiler, prover, Kani, host or wallet action."""
from pathlib import Path
import json,lzma,hashlib,collections,subprocess,ast
P=Path(__file__).resolve().parent;B=P.parent;root=P.parents[2]
def read(p):return json.loads((P/p).read_text())
rows=read('rows12.json');tot=read('totals.json');k=read('k4-credit-check.json');pins=read('pins.json');defs=read('definition-audit12.json');m=read('manifest.json');support=read('current-support12.json');audit=read('status-audit12.json')
assert len(rows)==407 and len({r['id'] for r in rows})==407
assert collections.Counter(r['recount12_status'] for r in rows)==tot['statuses']
assert collections.Counter(r['recount12_class'] for r in rows)=={'P':400,'C':4,'T':3}
assert tot['statuses']=={'REDUCED':176,'OPEN':68,'CLOSED-ON-RESEARCH':87,'EVIDENCED':14,'CLOSED-ON-CANDIDATE':62}
assert tot['open_dependencies']=={'a':6,'b':58,'c':3,'d':1}
assert {r['id'] for r in tot['status_changes']}=={'V177','V180'}
assert len(defs)==407 and all(z['path'].endswith('LOG.md') for d in defs for z in d['changed'])
assert pins['base']=='d6b809c9e8a' and pins['revisions']['rw']=='d4ed1ba89f05a754d3982b9250f53acbd405ce7b'
assert pins['local_candidate_ref']['revision']=='8e450dab55887ad4481fc600a4b0551645725296'
assert len(k['historical_credits'])==305 and len(k['new_K9_gates'])==143
assert k['historical_suspensions']==['C044','C084','C088','C089']
assert k['new_projection_suspensions']==['K93109','K93110','K93111']
assert collections.Counter(z['k4_status'] for z in k['historical_credits'])=={'RESTORED':24,'UNAFFECTED':79,'SUSPENDED':199,'WITHDRAWN':3}
ks={z['credit_id']:z for z in k['historical_credits']}
for id in ['C051','C053','C163','C164']:assert ks[id]['k3_status']==ks[id]['k4_status']=='RESTORED'
assert ks['C156']['k3_status']==ks['C156']['k4_status']=='SUSPENDED'
assert all(not r['depends_on_still_suspended_credit'] for r in support)
for r in support:
 assert all(ks[c]['k4_status']!='SUSPENDED' for c in r.get('current_kani_support',[]))
for id in k['historical_suspensions']:
 assert ks[id]['trace_location'] is None and ks[id]['trace_path_inventory']==[]
assert audit['D597_receipt_validation']['status']=='PASS'
assert audit['D597_receipt_validation']['unresolved_constants']==0
raw=audit['D597_raw_roots']['roots'];assert len(raw)==32
assert all(r['equal'] and set(r['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound']) for r in raw)
assert len(audit['D624_D625']['contracts'])==4 and audit['endpoint_premises_removed_added_weakened']==[0,0,0]
assert tot['Lean']==tot['Kani']==0 and tot['Env_J']=='93400-93439 unused'
# Verify retained snapshot bytes against the recorded SHA; large provider
# inputs remain content-addressed committed Git blobs at the recorded pins.
contents={};checked=set();git_only=0
for z in m:
 assert len(z['blob'])==40 and len(z['sha256'])==64
 if z.get('snapshot'):
  f=z['snapshot']
  if f not in contents:contents[f]=json.loads(lzma.decompress((P/f).read_bytes()))
  v=contents[f][z['snapshot_key']]
  b=v['data'].encode() if v['encoding']=='utf8' else __import__('base64').b64decode(v['data'])
  if z['sha256'] not in checked:
   assert hashlib.sha256(b).hexdigest()==z['sha256'];checked.add(z['sha256'])
 else:git_only+=1
manifest_keys={z['ref']+':'+z['path'] for z in m}
for d in defs:
 assert all(z['ref']+':'+z['path'] in manifest_keys for z in d['sources'])
for p in P.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
ledger=(root/'design/PRIVACY-LEDGER-20261026.md').read_text();original=subprocess.check_output(['git','show',pins['base']+':design/PRIVACY-LEDGER-20261026.md']).decode();assert ledger.startswith(original)
table=ledger[ledger.index('| Inventory / status |',ledger.index('## Recount 12')):].split('\n\n',1)[0]
assert all(len(l.split('|'))==15 for l in table.splitlines())
assert ledger.count('## Recount 12 2026-11-04 (B)')==1 and 'Target not yet established' in ledger
assert len([l for l in (B/'ROWS12.md').read_text().splitlines() if l.startswith('| V')])==407
assert 'V258' in {r['row'] for r in read('v183-consumers12.json')}
files=[p for p in P.rglob('*') if p.is_file() and '__pycache__' not in str(p)];assert all(p.stat().st_size<20*1024**2 for p in files)
size=sum(p.stat().st_size for p in files);assert size<100*1024**2
out={'status':'PASS','rows':407,'statuses':tot['statuses'],'open_dependencies':tot['open_dependencies'],'historical_credits':305,'unique_new_K9_receipts':143,'k4_historical_suspensions':k['historical_suspensions'],'k4_projection_suspensions':k['new_projection_suspensions'],'snapshots_sha_checked':len(checked),'manifest_entries':len(m),'large_input_git_references':git_only,'evidence_bytes':size,'Lean':0,'Kani':0,'base':pins['base'],'candidate':pins['revisions']['rw'],'limitations':'Inspection and retained-provider receipt audit only; no new compile, raw walk, trace or release replay. Local stale candidate ref explicitly distinguished.'}
(P/'validation12.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out,indent=1))
