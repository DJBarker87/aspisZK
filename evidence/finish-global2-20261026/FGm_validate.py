from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];passes={};missing=[]
for n in range(1,101):
 p=E/f'FGm_{n:03}'/'receipt.json'
 if not p.exists():missing.append(n);continue
 r=json.loads(p.read_text());receipts.append(r)
 assert r['command'][3:6]==['-j1','-M7000','-DElab.async=false'],r['attempt']
 assert r['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),r['attempt']
 assert int(r['swaps'])==0,r['attempt']
 assert (E/(r['attempt']+'-reservation.json')).exists()
 admitted=json.loads((E/(r['attempt']+'-reservation.json')).read_text())
 assert admitted['allowed'] and admitted['all_populated_scopes_bounded'],r['attempt']
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line and 'native_decide' not in line,line
   if 'depends on axioms:' in line:
    names=set(line.split('[')[-1].rstrip(']').split(', '));assert names<=set(['propext','Classical.choice','Quot.sound']),line
  for name,h in r['source_hashes'].items():passes.setdefault((name,h),[]).append(r['attempt'])
sources=[]
for p in sorted((R/'lean').glob('FGm_*.lean')):
 found=passes.get((p.name,sha(p)),[])
 sources.append(dict(source=str(p.relative_to(R)),sha256=sha(p),passing=found))
 assert found,('unverified current source',p)
 text=p.read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',text),p
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',text),p
# Build a fresh field inventory attached to this new root.
catalog={}
for r in receipts:
 if r['exit_status']:continue
 s=(E/r['attempt']/'stdout.log').read_text()
 for block in re.split(r'(?=^structure )',s,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  name=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  if name in catalog:assert catalog[name]['fields']==fields,name
  catalog[name]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
base=json.loads((R/'evidence/recount7-20261026/Rc7_field_catalog.json').read_text())
unchanged=[]
for key in catalog.keys()&base.keys():
 assert catalog[key]['fields']==base[key]['fields'],('changed inherited field',key)
 unchanged.append(key)
(E/'FGm_field_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
report=dict(limit=100,charged=len(receipts),unlaunched=missing,passing=sum(r['exit_status']==0 for r in receipts),failed=[r['attempt'] for r in receipts if r['exit_status']],kani_runs=0,kani_limit=0,total_compiler_wall_seconds=sum(r['wall_seconds'] for r in receipts),maximum_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),sources=sources,fresh_structures=len(catalog),byte_identical_inherited_structures=sorted(unchanged),receipts=[{k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']} for r in receipts])
(E/'FGm_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['sources','receipts','byte_identical_inherited_structures']},indent=2))
if '--final' in sys.argv:assert len(receipts)==100 and not missing
