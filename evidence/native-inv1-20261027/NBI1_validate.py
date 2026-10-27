#!/usr/bin/env python3
"""Independent static checks; deliberately invokes no Rust/Kani/Lean tools."""
import json,hashlib,subprocess,time,resource,sys
from pathlib import Path
O=Path(__file__).parent;started=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
x=json.loads((O/'NBI1_INVENTORY.json').read_text());files=json.loads((O/'NBI1_SOURCE_FILES.json').read_text())
for p,r in files.items():assert sha(Path(p).read_bytes())==r['sha256'] and r['working_copy_matches'],p
byid={f['id']:f for f in x['functions']};assert len(byid)==345
units={u['id']:u for u in x['bridge_units']}
for f in byid.values():
 b=Path(f['file']).read_bytes()
 for kind in ('body','function'):
  start,end=f[kind+'_byte_range'];assert sha(b[start:end])==f[kind+'_sha256'],f['id']
 assert f['bridge_unit'] in units
 for e in f['callees']:
  assert e['resolution']!='unresolved project call',(f['id'],e)
  if not f['closed_leaf_packet']:assert all(t in byid for t in e['targets']),(f['id'],e)
leaves=[f for f in byid.values() if f['closed_leaf_packet']];assert len(leaves)==13
for f in leaves:assert Path('evidence',f['closed_leaf_packet']).is_file()
for u in units.values():
 assert not u['grouped_with'],u['id']
 for d in u['callee_bridges']:assert units[d]['bottom_up_group']<u['bottom_up_group'],(u['id'],d)
C=set(json.loads(Path('evidence/replay-deployed2-20261027/RPx_reachable-constants.json').read_text()))
audit_cache={}
for n,r in x['models'].items():
 assert n in C and r['in_deployed_closure'],n
 assert sha(Path(r['source']).read_bytes())==r['source_sha256'],n
 owner=r['replayed_owner'];assert owner['module']==r['module'],n
 ap=owner['audit']
 if ap not in audit_cache:
  a=json.loads(Path(ap).read_text());rs=a.get('declarations',[])
  if not isinstance(rs,list):rs=a.get('records',[])
  audit_cache[ap]={(v['name'],v['module']) for v in rs if isinstance(v,dict) and 'name' in v and 'module' in v}
 assert (n,r['module']) in audit_cache[ap],n
for r in x['closure_inputs']:assert sha(Path(r['file']).read_bytes())==r['sha256']
assert x['budget_used']=={'Lean':0,'Kani':0,'Rust':0}
subprocess.run(['git','diff','--exit-code',x['frozen_revision'],'--','crates','programs','Cargo.lock'],check=True,stdout=subprocess.PIPE)
# Release names are build labels, not Cargo default feature sets.
plan=json.loads(Path('evidence/sbf-identity-20261024/recapture-plan.json').read_text())['builds']
for p in plan[:2]:
 cmd=p['command'];assert cmd[cmd.index('--features')+1]=='pool-adapter,private-leaf-salts'
for r in x['no_separate_counterpart']:assert not next(f for f in byid.values() if f['row']==r['row'])['cohort_definitions']
ru=resource.getrusage(resource.RUSAGE_SELF)
receipt={'target':'NBI1_INVENTORY.json and NBI1_INVENTORY.md static source/closure inventory','command':['python3',str(O/'NBI1_validate.py')],'exit_status':0,'wall_seconds':time.monotonic()-started,'peak_rss_bytes':ru.ru_maxrss,'swap_count':ru.ru_nswap,'worker_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'frozen_source_revision':x['frozen_revision'],'dirty_scope':'Own evidence files only; exact hashes below','axioms':'N/A: zero new theorem/compile','functions':len(byid),'cohort_names':len(x['models']),'source_files':len(files),'closed_leaves':len(leaves),'units':len(units),'unresolved_project_call_edges':0,'no_separate_counterpart':len(x['no_separate_counterpart']),'build_runs':x['budget_used'],'file_hashes':{str(p):sha(p.read_bytes()) for p in sorted(O.glob('NBI1_*')) if p.suffix in ('.py','.md','.json') and p.name not in ('NBI1_VALIDATE.json','NBI1_AST_INDEX.json','NBI1_COHORT_INDEX.json','NBI1_REACH_DRAFT.json')},'scope':'Static inventory validation only; not a formal/native refinement or release build'}
(O/'NBI1_VALIDATE.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_bytes','swap_count','functions','cohort_names','closed_leaves','units','no_separate_counterpart']}))
