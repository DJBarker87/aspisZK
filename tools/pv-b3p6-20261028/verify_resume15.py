from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume15';rows=json.loads((O/'receipt-index.json').read_text());errors=[]
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rows:
 p=O/r['receipt'];x=json.loads(p.read_text());base=p.parent.parent
 if not 70100<=r['attempt']<=70199:errors.append(['id',r['attempt']])
 if hashlib.sha256((base/'source.lean').read_bytes()).hexdigest()!=r['source_sha256']:errors.append(['source_snapshot',r['attempt']])
 if x.get('limits')!=expected:errors.append(['limits',r['attempt'],x.get('limits')])
 if r['swaps']!=0:errors.append(['swap',r['attempt']])
 if not (0<r['peak_rss_kib']<8*1024*1024):errors.append(['rss',r['attempt']])
 for gate in ['reservation.json','barrier.json']:
  if json.loads((base/gate).read_text()).get('allowed')is not True:errors.append(['admission',r['attempt'],gate])
 if not r['lean_source_revision']:errors.append(['revision',r['attempt']])
 if r['exit']==0:
  for line in r['print_axioms']:
   match=re.search(r'depends on axioms:\s*\[([^\]]*)\]',line)
   if match:
    names={n.strip()for n in match[1].split(',')if n.strip()}
    if not names<= {'propext','Classical.choice','Quot.sound'}:errors.append(['axioms',r['attempt'],line])
# Verify the actual no-repeat invariant across this round's charged attempts.
failed={}
for r in sorted(rows,key=lambda r:r['attempt']):
 if r['source_sha256']in failed:errors.append(['unchanged_failed_source',failed[r['source_sha256']],r['attempt']])
 if r['exit']!=0:failed[r['source_sha256']]=r['attempt']
ids=[r['attempt']for r in rows]
if len(ids)!=len(set(ids)):errors.append(['duplicate_ids'])
if len(rows)!=100:errors.append(['attempt_count',len(rows)])
audits=[r for r in rows if r['attempt']>=70197]
if [r['attempt']for r in sorted(audits,key=lambda r:r['attempt'])]!=[70197,70198,70199]:errors.append(['audit_ids'])
if any(r['exit']!=0 for r in audits):errors.append(['audit_failure'])
changed=subprocess.check_output(['git','diff','--name-only','15819d2768','--'],text=True).splitlines()
if any(not(p.startswith('tools/pv-b3p6-20261028/')or p.startswith('evidence/pv-b3p6-20261028/'))for p in changed):errors.append(['scope',changed])
if any('PV_B3Q_'in p for p in changed):errors.append(['peer_source_edited'])
large=[str(p)for p in O.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024]
if large:errors.append(['large_files',large])
state=json.loads((O/'TALLY-resume15.json').read_text())
x=dict(entry_revision='15819d2768e2ed80a614edae6aa5d7dcb9055e84',branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),lean_attempts=len(rows),pass_count=sum(r['exit']==0 for r in rows),reject_count=sum(r['exit']!=0 for r in rows),native_scopes=0,kani_runs=0,audits=audits,guard_sha256=hashlib.sha256(Path('tools/pv-b3p6-20261028/compile_resume15.py').read_bytes()).hexdigest(),unchanged_failed_source_retries=0,environment_failure_exceptions_used=0,refusals=len(state.get('refusals',[])),void_attempts=[],errors=errors,native_associations_new=0,endpoint_premises_removed=0,trust_fields_unchanged=['entropy_law','entropy_kernel','observation'],compiler_boundary_retained='V370 / pending owner D381,D386')
(O/'verification-summary.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['lean_attempts','pass_count','reject_count','refusals','errors']}));assert not errors,errors
