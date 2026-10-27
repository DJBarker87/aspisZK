"""Source invalidation audit only; never compiles or installs shared sources."""
from pathlib import Path
import json,subprocess,hashlib,re
E=Path('evidence/pv-integ1-20261027/d298');HEAD='9ff5a4594e'
def blob(rev,p):
 r=subprocess.run(['git','rev-parse',rev+':'+p],text=True,capture_output=True)
 return r.stdout.strip() if r.returncode==0 else None
old=json.loads(Path('evidence/pv-integ1-20261027/lean-import-audit.json').read_text());rows=[]
for m,r in old['modules'].items():
 if not r.get('resolution'):continue
 p=r['resolution']['path'];before=blob('0c9dc9a4cc',p);after=blob(HEAD,p)
 rows.append(dict(module=m,path=p,base='0c9dc9a4cc',before_blob=before,integrated_blob=after,changed=before!=after,authority=r['resolution']))
for p in sorted(Path('evidence/pv-batch1-20261027/lean').glob('*.lean')):
 before=blob('c9abf274fa',str(p));after=blob(HEAD,str(p))
 rows.append(dict(module=p.stem,path=str(p),base='c9abf274fa',before_blob=before,integrated_blob=after,changed=before!=after,imports=re.findall(r'^import\s+(\S+)',p.read_text(),re.M)))
# Stronger coverage: no existing Lean file in either audited predecessor changed.
changes={base:subprocess.check_output(['git','diff','--name-status','--diff-filter=CDMRTUXB',base,HEAD,'--','*.lean'],text=True) for base in ['0c9dc9a4cc','c9abf274fa']}
changed=[r for r in rows if r['changed']]
report=dict(integrated=HEAD,changed_imported_sources=changed,existing_lean_changes=changes,modules=rows,source_rows=len(rows),recompile_required=bool(changed or any(changes.values())),lean_attempts=0,env_j_used_ids=[],env_j_unused_range=[28000,28099],kani_attempts=0,shared_source_writes=0,reused_op223_receipts=['evidence/pv-integ1-20261027/53906.json','evidence/pv-integ1-20261027/53907.json'],reused_batch_audits=['evidence/pv-batch1-20261027/lean-receipts/53701/receipt.json','evidence/pv-batch1-20261027/lean-receipts/53702/receipt.json','evidence/pv-batch1-20261027/lean-receipts/53703/receipt.json'],accepted_axioms=['propext','Classical.choice','Quot.sound'],scope='source invalidation assessment and historical receipt reuse; no fresh elaboration or coherent deployment closure replay claimed')
(E/'lean-source-assessment.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='modules'},indent=2));assert not report['recompile_required']
