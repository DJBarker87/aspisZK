"""Focused094 support/finding audit; excludes all already audited136/support roots."""
from pathlib import Path
import json,subprocess,sys,shutil
E=Path(__file__).resolve().parent
assert json.loads((E/'NNG_L647/receipt.json').read_text())['exit_status']==0
subprocess.run([sys.executable,str(E/'NNG_prepare094_audit.py')],check=True)
subprocess.run([sys.executable,str(E/'NNG_compile.py'),'NNG_L656','NNG_S094_COMBINED'],check=True)
def execute(old,attempt,prefix='NNG_S094_',extra=None):
 x=json.loads((E/(old+'.json')).read_text())
 for k in ['deps_fingerprint','source_revision','source_tree_dirty']:x.pop(k,None)
 def convert(v):
  if isinstance(v,str):return v.replace('NNG_C136_','NNG_S094_').replace('candidate136','support094')
  if isinstance(v,list):return[convert(a)for a in v]
  if isinstance(v,dict):return{k:convert(a)for k,a in v.items()}
  return v
 x=convert(x);x['attempt']=attempt
 if extra:x.update(extra)
 (E/(attempt+'.json')).write_text(json.dumps(x,indent=1))
 subprocess.run([sys.executable,str(E/'NNG_run.py'),attempt],check=True)
shutil.copyfile(E/'NNG_S094_ProofDriver.lean',E/'NNG_generated/NNG_S094_ProofDriver.lean')
execute('NNG_L360','NNG_L657')
execute('NNG_L361','NNG_L658')
groups=json.loads((E/'NNG_S094_AUDIT_ROOTS.json').read_text())['groups']
for i in range(len(groups)):
 execute('NNG_L362',f'NNG_L{659+i}',extra={'module':f'094 support raw ax2 proof{i}', 'command':['python3','NNG_S094_audit_batch.py',f'proof{i}'],'collect_globs':[f'NNG_S094_audit/proof{i}/*']})
results=[]
for i in range(len(groups)):
 r=json.loads((E/f'NNG_S094_audit/proof{i}/proof{i}.json').read_text());assert r['exit_status']==0
 results+=r['results']
assert {x['root']for x in results}=={x for group in groups for x in group}
standard={'propext','Classical.choice','Quot.sound'}
assert all(x['equal'] and set(x['collect_axioms'])<=standard and set(x['walked_axioms'])<=standard for x in results)
(E/'NNG_S094_AUDIT_SUMMARY.json').write_text(json.dumps({'status':'PASS','roots':len(results),'groups':len(groups),'standard_axioms_only':True,'raw_matches_collector':True,'finding_receipt':'NNG_L659/receipt.json','combined_receipt':'NNG_L656/receipt.json','fixtures_receipt':'NNG_L363/receipt.json (unchanged raw walker semantics; retained)','results':results},indent=1))
print(json.dumps({'status':'PASS','roots':len(results),'groups':len(groups)}))
