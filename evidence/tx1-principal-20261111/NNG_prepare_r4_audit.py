"""Prepare only new revision4 own roots, with retained raw controls reused."""
from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent
selected={}
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 if int(f.parent.name[-3:])<801:continue
 d=json.loads(f.read_text());m=d.get('module','');src=E/'NNG_generated'/(m+'.lean');snap=f.parent/'sources'/'NNG_generated'/(m+'.lean')
 if d.get('kind')=='lean' and d.get('exit_status')==0 and src.is_file() and snap.is_file() and src.read_bytes()==snap.read_bytes():selected[m]=f
assert 'NNG_Candidate094' in selected
roots=[]
for m,f in selected.items():
 log=(f.parent/'stdout.log').read_text();assert 'sorryAx' not in log,m
 roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",log)
roots=sorted(set(roots));assert 'AspisR1.NNG_Candidate094.candidate' in roots
prefix='NNG_R4094_';groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/(prefix+'COMBINED.lean')).write_text('import NMQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in sorted(selected)))
(E/(prefix+'AUDIT_ROOTS.json')).write_text(json.dumps(dict(roots=roots,groups=groups,selected_receipts={m:str(f.relative_to(E))for m,f in selected.items()},prior_roots_excluded=True,controls='Reuse unchanged passing L363 raw walker controls; no collector/walker change'),indent=1))
(E/(prefix+'AUDIT_MODULES.json')).write_text(json.dumps([[prefix+'COMBINED']]*len(groups)))
a=(E/'NNG_F9094_ProofDriver.lean').read_text();b=a.replace('NNG_F9094_',prefix)
(E/(prefix+'ProofDriver.lean')).write_text(b)
(E/(prefix+'DRIVER.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True))))
for name in ['link.py','audit_batch.py']:(E/(prefix+name)).write_text((E/('NNG_F9094_'+name)).read_text().replace('NNG_F9094_',prefix))
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in [prefix+'AUDIT_ROOTS.json',prefix+'AUDIT_MODULES.json','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']}
(E/(prefix+'AUDIT_MANIFEST_PINS.json')).write_text(json.dumps(pins,indent=1))
env=json.loads((E/'NNG_REV4_ENV.json').read_text())
for old,new in [('NNG_L687','NNG_L961'),('NNG_L688','NNG_L962')]+[('NNG_L689',f'NNG_L{963+i}')for i in range(len(groups))]:
 x=json.loads((E/(old+'.json')).read_text());x={k:v for k,v in x.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 def convert(v):
  if isinstance(v,str):return v.replace('NNG_F9094_',prefix)
  if isinstance(v,list):return[convert(a)for a in v]
  if isinstance(v,dict):return{k:convert(a)for k,a in v.items()}
  return v
 x=convert(x);x['attempt']=new;x['env']=env
 if old=='NNG_L687':
  x['command']=[v.replace('NNG_objects/','NNG_R4_objects/')for v in x['command']]
  src=E/'NNG_generated'/(prefix+'ProofDriver.lean');src.write_text(b)
 if old=='NNG_L689':
  i=int(new[-3:])-963;x.update(module=f'Revision4 own roots raw ax2 proof{i}',command=['python3',prefix+'audit_batch.py',f'proof{i}'],collect_globs=[prefix+f'audit/proof{i}/*'])
 (E/(new+'.json')).write_text(json.dumps(x))
print(json.dumps(dict(modules=len(selected),roots=len(roots),groups=len(groups))))
