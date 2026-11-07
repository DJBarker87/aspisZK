from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent
selected={}
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 if int(f.parent.name[-3:])<666:continue
 d=json.loads(f.read_text());m=d.get('module','');src=E/'NNG_generated'/(m+'.lean');snap=f.parent/'sources'/'NNG_generated'/(m+'.lean')
 if d.get('kind')=='lean' and d.get('exit_status')==0 and src.is_file() and snap.is_file() and src.read_bytes()==snap.read_bytes():selected[m]=f
assert 'NNG_ConcreteCalls094' in selected
roots=[]
for m,f in selected.items():
 log=(f.parent/'stdout.log').read_text();assert 'sorryAx' not in log,m
 roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",log)
roots=sorted(set(roots));assert len(roots)>20
prefix='NNG_F9094_';groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/'NNG_F9094_COMBINED.lean').write_text('import NMQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in sorted(selected)))
(E/'NNG_generated/NNG_F9094_COMBINED.lean').write_text((E/'NNG_F9094_COMBINED.lean').read_text())
(E/(prefix+'AUDIT_ROOTS.json')).write_text(json.dumps(dict(roots=roots,groups=groups,selected_receipts={m:str(f.relative_to(E))for m,f in selected.items()},prior_roots_excluded=True),indent=1))
(E/(prefix+'AUDIT_MODULES.json')).write_text(json.dumps([['NNG_F9094_COMBINED']]*len(groups)))
a=(E/'NNG_S094_ProofDriver.lean').read_text();b=a.replace('NNG_S094_',prefix)
(E/(prefix+'ProofDriver.lean')).write_text(b);(E/'NNG_generated'/(prefix+'ProofDriver.lean')).write_text(b)
(E/(prefix+'DRIVER.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True))))
for name in ['link.py','audit_batch.py']:(E/(prefix+name)).write_text((E/('NNG_S094_'+name)).read_text().replace('NNG_S094_',prefix))
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in [prefix+'AUDIT_ROOTS.json',prefix+'AUDIT_MODULES.json','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']}
(E/(prefix+'AUDIT_MANIFEST_PINS.json')).write_text(json.dumps(pins,indent=1))
x=json.loads((E/'NNG_L666.json').read_text());base={k:v for k,v in x.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
x=json.loads(json.dumps(base));x.update(attempt='NNG_L686',module='NNG_F9094_COMBINED',sources=['NNG_generated/NNG_F9094_COMBINED.lean']);x['command']=[v.replace('NNG_TotalParse094','NNG_F9094_COMBINED')for v in x['command']];(E/'NNG_L686.json').write_text(json.dumps(x))
for old,new in [('NNG_L360','NNG_L687'),('NNG_L361','NNG_L688')]+[('NNG_L362',f'NNG_L{689+i}')for i in range(len(groups))]:
 x=json.loads((E/(old+'.json')).read_text());x={k:v for k,v in x.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 def convert(v):
  if isinstance(v,str):return v.replace('NNG_C136_',prefix).replace('NNG_CANDIDATE_COMBINED','NNG_F9094_COMBINED')
  if isinstance(v,list):return[convert(a)for a in v]
  if isinstance(v,dict):return{k:convert(a)for k,a in v.items()}
  return v
 x=convert(x);x['attempt']=new;x['env']=base['env']
 if old=='NNG_L362':
  i=int(new[-3:])-689;x.update(module=f'F9 continuation raw ax2 proof{i}',command=['python3',prefix+'audit_batch.py',f'proof{i}'],collect_globs=[prefix+f'audit/proof{i}/*'])
 (E/(new+'.json')).write_text(json.dumps(x))
print(json.dumps(dict(modules=len(selected),roots=len(roots),groups=len(groups))))
