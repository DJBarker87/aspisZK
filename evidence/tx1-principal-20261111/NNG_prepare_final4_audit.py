"""Select source-matched NEW own roots only; isolate raw groups to at most twelve roots."""
from pathlib import Path
import re,json,hashlib,difflib,sys
E=Path(__file__).resolve().parent
old=set()
for p in E.glob('NNG_*AUDIT_ROOTS.json'):
 if 'R4Final_' not in p.name:
  d=json.loads(p.read_text());old.update(r for r in d.get('roots',[]) if isinstance(r,str))
selected={}
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 i=int(f.parent.name[-3:])
 if not (750<=i<=800 or 920<=i<=959):continue
 d=json.loads(f.read_text());m=d.get('module','')
 if not m.startswith('NNG_') or m.endswith(('COMBINED','ProofDriver')):continue
 src=E/'NNG_generated'/(m+'.lean');snap=f.parent/'sources'/'NNG_generated'/(m+'.lean')
 if d.get('kind')=='lean' and d.get('exit_status')==0 and src.is_file() and snap.is_file() and src.read_bytes()==snap.read_bytes():selected[m]=f
assert 'NNG_Candidate328' in selected
roots=[]
for m,f in selected.items():
 log=(f.parent/'stdout.log').read_text();assert 'sorryAx' not in log,m
 roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",log)
roots=sorted(set(roots)-old);assert 'AspisR1.NNG_Candidate328.candidate' in roots
prefix='NNG_R4Final_';n=int(sys.argv[1]);assert 1<=n<=len(roots)
groups=[roots[len(roots)*i//n:len(roots)*(i+1)//n]for i in range(n)];assert max(map(len,groups))<=12
(E/(prefix+'COMBINED.lean')).write_text('import NMQ_COMBINED_IMPORT\nimport NNG_Candidate094\n'+''.join('import '+m+'\n'for m in sorted(selected)))
(E/(prefix+'AUDIT_ROOTS.json')).write_text(json.dumps(dict(roots=roots,groups=groups,selected_receipts={m:str(f.relative_to(E))for m,f in selected.items()},prior_roots_excluded=sorted(old),controls='Unchanged passing L363 raw walker controls reused; all roots audited once'),indent=1))
(E/(prefix+'AUDIT_MODULES.json')).write_text(json.dumps([[prefix+'COMBINED']]*len(groups)))
a=(E/'NNG_R4094_ProofDriver.lean').read_text();b=a.replace('NNG_R4094_',prefix)
(E/(prefix+'ProofDriver.lean')).write_text(b)
(E/(prefix+'DRIVER.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True))))
for n in ['link.py','audit_batch.py']:(E/(prefix+n)).write_text((E/('NNG_R4094_'+n)).read_text().replace('NNG_R4094_',prefix))
names=[prefix+'AUDIT_ROOTS.json',prefix+'AUDIT_MODULES.json','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']
(E/(prefix+'AUDIT_MANIFEST_PINS.json')).write_text(json.dumps({n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in names},indent=1))
env=json.loads((E/'NNG_REV4_ENV.json').read_text())
for oldid,newid in [('NNG_L961','NNG_L976'),('NNG_L962','NNG_L977')]+[('NNG_L963',f'NNG_L{978+i}')for i in range(len(groups))]:
 x=json.loads((E/(oldid+'.json')).read_text());x={k:v for k,v in x.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 def conv(v):
  if isinstance(v,str):return v.replace('NNG_R4094_',prefix)
  if isinstance(v,list):return[conv(a)for a in v]
  if isinstance(v,dict):return{k:conv(a)for k,a in v.items()}
  return v
 x=conv(x);x['attempt']=newid;x['env']=env
 if oldid=='NNG_L961':(E/'NNG_generated'/(prefix+'ProofDriver.lean')).write_text(b)
 if oldid=='NNG_L963':
  i=int(newid[-3:])-978;x.update(module=f'Revision4 final NEW own roots raw ax2 proof{i}',command=['python3',prefix+'audit_batch.py',f'proof{i}'],collect_globs=[prefix+f'audit/proof{i}/*'])
 (E/(newid+'.json')).write_text(json.dumps(x))
print(json.dumps(dict(modules=len(selected),roots=len(roots),groups=len(groups))))
