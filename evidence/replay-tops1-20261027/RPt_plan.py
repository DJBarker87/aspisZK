from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]; P=R/'evidence/replay-dry9-20261027'
load=lambda p:json.loads(p.read_text())
base=load(R/'evidence/replay-dry6-20261026/RPz5_source-plan.json')['modules']
p7=load(R/'evidence/replay-dry8-20261026/RPz7_plan.json')
mapping={n:n for n in p7['order']};mapping.update(p7['mapping'])
for name in ['RPz8_plan.json','RPz8_ARX-plan.json']:
 for row in load(P/name)['rows']:
  mapping[row['original']]=row['module']
  # Original import graph is recovered from the import-only snapshot.
  base[row['original']]={'kind':'repository','source':row.get('original_source',row['source']),'imports':row['imports']}
reverse={v:k for k,v in mapping.items()}
for n,x in base.items():x['imports']=[reverse.get(i,i) for i in x.get('imports',[])]
new={}; order=[]; unresolved=[]
def visit(n):
 if n in mapping or base.get(n,{}).get("kind")=="trusted-library" or n.startswith("Mathlib.") or n=="Aeneas":return
 if n in new:return
 p=R/'lean'/(n.replace('.','/')+'.lean')
 if not p.is_file():
  candidates=[p for p in R.rglob(n.replace('.','/')+'.lean') if '/evidence/' not in str(p)]
  if len(candidates)!=1:unresolved.append([n,[str(p.relative_to(R)) for p in candidates]]);return
  p=candidates[0]
 text=p.read_text(); imports=['Init']
 for line in text.splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 new[n]={'original':n,'module':'RPt_'+n,'original_source':str(p.relative_to(R)),'original_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'original_imports':imports}
 for i in imports:visit(i)
 order.append(n)
roots=['FJp_Top','FJu_Top','BEn_Top']
for n in ['FJv_Top','FJv_Deployed']:
 if (R/'lean'/(n+'.lean')).exists():roots.append(n)
for n in roots:visit(n)
assert not unresolved,unresolved
mapping.update({n:r['module'] for n,r in new.items()})
for n in order:
 row=new[n];p=R/row['original_source'];text=p.read_text()
 text=re.sub(r'^import (.*)$',lambda m:'import '+' '.join(mapping.get(i,i) for i in m[1].split()),text,flags=re.M)
 dst=E/(row['module']+'.lean');dst.write_text(text)
 row.update(source=str(dst.relative_to(R)),sha256=hashlib.sha256(dst.read_bytes()).hexdigest(),imports=[mapping.get(i,i) for i in row['original_imports']])
 base[n]={'kind':'repository','source':row.get('original_source',row['source']),'imports':row['original_imports']}
def closure(n):
 seen=set()
 def go(m):
  if m in seen:return
  if base.get(m,{}).get('kind')=='trusted-library':return
  seen.add(m)
  for i in base.get(m,{}).get('imports',[]):go(i)
 go(n);return sorted(seen)
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'roots':roots,'rows':[new[n] for n in order],'mapping':mapping,'closures':{n:closure(n) for n in roots},'new_modules':len(new),'reused_cohort_modules':5260,'unresolved':unresolved,'limit':400}
(E/'RPt_plan.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['rows','mapping','closures']});print('closures',{n:len(c) for n,c in out['closures'].items()})
