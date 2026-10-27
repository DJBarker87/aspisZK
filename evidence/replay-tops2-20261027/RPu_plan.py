from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=R/'evidence/replay-tops1-20261027'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=load(P/'RPt_plan.json');green={d['module'] for f in P.glob('RPt_*/receipt.json') if (d:=load(f))['exit_status']==0}
mapping={k:v for k,v in p['mapping'].items() if not v.startswith('RPt_') or v in green}
base=load(R/'evidence/replay-dry6-20261026/RPz5_source-plan.json')['modules'];reverse={v:k for k,v in p['mapping'].items()}
for n,x in base.items():x['imports']=[reverse.get(i,i) for i in x.get('imports',[])]
for r in p['rows']:base[r['original']]={'kind':'repository','source':r['original_source'],'imports':r['original_imports']}
for fn in ['RPz8_plan.json','RPz8_ARX-plan.json']:
 for row in load(R/'evidence/replay-dry9-20261027'/fn)['rows']:
  base[row['original']]={'kind':'repository','source':row.get('original_source',row['source']),'imports':[reverse.get(i,i) for i in row['imports']]}
files=subprocess.check_output(['rg','--files','-g','*.lean','-g','!evidence/**'],cwd=R,text=True).splitlines()
new={};order=[];unresolved=[]
def visit(n):
 if n in mapping or base.get(n,{}).get('kind')=='trusted-library' or n.startswith('Mathlib.') or (n=='Aeneas' or n.startswith('Aeneas.')):return
 if n in new:return
 path=R/base[n]['source'] if n in base else R/'lean'/(n.replace('.','/')+'.lean')
 if not path.is_file():
  candidates=[R/f for f in files if '/evidence/' not in f and (f.endswith('/'+n.replace('.','/')+'.lean') or f==n.replace('.','/')+'.lean')]
  if len(candidates)!=1:unresolved.append([n,[str(q.relative_to(R)) for q in candidates]]);return
  path=candidates[0]
 imports=['Init']
 for line in path.read_text().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 new[n]={'original':n,'module':'RPu_'+n.replace('.','_'),'original_source':str(path.relative_to(R)),'original_sha256':sha(path),'original_imports':imports}
 base[n]={'kind':'repository','source':str(path.relative_to(R)),'imports':imports}
 for i in imports:visit(i)
 order.append(n)
roots=['FJp_Top','FJu_Top','FJv_Top','FJv_Deployed']
for n in roots:visit(n)
assert not unresolved,unresolved
mapping.update({n:r['module'] for n,r in new.items()})
for n in order:
 row=new[n];old=(R/row['original_source']).read_text();text=re.sub(r'^import (.*)$',lambda m:'import '+' '.join(mapping.get(i,i) for i in m[1].split()),old,flags=re.M)
 dst=E/(row['module']+'.lean');dst.write_text(text)
 assert re.sub(r'^import .*\n','',old,flags=re.M)==re.sub(r'^import .*\n','',text,flags=re.M)
 row.update(source=str(dst.relative_to(R)),sha256=sha(dst),imports=[mapping.get(i,i) for i in row['original_imports']])
def closure(n):
 seen=set()
 def go(m):
  if m in seen or base.get(m,{}).get('kind')=='trusted-library':return
  seen.add(m)
  for i in base.get(m,{}).get('imports',[]):go(i)
 go(n);return sorted(seen)
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'roots':roots,'rows':[new[n] for n in order],'mapping':mapping,'closures':{n:closure(n) for n in roots},'new_modules':len(new),'unresolved':unresolved,'limit':500}
(E/'RPu_plan.json').write_text(json.dumps(out,indent=2)+'\n')
pins=[]
for name in ['RPt_HANDOFF.md','RPt_plan.json','RPt_frontier.json','RPt_retained-object-pins.json','RPt_toolchain-pins.json','RPt_inherited-pins.json','RPt_final-verification.json']:
 f=P/name;pins.append({'path':str(f.relative_to(R)),'sha256':sha(f),'bytes':f.stat().st_size})
(E/'RPu_inherited-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print('sources',len(new),'closures',{k:len(v) for k,v in out['closures'].items()})
