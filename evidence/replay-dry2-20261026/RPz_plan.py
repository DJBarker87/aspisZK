"""Select committed repository sources and derive their actual import closure."""
from pathlib import Path
import json,subprocess,hashlib,re,collections
E=Path(__file__).resolve().parent; R=E.parents[1]
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
old=json.loads((R/'evidence/replay-dry-20261026/RPy_graph.json').read_text())['modules']
rc=json.loads((R/'evidence/recount7-20261026/Rc7_selected_closure.json').read_text())
paths=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();idx=collections.defaultdict(list)
for p in paths:idx[Path(p).name].append(p)
sha=lambda b:hashlib.sha256(b).hexdigest()
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
mods={};order=[];active=set();errors=[]
def visit(m):
 if m in mods:return
 if m in active:raise ValueError('cycle '+m)
 active.add(m)
 if m.split('.')[0] in {'Init','Lean','Std','Lake','Mathlib','Aeneas','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}:
  mods[m]={'kind':'trusted-library'};active.remove(m);return
 suffix=m.replace('.','/')+'.lean'
 cand=[p for p in idx[Path(suffix).name] if p==suffix or p.endswith('/'+suffix)]
 canonical=[p for p in ['lean/'+suffix,'docs/research/100bit-spend-path-20261013/lean/'+suffix] if p in cand]
 expected=rc.get(m,{}).get('source',{}).get('sha256') or old.get(m,{}).get('source_sha256')
 matches=[p for p in cand if sha((R/p).read_bytes())==expected]
 choices=matches or canonical
 if not choices and len({sha((R/p).read_bytes()) for p in cand})==1:choices=cand
 if not choices:
  errors.append({'module':m,'candidates':cand,'expected_sha256':expected});mods[m]={'kind':'unresolved'};active.remove(m);return
 p=choices[0];data=(R/p).read_bytes();s=uncomment(data.decode())
 imports=[] if re.search(r'^\s*prelude\b',s,re.M) else ['Init']
 for line in s.splitlines():
  hit=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if hit:imports.extend(n for n in re.findall(r'[A-Za-z_][\w.]*',hit[1]) if n!='all')
 imports=list(dict.fromkeys(imports))
 for n in imports:visit(n)
 mods[m]={'kind':'repository','source':p,'sha256':sha(data),'bytes':len(data),'imports':imports,'historical_source_match':expected==sha(data) if expected else None}
 active.remove(m);order.append(m)
visit('Rc7_Top')
(E/'RPz_source-plan.json').write_text(json.dumps(dict(revision=rev,target='AspisR1.Rc7_Top.deployed',order=order,modules=mods,unresolved=errors),indent=2)+'\n')
print('repository',len(order),'trusted direct imports',sum(x['kind']=='trusted-library' for x in mods.values()),'unresolved',len(errors));print(json.dumps(errors)[:3000]);print(order[:15])
