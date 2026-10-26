from pathlib import Path
import json,subprocess,hashlib,re,collections
E=Path(__file__).resolve().parent;R=E.parents[1];P=R/'evidence/replay-dry2-20261026'
g=json.loads((P/'RPz_source-plan.json').read_text());s=json.loads((P/'RPz_state.json').read_text())['state'];pins=json.loads((E/'RPz2_inherited-source-manifest.json').read_text())['modules'];recover={x['module']:x['source_pin'] for x in json.loads((P/'RPz_source-recovery.json').read_text())};idx=collections.defaultdict(list)
for p in subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines():idx[Path(p).name].append(p)
h=lambda b:hashlib.sha256(b).hexdigest();new=[];active=set()
def strip(t):
 return re.sub(r'/\-.*?\-/|--[^\n]*',' ',t,flags=re.S)
def visit(m):
 if m in active:raise Exception('cycle '+m)
 x=g['modules'].get(m,{})
 if x.get('kind') in ['repository','trusted-library']:return
 if m.split('.')[0] in {'Init','Lean','Std','Lake','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}:g['modules'][m]={'kind':'trusted-library'};return
 pin=recover.get(m) or pins.get(m,{}).get('source_pin');data=None;path=None
 if pin:
  data=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']]);assert h(data)==pin['sha256'];path=pin['path']
 else:
  suffix=m.replace('.','/')+'.lean';cs=[p for p in idx[Path(suffix).name] if p==suffix or p.endswith('/'+suffix)]
  can=[p for p in ['lean/'+suffix,'docs/research/100bit-spend-path-20261013/lean/'+suffix] if p in cs]
  if can:path=can[0]
  elif len({h((R/p).read_bytes()) for p in cs})==1 and cs:path=cs[0]
  if path:data=(R/path).read_bytes()
 if data is None:return
 active.add(m);t=strip(data.decode());imports=[] if re.search(r'^\s*prelude\b',t,re.M) else ['Init']
 for line in t.splitlines():
  z=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if z:imports += [n for n in re.findall(r'[A-Za-z_][\w.]*',z[1]) if n!='all']
 imports=list(dict.fromkeys(imports))
 for n in imports:visit(n)
 out=E/'RPz2_recovered'/Path(m.replace('.','/')+'.lean');out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
 g['modules'][m]={'kind':'repository','source':path,'sha256':h(data),'bytes':len(data),'imports':imports,'recovery_pin':pin,'snapshot':str(out.relative_to(R))};new.append(m);active.remove(m)
for m in list(g['modules']):visit(m)
# Re-traverse all actual imports; longest remaining path to target gets priority.
order=[];seen=set();distance={};chain={}
def walk(m):
 if m in seen:return
 seen.add(m);x=g['modules'].get(m,{})
 if x.get('kind')!='repository':return
 for n in x['imports']:walk(n)
 order.append(m)
walk('Rc7_Top')
def dist(m,d):
 if distance.get(m,-1)>=d:return
 distance[m]=d
 for n in g['modules'].get(m,{}).get('imports',[]):dist(n,d+1)
dist('Rc7_Top',0)
# The longest dependency chain with already passed/trusted vertices costing zero.
def cost(m):
 if m in chain:return chain[m][0]
 x=g['modules'].get(m,{})
 if x.get('kind')!='repository' or s.get(m)=='passed':chain[m]=(0,None);return 0
 ns=x['imports'];n=max(ns,key=cost) if ns else None;chain[m]=(1+(cost(n) if n else 0),n);return chain[m][0]
cost('Rc7_Top');critical=[];m='Rc7_Top'
while m:critical.append(m);m=chain.get(m,(0,None))[1]
g.update(order=order,recovered=new,continuation_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),distance_to_top=distance,critical_path=critical,critical_path_remaining_weight=chain['Rc7_Top'][0]);g['unresolved']=[m for m in seen if g['modules'].get(m,{}).get('kind')!='repository' and g['modules'].get(m,{}).get('kind')!='trusted-library']
(E/'RPz2_source-plan.json').write_text(json.dumps(g,indent=2)+'\n')
ready=[m for m in order if m not in s or s[m]=='blocked' if all(g['modules'].get(n,{}).get('kind')=='trusted-library' or s.get(n)=='passed' for n in g['modules'][m]['imports'])]
print('recovered',len(new),'selected',len(order),'unresolved',len(g['unresolved']),'ready',ready,'critical length',chain['Rc7_Top'][0]);print('critical',critical)
