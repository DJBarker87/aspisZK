"""Read committed sources only; compute Rc7_Top's transitive import graph."""
from pathlib import Path
import subprocess,json,hashlib,collections,re
E=Path(__file__).resolve().parent; R=E.parents[1]
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
old=json.loads((R/'evidence/replay-dry3-20261026/RPz2_source-plan.json').read_text())
files=subprocess.check_output(['git','ls-tree','-r','--name-only',rev],text=True).splitlines()
idx=collections.defaultdict(list)
for p in files:
 if p.endswith('.lean'):idx[Path(p).name].append(p)
h=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return (R/p).read_bytes() # clean tracked inputs verified below against git blob
blobs=dict(line.split(None,3)[2:4] for line in subprocess.check_output(['git','ls-tree','-r',rev],text=True).splitlines()) if False else {}
# Git blob identifiers validate working-tree bytes against this exact revision.
for line in subprocess.check_output(['git','ls-tree','-r',rev],text=True).splitlines():
 meta,p=line.split('\t',1);blobs[p]=meta.split()[2]
def checked(p):
 b=read(p);assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blobs[p],p;return b
# Nested Lean comments must not introduce fictitious import lines.
def strip(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
trusted={'Init','Lean','Std','Lake','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}
mods={};order=[];active=set();selections={}
def visit(m):
 if m in active:raise ValueError('cycle '+m)
 if m in mods:return
 if m.split('.')[0] in trusted:mods[m]={'kind':'trusted-library'};return
 suffix=m.replace('.','/')+'.lean';cs=[p for p in idx[Path(suffix).name] if p==suffix or p.endswith('/'+suffix)]
 if not cs and m.rsplit('.',1)[-1] not in {'Funs','Types','FunsExternal','TypesExternal','Basic','Impl','Equiv','Degree','Proofs','Modular'}:
  cs=idx[Path(suffix).name][:] # committed flat source snapshots may retain a qualified import name
 canonical=[p for p in ['lean/'+suffix,'docs/research/100bit-spend-path-20261013/lean/'+suffix,'docs/research/v8-full-view-zk-20260912/lean/'+suffix,'docs/research/v8-r0-zk-20261009/lean/'+suffix] if p in cs]
 prior=old['modules'].get(m,{})
 if canonical:p=canonical[0];why='committed canonical research source'
 elif prior.get('kind')=='repository':
  p=prior.get('snapshot',prior['source']);why='committed predecessor selection'
  assert p in blobs,(m,p)
 else:
  # Exclude explicitly rejected/diagnostic variants, never silently pick a different proof.
  main=[p for p in cs if not any(s in p.lower() for s in ['/diagnostics/','/rejected','/attempt-','/worker-archive','/original-worker','/cache/','/remote-evidence/'])]
  groups=collections.defaultdict(list)
  for p in main or cs:groups[h(checked(p))].append(p)
  selections[m]={'all_candidates':cs,'non_diagnostic_candidates':main,'distinct_non_diagnostic_hashes':{k:v for k,v in groups.items()}}
  if len(groups)!=1:
   variants=main or cs
   normalized={re.sub(r'\s+',' ',re.sub(r'^\s*set_option (?:maxHeartbeats|maxRecDepth) [^\n]*','',strip(checked(f).decode()),flags=re.M)).strip() for f in variants}
   no_override=[f for f in variants if not re.search(r'^\s*set_option (?:maxHeartbeats|maxRecDepth) ',checked(f).decode(),re.M)]
   if variants and len(normalized)==1 and no_override:
    p=no_override[0];why='committed research variant with identical declarations and no heartbeat/depth overrides'
    selections[m]['option_only_variants']=True
   else:
    mods[m]={'kind':'unresolved','reason':'no committed source' if not cs else 'genuine source ambiguity','candidates':cs};return
  else:p=next(iter(groups.values()))[0];why='unique committed research content after explicit diagnostic exclusion'
 data=checked(p);s=strip(data.decode());imports=[] if re.search(r'^\s*prelude\b',s,re.M) else ['Init']
 for line in s.splitlines():
  z=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if z:imports += [n for n in re.findall(r'[A-Za-z_][\w.]*',z[1]) if n!='all']
 imports=list(dict.fromkeys(imports));active.add(m)
 for n in imports:visit(n)
 active.remove(m);mods[m]={'kind':'repository','source':p,'sha256':h(data),'bytes':len(data),'imports':imports,'selection':why,'changed_from_predecessor':prior.get('sha256')!=h(data)};order.append(m)
visit('Rc7_Top')
D={}
def dist(m,d):
 if D.get(m,-1)>=d:return
 D[m]=d
 for n in mods[m].get('imports',[]):dist(n,d+1)
dist('Rc7_Top',0)
out={'revision':rev,'target':'AspisR1.Rc7_Top.deployed','root':'lean/Rc7_Top.lean','modules':mods,'order':order,'distance_to_top':D,'unresolved':sorted(m for m,x in mods.items() if x['kind']=='unresolved'),'selections':selections,'predecessor_unresolved_resolution':{m:mods.get(m,{'kind':'out-of-scope'}) for m in old['unresolved']}}
(E/'RPz3_source-plan.json').write_text(json.dumps(out,indent=2)+'\n')
print('REPOSITORY CLOSURE',len(order),'TRUSTED DIRECT IMPORTS',sum(x['kind']=='trusted-library' for x in mods.values()),'UNRESOLVED',len(out['unresolved']))
print('changed',[(m,mods[m]['selection']) for m in order if mods[m]['changed_from_predecessor']]);print('unresolved',out['unresolved'])
