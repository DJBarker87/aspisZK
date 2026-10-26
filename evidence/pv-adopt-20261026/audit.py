#!/usr/bin/env python3
"""Git-object-only adoption audit; no checkout, build, or ref updates."""
import subprocess,json,pathlib,re,hashlib,datetime
OUT=pathlib.Path(__file__).resolve().parent
PINS=json.loads((OUT/'revisions.json').read_text()); C=PINS['codex/pv-adopt-20261026']; ROOT='docs/research/v8-r0-zk-20261009/lean/'
def git(*a,check=True):
 p=subprocess.run(['git',*a],capture_output=True,text=True)
 if check and p.returncode: raise RuntimeError(p.stderr)
 return p

def save(n,x): (OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sources(rev):
 lines=git('ls-tree','-r',rev,'--',ROOT).stdout.splitlines(); objs=[]
 for l in lines:
  meta,path=l.split('\t',1)
  if path.endswith('.lean'): objs.append((path,meta.split()[2]))
 p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 result={}
 # communicate batches via one process without pipe deadlock
 for path,oid in objs:
  p.stdin.write((oid+'\n').encode());p.stdin.flush();h=p.stdout.readline().decode().split(); b=p.stdout.read(int(h[2]));p.stdout.read(1); result[path]=b.decode()
 p.stdin.close();p.wait();return result
refs=list(PINS); siblings=refs[2:7]
merges=[]
for ref in siblings+['research']:
 p=git('merge-tree','--write-tree','--name-only',C,PINS[ref],check=False); lines=p.stdout.splitlines(); conflicts=[]
 if p.returncode==1:
  for l in lines[1:]:
   if not l: break
   conflicts.append(l)
 merges.append(dict(ref=ref,head=PINS[ref],command=['git','merge-tree','--write-tree','--name-only',C,PINS[ref]],exit=p.returncode,tree=lines[0] if lines else None,conflicting_paths=conflicts,stdout=p.stdout,stderr=p.stderr))
save('merges.json',merges)
drift=[]
for l in git('diff','--name-status','--no-renames','3f9177b647',PINS['research'],'--','crates/','programs/').stdout.splitlines():
 status,path=l.split('\t');drift.append(dict(status=status,path=path,invalidates_elf_pin_evidence=True,required='Rebuild all three ELFs and confirm default/devnet/Pool pins; do not reuse historical pins for changed source.'))
save('research-drift.json',dict(base='3f9177b6477a8ae91d028139be2a9c555fc300e7',research=PINS['research'],paths=drift,count=len(drift)))
all_sources={r:sources(PINS[r]) for r in [refs[1],*siblings,'research']}; candidate=all_sources[refs[1]]
mods=lambda ss:{p[len(ROOT):-5].replace('/','.'):(p,s) for p,s in ss.items()}
cm=mods(candidate); graph={m:re.findall(r'^import\s+([^\n]+)',s,re.M) for m,(p,s) in cm.items()}; graph={m:[v for x in xs for v in x.split() if not v.startswith('--')] for m,xs in graph.items()}
seen=set();order=[]
def walk(m):
 if m in seen:return
 seen.add(m)
 for d in graph.get(m,[]):walk(d)
 if m in cm:order.append(m)
walk('R1Z.PrivacyR1HeadlineDeployedReal');closure=set(order)
family=lambda m: m.startswith(('R1Z.PV_','R1Z.PDict_','R1Z.ProverRw'))
# Shortest headline import paths, explicitly null when not imported.
def route(target):
 q=[['R1Z.PrivacyR1HeadlineDeployedReal']];v=set()
 for path in q:
  m=path[-1]
  if m==target:return path
  if m in v:continue
  v.add(m);q.extend(path+[x] for x in graph.get(m,[]) if x in cm)
 return None
inventory=[]
for ref in [*siblings,'research']:
 for m,(path,s) in mods(all_sources[ref]).items():
  if family(m):inventory.append(dict(ref=ref,module=m,path=path,in_candidate=m in cm,in_headline_import_closure=m in closure,blob_sha256=hashlib.sha256(s.encode()).hexdigest()))
missing=sorted({i['module'] for i in inventory if not i['in_headline_import_closure']})
save('closure.json',dict(candidate=C,root='R1Z.PrivacyR1HeadlineDeployedReal',theorem='R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed',topological_modules=order,external_imports=sorted(seen-set(cm)),edges={m:graph[m] for m in order},headline_family_modules=sorted(m for m in closure if family(m)),routes={m:route(m) for m in ['R1Z.ProverRwFull','R1Z.ProverRwP6BodyData',*sorted(m for m in closure if family(m))]},inventory=inventory,unimported_modules=missing,unimported_count=len(missing)))
# Lexical namespaces: strip nested block/line comments, track section/end, retain namespace stack.
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:
   if s[i]=='\n':out.append('\n')
   i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
def declarations(ss):
 out=[]
 for path,s in ss.items():
  m=path[len(ROOT):-5].replace('/','.')
  if not family(m):continue
  ns=[];stack=[]
  for ln,line in enumerate(uncomment(s).splitlines(),1):
   x=re.match(r'^\s*(namespace|section|noncomputable section)\b\s*([^\s]*)',line)
   if x:
    kind,n=x.groups();stack.append((kind,len(ns)))
    if kind=='namespace':ns.extend(n.split('.'))
    continue
   if re.match(r'^\s*end(?:\s|$)',line):
    if stack:kind,k=stack.pop();ns=ns[:k]
    continue
   x=re.match(r'^(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|def|structure)\s+([^\s(:{]+)',line)
   if x:
    kind,name=x.groups()
    if line.startswith('private '):continue
    fqn=name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns+[name])
    out.append(dict(fqn=fqn,kind=kind,path=path,line=ln,module=m,source_line=line,sha256=hashlib.sha256(s.encode()).hexdigest()))
 return out
decls={r:declarations(ss) for r,ss in all_sources.items() if r!='research'}
group={}
for ref,ds in decls.items():
 for d in ds:group.setdefault(d['fqn'],[]).append(dict(ref=ref,**d))
collisions=[];shared=[]
for name,entries in group.items():
 if len({e['ref'] for e in entries})<2:continue
 unique={(e['path'],e['sha256'],e['line']) for e in entries}
 (collisions if len({e['path'] for e in entries})>1 else shared).append(dict(fqn=name,entries=entries,distinct_locations=len(unique)))
save('declarations.json',dict(method='Column-zero theorem/def/structure declarations (also modifiers); nested block comments removed; namespace/section/end tracked; private declarations excluded from public FQN collision set. Same file inherited in multiple histories is shared, not a namespace collision. Different versions at the same file path are merge reconciliation, listed separately.',declarations=decls,collisions=collisions,shared_declarations=shared))
print(json.dumps(dict(merges=[(x['ref'],x['exit'],len(x['conflicting_paths'])) for x in merges],drift=len(drift),closure=len(order),families=len([m for m in closure if family(m)]),unimported=len(missing),collisions=len(collisions)),indent=2))
