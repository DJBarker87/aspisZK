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
 lines=git('ls-tree','-r',rev,'--',ROOT,'docs/research/100bit-spend-path-20261013/lean/','docs/research/v8-r0-sem-proof-20261008/lean/','docs/research/v8-full-view-zk-20260912/lean/').stdout.splitlines(); objs=[]
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
save('candidate-research-net-difference.json',dict(base='3f9177b6477a8ae91d028139be2a9c555fc300e7',research=PINS['research'],paths=drift,count=len(drift)))
control=git('merge-base','3f9177b647',PINS['research']).stdout.strip()
commits=git('log','--format=%H','3f9177b647..'+PINS['research'],'--','crates/','programs/').stdout.splitlines()
newpaths=[]
for l in git('diff','--name-status','--no-renames',control,PINS['research'],'--','crates/','programs/').stdout.splitlines():
 status,path=l.split('\t');newpaths.append(dict(status=status,path=path,invalidates_elf_pin_evidence=True,required='Rebuild default/devnet/Pool and confirm all three pins.'))
save('research-drift.json',dict(candidate_baseline='3f9177b6477a8ae91d028139be2a9c555fc300e7',research_control=control,research=PINS['research'],research_commits_changing_crates_or_programs=commits,paths=newpaths,count=len(newpaths),net_candidate_research_difference_count=len(drift),interpretation='The direct two-tree diff reverses existing candidate-only changes. Research history since the candidate baseline has no such source changes when commits and control-to-research diff are empty.'))
all_sources={r:sources(PINS[r]) for r in [refs[1],*siblings,'research']}; candidate=all_sources[refs[1]]
def mods(ss):
 result={}
 for p,s in ss.items():
  if p.startswith(ROOT):m=p[len(ROOT):-5].replace('/','.')
  elif '/lean/prover-rw-20261023/' in p and pathlib.Path(p).stem.startswith('ProverRwFull'):m='R1Z.'+pathlib.Path(p).stem
  elif '/lean/' in p:m=p.split('/lean/',1)[1][:-5].replace('/','.')
  else:continue
  result[m]=(p,s)
 return result
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
save('closure.json',dict(candidate=C,root='R1Z.PrivacyR1HeadlineDeployedReal',theorem='R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed',topological_modules=order,external_imports=sorted(seen-set(cm)),edges={m:graph[m] for m in order},headline_family_modules=sorted(m for m in closure if family(m)),routes={m:route(m) for m in ['R1Z.ProverRwFull','R1Z.ProverRwP6BodyData',*sorted(m for m in closure if family(m))]},inventory=inventory,unimported_modules=missing,unimported_count=len(missing),unimported_sibling_modules=sorted({i['module'] for i in inventory if i['ref'] in siblings and not i['in_headline_import_closure']}),unimported_sibling_additions=sorted({i['module'] for i in inventory if i['ref'] in siblings and not i['in_candidate']}),research_source_identification=sorted({i['module'] for i in inventory if i['ref']=='research' and i['module'].startswith('R1Z.PV_Src_')})))
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
  m=next((m for m,(p,_) in mods({path:s}).items()),'')
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
# Store compact locations; avoid repeating inherited source text and hashes thousands of times.
index={r:{(d['fqn'],d['path'],d['line']):i for i,d in enumerate(ds)} for r,ds in decls.items()}
def compact_groups(groups):
 return [dict(fqn=g['fqn'],distinct_locations=g['distinct_locations'],entries=[[e['ref'],index[e['ref']][(e['fqn'],e['path'],e['line'])]] for e in g['entries']]) for g in groups]
save('declarations.json',dict(method='Column-zero theorem/def/structure plus modifiers; nested block/line comments removed; namespace/section/end tracked. Private declarations excluded. Entries in duplicate groups are [ref, zero-based declaration index]. Same path inherited in multiple histories is shared, not a public-name collision. Lexical audit only; no Lean elaboration run.',declarations={r:[{k:d[k] for k in ['fqn','kind','module','line']} for d in ds] for r,ds in decls.items()},collisions=compact_groups(collisions),shared_declarations=compact_groups(shared)))
# Independent support roots, deliberately separate from the current headline route.
union=dict(cm);bindings={m:C for m in cm}
for ref in [*siblings,'research']:
 for m,value in mods(all_sources[ref]).items():
  if m not in union:union[m]=value;bindings[m]=PINS[ref]
roots=['R1Z.PrivacyR1HeadlineDeployedReal','R1Z.ProverRwFullFuns','R1Z.ProverRwP6BodyData','R1Z.PV_RW_FrozenManifest',
 'R1Z.PDict_Installed','R1Z.PDict_CarrierInstall','R1Z.PDict_RemainingDictionary231','R1Z.PDict_FormatterClosure262',
 'R1Z.PV_RunJoin_Endpoint','R1Z.PV_RunJoin_SourceConstructor','R1Z.PV_RunJoin_InstalledTransport','R1Z.PV_RunJoin_OsFailureEndpoint','R1Z.PV_RunJoin_PublicFailureEndpoint',
 'R1Z.PV_Src_NativeIdentification','R1Z.PV_Src_NativeConsumer','R1Z.PV_Src_NativePremises']
roots+=sorted(m for m in union if re.match(r'R1Z\.PV_CB_Op[0-9]+Source$',m) or m=='R1Z.PV_CB_TakeSource' or m.startswith('R1Z.PV_CB3_') and m.endswith('Source'))
ug={m:re.findall(r'^import\s+([^\n]+)',s,re.M) for m,(p,s) in union.items()};ug={m:[v for x in xs for v in x.split() if not v.startswith('--')] for m,xs in ug.items()}
us=set();uo=[]
def uwalk(m):
 if m in us:return
 us.add(m)
 for d in ug.get(m,[]):uwalk(d)
 if m in union:uo.append(m)
for m in roots:uwalk(m)
save('support-closure.json',dict(scope='Proposed independent support-root audit, NOT the current endpoint dependency closure and NOT a checked merged tree. Candidate objects take precedence; only missing modules are borrowed from pinned siblings/research. Final integration must regenerate from its single accepted source revision.',roots=roots,modules=[dict(module=m,path=union[m][0],revision=bindings[m],sha256=hashlib.sha256(union[m][1].encode()).hexdigest(),imports=ug[m]) for m in uo],external_imports=sorted(us-set(union)),missing_roots=sorted(set(roots)-set(union))))
save('headline-sources.json',[dict(module=m,path=cm[m][0],revision=C,sha256=hashlib.sha256(cm[m][1].encode()).hexdigest(),imports=graph[m]) for m in order])
print(json.dumps(dict(merges=[(x['ref'],x['exit'],len(x['conflicting_paths'])) for x in merges],research_drift=len(newpaths),net_tree_difference=len(drift),closure=len(order),families=len([m for m in closure if family(m)]),unimported=len(missing),collisions=len(collisions)),indent=2))
