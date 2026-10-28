from pathlib import Path
import re,json,hashlib,subprocess,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028')
T=D/'client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pattern=re.compile(r'(?:String::(?:with_capacity|reserve_exact)|Path::(?:join|_join)|PathBuf::(?:push|_push))')
candidates=[];pins=[]
for p in sorted(T.glob('*.mir')):
 pins.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 fn='';body=[];hits=[];start=0
 with p.open() as f:
  for n,line in enumerate(f,1):
   if line.startswith('fn '):fn=line.rstrip();start=n;body=[];hits=[]
   if fn:
    body.append(line)
    if pattern.search(line) and not line.lstrip().startswith('// + const_'):
     hits.append(dict(line=n,text=line.rstrip()))
    if line=='}\n':
     if hits:
      idx=len(candidates);out=D/'mir-sites'/f'{idx:04}.mir.xz';out.parent.mkdir(exist_ok=True)
      out.write_bytes(lzma.compress(''.join(body).encode(),preset=6))
      candidates.append(dict(id=idx,mir=str(p),function=fn,start=start,hits=hits,body_sha256=hashlib.sha256(''.join(body).encode()).hexdigest(),body=f'mir-sites/{idx:04}.mir.xz'))
     fn=''
(D/'mir-candidates.json').write_text(json.dumps(candidates,indent=2)+'\n')
# The complete per-crate optimized IR graph includes references via vtables and
# globals. It is a conservative syntactic graph, NOT a resolved indirect graph.
name={};graph={};targetcalls=[];indirect=[];definitions=set();pinsll=[]
sym=r'@("[^"\n]+"|[-A-Za-z$._0-9]+)'
for p in sorted(T.glob('*.ll')):
 pinsll.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 current=None;comment=''
 with p.open() as f:
  for n,line in enumerate(f,1):
   if line.startswith('; ') and not line.startswith('; Function Attrs'):comment=line[2:].strip()
   if line.startswith(('define ','declare ')):
    m=re.search(sym+r'\(',line)
    if m:
     s=m.group(1).strip('"');name.setdefault(s,comment)
     if line.startswith('define '):current=s;definitions.add(s);graph.setdefault(s,set())
   elif line.startswith('@'):
    ss=re.findall(sym,line)
    if ss:graph.setdefault(ss[0].strip('"'),set()).update(x.strip('"') for x in ss[1:])
   if current:
    refs=set(x.strip('"') for x in re.findall(sym,line));refs.discard(current)
    graph[current].update(refs)
    if re.search(r'\b(call|invoke)\b',line) and not refs:
     indirect.append(dict(caller=current,file=str(p),line=n,text=line.strip()))
    if line.startswith('}'):current=None
roots=[s for s,v in name.items() if v=='devnet_spend::main']
reach=set(roots);queue=list(roots)
while queue:
 s=queue.pop()
 for x in graph.get(s,[]):
  if x not in reach:reach.add(x);queue.append(x)
for s,refs in graph.items():
 for t in refs:
  if pattern.search(name.get(t,'')):
   targetcalls.append(dict(caller=s,caller_name=name.get(s),target=t,target_name=name.get(t),direct_graph_reachable=s in reach))
# Record every unresolved declaration and indirect edge instead of silently
# treating it as unreachable. Precompiled sysroot bodies are a separate cone.
missing=[dict(symbol=s,name=name.get(s)) for s in sorted(reach) if s not in definitions and s not in graph and not s.startswith(('llvm.','anon.'))]
result=dict(roots=[dict(symbol=s,name=name.get(s)) for s in roots],defined_functions=len(definitions),reachable_symbols=len(reach),direct_target_calls=targetcalls,unresolved_reachable=missing,indirect_calls=[x for x in indirect if x['caller'] in reach],complete=False,limitation='Unresolved indirect dispatch and precompiled sysroot bodies prevent an exhaustive reachable-call certificate. MIR candidates include uninstantiated/unreachable generic functions; they are not all reachable.')
(D/'ir-reachability.json').write_text(json.dumps(result,indent=2)+'\n')
with lzma.open(D/'ir-graph.json.xz','wt') as f:json.dump(dict(names=name,edges={k:sorted(v) for k,v in graph.items()},reachable=sorted(reach)),f)
(D/'ir-mir-pins.json').write_text(json.dumps(dict(mir=pins,llvm=pinsll),indent=2)+'\n')
print(json.dumps(dict(mir_candidates=len(candidates),llvm_definitions=len(definitions),roots=result['roots'],reachable=len(reach),direct_target_calls=len(targetcalls),unresolved=len(missing),indirect=len(result['indirect_calls']))))
