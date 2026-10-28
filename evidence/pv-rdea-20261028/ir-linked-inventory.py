from pathlib import Path
import re,json,subprocess,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');T=D/'client-target/release/deps'
rawsym=r'@("[^"\n]+"|[-A-Za-z$._0-9]+)'
name={};graph={};definitions=set();indirect=[];calls=[]
for p in sorted(T.glob('*.ll')):
 local=set()
 with p.open() as f:
  for line in f:
   if (line.startswith('@') and re.search(r'=\s*(?:private|internal)\b',line)) or re.match(r'^define (?:private|internal)\b',line):
    m=re.search(rawsym,line)
    if m:local.add(m[1].strip('"'))
 def qualify(s):
  s=s.strip('"');return p.name+'::'+s if s in local else s
 current=None;comment=''
 with p.open() as f:
  for n,line in enumerate(f,1):
   if line.startswith('; ') and not line.startswith('; Function Attrs'):comment=line[2:].strip()
   if line.startswith(('define ','declare ')):
    m=re.search(rawsym+r'\(',line)
    if m:
     s=qualify(m[1]);name.setdefault(s,comment)
     if line.startswith('define '):current=s;definitions.add(s);graph.setdefault(s,set())
   elif line.startswith('@'):
    ss=re.findall(rawsym,line)
    if ss:graph.setdefault(qualify(ss[0]),set()).update(qualify(x) for x in ss[1:])
   if current:
    refs={qualify(x) for x in re.findall(rawsym,line)};refs.discard(current);graph[current].update(refs)
    if not line.lstrip().startswith(';') and re.search(r'\b(call|invoke)\b',line):
     m=re.search(r'\b(?:call|invoke)\b[^;]*?'+rawsym+r'\(',line)
     if m:calls.append(dict(caller=current,target=qualify(m[1]),file=p.name,line=n,instruction=line.strip()))
     elif not re.search(r'\basm\b',line):indirect.append(dict(caller=current,file=p.name,line=n,instruction=line.strip()))
    if line.startswith('}'):current=None
roots=[s for s,v in name.items() if v=='devnet_spend::main'];reach=set(roots);queue=list(roots)
while queue:
 for x in graph.get(queue.pop(),[]):
  if x not in reach:reach.add(x);queue.append(x)
linkedraw=subprocess.check_output(['nm','--defined-only',str(D/'client-target/release/devnet_spend')],text=True)
linked={line.split()[-1] for line in linkedraw.splitlines() if len(line.split())>=3}
interesting=re.compile(r'(?:String::(?:with_capacity|reserve_exact)|Path::(?:join|_join)|PathBuf::(?:push|_push)|Itertools.*join|anyhow::ensure::render|aspis_prover::pow)')
selected=[dict(symbol=s,name=v,direct_graph_reachable=s in reach,linked_out_of_line=s in linked) for s,v in name.items() if interesting.search(v)]
targetcalls=[dict(**c,caller_name=name.get(c['caller']),target_name=name.get(c['target']),direct_graph_reachable=c['caller'] in reach,linked_out_of_line=c['caller'] in linked) for c in calls if interesting.search(name.get(c['target'],''))]
result=dict(private_symbols_qualified_by_LLVM_unit=True,roots=roots,defined_functions=len(definitions),direct_graph_reachable_symbols=len(reach),target_calls=targetcalls,selected_symbols=selected,unresolved_indirect=[dict(**x,caller_name=name.get(x['caller'])) for x in indirect if x['caller'] in reach],complete=False,reason='Private names are unit-qualified; actual linked symbol membership recorded. Unresolved indirect dispatch and precompiled sysroot bodies remain; absence of an out-of-line symbol is not by itself proof of unreachable source because of LLVM inlining.')
(D/'ir-linked-inventory.json').write_text(json.dumps(result,indent=2)+'\n')
with lzma.open(D/'ir-unit-qualified-graph.json.xz','wt') as f:json.dump(dict(names=name,edges={k:sorted(v) for k,v in graph.items()},reachable=sorted(reach),linked=sorted(linked)),f)
print(json.dumps(dict(definitions=len(definitions),reachable=len(reach),target_calls=len(targetcalls),indirect=len(result['unresolved_indirect']))))
