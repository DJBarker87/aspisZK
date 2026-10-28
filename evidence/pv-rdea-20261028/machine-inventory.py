from pathlib import Path
import json,re,subprocess,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');binary=D/'client-target/release/devnet_spend'
# Linked image, including precompiled std. Every indirect transfer is retained
# as an unresolved edge; no absent direct edge is an unreachability claim.
cmd=['objdump','-d','-C','--no-show-raw-insn',str(binary)]
p=subprocess.Popen(cmd,stdout=subprocess.PIPE,text=True)
graph={};calls=[];indirect=[];function=None;target=re.compile(r'(?:alloc::string::String::(?:with_capacity|reserve_exact)|std::path::(?:Path::_join|PathBuf::_push))')
for n,line in enumerate(p.stdout,1):
 m=re.match(r'^([0-9a-f]+) <(.*)>:',line)
 if m:function=m[2];graph.setdefault(function,set());continue
 if function:
  refs=re.findall(r'<([^>]+)>',line)
  for ref in refs:
   name=re.sub(r'\+0x[0-9a-f]+$','',ref)
   if name!=function:graph[function].add(name)
  if re.search(r'\b(?:call|jmp)\s+\*',line):indirect.append(dict(function=function,instruction=line.strip()))
  if re.search(r'\b(?:call|jmp)\s+',line) and any(target.search(x) for x in refs):
   calls.append(dict(function=function,instruction=line.strip()))
assert p.wait()==0
roots=[n for n in graph if n=='devnet_spend::main'];reach=set(roots);q=list(roots)
while q:
 for n in graph.get(q.pop(),[]):
  if n not in reach:reach.add(n);q.append(n)
result=dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),command=cmd,functions=len(graph),roots=roots,syntactically_reached=len(reach),target_transfers=calls,unresolved_indirect=[x for x in indirect if x['function'] in reach],complete=False,reason='Conservative direct/address-reference closure; unresolved indirect calls and jump tables remain. All linked functions also saved as an overapproximation. No source-only candidate is called unreachable merely because its out-of-line symbol is absent.')
(D/'machine-reachability.json').write_text(json.dumps(result,indent=2)+'\n')
with lzma.open(D/'machine-graph.json.xz','wt') as f:json.dump({k:sorted(v) for k,v in graph.items()},f)
print(json.dumps({k:v for k,v in result.items() if k in ['functions','roots','syntactically_reached']}));print('target transfers',len(calls),'unresolved indirect',len(result['unresolved_indirect']))
