from pathlib import Path
import json,re,subprocess,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');b=D/'client-target/release/devnet_spend'
reltext=subprocess.check_output(['readelf','-rW',str(b)],text=True)
relative={int(a,16):int(v,16) for a,v in re.findall(r'^([0-9a-f]+)\s+[0-9a-f]+\s+R_X86_64_RELATIVE\s+([0-9a-f]+)\s*$',reltext,re.M)}
p=subprocess.Popen(['objdump','-d','-C','--no-show-raw-insn',str(b)],stdout=subprocess.PIPE,text=True)
functions={};instructions=[];current=None
for line in p.stdout:
 m=re.match(r'^([0-9a-f]+) <(.*)>:',line)
 if m:current=int(m[1],16);functions[current]=m[2];continue
 if current is not None and re.search(r'\b(?:call|jmp)\s',line):instructions.append((current,line.strip()))
assert p.wait()==0
edges={a:set() for a in functions};unknown=[];calls=[]
for a,line in instructions:
 direct=re.search(r'\b(?:call|jmp)\s+([0-9a-f]+)\b',line)
 got=re.search(r'#\s*([0-9a-f]+)',line)
 dest=int(direct[1],16) if direct else relative.get(int(got[1],16)) if got else None
 if dest in functions:
  if dest!=a:edges[a].add(dest)
  if re.search(r'(?:std::path::(?:Path::_join|PathBuf::_push)|alloc::string::String::(?:with_capacity|reserve_exact))',functions[dest]):calls.append(dict(caller=functions[a],target=functions[dest],instruction=line))
 elif re.search(r'\b(?:call|jmp)\s+\*',line):unknown.append(dict(caller=functions[a],instruction=line))
roots=[a for a,n in functions.items() if n=='devnet_spend::main'];reach=set(roots);q=list(roots)
while q:
 for a in edges[q.pop()]:
  if a not in reach:reach.add(a);q.append(a)
result=dict(binary_sha256=hashlib.sha256(b.read_bytes()).hexdigest(),function_count=len(functions),relative_relocations=len(relative),resolved_direct_or_GOT_reachable=len(reach),target_calls=calls,unresolved_indirect=unknown,complete=False,reason='Register-based callbacks/trait dispatch and tail jumps still unresolved; exact linked function inventory is an overapproximation, not a proof of each function reachable. Includes precompiled std. String constructors inlined in sysroot bodies need source reconciliation.')
(D/'machine-relocations.json').write_text(json.dumps(result,indent=2)+'\n')
with lzma.open(D/'machine-relocations-graph.json.xz','wt') as f:json.dump(dict(functions={hex(k):v for k,v in functions.items()},edges={functions[k]:[functions[x] for x in v] for k,v in edges.items()},reachable=[functions[a] for a in reach]),f)
print(json.dumps({k:v for k,v in result.items() if k in ['function_count','relative_relocations','resolved_direct_or_GOT_reachable']}));print(json.dumps(calls,indent=2))
