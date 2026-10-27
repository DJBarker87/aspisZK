"""Read symbol/call/relocation evidence from the actual optimized client ELF."""
import pathlib,subprocess,re,json,hashlib,collections
H=pathlib.Path(__file__).resolve().parent
B=H/'candidate/bin/devnet_spend';O=H/'binary-route';O.mkdir(exist_ok=False)
def run(*a):return subprocess.check_output(a,text=True)
nm=run('nm','-S','-n','-C',str(B));asm=run('objdump','-d','-C','-Mintel','--no-show-raw-insn',str(B));rel=run('readelf','-rW',str(B))
for name,text in [('symbols.txt',nm),('full-disassembly.txt',asm),('relocations.txt',rel)]: (O/name).write_text(text)
syms={}
for l in nm.splitlines():
 m=re.match(r'([0-9a-f]+) ([0-9a-f]+) [Tt] (.*)',l)
 if m:syms[int(m[1],16)]=dict(symbol=m[3],start=int(m[1],16),size=int(m[2],16))
got={}
for l in rel.splitlines():
 m=re.match(r'([0-9a-f]+)\s+\S+\s+R_X86_64_RELATIVE\s+([0-9a-f]+)',l)
 if m:got[int(m[1],16)]=int(m[2],16)
blocks={};a=None
for l in asm.splitlines():
 m=re.match(r'([0-9a-f]+) <(.*)>:',l)
 if m:a=int(m[1],16);blocks[a]=[]
 elif a in syms:
  m=re.match(r'\s*([0-9a-f]+):\s+(\S+)\s*(.*)',l)
  if m and int(m[1],16)<a+syms[a]['size']:blocks[a].append(dict(pc=m[1],op=m[2],args=m[3]))
def target(i):
 m=re.match(r'([0-9a-f]+) <',i['args'])
 if m:return int(m[1],16)
 m=re.search(r'# ([0-9a-f]+)',i['args']);return got.get(int(m[1],16)) if m else None
edges=collections.defaultdict(list)
for a,ins in blocks.items():
 for i in ins:
  if i['op'] in ['call','jmp']:
   b=target(i)
   if b in syms:edges[a].append((b,i))
roots=[a for a,s in syms.items() if s['symbol']=='devnet_spend::main'];assert len(roots)==1
parents={roots[0]:None};todo=collections.deque(roots)
while todo:
 a=todo.popleft()
 for b,i in edges[a]:
  if b not in parents:parents[b]=(a,i);todo.append(b)
selected=[a for a,s in syms.items() if any(x in s['symbol'] for x in ['devnet_spend::main','devnet_spend::plan::','RealR1_client','generate_for_mask_nonce','retry_attempt','prove_masked_retrying','StateOnlyAttemptSecrets::generate'])]
rows=[]
for a in selected:
 path=[];v=a
 if a in parents:
  while parents[v] is not None:
   u,i=parents[v];path.append(dict(caller=syms[u]['symbol'],caller_start=hex(u),site='0x'+i['pc'],instruction=i['op']+' '+i['args'],callee=syms[v]['symbol'],callee_start=hex(v)));v=u
  path.reverse()
 rows.append(dict(**syms[a],resolved_reachable=a in parents,path=path))
(O/'route-symbols.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'route-disassembly.txt').write_text('\n'.join(f"{a:x} <{syms[a]['symbol']}>\n"+'\n'.join(f"{i['pc']}: {i['op']} {i['args']}" for i in blocks.get(a,[])) for a in selected))
meta=dict(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),binary_bytes=B.stat().st_size,symbols_sha256=hashlib.sha256(nm.encode()).hexdigest(),disassembly_sha256=hashlib.sha256(asm.encode()).hexdigest(),relocations_sha256=hashlib.sha256(rel.encode()).hexdigest(),resolved_reachable_symbols=len(parents),limitations='Resolved direct and RIP-relative GOT edges are a lower bound. Inlined adapters and register-indirect callbacks require source/PC association; mere symbol presence is not reachability.')
(O/'meta.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta));print(json.dumps([(r['symbol'],r['resolved_reachable']) for r in rows]))
assert any('generate_for_mask_nonce' in r['symbol'] and r['resolved_reachable'] for r in rows),'Inspect callback edges manually; selected64 symbol not reached by resolved edges'
assert not any('StateOnlyAttemptSecrets::generate' in r['symbol'] and 'generate_for_mask_nonce' not in r['symbol'] and r['resolved_reachable'] for r in rows),'Unexpected generic96 route reachable'
