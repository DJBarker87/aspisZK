#!/usr/bin/env python3
"""Static inventory only. Reachability/taint require source and caller review."""
from pathlib import Path
import subprocess,re,json,hashlib,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');name=sys.argv[1];B=H/'bin'/('devnet_spend-'+name);O=H/'dual-evidence'/name
if (O/'extraction.json').exists(): (O/'extraction-initial.json').write_bytes((O/'extraction.json').read_bytes())
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip());t=time.monotonic()
def run(*cmd):return subprocess.check_output(cmd,text=True)
nm=run('nm','-S','-n','-C',str(B));(O/'symbols.txt').write_text(nm)
asm=run('objdump','-d','-C','-Mintel','--no-show-raw-insn',str(B));(O/'full-disassembly.txt').write_text(asm)
rel=run('readelf','-rW',str(B));(O/'relocations.txt').write_text(rel)
syms={}
for line in nm.splitlines():
 m=re.match(r'([0-9a-f]+) ([0-9a-f]+) [Tt] (.*)',line)
 if m:syms[int(m[1],16)]=dict(symbol=m[3],start=int(m[1],16),size=int(m[2],16))
blocks={};a=None
for line in asm.splitlines():
 m=re.match(r'([0-9a-f]+) <(.*)>:',line)
 if m:a=int(m[1],16);blocks[a]=[]
 elif a in syms:
  m=re.match(r'\s*([0-9a-f]+):\s+(\S+)\s*(.*)',line)
  if m and int(m[1],16)<a+syms[a]['size']:blocks[a].append(dict(address='0x'+m[1],op=m[2],args=m[3]))
got={}
for line in rel.splitlines():
 m=re.match(r'([0-9a-f]+)\s+\S+\s+R_X86_64_RELATIVE\s+([0-9a-f]+)',line)
 if m:got[int(m[1],16)]=int(m[2],16)
def target(i):
 m=re.match(r'([0-9a-f]+) <',i['args'])
 if m:return int(m[1],16)
 m=re.search(r'# ([0-9a-f]+)',i['args']);return got.get(int(m[1],16)) if m else None
calls=[]
for a,ins in blocks.items():
 for i in ins:
  if i['op'] in ['call','jmp']:
   dest=target(i)
   calls.append(dict(caller=syms[a]['symbol'],caller_start=hex(a),site=i['address'],op=i['op'],args=i['args'],callee=syms.get(dest,{}).get('symbol'),callee_start=hex(dest) if dest else None))
roots=[a for a,s in syms.items() if s['symbol']=='devnet_spend::main'];reach=set(roots);todo=roots[:]
edges={}
for c in calls:
 if c['callee_start'] and int(c['callee_start'],16) in syms:edges.setdefault(int(c['caller_start'],16),[]).append(int(c['callee_start'],16))
while todo:
 for dest in edges.get(todo.pop(),[]):
  if dest not in reach:reach.add(dest);todo.append(dest)
patterns=['aspis_','devnet_spend::','sha2::','sha2_','sha256','curve25519','ed25519','getrandom::','serde_json::','solana_keypair::']
selected={a for a,s in syms.items() if any(p in s['symbol'] for p in patterns)}
texts=[];rows=[]
for a in sorted(selected):
 s=syms[a];ins=blocks.get(a,[])
 texts.append(f"{a:x} <{s['symbol']}> size={s['size']:x}\n"+'\n'.join(f"  {i['address'][2:]}: {i['op']} {i['args']}".rstrip() for i in ins)+'\n')
 rows.append(dict(symbol=s['symbol'],start=hex(a),end=hex(a+s['size']),instruction_count=len(ins),direct_reachable=a in reach,branches=[i for i in ins if i['op'].startswith('j') and i['op']!='jmp'],division=[i for i in ins if i['op'] in ['div','idiv']],indirect=[i for i in ins if i['op'] in ['call','jmp'] and target(i) is None],review='inventory, not taint verdict'))
(O/'selected-disassembly.txt').write_text('\n'.join(texts));(O/'inventory.json').write_text(json.dumps(rows,indent=1)+'\n');(O/'calls.json').write_text(json.dumps(calls,indent=1)+'\n')
meta=dict(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),binary_bytes=B.stat().st_size,full_disassembly_sha256=hashlib.sha256(asm.encode()).hexdigest(),source_revision=json.loads((O/'receipt.json').read_text())['source_revision'],limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},symbols=len(syms),selected_symbols=len(rows),roots=[hex(a) for a in roots],direct_reachable_symbols=len(reach),selected_direct_reachable=sum(r['direct_reachable'] for r in rows),incomplete_edges='register-indirect function pointers, dynamic library calls, inlining and data callbacks require manual provenance; direct closure is a lower bound',exit_status=0,wall_seconds=time.monotonic()-t,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)',target=['objdump','-d','-C','-Mintel','--no-show-raw-insn',str(B)])
(O/'extraction.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
