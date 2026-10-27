#!/usr/bin/env python3
"""Extract actual example symbols and static call sites; never classify taint automatically."""
from pathlib import Path
import subprocess,json,re,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026')
B=H/'target/release/examples/r1p_retry_gate'; O=H/'audit-20261027'; O.mkdir(exist_ok=False)
def run(*cmd): return subprocess.check_output(cmd,text=True)
nm=run('nm','-S','-n','-C',str(B)); (O/'symbols.txt').write_text(nm)
asm=run('objdump','-d','-C','-Mintel','--no-show-raw-insn',str(B)); (O/'full-disassembly.txt').write_text(asm)
rel=run('readelf','-rW',str(B)); (O/'relocations.txt').write_text(rel)
syms={}
for line in nm.splitlines():
 m=re.match(r'([0-9a-f]+) ([0-9a-f]+) [Tt] (.*)',line)
 if m:syms[int(m[1],16)]=dict(symbol=m[3],start=int(m[1],16),size=int(m[2],16))
blocks={}; a=None
for line in asm.splitlines():
 m=re.match(r'([0-9a-f]+) <(.*)>:',line)
 if m:a=int(m[1],16); blocks[a]=[]
 elif a is not None:
  m=re.match(r'\s*([0-9a-f]+):\s+(\S+)\s*(.*)',line)
  if m and a in syms and int(m[1],16)<a+syms[a]['size']:blocks[a].append(dict(address='0x'+m[1],op=m[2],args=m[3],line=line))
got={}
for line in rel.splitlines():
 m=re.match(r'([0-9a-f]+)\s+\S+\s+R_X86_64_RELATIVE\s+([0-9a-f]+)',line)
 if m:got[int(m[1],16)]=int(m[2],16)
def target(i):
 m=re.match(r'([0-9a-f]+) <',i['args'])
 if m:return int(m[1],16)
 m=re.search(r'# ([0-9a-f]+)',i['args'])
 return got.get(int(m[1],16)) if m else None
patterns=['aspis_core::field::','aspis_core::circle::','aspis_r1_cost_probe::ct_pole::','aspis_r1_cost_probe::host_semantic::','aspis_r1_cost_probe::host_sumcheck::','aspis_r1_cost_probe::sampler::','aspis_r1_cost_probe::host_transcript::','aspis_r1_cost_probe::prover::prove_masked','aspis_prover::state_only_hiding::','aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::generate','aspis_statement::logup::','aspis_statement::pool_v1::pair_forest_copy_builder::','aspis_statement::pool_v1::pair_tree_profile::']
selected={a for a,s in syms.items() if any(p in s['symbol'] for p in patterns)}
callers=[]
for a,ins in blocks.items():
 for i in ins:
  t=target(i)
  if i['op'] in ['call','jmp'] and t in selected:callers.append(dict(caller=syms[a]['symbol'],caller_start=hex(a),site=i['address'],instruction=i['line'],callee=syms[t]['symbol'],callee_start=hex(t)))
rows=[];texts=[]
for a in sorted(selected):
 s=syms[a];ins=blocks.get(a,[])
 texts.append(f"{a:x} <{s['symbol']}> size={s['size']:x}\n"+'\n'.join(i['line'] for i in ins)+'\n')
 rows.append(dict(symbol=s['symbol'],start=hex(a),end=hex(a+s['size']),instruction_count=len(ins),branches=[i for i in ins if i['op'].startswith('j') and i['op']!='jmp'],division=[i for i in ins if i['op'] in ['div','idiv']],calls=[dict(**i,target=syms.get(target(i),{}).get('symbol')) for i in ins if i['op'] in ['call','jmp']],review='not automatically classified'))
(O/'selected-disassembly.txt').write_text('\n'.join(texts)); (O/'inventory.json').write_text(json.dumps(rows,indent=2)+'\n'); (O/'call-sites.json').write_text(json.dumps(callers,indent=2)+'\n')
meta=dict(binary=str(B),sha256=hashlib.sha256(B.read_bytes()).hexdigest(),bytes=B.stat().st_size,rustc=run('rustc','-Vv'),objdump=run('objdump','--version'),elf_comment=run('readelf','-p','.comment',str(B)),symbols=len(rows),calls=len(callers),instructions=sum(r['instruction_count'] for r in rows),classification='supplementary candidate example, not identified deployed binary',inlining='inlined kernels require caller operand provenance; selected symbol list not a complete call graph')
(O/'identity.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
