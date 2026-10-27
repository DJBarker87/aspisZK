#!/usr/bin/env python3
"""Conservative symbol-level instruction diff; no equivalence inferred from source equality."""
import subprocess,re,json,pathlib,sys,hashlib,difflib
h,c,o=map(pathlib.Path,sys.argv[1:]);o.mkdir(exist_ok=True)
def symbols(p):
 raw=subprocess.check_output(['objdump','-d','-C','-M','intel','--no-show-raw-insn',str(p)],text=True)
 funcs={};name=None
 for line in raw.splitlines():
  m=re.match(r'^([0-9a-f]+) <(.+)>:$',line)
  if m:name=m[2];funcs[name]=[int(m[1],16),[]]
  elif name:
   m=re.match(r'\s*([0-9a-f]+):\s+(.+)',line)
   if m:funcs[name][1].append((int(m[1],16),m[2]))
 return funcs
H,C=symbols(h),symbols(c)
def relocations(p,table):
 byaddr={v[0]:k for k,v in table.items()};out={}
 raw=subprocess.check_output(['readelf','-rW',str(p)],text=True)
 for line in raw.splitlines():
  parts=line.split()
  if len(parts)>=4 and re.fullmatch('[0-9a-f]{16}',parts[0]):
   if parts[2]=='R_X86_64_RELATIVE':
    target=int(parts[3],16)
    if target in byaddr:out[int(parts[0],16)]=byaddr[target]
   elif parts[2] in ['R_X86_64_GLOB_DAT','R_X86_64_JUMP_SLOT'] and len(parts)>=5:
    out[int(parts[0],16)]=parts[4]
 return out
RH,RC=relocations(h,H),relocations(c,C)
def canonical(s):
 s=re.sub(r'::h[0-9a-f]{16}\b','',s)
 s=s.replace('pv_dudect::kernels::state_only_hiding','aspis_prover::state_only_hiding').replace('pv_dudect::kernels::entropy','aspis_prover::state_only_entropy')
 s=s.replace('pv_dudect::kernels::ct_pole','aspis_r1_cost_probe::ct_pole').replace('pv_dudect::kernels::prover_shared','aspis_r1_cost_probe::prover_shared')
 s=s.replace('state_only_hiding::measure_qm31','state_only_hiding::SeedExpander::qm31').replace('state_only_hiding::measure_m31','state_only_hiding::SeedExpander::m31')
 return s
def norm(entry,relocs):
 base,rows=entry;end=rows[-1][0]+16 if rows else base
 result=[]
 for addr,s in rows:
  # Resolve ELF GOT relocations before stripping address annotations.
  rip=re.search(r'\[rip(?:[+-]0x[0-9a-f]+)?\]',s)
  comment=re.search(r'# ([0-9a-f]+)(?: <(.+)>)?',s)
  if rip and comment:
   address=int(comment[1],16)
   symbol=relocs.get(address) or comment[2]
   if symbol:
    s=s[:rip.start()]+'[RIP:'+canonical(symbol)+']'+s[rip.end():]
    s=s.split('#',1)[0].strip()
   # Unresolved RIP targets are deliberately retained; never equate by erasure.
  m=re.search(r'\b([0-9a-f]+) <(.+)>',s)
  if m:
   target=int(m[1],16);sym=canonical(m[2])
   replacement='LOCAL+'+hex(target-base) if base<=target<end and ('+' in sym or target==base) else sym
   s=s[:m.start()]+replacement+s[m.end():]
  result.append(s.strip())
 return result
patterns={
 'mask-m31':['SeedExpander::m31','measure_m31','sample_mask_cells'],
 'mask-qm31':['SeedExpander::qm31','measure_qm31'],
 'pole':['ct_pole::all_slots_clear','host_semantic::no_pole'],
 'm31-inv':['field::M31::inv','inverse_m'],
 'qm31-inv':['field::QM31::inv','field::QM31::try_inv','inverse_q'],
 'compress':['prover_shared::compress_tagged_tuple','host_semantic::copy_endpoint_values'],
 'seed-checks':['generate_for_mask_nonce','entropy::seed_check'],
}
summary={'binary_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [h,c]},'normalization':'resolved branch offsets, module/adapter names, ELF-relocated GOT callees and symbolic RIP references only; opcodes/registers/literal immediates preserved; anonymous data symbols stay distinct','families':{}}
for family,ps in patterns.items():
 hs={k:v for k,v in H.items() if any(p in k for p in ps)};cs={k:v for k,v in C.items() if any(p in k for p in ps)}
 item={'harness_symbols':list(hs),'candidate_symbols':list(cs),'comparisons':[]}
 for hn,hv in hs.items():
  matches=[cn for cn in cs if canonical(hn)==canonical(cn)]
  for cn in matches:
   a,b=norm(hv,RH),norm(cs[cn],RC);equal=a==b
   name=family+'-'+str(len(item['comparisons']))
   (o/(name+'.diff')).write_text('\n'.join(difflib.unified_diff(a,b,fromfile=hn,tofile=cn))+'\n')
   item['comparisons'].append(dict(harness=hn,candidate=cn,equal=equal,harness_instructions=len(a),candidate_instructions=len(b),diff=name+'.diff'))
 item['result']='equal standalone symbol only; verify timed call site below' if item['comparisons'] and all(x['equal'] for x in item['comparisons']) else 'NOT instruction-equivalent / no matched standalone symbol; harness binary only'
 summary['families'][family]=item
 for label,table in [('harness',hs),('candidate',cs)]:
  (o/(family+'-'+label+'.asm')).write_text('\n\n'.join(k+' @ '+hex(v[0])+'\n'+'\n'.join(norm(v,RH if label=='harness' else RC)) for k,v in table.items())+'\n')
# Preserve adapter/main call sites so inlining cannot be mistaken for a standalone-symbol measurement.
for label,table in [('harness',H),('candidate',C)]:
 selected={k:v for k,v in table.items() if (label=='harness' and ('pv_dudect::main' in k or 'measure_' in k or 'seed_check' in k or 'inverse_' in k)) or (label=='candidate' and 'host_semantic::' in k and any(x in k for x in ['pole','compress','tuple']))}
 (o/(label+'-call-sites.asm')).write_text('\n\n'.join(k+' @ '+hex(v[0])+'\n'+'\n'.join(norm(v,RH if label=='harness' else RC)) for k,v in selected.items())+'\n')
(o/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
