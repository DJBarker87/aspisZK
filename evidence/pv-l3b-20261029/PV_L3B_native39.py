"""Cross-check all diagnostic kernel origins against linked-image functions."""
from pathlib import Path
import json,lzma,subprocess,re,hashlib,bisect,collections
D=Path(__file__).resolve().parent;L=D.parent/'codex-pv-l3a-20261029'
flags={}
for label,root in [('baseline',D.parent/'codex-pv-rdea-20261028/client-target'),('debug',D/'client-target')]:
 units=[]
 for p in (root/'release/.fingerprint').glob('*/*.json'):
  try:r=json.loads(p.read_text())
  except (ValueError,OSError):continue
  if 'rustflags' in r:units.append(dict(file=str(p),rustflags=r['rustflags'],features=r.get('features'),profile=r.get('profile')))
 flags[label]=units
(D/'configuration-fingerprints.json').write_text(json.dumps(flags,indent=2)+'\n')
inputs={}
root=D.parent/'codex-pv-fscan-20261028/src'
for p in [root/'tools/r1-cost-probe/Cargo.lock',root/'tools/r1-cost-probe/Cargo.toml',D.parent/'codex-pv-rdea-20261028/emit-wrapper.py']:
 inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'build-input-hashes.json').write_text(json.dumps(inputs,indent=2)+'\n')
def instructions(s):
 out=[]
 for line in s.splitlines():
  m=re.match(r'\s*([\da-f]+):\s+([a-z][a-z\d_.]*)\s*(.*)',line)
  if m:out.append((int(m[1],16),m[2],m[3]))
 return out
def norm(i):
 s=re.sub(r'-?0x[\da-f]+\(%rip\)','RIP_RELOC',i[2]);s=re.sub(r'\s+#\s+.*','',s)
 if i[1].startswith(('j','call')):s=re.sub(r'^[\da-f]+\s+<','DIRECT_TARGET <',s)
 return i[1]+' '+re.sub(r'<.*>','',s).strip()
with lzma.open(L/'disassembly.txt.xz','rt') as f:old=instructions(f.read())
asm=subprocess.check_output(['objdump','-d','-C','--no-show-raw-insn',str(D/'client-target/release/devnet_spend')],text=True)
new=instructions(asm);oa=[i[0] for i in old];na=[i[0] for i in new]
syms=json.loads((D/'symbol-address-comparison.json').read_text())
maps=[];functions=[]
for s in syms:
 if len(s['baseline'])!=1 or not s.get('debug') or len(s['debug'])!=1:continue
 a,z=s['baseline'][0];b,w=s['debug'][0]
 x=old[bisect.bisect_left(oa,a):bisect.bisect_left(oa,a+z)];y=new[bisect.bisect_left(na,b):bisect.bisect_left(na,b+w)]
 equal=[norm(i) for i in x]==[norm(i) for i in y]
 functions.append(dict(name=s['name'],baseline=[a,a+z],debug=[b,b+w],masked_sequence_equal=equal,baseline_instructions=len(x),debug_instructions=len(y)))
 if equal:maps.extend((j[0],i[0]) for i,j in zip(x,y))
maps=sorted(set(maps));ma=[x[0] for x in maps]
with lzma.open(D/'dwarf-all-instances.json.xz','rt') as f:rows=json.load(f)
selected=[];counts=collections.Counter()
for r in rows:
 file=r.get('decl_file') or '';name=r.get('name') or '';link=r.get('linkage_name') or ''
 family=None
 if 'aspis-core/src/field.rs' in file or ('field.rs' in file and 'aspis_core' in link):family='F2-field'
 if 'field/wide_exact.rs' in file:family='F2-WideExact'
 if 'r0/scalar.rs' in file:family='F2-CodeField'
 if 'ct_pole.rs' in file:family='F1-pole'
 if 'host_semantic.rs' in file and any(x in name for x in ['no_pole','copy_','build_with_material']):family='F1-readers/caller'
 if ('prover_shared.rs' in file or 'host_forest.rs' in file) and 'compress' in name:family='F1-compression'
 if family:
  mapped=[];missing=[]
  for lo,hi in r['ranges']:
   inds=range(bisect.bisect_left(na,lo),bisect.bisect_left(na,hi))
   for idx in inds:
    addr=na[idx];mi=bisect.bisect_left(ma,addr)
    if mi<len(ma) and ma[mi]==addr:mapped.append([addr,maps[mi][1]])
    else:missing.append(addr)
  selected.append(dict(**r,family=family,guide_instruction_pairs=mapped,unmapped_debug_instructions=missing,provenance='diagnostic DWARF plus heuristic masked per-function instruction alignment; NOT exact shipped DWARF'))
  counts[family]+=1
with lzma.open(D/'inline-kernel-guide.json.xz','wt') as f:json.dump(selected,f)
(D/'whole-function-alignment.json').write_text(json.dumps(functions,indent=2)+'\n')
(D/'inline-coverage.json').write_text(json.dumps(dict(families=counts,selected_instances=len(selected),with_unmapped_instructions=sum(bool(x['unmapped_debug_instructions']) for x in selected),functions_compared=len(functions),functions_equal_under_mask=sum(x['masked_sequence_equal'] for x in functions),scope='all concrete DIEs emitted by the debug build, NOT a claim that DWARF enumerates every shipped optimized origin'),indent=2)+'\n')
for name in ['dwarf-kernel-instances.json']:
 p=D/name;raw=p.read_bytes();(D/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 with lzma.open(D/(name+'.xz'),'wb') as f:f.write(raw)
print(dict(counts))
