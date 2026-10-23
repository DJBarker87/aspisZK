#!/usr/bin/env python3
"""One native FIRST-ENTRY gate. Called ONLY inside the capped S2A runner.
Same scanner nondet-return overapproximation as the inherited source gate;
no SDK stubs, no owned reference run. Pointwise comparison overapproximation
includes the real zero/nonzero outcome and retains every other memcmp body.
"""
from pathlib import Path
import json, re, subprocess, hashlib, sys
H=Path(__file__).resolve().parent; B=Path('/home/dombarker/.kani/kani-0.67.0/bin'); window=int(sys.argv[1]); assert 0<=window<2; wanted=f'S2A_native::S2A_tail_window{window}'; O=H/f'S2A-native-gate-tail{window}-v3'; O.mkdir(exist_ok=False)
rows=[]
for p in (H/'S2A-native-target').rglob('s2a_native_tail_windows*.kani-metadata.json'):
 for r in json.loads(p.read_text()).get('proof_harnesses',[]):
  if r['pretty_name']==wanted: rows.append((p,r))
assert len(rows)==1,rows
metadata,row=rows[0]; raw=Path(row['goto_file']); assert raw.name.endswith('.symtab.out')
assert row['attributes']['kind']=='Proof' and not row['attributes']['verified_stubs']
names=json.loads(Path(str(raw).replace('.symtab.out','.pretty_name_map.json')).read_text())
scan=[k for k,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in k]; assert len(scan)==1,scan
entry=[k for k,v in names.items() if v==wanted];assert len(entry)==1
assert names['s126_coupled_cmp']=='S2A_native::s126_coupled_cmp'
(O/'comparison-declaration.c').write_text('#include <stddef.h>\nint S2A_memcmp(const void *,const void *,size_t);\nint (*S2A_keep)(const void *,const void *,size_t)=S2A_memcmp;\n')
(O/'comparison-body.c').write_text('#include <stddef.h>\nint memcmp(const void *,const void *,size_t);\nint s126_coupled_cmp(const unsigned char *,const unsigned char *,size_t);\nint S2A_memcmp(const void *a,const void *b,size_t n){if(n==688)return s126_coupled_cmp(a,b,n);return memcmp(a,b,n);}\n')
libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c')
cmds=[
 [B/'goto-cc',raw,libc,O/'comparison-declaration.c','-o',O/'linked.out'],
 [B/'goto-instrument','--replace-calls','memcmp:S2A_memcmp',O/'linked.out',O/'replaced.out'],
 [B/'goto-cc',O/'replaced.out',O/'comparison-body.c','-o',O/'comparison.out'],
 [B/'goto-instrument','--remove-function-body',scan[0],O/'comparison.out',O/'removed.out'],
 [B/'goto-instrument','--generate-function-body',re.escape(scan[0]),'--generate-function-body-options','nondet-return',O/'removed.out',O/'abstract.out'],
 [B/'goto-cc',O/'abstract.out','--function',entry[0],'-o',O/'entry.out'],
 [B/'goto-instrument','--add-library','--no-malloc-may-fail',O/'entry.out',O/'library.out'],
 [B/'goto-instrument','--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',O/'library.out',O/'reachable.out'],
 [B/'goto-instrument','--ensure-one-backedge-per-target',O/'reachable.out',O/'ready.out'],
 [B/'cbmc','--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','48','--sat-solver','cadical','--slice-formula','--unwinding-assertions',O/'ready.out']]
cmds=[[str(x) for x in a] for a in cmds]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[raw,metadata,Path(str(raw).replace('.symtab.out','.pretty_name_map.json')),H/'S2A-native-v3/src/lib.rs',H/'S2A-native-v3/Cargo.toml',H/'S2A-native-v3/Cargo.lock',Path(__file__),libc,*[B/n for n in ['goto-cc','goto-instrument','cbmc']],O/'comparison-declaration.c',O/'comparison-body.c']
pins={str(p):{'sha256':sha(p),'size':p.stat().st_size} for p in files}
# Pin every inherited local Rust dependency, not just the four caller files.
D=Path('/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src')
for folder in [D/'crates/aspis-core',D/'crates/aspis-statement',D/'crates/aspis-r1-cost-probe']:
 for p in folder.rglob('*'):
  if p.is_file() and (p.suffix=='.rs' or p.name=='Cargo.toml'):pins[str(p)]={'sha256':sha(p),'size':p.stat().st_size}
(O/'inputs.json').write_text(json.dumps(dict(commands=cmds,pins=pins,harness=row,abstracted_scanner=scan[0],scope=__doc__),indent=2)+'\n')
for i,cmd in enumerate(cmds):
 if i==len(cmds)-1:
  inv=cmd[:-1]+['--show-properties','--json-ui',cmd[-1]]
  subprocess.run(inv,stdout=(O/'properties.json').open('w'),stderr=subprocess.STDOUT,check=True,timeout=30)
 with (O/f'step-{i}.log').open('w') as f:
  r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=160)
 if i<len(cmds)-1:assert r.returncode==0,(i,r.returncode)
 else:
  print((O/f'step-{i}.log').read_text()[-14000:]);print('CBMC exit:',r.returncode)
  (O/'cbmc-exit.json').write_text(json.dumps({'exit_status':r.returncode})+'\n')
  raise SystemExit(r.returncode)
