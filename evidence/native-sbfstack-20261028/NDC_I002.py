from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');O=H.parent
obj='/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objdump'
r={}
for mode,tgt,prog in [('verifier','sbf-target-verifier','aspis_r1_cost_probe_program'),('pool','sbf-target-pool','aspis_pool')]:
 p=O/'codex-cx-lowering2-20261026'/tgt/'sbpf-solana-solana/release'/('deps/'+prog+'.so')
 for kind,args in [('symbols',['-t']),('disassembly',['-d','--demangle'])]:
  q=subprocess.run([obj,*args,str(p)],capture_output=True,text=True);out=H/('NDC_'+mode+'_'+kind+'.txt');out.write_text(q.stdout+q.stderr)
  print(mode,kind,q.returncode,len(q.stdout),q.stdout[:4500] if kind=='symbols' else q.stdout[:1500])
 r[mode]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
for name,a in json.loads((H/'NDC_ELFS.json').read_text()).items():
 q=subprocess.run([obj,'-d','--demangle',a['path']],capture_output=True,text=True);(H/('NDC_'+name+'_final_disassembly.txt')).write_text(q.stdout+q.stderr);print('FINAL',name,q.returncode,len(q.stdout),q.stdout[:1000])
print(json.dumps(r));(H/'NDC_UNSTRIPPED.json').write_text(json.dumps(r,indent=2)+'\n')
reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for crate in ['solana-sbpf-0.21.1','solana-program-runtime-4.2.1','solana-bpf-loader-program-4.2.1']:
 for p in (reg/crate/'src').rglob('*.rs'):
  t=p.read_text();ls=t.splitlines();hits=[i for i,s in enumerate(ls) if any(k in s for k in ['stack_frame_size','enable_stack_frame_gaps','dynamic_stack_frames','stack_frame_gaps','StackAccessViolation','fn push','fn get_sbpf_version','SBPFVersion::V0'])]
  if hits:
   print('RUNTIME',p,'sha256',hashlib.sha256(p.read_bytes()).hexdigest())
   for i in hits:
    print('\n'.join(f'{j+1}: {ls[j]}' for j in range(max(0,i-3),min(len(ls),i+8))))
