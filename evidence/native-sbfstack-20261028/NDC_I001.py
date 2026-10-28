from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028')
O=H.parent
r={}
for name,base in [('default',O/'codex-cx-native-elfscope-20261028/NCR_B003/artifacts'),('devnet',O/'codex-cx-native-elfpins-20261028/NCY_B001/artifacts'),('pool',O/'codex-cx-native-elfpins-20261028/NCY_B002/artifacts')]:
 for p in base.glob('*.so'):
  r[name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
  q=subprocess.run(['readelf','-aW',str(p)],capture_output=True,text=True);(H/('NDC_'+name+'_readelf.txt')).write_text(q.stdout+q.stderr)
print(json.dumps(r))
for p in Path('/home/dombarker/.cache/solana/v1.52').rglob('llvm-objdump'):print('OBJDUMP',p)
for base in [Path('/home/dombarker/.cargo/registry/src'),O/'codex-cx-lowering2-20261026']:
 for pat in (['*/solana-sbpf-*','*/solana_rbpf-*','*/solana-program-runtime-*','*/solana-bpf-loader-program-*'] if base.name=='src' else ['**/*unstripped*','**/aspis_r1_cost_probe_program.so','**/aspis_pool.so']):
  for p in base.glob(pat):print('CANDIDATE',p)
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
print('CGROUP',json.dumps({n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max','memory.peak','memory.swap.peak']}))
(H/'NDC_ELFS.json').write_text(json.dumps(r,indent=2)+'\n')
