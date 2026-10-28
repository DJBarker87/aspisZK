from pathlib import Path
import json,subprocess,hashlib,re,struct
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');O=H.parent
reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');out={}
for crate in ['solana-sbpf-0.21.1','solana-program-runtime-4.2.1','solana-bpf-loader-program-4.2.1','solana-syscalls-4.2.1','solana-svm-4.2.1']:
 d=reg/crate
 for name in ['.cargo_vcs_info.json','Cargo.toml','src/vm.rs','src/program.rs','src/interpreter.rs','src/elf.rs','src/memory_region.rs','src/memory_management.rs','src/error.rs','src/lib.rs','src/syscalls/mod.rs','src/execution_budget.rs']:
  p=d/name
  if p.exists():out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'text':p.read_text()}
(H/'NDC_RUNTIME_SOURCES.json').write_text(json.dumps(out,indent=2)+'\n')
for p,j in out.items():
 if p.endswith('.cargo_vcs_info.json'):print(p,j['text'])
 for i,line in enumerate(j['text'].splitlines()):
  if any(x in line for x in ['enable_stack_frame_gaps:','stack_frame_size:','SBPFVersion::V0','e_flags','DEFAULT_STACK_FRAME_SIZE','create_program_runtime_environment_v1','AccessViolation','vm_to_host','frame_gaps','manual_stack_frame_bump']):print(p,i+1,line)
for mode,tgt in [('verifier','sbf-target-verifier'),('pool','sbf-target-pool')]:
 d=O/'codex-cx-lowering2-20261026'/tgt/'sbpf-solana-solana/release/deps'
 for p in d.glob('libaspis*.rlib'):print('RLIB',mode,p,p.stat().st_size)
# Native corpus candidate artifact names only; do not traverse unrelated worktrees.
for name in ['codex-cx-leaf-cache-20261027','codex-cx-lowering2-20261026','codex-cx-native-elfpins-20261028']:
 d=O/name
 for p in d.glob('**/libaspis*.rlib'):
  if 'sbpf-solana' not in str(p): print('NATIVE_CANDIDATE',p,p.stat().st_size)
# Exact warned symbols vs whole unstripped symbols, including generic instances.
w=json.loads((H/'NDC_WARNINGS.json').read_text());r={}
for mode in ['verifier','pool']:
 t=(H/('NDC_'+mode+'_symbols.txt')).read_text()
 r[mode]={s['symbol']:s['symbol'] in t for row in w for s in row['diagnostics'].values()}
print('EXACT_DIAGNOSTIC_SYMBOLS',json.dumps(r))
(H/'NDC_EXACT_SYMBOLS.json').write_text(json.dumps(r,indent=2)+'\n')
