#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2e-20261023';T=Path(__file__).parent
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2e-20261023'
kind,num,target=sys.argv[1:4];attempt=f'{kind}-{int(num):03d}';assert not (E/attempt).exists()
assert kind in ['rust','charon','aeneas','lean','kani','sbf']
if kind in ['lean','kani']: assert int(num)<=(100 if kind=='lean' else 60)
subprocess.run(['ssh',HOST,'mkdir','-p',H],check=True)
for name in ['S2E_run_host.py','S2E_reservation.py']:
 subprocess.run(['scp',str(T/name),HOST+':'+H+'/'+name],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['rsync','-az',str(E/'S2E-reference')+'/',HOST+':'+H+'/S2E-reference/'],check=True)
for p in (D/'lean').glob('S2E_*.lean'):
 subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True,stdout=subprocess.DEVNULL)
env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','RUSTFLAGS':'--cfg aeneas_ref -C link-arg=-Wl,--threads=1'}
source=['S2E-reference/src/lib.rs','S2E-reference/src/S2E_Reference.rs','S2E-reference/Cargo.toml'];deps={'scope':'owned reference candidate; actual child/native bindings not certified'}
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
if kind=='sbf':
 source=['S2E_sbf_host.py','S2E-frozen-sources.json','S2E-devnet-programs.json']
 command=['python3','S2E_sbf_host.py',target]
 deps={'frozen_source_inventory_sha256':hashlib.sha256((E/'S2E-frozen-sources.json').read_bytes()).hexdigest(),'scope':'fresh explicit three-ELF gate requested for cfg-only reference work; no source change to production'}
elif kind=='rust':
 command=['cargo','check','--release','--manifest-path','S2E-reference/Cargo.toml','--target-dir','rust-target','-j','4']
elif kind=='charon':
 env.update(RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=H+'/charon-target')
 command=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--opaque','aspis_statement','--opaque','aspis_r1_cost_probe','--opaque','solana_program_error']
 roots=['release_shared','shape1','admission','proof_gate','nonzero_from','stage1','checkpoint_continuation','public_continuation','decoded_continuation','statement_continuation','proof_continuation','first_and_copy','after_first','stage2','stage2_proof','stage2_checkpoint','stage2_tail','shared_allowed','owned_data_len','owned_acquire_checkpoint','owned_acquire_shared','owned_release_guards']
 for name in roots: command+=['--start-from','crate::S2E_Reference::'+name,'--include','crate::S2E_Reference::'+name]
 for name in ['OwnedSdk','OwnedAccount','OwnedDataCell','OwnedLamportsCell','LiveGuards','Children','Validated']:
  command+=['--include','crate::S2E_Reference::'+name]
 layouts=['pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1','pool_v1::pair_forest_terminal::PoolV1PairForestTerminalCommonV1','pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','pool_v1::pair_forest_terminal::_::common']
 for name in layouts: command+=['--include','aspis_statement::'+name]
 # Reuse the complete layout allowlist of the accepted owned SDK extraction.
 import ast
 inherited=(R/'tools/s126-sdk-modular-20261021/extract-owned-host.py').read_text()
 for line in inherited.splitlines():
  if line.startswith('layouts=') or line.startswith('layouts +='):
   for name in ast.literal_eval(line.split('=',1)[1].strip()): command+=['--include',name]
 for name in ['ProgramError']:command+=['--include','solana_program_error::'+name]
 command+=['--dest-file',H+'/S2E_Reference.llbc','--','--manifest-path',H+'/S2E-reference/Cargo.toml','--offline','--release','--lib','--jobs','1']
elif kind=='aeneas':
 command=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','S2E_Reference','-dest',H+'/generated','-subdir','S2E_Reference','-split-files','-emit-json',H+'/S2E_Reference.llbc']
 source+=['S2E_Reference.llbc']
elif kind=='lean':
 source=[target+'.lean']; command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean']
 env={'LEAN_PATH':'.:generated:/home/dombarker/project-offloads/codex-cx-s2a-20261023/S2A-cache:/home/dombarker/project-offloads/codex-cx-s2a-20261023:/home/dombarker/project-offloads/codex-cx-s2c-20261023:/home/dombarker/project-offloads/codex-cx-s2d-20261023/objects:/home/dombarker/project-offloads/codex-cx-import-union-20261022/objects:/home/dombarker/project-offloads/codex-cx-import-union-20261022/retained-objects:/home/dombarker/project-offloads/aspis-joint-20261019/objects'}
 if (E/'S2E-host-pins.json').exists():
  pins=json.loads((E/'S2E-host-pins.json').read_text())
  deps={'host_pins_sha256':hashlib.sha256((E/'S2E-host-pins.json').read_bytes()).hexdigest(),
        'selected_objects':{m:v['selected'] for m,v in pins['objects'].items()},
        'inherited_transitive_overlay':'s2a-20261023/final-objects-and-tools.json; sysroot and Aeneas dependencies reused, no coherent release replay'}
  source=[p.name for p in sorted((D/'lean').glob('S2E_*.lean'))]
 prior=json.loads((D/'evidence/s2a-20261023/lean-013/receipt.json').read_text())['env']['LEAN_PATH']
 env['LEAN_PATH']+=':'+prior.replace('S2A-cache','/home/dombarker/project-offloads/codex-cx-s2a-20261023/S2A-cache')
 subprocess.run(['ssh',HOST,f"cd {H} && printf 'name = \"s2e\"\nversion = \"0.1.0\"\n' > lakefile.toml && printf 'leanprover/lean4:v4.32.0\n' > lean-toolchain"],check=True)
else:
 subprocess.run(['rsync','-az',str(E/'S2E-steps')+'/',HOST+':'+H+'/S2E-steps/'],check=True)
 source+=['S2E-steps/src/lib.rs','S2E-steps/src/S2E_Trusted.rs','S2E-steps/Cargo.toml']
 command=['cargo-kani','kani','--manifest-path','S2E-steps/Cargo.toml','--target-dir','kani-target','-j','4','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','--harness-timeout','120s','--exact','--harness',target,'--output-format','terse']
 env['RUSTFLAGS']='-C link-arg=-Wl,--threads=1'
 deps['trusted_spec']=json.loads((E/'S2E-step-domain.json').read_text())
cfg=dict(attempt=attempt,kind=kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=command,sources=source,timeout=600 if kind=='sbf' else 180,deps_fingerprint=deps,env=env,expected_time='cached optimized compilation/translation of owned caller; no cryptographic arithmetic')
(E/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp',str(E/(attempt+'.json')),HOST+':'+H+'/'+attempt+'.json'],check=True,stdout=subprocess.DEVNULL)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2E_reservation.py {attempt}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2E_run_host.py {attempt}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['scp',HOST+':'+H+'/'+attempt+'-reservation.json',str(E)],check=True,stdout=subprocess.DEVNULL)
sys.exit(r.returncode)
