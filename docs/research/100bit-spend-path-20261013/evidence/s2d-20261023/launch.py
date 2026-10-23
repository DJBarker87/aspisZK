#!/usr/bin/env python3
"""One immutable focused host attempt; aggregate admission then capped scope."""
from pathlib import Path
import hashlib,json,subprocess,sys
base=Path(__file__).resolve().parent
root=next(p for p in base.parents if (p/'programs/r1-cost-probe/src/lib.rs').exists())
host='dombarker@100.108.41.90'; remote='/home/dombarker/project-offloads/codex-cx-s2d-20261023'
kind,number,target=sys.argv[1:]; attempt=f'{kind}-{int(number):03d}'
assert kind in ['lean','kani']; assert 1<=int(number)<=(100 if kind=='lean' else 60)
assert not (base/(attempt+'.json')).exists(),'attempt already allocated'
def call(args,**kw):return subprocess.run(args,check=True,**kw)
call(['ssh',host,'mkdir -p '+remote+'/kani-spec/src'])
sources=[]
if kind=='lean':
 for name in [target,'S2TrustedSdkBorrow.lean']:
  src=root/'docs/research/100bit-spend-path-20261013/lean'/name
  call(['scp',str(src),host+':'+remote+'/'+name]); sources.append(name)
 command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target.replace('.lean','.olean'),target]
 env={'LEAN_PATH':'.'}
else:
 sources=['kani-spec/src/lib.rs','kani-spec/Cargo.toml']
 command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path','kani-spec/Cargo.toml','--target-dir','kani-target','--harness',target,'--exact','--output-format','terse']
 env={'CARGO_BUILD_JOBS':'4','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_NET_OFFLINE':'true'}
for name in ['run_host.py','reservation.py','lakefile.toml','lean-toolchain']+(sources if kind=='kani' else []):
 call(['scp',str(base/name),host+':'+remote+'/'+name])
# Reuse the already audited, unchanged trust object; never overwrite shared cache.
call(['ssh',host,'cd '+remote+' && cmp S2TrustedSdkBorrow.lean ../codex-cx-s2-trust-20261023/S2TrustedSdkBorrow.lean && cp -n ../codex-cx-s2-trust-20261023/S2TrustedSdkBorrow.olean .']) if kind=='lean' else None
deps=subprocess.check_output(['ssh',host,'sha256sum /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean '+remote+'/S2TrustedSdkBorrow.olean'],text=True) if kind=='lean' else 'standalone verbatim source extraction, no dependency crates; Kani 0.67.0'
cfg=dict(attempt=attempt,kind=kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),command=command,sources=sources,env=env,timeout=180,deps_fingerprint=deps,expected_time='focused elaboration' if kind=='lean' else 'optimized compile and constant Option discriminant check')
(base/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
call(['scp',str(base/(attempt+'.json')),host+':'+remote+'/'])
result=subprocess.run(['ssh',host,'cd '+remote+' && python3 reservation.py '+attempt+'-reservation.json && systemd-run --user --scope --unit=s2d-'+attempt+' -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 run_host.py '+attempt+'.json'])
for name in [attempt,attempt+'-reservation.json']:
 call(['scp','-r',host+':'+remote+'/'+name,str(base)])
sys.exit(result.returncode)
