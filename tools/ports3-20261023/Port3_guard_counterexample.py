#!/usr/bin/env python3
"""One optimized native counterexample in a private capped host workspace."""
import hashlib,json,pathlib,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];T=R/'tools/ports3-20261023';E=R/'evidence/ports3-20261023'
HOST='dombarker@100.108.41.90';REMOTE='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[R/'Cargo.toml',R/'Cargo.lock']
for name in ['aspis-core','aspis-statement','aspis-r1-cost-probe']:
 files += [R/'crates'/name/'Cargo.toml',*(R/'crates'/name/'src').rglob('*.rs')]
pins={str(p.relative_to(R)):sha(p) for p in files}
verify='''from pathlib import Path
import hashlib,json
root=Path('''+repr(REMOTE+'/src')+''')
pins='''+repr(pins)+'''
bad=[p for p,h in pins.items() if hashlib.sha256((root/p).read_bytes()).hexdigest()!=h]
print(json.dumps({'checked':len(pins),'mismatches':bad}))
assert not bad
'''
r=subprocess.run(['ssh',HOST,'python3 -c '+shlex.quote(verify)],capture_output=True,text=True,check=True)
(E/'rust-002-source-validation.json').write_text(r.stdout)
cfg={'attempt':'rust-002','kind':'rust-native-counterexample','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'command':['/home/dombarker/.cargo/bin/cargo','test','--release','--offline','-j','4','--manifest-path','writer-boundary/Cargo.toml','s2_full_weights_outside_provenance_writer_returns','--','--nocapture'],
 'sources':['writer-boundary/Cargo.toml','writer-boundary/src/lib.rs'], 'timeout':180,
 'env':{'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'4','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':REMOTE+'/rust-target','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_DEBUG':'0'},
 'deps_fingerprint':{'source_snapshot_pins':pins},
 'expected_time':'Time expected in cached optimized compilation of pinned crates. Counterexample execution is two checkpoint calls, not arithmetic/proof generation or elimination.',
 'scope':'Typed S2 width64 inputs outside next/query provenance; native writer success refutes complement rejection, not reached-spend security'}
c=T/'rust-002.json';c.write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(c),str(T/'Port3_run_host.py'),HOST+':'+REMOTE+'/'],check=True)
subprocess.run(['scp','-q',str(T/'writer-boundary/src/lib.rs'),HOST+':'+REMOTE+'/writer-boundary/src/'],check=True)
subprocess.run(['scp','-q',str(T/'writer-boundary/Cargo.toml'),HOST+':'+REMOTE+'/writer-boundary/'],check=True)
admission='''from pathlib import Path
import json
rows=[]
for p in Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service').rglob('*.scope'):
 try:
  if not (p/'cgroup.procs').read_text().strip() or p.name=='init.scope':continue
  rows.append({'scope':str(p),'max':(p/'memory.max').read_text().strip(),'current':(p/'memory.current').read_text().strip()})
 except FileNotFoundError:pass
assert all(r['max']!='max' for r in rows)
n=sum(int(r['max']) for r in rows)
print(json.dumps({'scopes':rows,'reserved_bytes':n,'additional_bytes':8589934592,'limit_bytes':55*1024**3}))
assert n+8589934592<=55*1024**3
'''
r=subprocess.run(['ssh',HOST,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True)
(E/'rust-002-reservation.json').write_text(r.stdout)
r=subprocess.run(['ssh',HOST,f'cd {REMOTE} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port3_run_host.py rust-002.json'],capture_output=True,text=True)
(E/'rust-002-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',HOST+':'+REMOTE+'/rust-002',str(E)],check=True)
print(r.stdout);print(r.stderr);raise SystemExit(r.returncode)
