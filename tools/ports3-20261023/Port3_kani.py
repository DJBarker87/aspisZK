#!/usr/bin/env python3
"""Capped optimized host Kani; private sources and inherited native pins."""
import pathlib,json,subprocess,shlex,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[2];T=R/'tools/ports3-20261023';E=R/'evidence/ports3-20261023'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
crate,harness=sys.argv[1:]; n=1+max((int(p.stem.split('-')[1]) for p in T.glob('kani-*.json')),default=0);assert n<=60
a=f'kani-{n:03d}'
pins=json.loads((E/'rust-002/receipt.json').read_text())['deps_fingerprint']['source_snapshot_pins']
check='from pathlib import Path;import hashlib,json;r=Path('+repr(B+'/src')+');p='+repr(pins)+';bad=[k for k,v in p.items() if hashlib.sha256((r/k).read_bytes()).hexdigest()!=v];print(json.dumps({"checked":len(p),"mismatches":bad}));assert not bad'
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(check)],capture_output=True,text=True,check=True);(E/f'{a}-source-validation.json').write_text(r.stdout)
c={'attempt':a,'kind':'kani','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
'command':['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',crate+'/Cargo.toml','--lib','--exact','--harness',harness,'-Z','function-contracts','-Z','stubbing','--no-assertion-reach-checks','--solver','kissat','--output-format','old','-Z','unstable-options','--cbmc-args','--object-bits','16','--unwinding-assertions'],
'sources':[crate+'/Cargo.toml',crate+'/src/lib.rs'],'timeout':240,
'env':{'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR':B+'/kani-target','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','RUSTFLAGS':'-C link-arg=-Wl,--threads=4'},
'deps_fingerprint':{'source_snapshot_pins':pins},'expected_time':'Optimized Kani compilation, then symbolic native writer serialization and ordered pointer/length digest checks. No dense field elimination.'}
p=T/f'{a}.json';p.write_text(json.dumps(c,indent=2)+'\n')
subprocess.run(['ssh',H,'mkdir -p '+B+'/'+crate+'/src'],check=True)
for rel in ['Cargo.toml','src/lib.rs']:
 subprocess.run(['scp','-q',str(T/crate/rel),H+':'+B+'/'+crate+'/'+rel],check=True)
subprocess.run(['scp','-q',str(p),str(T/'Port3_run_host.py'),H+':'+B+'/'],check=True)
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
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True);(E/f'{a}-reservation.json').write_text(r.stdout)
r=subprocess.run(['ssh',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port3_run_host.py {a}.json'],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
