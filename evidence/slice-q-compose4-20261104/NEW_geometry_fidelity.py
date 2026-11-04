"""Actual frozen inverse native/emitted fidelity; finite checks, never universal credit."""
from NEW_remote import *
import sys,shlex,hashlib
R=E.parent.parent;a=sys.argv[1];bad=sys.argv[2:] == ['bad']
assert a in ['NEW_N003','NEW_N004'] and not (E/a).exists()
active=E/'NEW_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,kind='native')))
admit(a)
ni=['/home/dombarker/.cargo/bin/cargo','run','--manifest-path',B+'/NEW_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NEW_fidelity_target','--features','private-leaf-salts,optimized-terminal,program-build','--release','-j','1','--example','NEW_geometry']
if bad:ni += ['--','--bad']
cfg=dict(attempt=a,kind='native',target='actual QueryGeometry::for_range native/emitted fidelity'+(' wrong-result control' if bad else ''),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=['NEW_gate.py','NEW_graph.py','NEW_TOOL_PINS.json','NEW_SOURCE_PINS.json','NEW_src/Cargo.lock','NEW_src/Cargo.toml','NEW_src/crates/aspis-core/Cargo.toml','NEW_src/crates/aspis-core/src/field.rs','NEW_src/crates/aspis-core/src/lib.rs','NEW_src/crates/aspis-r1-cost-probe/src/verifier.rs','NEW_src/crates/aspis-r1-cost-probe/src/fast_domain.rs','NEW_src/crates/aspis-r1-cost-probe/Cargo.toml','NEW_src/crates/aspis-r1-cost-probe/examples/NEW_geometry.rs'],command=['python3','NEW_gate.py',a+'.json'],native_command=ni,timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OPT_LEVEL='3',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEW_tmp'),deps_fingerprint=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),expected_time='Optimized core/example compilation followed by seven geometry translator-fidelity fixtures, all rows/lanes, empty and Query error branches; no Kani or arithmetic proof')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
upload(a,{a+'.json':json.dumps(cfg),'NEW_gate.py':(E/'NEW_gate.py').read_text(),'NEW_graph.py':(E/'NEW_graph.py').read_text(),'NEW_TOOL_PINS.json':(E/'NEW_TOOL_PINS.json').read_text()})
r=ssh(a,'cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-graph.stderr',a+'-lock-check.json',a+'-source-check.json',a+'-tool-check.json']
r=ssh(a,'python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {names!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'NEW_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
subprocess.run([sys.executable,str(E/'NEW_recover_sources.py'),a],check=True)
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print((E/a/'stdout.log').read_text()[-1500:]);sys.exit(rc['exit_status'])
