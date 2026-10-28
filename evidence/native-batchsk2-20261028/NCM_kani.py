from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCM_host as h
a=sys.argv[1];harness=sys.argv[2]
assert a.startswith('NCM_K') and not (E/a/'receipt.json').exists()
h.admit(a+'UPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NCM_gate.py")!r}).write_text({(E/"NCM_gate.py").read_text()!r})');assert r.returncode==0,r.stderr
sources=['NCM_src/Cargo.lock','NCM_gate.py','NCM_KMX_copy_stubs.patch','NCM_native.patch','NCM_src/KMX_stubs.rs']+['NCM_src/crates/aspis-r1-cost-probe/src/'+n for n in ['lib.rs','candidate.rs','multiproof.rs','NCM_spy.rs','NCM_candidate.rs','NCM_multiproof.rs']]+['NCM_src/crates/aspis-core/src/state_only_private_merkle.rs']
cfg=dict(attempt=a,kind='kani',sources=sources,command=['python3','NCM_gate.py',a,harness,'--cbmc-args','--unwinding-assertions'],timeout=240,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','TMPDIR':h.B+'/NCM_tmp'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_receipt':a+'-graph.json'},expected_time='optimized cold compilation for first run, then one named native helper byte window SAT step; no SHA or field multiplication')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NCM_host.py'),a]);assert r.returncode==0,'own launch/recovery error; do not resubmit'
r=h.remote_py(f'''from pathlib import Path
import json,hashlib
b=Path({h.B!r});names=[{(a+'-graph.json')!r},{(a+'-metadata.stderr')!r}]
print(json.dumps(dict(files={{n:(b/n).read_text() for n in names if (b/n).is_file()}},lock_now=hashlib.sha256((b/'NCM_src/Cargo.lock').read_bytes()).hexdigest())))''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out['files'].items():(E/n).write_text(s)
(E/(a+'-lock-recovery.json')).write_text(json.dumps(out,indent=2)+'\n')
assert out['lock_now']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','STOP frozen lock drift'
print('lock recovery unchanged',a)
