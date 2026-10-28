from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
a=sys.argv[1];harness=sys.argv[2]
cfg=dict(attempt=a,kind='kani',sources=['KDX_src/Cargo.lock','KDX_src/crates/aspis-r1-cost-probe/src/multiproof.rs','KDX_src/crates/aspis-r1-cost-probe/src/KDX_copy.rs','KDX_gate.py'],command=['python3','KDX_gate.py',a,harness]+sys.argv[3:],timeout=240,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_TARGET_DIR':h.B+'/KDX_target','CARGO_PROFILE_TEST_OPT_LEVEL':'3','CARGO_PROFILE_TEST_DEBUG':'0','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_TEST_OVERFLOW_CHECKS':'true','TMPDIR':h.B+'/KDX_tmp'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_receipt':a+'-graph.json'},expected_time='optimized Kani codegen then focused copy diagnostic; no bridge claim')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'KDX_host.py'),a]);sys.exit(r.returncode)
