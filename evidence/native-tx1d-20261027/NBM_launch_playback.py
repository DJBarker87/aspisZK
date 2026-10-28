from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
h.admit('NBM_PLAYBACKUPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBM_playback.py")!r}).write_text({(E/"NBM_playback.py").read_text()!r})');assert r.returncode==0,r.stderr
cfg=dict(attempt='NBM_R001',kind='rust',sources=['NBM_src/Cargo.lock','NBM_src/crates/aspis-r1-cost-probe/src/multiproof.rs','NBM_src/crates/aspis-r1-cost-probe/src/NBM_copy.rs','NBM_playback.py'],command=['python3','NBM_playback.py','NBM_R001','multiproof::NBM_copy::kani_concrete_playback_NBJ_count_copy_prefix_8053088788365222636'],timeout=240,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_TARGET_DIR':h.B+'/NBM_target','CARGO_PROFILE_TEST_OPT_LEVEL':'3','CARGO_PROFILE_TEST_DEBUG':'0','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_TEST_OVERFLOW_CHECKS':'true','TMPDIR':h.B+'/NBM_tmp'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','trace':'verbatim NBJ_K050 generated test and harness; module name NBM_copy','graph_receipt':'NBM_R001-graph.json'},expected_time='optimized native playback-test compilation, then one generated K050 trace; no solver')
(E/'NBM_R001.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBM_host.py'),'NBM_R001']);sys.exit(r.returncode)
