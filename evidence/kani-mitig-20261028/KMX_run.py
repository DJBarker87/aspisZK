from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
a=sys.argv[1];kind=sys.argv[2];cmd=sys.argv[3:]
count=len(list(E.glob('KMX_K[0-9][0-9][0-9].json')))
assert kind!='kani' or count<80,'Kani budget exhausted'
assert not (E/(a+'.json')).exists(),'attempt already submitted/configured'
sources=['KMX_src/Cargo.lock','KMX_gate.py']+[str(x.relative_to(E)) for x in E.glob('KMX_*.rs.txt')]
# host snapshots actual Rust files, not local transport names
sources=['KMX_src/Cargo.lock','KMX_gate.py']+['KMX_src/crates/aspis-r1-cost-probe/src/'+x.name[:-4] for x in E.glob('KMX_*.rs.txt')]
if (E/'KMX_EXTRA_SOURCES.json').exists():sources=list(dict.fromkeys(sources+json.loads((E/'KMX_EXTRA_SOURCES.json').read_text())))
cfg=dict(attempt=a,kind=kind,sources=sources,command=cmd,timeout=600,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_TEST_OPT_LEVEL':'3','CARGO_PROFILE_TEST_DEBUG':'0','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_TEST_OVERFLOW_CHECKS':'true','TMPDIR':h.B+'/KMX_tmp'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_receipt':a+'-graph.json'},expected_time='optimized focused copy controls; codegen then named CBMC property; no leaf claim')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'KMX_host.py'),a]);sys.exit(r.returncode)
