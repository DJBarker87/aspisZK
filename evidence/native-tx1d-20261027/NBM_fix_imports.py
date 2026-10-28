from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
h.admit('NBM_IMPORTFIX')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBM_src/crates/aspis-r1-cost-probe/src/NBM_copy.rs")!r}).write_text({(E/"NBM_copy.rs.txt").read_text()!r})');assert r.returncode==0,r.stderr
cfg=json.loads((E/'NBM_R002.json').read_text());cfg['attempt']='NBM_R003';cfg['command'][2]='NBM_R003';cfg['deps_fingerprint']['graph_receipt']='NBM_R003-graph.json';cfg['expected_time']='optimized native K050 playback after adding no_std alloc imports; verbatim test and harness bodies unchanged'
(E/'NBM_R003.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBM_host.py'),'NBM_R003']);sys.exit(r.returncode)
