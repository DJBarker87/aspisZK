from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
old=E.parents[1]/'evidence/native-tx1c-20261027/NBJ_gate.py'
s=old.read_text().replace('NBJ_','NBM_');(E/'NBM_gate.py').write_text(s)
h.admit('NBM_REPROUPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBM_gate.py")!r}).write_text({s!r})');assert r.returncode==0,r.stderr
cfg=json.loads((E/'NBM_R003.json').read_text());cfg.update(attempt='NBM_K001',kind='kani',command=['python3','NBM_gate.py','NBM_K001','multiproof::NBM_copy::NBJ_count_copy_prefix','-Z','concrete-playback','--concrete-playback','print'],expected_time='optimized verification codegen then minimal copy-harness diagnostic; no bridge credit; not a timed-out shape')
cfg['sources'][-1]='NBM_gate.py';cfg['deps_fingerprint']['graph_receipt']='NBM_K001-graph.json'
(E/'NBM_K001.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBM_host.py'),'NBM_K001']);sys.exit(r.returncode)
