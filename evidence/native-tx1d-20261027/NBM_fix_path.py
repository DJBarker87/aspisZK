from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
h.admit('NBM_PATHFIX')
r=h.remote_py(f'''from pathlib import Path
p=Path({(h.B+'/NBM_src/crates/aspis-r1-cost-probe/src/multiproof.rs')!r})
s=p.read_text();assert s.count('mod NBM_copy;')==1
p.write_text(s.replace('mod NBM_copy;', '#[path = "NBM_copy.rs"]\\nmod NBM_copy;'))
''');assert r.returncode==0,r.stderr
cfg=json.loads((E/'NBM_R001.json').read_text());cfg['attempt']='NBM_R002';cfg['command'][2]='NBM_R002';cfg['deps_fingerprint']['graph_receipt']='NBM_R002-graph.json';cfg['expected_time']='optimized native playback test after repairing only the scratch module path; reused native dependency objects'
(E/'NBM_R002.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBM_host.py'),'NBM_R002']);sys.exit(r.returncode)
