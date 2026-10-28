from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
h.admit(sys.argv[1]);payload=json.loads((E/'KMX_all_payload.json').read_text())
# Avoid OS argv limits, preserving the exact source text.
for name,text in payload.items():
 r=h.remote_py('from pathlib import Path\np=Path('+repr(h.B+'/KMX_src/'+name)+')\nif p.is_symlink():p.unlink()\np.write_text('+repr(text)+')\nprint('+repr(name)+')')
 assert r.returncode==0,r.stderr
(E/'KMX_EXTRA_SOURCES.json').write_text(json.dumps(['KMX_src/'+n for n in payload],indent=2)+'\n')
print('installed replay modules and frozen scratch parent overlays',len(payload))
