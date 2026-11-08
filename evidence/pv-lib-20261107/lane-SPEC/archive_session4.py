"""Archive retained raw results without running Lean or changing the walker."""
from pathlib import Path
import hashlib,json,lzma
P=Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/evidence')
results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in (P/'out-49794-w3.log').read_text().splitlines() if l.startswith('NEP62_RESULT ')]
assert len(results)==7
files=[P/'raw-audit'/('NEP_pv-thread_'+v['root']+'_REACHABLE.txt') for v in results]
assert all(f.exists() for f in files)
data=json.dumps({f.name:f.read_text() for f in files},sort_keys=True).encode()
(P/'SESSION4_RAW_GRAPH_ARCHIVE.json.xz').write_bytes(lzma.compress(data))
(P/'SESSION4_RAW_GRAPH_ARCHIVE.json.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
(P/'SESSION4_RAW_GRAPH_MANIFEST.json').write_text(json.dumps({'roots':results,'files':[{'name':f.name,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in files]},indent=2)+'\n')
print(json.dumps(results,indent=2))
