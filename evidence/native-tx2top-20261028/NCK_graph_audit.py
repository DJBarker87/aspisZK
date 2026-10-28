from pathlib import Path
import json,lzma,subprocess,tomllib
from NCK_graph import exact_graph
E=Path(__file__).resolve().parent
f=tomllib.loads(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock']).decode())
seen={}
for line in (E/'NCK_K_TRANSPORT.jsonl').read_text().splitlines():
 r=json.loads(line);o=r['stdout']
 if isinstance(o,dict):o=lzma.decompress((E/o['artifact']).read_bytes()).decode()
 if r['exit']!=0 or not o.startswith('{') or '"packages"' not in o:continue
 m=next(json.loads(l) for l in o.splitlines() if l.startswith('{'))
 seen[r['attempt']]=exact_graph(m,f)
(E/'NCK_GRAPH_RETROSPECTIVE.json').write_text(json.dumps(seen,indent=2)+'\n')
print('exact graph audits',len(seen),'canonical hashes',len({r['canonical_graph_sha256'] for r in seen.values()}))
