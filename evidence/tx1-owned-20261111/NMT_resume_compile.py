"""Serial focused compiler for resumed modules; preserves every failed scope."""
from NMT_formal import run,E
import json,sys,hashlib
for m in sys.argv[1:]:
 rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()
 same=[r for r in rows if r.get('module')==m and h in r.get('source_hashes',{}).values()]
 if same:
  if same[-1]['exit_status']==0:continue
  raise RuntimeError('Unchanged failed source refused: '+m)
 n=max(int(r['attempt'][-3:])for r in rows if r.get('attempt','').startswith('NMT_L') and 'exit_status'in r)+1
 assert 61<=n<=310
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:break
