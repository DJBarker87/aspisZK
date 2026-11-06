"""Retain exact positive/control receipts; no theorem or row is inferred."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
pairs=[(9,10),(11,12),(13,14),(15,16),(17,19),(20,21),(22,23),(24,25),(26,27),(31,32),(34,35),(38,39),(41,42)]
out=[]
for pos,neg in pairs:
 ids=[f'NKE_K{n:03}' for n in [pos,neg]]
 rows=[json.loads((E/i/'receipt.json').read_text()) for i in ids]
 assert rows[0]['exit_status']==0 and rows[1]['exit_status']==1,ids
 assert rows[0]['source_hashes']==rows[1]['source_hashes'],ids
 for i,r in zip(ids,rows):
  graph=json.loads((E/(i+'-graph-check.json')).read_text());lock=json.loads((E/(i+'-lock-check.json')).read_text())
  assert graph['graph_matches_frozen'] and lock['unchanged'],i
  assert r['swaps']=='0'
 out.append(dict(positive=ids[0],control=ids[1],harness=rows[0]['module'],source_hashes=rows[0]['source_hashes'],positive_wall=rows[0]['wall_seconds'],control_wall=rows[1]['wall_seconds']))
(E/'NKE_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=out,kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',row_credit=False),indent=2)+'\n')
print(json.dumps(dict(matched_pairs=len(out),source_pairs_equal=True,frozen_graphs=True,unchanged_locks=True)))
