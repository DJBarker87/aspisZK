"""Source comparison for canonical prerequisites; no equivalence inferred from names."""
from pathlib import Path
import subprocess,json,hashlib,re,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();idx=collections.defaultdict(list)
for p in paths:
 if p.endswith('.lean') and '/sources/' not in p:idx[Path(p).stem].append(p)
idx['PreparedFromQmSourceBridge'].append('docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-source-fromqm-20261020/sources/PreparedFromQmSourceBridge.lean')
G=json.loads((E/'NFY_SOURCE_GRAPH.json').read_text());reuse=json.loads((E/'NFY_CANONICAL_REUSE.json').read_text());records=[]
def choose(n):
 ps=idx[n]
 ps=sorted(ps,key=lambda p:(not p.startswith('lean/'),not p.startswith('evidence/replay-dry8-20261026/'),len(p),p));return ps[0] if ps else None
def raw(p):return subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
def strip(t):return '\n'.join(l for l in t.splitlines() if not l.startswith('import ')).strip()
for n,m in reuse.items():
 a=G[n]['path'] if n in G else choose(n);b=choose(m)
 if not a or not b:records.append(dict(legacy=n,canonical=m,legacy_path=a,canonical_path=b,comparison='source path unavailable; canonical reuse justified only by NFX object pin/scan, not source equality'));continue
 x=raw(a);y=raw(b);same=strip(x.decode())==strip(y.decode())
 records.append(dict(legacy=n,canonical=m,legacy_path=a,canonical_path=b,legacy_sha256=hashlib.sha256(x).hexdigest(),canonical_sha256=hashlib.sha256(y).hexdigest(),non_import_body_identical=same,comparison='byte-identical non-import body' if same else 'distinct canonical proof source; reused admitted result, no legacy-to-canonical equality asserted'))
(E/'NFY_REUSE_PROVENANCE.json').write_text(json.dumps(records,indent=1)+'\n')
print(json.dumps(dict(pairs=len(records),identical=sum(r.get('non_import_body_identical',False) for r in records),different=sum(r.get('non_import_body_identical') is False for r in records))))
