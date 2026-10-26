"""Read-only check of every inherited direct dependency object at its actual path."""
from pathlib import Path
import json,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1];reuse=json.loads((E/'RPz3_reuse.json').read_text());pins=collections.defaultdict(dict);edges=[]
for m,rel in reuse['receipts'].items():
 if reuse['state'][m]!='passed':continue
 for n,pin in json.loads((R/rel).read_text())['deps_fingerprint']['selected_objects'].items():
  want={k:pin[k] for k in ['sha256','bytes']};pins[pin['path']][pin['sha256']]=want;edges.append({'module':m,'dependency':n,**pin})
payload='''from pathlib import Path
import hashlib,json
paths=json.loads(%r);actual={}
for f in paths:
 p=Path(f)
 actual[f]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} if p.is_file() else None
print(json.dumps(actual))
'''%json.dumps(list(pins))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr
actual=json.loads(r.stdout);bad=[e for e in edges if actual[e['path']]!={k:e[k] for k in ['sha256','bytes']}]
out={'checked_direct_edges':len(edges),'unique_actual_paths':len(actual),'conflicting_expected_hashes':{p:list(v) for p,v in pins.items() if len(v)>1},'mismatches':bad,'actual_objects':actual,'qualification':'Actual dependency paths are hashed on the host, including copied trusted library paths rather than assuming their source-path names coincide. No prover invocation.'}
(E/'RPz3_deps-reuse-check.json').write_text(json.dumps(out,indent=2)+'\n');print('edges',len(edges),'paths',len(actual),'conflicts',len(out['conflicting_expected_hashes']),'mismatches',len(bad))
