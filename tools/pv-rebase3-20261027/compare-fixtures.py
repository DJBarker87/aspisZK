from pathlib import Path
import json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-rebase3-20261027');rows=[]
for fixture in ['transfer','withdrawal']:
 paths={k:H/('fixtures-'+k)/(fixture+'-0') for k in ['research','candidate']}
 records={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()}
 files={}
 for name in ['public.bin','proof.bin']:
  a=(paths['research']/name).read_bytes();b=(paths['candidate']/name).read_bytes()
  files[name]=dict(byte_identical=a==b,research_sha256=hashlib.sha256(a).hexdigest(),candidate_sha256=hashlib.sha256(b).hexdigest(),research_bytes=len(a),candidate_bytes=len(b))
 equal={k:records['research'].get(k)==records['candidate'].get(k) for k in ['status','callbacks','attempts','audit']}
 rows.append(dict(fixture=fixture,files=files,returned_fields_equal=equal,records=records))
r=dict(revisions={k:(H/k/'source-revision.txt').read_text().strip() for k in paths},passed=all(all(x['returned_fields_equal'].values()) and all(v['byte_identical'] for v in x['files'].values()) for x in rows),comparisons=rows)
(H/'fixture-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));sys.exit(0 if r['passed'] else 2)
