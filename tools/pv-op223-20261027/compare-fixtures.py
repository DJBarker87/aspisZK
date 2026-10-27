from pathlib import Path
import json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-op223-20261027');rows=[]
for fixture in ['transfer','withdrawal']:
 paths={'research':Path('/home/dombarker/project-offloads/codex-pv-rebase-20261026/fixtures-candidate')/(fixture+'-0'),'candidate':H/'fixtures-candidate'/(fixture+'-0')}
 records={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()}
 files={}
 for name in ['public.bin','proof.bin']:
  a=(paths['research']/name).read_bytes();b=(paths['candidate']/name).read_bytes()
  files[name]=dict(byte_identical=a==b,research_sha256=hashlib.sha256(a).hexdigest(),candidate_sha256=hashlib.sha256(b).hexdigest(),research_bytes=len(a),candidate_bytes=len(b))
 equal={k:records['research'].get(k)==records['candidate'].get(k) for k in ['status','callbacks','attempts','audit']}
 ledgers={k:{p.name:p.read_bytes() for p in (v/'ledger').iterdir()} for k,v in paths.items()}
 equal['ledger_files_bytes']=ledgers['research']==ledgers['candidate']
 rows.append(dict(fixture=fixture,files=files,returned_fields_equal=equal,records=records))
r=dict(revisions={'research':(H/'baseline/source-revision.txt').read_text().strip(),'candidate':(H/'source-revision.txt').read_text().strip()},passed=all(all(x['returned_fields_equal'].values()) and all(v['byte_identical'] for v in x['files'].values()) for x in rows),comparisons=rows)
(H/'fixture-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));sys.exit(0 if r['passed'] else 2)
