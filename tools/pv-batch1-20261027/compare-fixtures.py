"""Exact fixed-fixture comparison, including durable reservations and error Results."""
from pathlib import Path
import json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch1-20261027')
B=H.parent/'codex-pv-rebase3-20261027/fixtures-candidate';C=H/'fixtures-prover-local'
pins=json.loads((H/'fixture-baseline-pins.json').read_text());rows=[]
def digest(b):return hashlib.sha256(b).hexdigest()
for fixture in ['transfer','withdrawal']:
 paths={'baseline':B/(fixture+'-0'),'candidate':C/(fixture+'-0')}
 records={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()}
 sets={k:{str(x.relative_to(p)) for x in p.rglob('*') if x.is_file() and x.name!='result.json'} for k,p in paths.items()}
 files={}
 for name in sorted(sets['baseline']|sets['candidate']):
  a=(paths['baseline']/name).read_bytes() if name in sets['baseline'] else None
  b=(paths['candidate']/name).read_bytes() if name in sets['candidate'] else None
  files[name]=dict(byte_identical=a==b,baseline_sha256=digest(a) if a is not None else None,candidate_sha256=digest(b) if b is not None else None,baseline_bytes=len(a) if a is not None else None,candidate_bytes=len(b) if b is not None else None)
  if a is not None and b is not None and a!=b:
   files[name]['first64_differing_offsets']=[i for i,(x,y) in enumerate(zip(a,b)) if x!=y][:64]
 pinned={name:files.get(name,{}).get('baseline_sha256')==sha for name,sha in pins[fixture].items()}
 views={k:{n:v for n,v in r.items() if n!='seconds'} for k,r in records.items()}
 rows.append(dict(fixture=fixture,files=files,file_sets_identical=sets['baseline']==sets['candidate'],baseline_pins=pinned,result_metadata_identical=views['baseline']==views['candidate'],baseline_result=views['baseline'],candidate_result=views['candidate'],failure_view='status string in result.json; no separate failure file',excluded_diagnostic_fields=['seconds']))
r=dict(rust_candidate_revision=(H/'candidate/source-revision.txt').read_text().strip(),baseline_source_revision='37794d7bff003fe396b43eb6e264bd9b29f40575',required_baseline_revision='c57a344726745387efb38d1571d885c69ce829ee',baseline_source_binding='fixture-baseline-binding.json',paired_runs=2,passed=all(x['file_sets_identical'] and x['result_metadata_identical'] and all(x['baseline_pins'].values()) and all(v['byte_identical'] for v in x['files'].values()) for x in rows),comparisons=rows)
(H/'fixture-comparison.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2),flush=True);sys.exit(0 if r['passed'] else 2)
