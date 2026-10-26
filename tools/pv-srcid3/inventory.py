#!/usr/bin/env python3
"""Read generated metadata, retaining exact harness attributes and file pins."""
import hashlib,json,pathlib,subprocess,sys
job='/home/dombarker/project-offloads/codex-pv-srcid-20261026'
remote='''import hashlib,json,pathlib
rows=[]
for p in pathlib.Path(JOB+'/kani-target').rglob('*.kani-metadata.json'):
 x=json.loads(p.read_text())
 for h in x.get('proof_harnesses',[]):
  if 'pv_srcid3' in h['pretty_name']:
   rows.append(dict(metadata_path=str(p),metadata_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),harness=h))
print(json.dumps(rows,indent=2))
'''.replace('JOB',repr(job))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,capture_output=True,text=True,check=True)
a=json.loads(r.stdout);assert len(a)>=9
for x in a:
 attrs=x['harness']['attributes'];assert attrs['stubs']==[] and attrs['verified_stubs']==[]
p=pathlib.Path('evidence/pv-srcid3-20261026/harness-inventory-refreshed.json');p.write_text(r.stdout)
print('\n'.join(f"{x['harness']['pretty_name']} unwind={x['harness']['attributes']['unwind_value']} stubs=[]" for x in a))
