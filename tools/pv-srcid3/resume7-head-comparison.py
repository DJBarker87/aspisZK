#!/usr/bin/env python3
import json,pathlib,subprocess,hashlib,io
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';d=json.loads((e/'resume7-plan.json').read_text());rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip();rows=[r for r in d['rows'] if r['research_source_exists']]
query=''.join(rev+':'+r['research_source_path']+'\n' for r in rows)
b=subprocess.check_output(['git','cat-file','--batch'],input=query.encode());s=io.BytesIO(b);out=[]
for r in rows:
 header=s.readline().decode().split()
 if header[-1]=='missing':data=None
 else:data=s.read(int(header[-1]));assert s.read(1)==b'\n'
 sha=hashlib.sha256(data).hexdigest() if data is not None else None
 out.append(dict(module=r['module'],path=r['research_source_path'],pinned_sha256=r['research_source_sha256'],current_head_sha256=sha,matches_pin=sha==r['research_source_sha256']))
result=dict(pinned_research_revision=d['research_revision'],current_research_head=rev,existing_sources=out,changed=[x for x in out if not x['matches_pin']])
(e/'resume7-current-head-comparison.json').write_text(json.dumps(result,indent=2)+'\n');print('HEAD',rev,'sources',len(rows),'changed',len(result['changed']))
