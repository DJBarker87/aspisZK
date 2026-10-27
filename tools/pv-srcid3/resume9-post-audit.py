#!/usr/bin/env python3
import pathlib,json,subprocess,hashlib,re
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';a=[json.loads(x) for x in (e/'resume9-attempts.jsonl').read_text().splitlines()];assert len(a)==100
expected={};conflicts=[];missing=[]
for r in a[-3:]:
 assert r['accepted']
 for line in r['dependency_objects']:
  if line.startswith('MISSING'):missing.append(line);continue
  sha,p=line.split('  ',1)
  if p in expected and expected[p]!=sha:conflicts.append(p)
  expected[p]=sha
 expected['/home/dombarker/project-offloads/aspis-joint-20261019/objects/'+r['module']+'.olean']=r['object_sha256']
code='''import pathlib,hashlib,json
expected=EXPECTED
m=[]
for name,sha in expected.items():
 p=pathlib.Path(name);got=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 if got!=sha:m.append(dict(path=name,expected=sha,current=got))
print(json.dumps(dict(checked=len(expected),mismatches=m)))
'''.replace('EXPECTED',repr(expected))
p=subprocess.run(['ssh','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);r=json.loads(p.stdout);r.update(conflicting_audit_inputs=conflicts,missing_fingerprint_objects=missing,expected_map_sha256=hashlib.sha256(json.dumps(expected,sort_keys=True).encode()).hexdigest());(e/'resume9-post-audit-object-check.json').write_text(json.dumps(r,indent=2)+'\n');assert not r['mismatches'] and not conflicts and not missing;print('Post-audit input/object hashes unchanged:',r['checked'])
