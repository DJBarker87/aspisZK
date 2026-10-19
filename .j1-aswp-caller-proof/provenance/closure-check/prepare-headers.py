from pathlib import Path
import json,hashlib,importlib.util
W=Path(__file__).resolve().parent;B=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge')
p=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/j1-r17-build-extracted-v2.py');s=importlib.util.spec_from_file_location('r',p);r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
d=json.loads((B/'manifest.json').read_text());pins=d['dependency_pins']|d['new_targets'];rows={}
def visit(n):
 if n not in pins or n in rows:return
 v=pins[n];source=B/v['source_snapshot'];obj=B/v['object_snapshot'];assert r.sha(source)==v['source_sha256'];assert r.sha(obj)==v['object_sha256']
 rows[n]={'source':str(source),'source_sha256':r.sha(source),'object':str(obj),'object_sha256':r.sha(obj),'source_imports':r.imports(source,implicit_init=True)}
 for dep in rows[n]['source_imports']:visit(dep)
for n in ['R1RecordFrameCodec','R1PublicInitFrame','R1TrailingStateFrame']:visit(n)
(W/'header-inputs.txt').write_text(''.join(x['object']+'\n' for x in rows.values()))
(W/'header-source-manifest.json').write_text(json.dumps({'scope':'Candidate project source closure to inspect via actual compiled headers. No producing receipt is inferred.','bridge_manifest_sha256':r.sha(B/'manifest.json'),'modules':rows},indent=2)+'\n')
print('header_inputs',len(rows))
