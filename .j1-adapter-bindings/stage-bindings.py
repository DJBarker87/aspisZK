from pathlib import Path
import importlib.util,json
w=Path('/home/dombarker/project-offloads/aspis-r1-j1a-adapter-public-adapted-20261016')
s=importlib.util.spec_from_file_location('r',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
p=w/'sources/SOURCE-MANIFEST.json';d=json.loads(p.read_text());n='ExtractedAdapterWithdrawalBindings';src=w/'sources'/(n+'.lean')
assert n not in d['modules']
for name,row in d['modules'].items():assert r.sha(w/'sources'/row['stage_as'])==row['source_sha256']
(w/'input-manifests').mkdir(exist_ok=True)
r.dump(w/'input-manifests/before-bindings.json',d)
d['modules'][n]={'stage_as':n+'.lean','source':'docs/research/100bit-spend-path-20261013/lean/'+n+'.lean','source_sha256':r.sha(src),'source_revision':'2405d1deba8d61a0410503e9df77b3fe397ebd44 plus new structural metadata theorem','imports':r.imports(src),'role':'Actual terminal-prefix metadata bindings; structural input only, no authentication or stage1 claim','axiom_requests':2}
d['topological_order'].append(n);r.dump(p,d);r.staged(w)
print(json.dumps({'module':n,'sha256':r.sha(src),'imports':d['modules'][n]['imports']},indent=2))
