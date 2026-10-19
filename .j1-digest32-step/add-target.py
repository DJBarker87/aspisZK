from pathlib import Path
import importlib.util,json
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-step-20261016/proofs')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
p=w/'sources/SOURCE-MANIFEST.json';m=json.loads(p.read_text());name='ExtractedDigest32Transcript';f=w/'sources'/(name+'.lean')
m['modules'][name]={'source':'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean','source_sha256':r.sha(f),'source_revision':'b92ab28465 actual extraction plus new transcript theorem','imports':r.imports(f),'stage_as':name+'.lean','role':'Actual constructor and three-call step equations; full33 caller and runtime remain OPEN','axiom_requests':5}
if name not in m['topological_order']:m['topological_order'].append(name)
r.dump(p,m);r.staged(w)
