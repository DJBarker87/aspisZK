from pathlib import Path
import hashlib,importlib.util,json,shutil
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-proof-20261016');P=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-joint-c16-20261016');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py') if not (W/'runner.py').exists() else None;external=json.loads((P/'external-inputs.json').read_text())
removed={'AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs'}
while True:
 more={n for n,x in external['modules'].items() if set(x['imports']) & removed}
 if more<=removed:break
 removed|=more
for n in removed:external['modules'].pop(n,None)
(W/'external-inputs.json').write_text(json.dumps(external,indent=2,sort_keys=True)+'\n') if not (W/'external-inputs.json').exists() else None;(W/'excluded-old-universe.json').write_text(json.dumps({'removed':sorted(removed),'base_snapshot_sha256':sha(P/'external-inputs.json'),'rule':'One coherent extended canonical carrier; prior and reverse importer caches excluded.'},indent=2)+'\n')
spec=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
names=[n for n in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','ExtractedPreparedModel','ExtractedTx1Model','ExtractedTx1Reachability'] if (W/'sources'/(n.replace('.','/')+'.lean')).exists()]
mods={}
for n in names:
 rel=n.replace('.','/')+'.lean';p=W/'sources'/rel;mods[n]={'source':'docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/'+rel,'source_sha256':r.sha(p),'source_revision':'e5c186ba3 actualtx1 + shared canonical carrier','imports':r.imports(p),'stage_as':rel,'role':'Focused shared carrier / exact emitted caller body parameterization; all boundaries explicit; no opaque global axioms','axiom_requests':p.read_text().count('#print axioms')}
r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':names,'groups':{'tx1':names}});r.staged(W);print('Staged '+str(names),flush=True)
