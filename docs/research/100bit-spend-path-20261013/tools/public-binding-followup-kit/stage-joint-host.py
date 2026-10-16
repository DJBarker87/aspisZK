#!/usr/bin/env python3
"""Stage the exact changed Types/Funs and only their six C dependents."""
from pathlib import Path
import hashlib,importlib.util,json,shutil
B=Path('/home/dombarker/project-offloads')
P=B/'aspis-r1-public-binding-followup-20261016';W=B/'aspis-r1-public-binding-joint-c16-20261016'
W.mkdir(exist_ok=True);(W/'sources').mkdir(exist_ok=True)
shutil.copy2(P/'runner.py',W/'runner.py')
external=json.loads((P/'external-inputs.json').read_text())
removed={'AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs'}
while True:
 additional={n for n,x in external['modules'].items() if set(x['imports']) & removed}
 if additional <= removed:break
 removed |= additional
for n in removed:external['modules'].pop(n,None)
(W/'excluded-old-universe.json').write_text(json.dumps({'removed_reverse_import_closure':sorted(removed),'base_snapshot_sha256':hashlib.sha256((P/'external-inputs.json').read_bytes()).hexdigest(),'reason':'Old universe objects and every reverse importer are excluded; changed current universe is produced only by staged fresh targets.'},indent=2)+'\n')
(W/'external-inputs.json').write_text(json.dumps(external,indent=2,sort_keys=True)+'\n')
spec=importlib.util.spec_from_file_location('runner',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
names=['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','ExtractedPublicPreparationSuccess','ExtractedPreparationSerializerFields','ExtractedPreparationSerializerLoop','ExtractedPreparationSerializerWhole','ExtractedPublicPreparationBinding','ExtractedFirstCallerReachability']
mods={}
for n in names:
 relative=n.replace('.','/')+'.lean';s=W/'sources'/relative;assert s.is_file(),s
 prefix='lean/bridge-public-callers-c16-20261016/' if n.startswith('AspisR1PublicPreparation.') else 'lean/'
 mods[n]={'source':'docs/research/100bit-spend-path-20261013/'+prefix+relative,'source_sha256':r.sha(s),'source_revision':'162f2a4d0 + c16ab4d76 shared callers emission','imports':r.imports(s),'stage_as':relative,'role':'Single coherent current callers universe; original79declarations token-identical;6Cdependents refreshed for changed import objects','axiom_requests':s.read_text().count('#print axioms')}
r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':names,'groups':{'c_joint':names}})
r.staged(W)
print('Staged2currentemissions+6Cdependents; external cache retained exactly; no compiler invoked')
