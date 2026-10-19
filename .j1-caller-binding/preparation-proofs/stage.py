from pathlib import Path
import importlib.util,json,shutil
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016/proofs-original')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/external-inputs-002.json')
data,_=r.verify_snapshot(base);shutil.copy2(base,w/'external-inputs.json')
order=['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','PublicPreparationActualAudit'];modules={}
for name in order:
 f=w/'sources'/(name.replace('.','/')+'.lean')
 modules[name]={'source':'docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-20261016/'+str(f.relative_to(w/'sources')),'source_sha256':r.sha(f),'source_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af exact emitted cut','imports':r.imports(f),'stage_as':str(f.relative_to(w/'sources')),'role':'Original generated helper cone; derived Debug functions excluded from standard-axiom claims','axiom_requests':5 if name=='PublicPreparationActualAudit' else 0}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':modules,'topological_order':order,'groups':{}});r.staged(w)
print(json.dumps({'snapshot_sha256':r.sha(w/'external-inputs.json'),'sources':modules},indent=2))
