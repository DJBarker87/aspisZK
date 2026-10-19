from pathlib import Path
import importlib.util,json,shutil
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-step-20261016/proofs')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/external-inputs-002.json')
data,_=r.verify_snapshot(base);shutil.copy2(base,w/'external-inputs.json')
order=['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','PublicPreparationActualAudit','ExtractedPublicPreparationSuccess'];modules={}
for name in order:
 f=w/'sources'/(name.replace('.','/')+'.lean')
 source='docs/research/100bit-spend-path-20261013/lean/'+('extracted-public-preparation-20261016/' if name!='ExtractedPublicPreparationSuccess' else '')+str(f.relative_to(w/'sources'))
 modules[name]={'source':source,'source_sha256':r.sha(f),'source_revision':'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af exact step extension / C proof18ad8c915','imports':r.imports(f),'stage_as':str(f.relative_to(w/'sources')),'role':'Exact shared actual constructor/step/preparation cone; no runtime preservation claim','axiom_requests':7 if name=='PublicPreparationActualAudit' else 3 if name=='ExtractedPublicPreparationSuccess' else 0}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':modules,'topological_order':order,'groups':{}});r.staged(w)
print(json.dumps({'snapshot_sha256':r.sha(w/'external-inputs.json'),'sources':modules},indent=2))
