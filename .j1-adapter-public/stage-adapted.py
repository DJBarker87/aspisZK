from pathlib import Path
import importlib.util,json,shutil
B=Path('/home/dombarker/project-offloads');w=B/'aspis-r1-j1a-adapter-public-adapted-20261016';j=B/'aspis-r1-j1a-adapter-public-joint-20261016';c=B/'aspis-r1-j1a-adapter-reconstruct-20261016/proofs'
s=importlib.util.spec_from_file_location('r',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
base=j/'external-inputs-joint.json';d,_=r.verify_snapshot(base)
removed={n:d['modules'].pop(n) for n in ['AspisR1AdapterReconstruct.Types','AspisR1AdapterReconstruct.FunsExternal','AspisR1AdapterReconstruct.Funs','ExtractedAdapterReconstructSuccess']}
assert not any(dep in removed for v in d['modules'].values() for dep in v['imports'])
assert len(d['roots'])==len({x['name'] for x in d['roots']})
d['provenance_files'][str(base)]=r.sha(base);d['scope']='Prior exact joint snapshot minus only four Adapter-dependent modules. One-sided fourteen-code Error instance naming adapter preserves rust_type, all other attributes, original source and cache. New proofs consume exact computations and fixed carriers.'
r.dump(w/'external-inputs-public.json',d);r.dump(w/'removed-adapter-pins.json',removed)
modules={};order=['AspisR1AdapterReconstruct.Types','AdapterPaymentDiscriminantAudit','AspisR1AdapterReconstruct.FunsExternal','AspisR1AdapterReconstruct.Funs','AdapterReconstructGeneratedAudit','ExtractedAdapterReconstructSuccess','ExtractedAdapterWithdrawalSuccess','ExtractedAdapterCallerBridge','ExtractedAdapterPublicBridge']
m=json.loads((c/'sources/SOURCE-MANIFEST.json').read_text())
for n in order:
 f=w/'sources'/(n.replace('.','/')+'.lean')
 if n in m['modules'] and n!='AspisR1AdapterReconstruct.Types':
  x=m['modules'][n];src=c/'sources'/x['stage_as'];assert r.sha(src)==x['source_sha256'];f.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,f)
 source=('docs/research/100bit-spend-path-20261013/lean/bridge-adapter-public-20261016/AspisR1AdapterReconstruct/Types.lean' if n=='AspisR1AdapterReconstruct.Types' else m['modules'][n]['source'] if n in m['modules'] else 'diagnostic/'+n+'.lean' if n=='AdapterPaymentDiscriminantAudit' else 'docs/research/100bit-spend-path-20261013/lean/'+n+'.lean')
 modules[n]={'stage_as':str(f.relative_to(w/'sources')),'source':source,'source_sha256':r.sha(f),'source_revision':'be46d7790 plus committed e97ac2bb0 and new fixed Adapter/public composition','imports':r.imports(f),'role':'Focused actual computation transport with fixed request/account/candidate carrier','axiom_requests':{'AdapterPaymentDiscriminantAudit':1,'AspisR1AdapterReconstruct.FunsExternal':2,'AdapterReconstructGeneratedAudit':4,'ExtractedAdapterReconstructSuccess':4,'ExtractedAdapterWithdrawalSuccess':1,'ExtractedAdapterCallerBridge':9,'ExtractedAdapterPublicBridge':3}.get(n,0)}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':modules,'topological_order':order,'groups':{}});r.staged(w)
print(json.dumps({'snapshot_sha256':r.sha(w/'external-inputs-public.json'),'targets':order},indent=2))
