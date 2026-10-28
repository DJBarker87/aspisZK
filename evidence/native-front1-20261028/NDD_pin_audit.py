import sys
sys.dont_write_bytecode=True
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front1-20261028'
rows=[json.loads(l) for l in (E/'NDD_ATTEMPTS.jsonl').read_text().splitlines()]
latest={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=r
accepted={};imports=[];prints=[]
for m,r in latest.items():
 if m in ['NDD_Inspect','NDD_Resolve','NDD_Audit']:continue
 p=E/(m+'.lean');sha=r['source_hashes']['NDD_generated/'+m+'.lean']
 assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha,('active source differs',m)
 accepted[m]=dict(source_sha256=sha,attempt=r['attempt'])
 imports.append('import '+m.replace('/','.'))
 ns=re.findall(r'^namespace (NDD_[\w.]+)',p.read_text(),re.M)
 for name in re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem (\w+)',p.read_text(),re.M):
  assert ns,(m,name)
  prints.append('#print axioms '+ns[0]+'.'+name)
required={p.stem for p in E.glob('NDD_*.lean') if p.stem not in ['NDD_Inspect','NDD_Resolve','NDD_Audit'] and re.search(r'^(?:@\[[^\n]*\]\s*)?theorem ',p.read_text(),re.M)}
assert required <= set(accepted),('unfinished Lean modules',sorted(required-set(accepted)))
(E/'NDD_Audit.lean').write_text('\n'.join(imports+prints)+'\n')
x=dict(B=B,accepted=accepted,initial=json.loads((E/'NDD_SOURCE.json').read_text()))
code='''from pathlib import Path
import json,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);c=b.parent/'codex-cx-sound-int2-20261025';cache=b.parent/'codex-cx-front1-cache-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selected={};sources={}
def pin(p):
 assert p.is_file(),str(p)
 selected[str(p)]=dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
for p,h in x['initial']['library'].items():
 p=Path(p);assert sha(p)==h,str(p);pin(p)
for old,v in x['initial']['cache_imports'].items():
 old=Path(old);folder=next(t for t in old.parents if t.name in ['codex-cx-cpilot-cache-20261028','codex-cx-leaf-cache-20261027'])
 p=cache/old.relative_to(folder);assert sha(p)==v['selected_sha256'],str(p);pin(p)
for m,v in x['accepted'].items():
 src=b/'NDD_generated'/(m+'.lean');assert sha(src)==v['source_sha256'],m
 pin(b/'NDD_objects'/(m+'.olean'));sources[m]=dict(path=str(src),sha256=sha(src))
models=['AspisR1SemanticCallExtraction/Funs','RawPoseidonExtensionSlice','JFv_RawExtractedSemanticCallOpsV20','S1M31EmbeddingSourceV1','AspisR72Sampler/Funs','AspisR1SelectedMaskProbe/Funs','FIq_Native01','FIq_Native02','FIo_NativeFuns','FIn_WeightsFuns','WeightsFieldExplicitDecoder','KMX_CopyMeaning','ExtractedMaskReducerOps','ExtractedMaskM31AddSub']
for m in models:
 obj=next((root/(m+'.olean') for root in [b/'NDD_objects',cache,c,c/'objects'] if (root/(m+'.olean')).is_file()),None)
 assert obj is not None,m
 pin(obj)
 src=next((root/(m+'.lean') for root in [c,c/'sources'] if (root/(m+'.lean')).is_file()),None)
 sources[m]=dict(path=str(src),sha256=sha(src)) if src else dict(source='inherited coherent workspace; source manifest below')
receipts={}
for n in ['object-source-manifest.json','final-closure-manifest.json','canonical-source-check.json']:
 p=c/n
 if p.is_file():receipts[str(p)]=dict(sha256=sha(p),bytes=p.stat().st_size)
tools={}
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),b.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon',b.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon-driver',b.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended']:
 tools[str(p)]=dict(sha256=sha(p),bytes=p.stat().st_size)
llbc=b/'NDD_reference.llbc'
print(json.dumps(dict(selected_objects=selected,sources=sources,coherent_manifests=receipts,tools=tools,llbc=dict(path=str(llbc),sha256=sha(llbc),bytes=llbc.stat().st_size))))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NDD_AUDIT_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'NDD_ACCEPTED_MODULES.json').write_text(json.dumps(accepted,indent=2)+'\n')
print(json.dumps(dict(modules=len(accepted),top_theorems=len(prints),selected_objects=len(out['selected_objects']))))
