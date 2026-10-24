#!/usr/bin/env python3
"""Static audit: current native spans, final proof receipts, caps and budget."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((E/'aeneas-004/sources/Port3_StageChildren.llbc').read_text())['translated']
rows=[]
for v in p['fun_decls']:
 if not v:continue
 text=v['item_meta'].get('source_text')
 if not text:continue
 files=[q for q in [R/'crates/aspis-r1-cost-probe/src/verifier.rs',R/'crates/aspis-r1-cost-probe/src/candidate.rs'] if text in q.read_text()]
 if not files:continue
 rows.append({'name':str(v['item_meta']['name']),'body_kind':'opaque' if v['body']=='Opaque' else 'emitted','source':str(files[0].relative_to(R)),'source_text_sha256':hashlib.sha256(text.encode()).hexdigest(),'source_text_bytes':len(text.encode())})
assert any('fn new(weights:&[K])' in (v['item_meta'].get('source_text') or '') and v['body']!='Opaque' for v in p['fun_decls'] if v)
assert not re.search(r'\bsorry\b',(E/'current-children/Funs.lean').read_text())
receipts=[json.loads(q.read_text()) for q in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
assert len(list(E.glob('kani-*/receipt.json')))<=60
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits
 if r['exit_status']==0:
  assert not any(x in '\n'.join(r['print_axioms']) for x in ['sorryAx','Lean.ofReduceBool','Lean.trustCompiler'])
final=[]
for src in sorted(L.glob('Port3_*.lean')):
 matches=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(src.name)==sha(src)]
 assert matches,src
 final.append({'module':src.stem,'sha256':sha(src),'receipt':matches[-1]['attempt']})
original=json.loads((E/'source-normalization.json').read_text())
for path,value in original['current_source_pins'].items():assert sha(R/path)==value,path
native=(R/'tools/ports3-20261023/pending-reached/src/lib.rs').read_text()
function=next(v['item_meta']['source_text'] for v in p['fun_decls'] if v and 'fn new(weights:&[K])' in (v['item_meta'].get('source_text') or ''))
assert function in native
emissions=[]
for stem,module,key in [('pending','Port3_NativePendingBody','generated_funs_sha256'),('batch','Port3_NativeBatchBody','source_sha256'),('geometry','Port3_NativeGeometryBody','source_sha256'),('query','Port3_NativeQueryBody','source_sha256'),('finish','Port3_NativeFinishBody','source_sha256'),('flush','Port3_NativeFlushBody','source_sha256')]:
 emission=json.loads((E/(stem+'-current-emission.json')).read_text())
 if key not in emission:
  key=next(k for k in emission if k.endswith('funs_sha256'))
 assert sha(E/'current-children/Funs.lean')==emission[key],stem
 assert sha(L/(module+'.lean'))==emission['module_sha256'],stem
 emissions.append({'stage':stem,'metadata':emission})
manifest={'schema':'ports3-continuation2-focused-proof-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'actual_lean_compiles':len(receipts),'kani_runs':len(list(E.glob('kani-*/receipt.json'))),'reserved_ids_without_lean':[q.stem for q in (R/'tools/ports3-20261023').glob('lean-*.json') if not (E/q.stem/'receipt.json').exists()],'native_spans':rows,'emissions':emissions,'accepted_final_modules':final,'limits':limits,'source_change_assessment':'No shipped changes, features, wire format, protocol parameters or ELF changes. Current parent query/row control is checked with an explicit S7 owned-push child; native push and flush mutable-std lowering plus owner arithmetic/prepare/model ports remain open. Checkpoint8/18 remain reference; no native all-nine closure or S2 target claim.','validation':'Focused cached modules only; no full frozen replay. Failed elaborations and timed-out Kani receive no proof credit.','elf_pins_inherited':['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']}
(E/'continuation2.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS',len(final),'final modules;',len(receipts),'actual Lean compiles;',manifest['kani_runs'],'Kani runs; current spans/caps/axioms/shipped pins')
