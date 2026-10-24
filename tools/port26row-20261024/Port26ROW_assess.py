#!/usr/bin/env python3
"""Read-only association and receipt checks; no native/build identity gate."""
from pathlib import Path
import hashlib,json,re,subprocess,time
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port26row-20261024'
L=R/'docs/research/100bit-spend-path-20261013/lean'; old=R/'evidence/port23push-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
script=R/'tools/port23push-20261024/Port23PUSH_audit.py'
s=script.read_text().replace("E=R/'evidence/port23push-20261024'", "E=R/'evidence/port26row-20261024'")
s=s.replace("j=json.loads((E/'Port23PUSH.llbc')", "j=json.loads((old/'Port23PUSH.llbc')")
s=s.replace("pins=json.loads((E/'source-pins.json')", "pins=json.loads((old/'source-pins.json')")
s=s.replace("p=E/'Port23PUSH-generated'/name", "p=old/'Port23PUSH-generated'/name")
s=s.replace('script_sha256=sha(pathlib.Path(__file__).read_bytes())','script_sha256=sha(script.read_bytes())')
exec(compile(s,str(script),'exec'),dict(__file__=str(script),old=old,script=script))
a=json.loads((E/'source-audit.json').read_text())
a['uninstantiated_parametric_row_equals_owned']=a.pop('actual_mutable_to_owned_equality')
a['port26_specialized_content_row_equality']=dict(established=True,theorem='Port26ROW.row_complete',receipt='lean-007/receipt.json')
a['audit_scope']='Inherited exact source/emission audit plus separately accepted Port26 content-instance equality; no native effect or identity claim.'
(E/'source-audit.json').write_text(json.dumps(a,indent=2)+'\n')
j=json.loads((old/'Port23PUSH.llbc').read_text())
def walk(x):
 if isinstance(x,dict):
  yield x
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
fs={f['def_id']:f for f in j['translated']['fun_decls'] if f}
calls=[x['Call']['call'] for x in walk(fs[3]['body']) if 'Call' in x]
call=next(c for c in calls if c['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')==14)
assert call['func']['Regular']['generics']['const_generics'][0]['kind']['Literal']['Scalar']['Unsigned']==['Usize','4']
types={}
for x in walk(j):
 if 'HashConsedValue' in x:
  k,v=x['HashConsedValue'];types[k]=v
def resolve(x,seen=()):
 if isinstance(x,dict):
  if 'Deduplicated' in x:
   k=x['Deduplicated']
   return resolve(types[k],seen+(k,)) if k in types and k not in seen else x
  return {k:resolve(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [resolve(v,seen) for v in x]
 return x
call_resolved=resolve(call)
graph=json.loads((old/'std-source-graph-focused.json').read_text())
hits=[]
for f in graph['files']:
 if any(x in f['path'] for x in ['core/src/array/mod.rs','core/src/slice/mod.rs','core/src/slice/iter.rs']):
  for h in f['hits']:
   if h['needle'] in ['fn into_iter(self) -> IterMut','pub const fn iter_mut(',"pub(super) const fn new(slice: &'a mut [T])"]:
    hits.append(dict(path=f['path'],whole_sha256=f['sha256'],**h))
accepted={}; attempts=[]
for p in sorted(E.glob('lean-*')):
 c=json.loads((p/'receipt.json').read_text()); attempts.append(c)
 assert json.loads((p/'integrity-pre.json').read_text())==json.loads((p/'integrity-go.json').read_text())==json.loads((p/'integrity-post.json').read_text())
 assert sha(p/'source.lean.txt')==c['source_sha256']
 if c['exit_status']==0:
  assert not any('sorryAx' in a for a in c['print_axioms'])
  for a in c['print_axioms']:
   if 'depends on axioms:' in a:
    ax=a.split('depends on axioms: [')[1].rstrip(']').split(', ')
    assert set(ax)<={'propext','Classical.choice','Quot.sound'}
  assert sha(L/(c['module']+'.lean'))==c['source_sha256']
  obj=Path(c['argv'][c['argv'].index('-o')+1]);assert sha(obj)==c['object_sha256']
  for d in c['dependencies']:
   assert sha(Path(d['object_path']))==d['object_sha256']
   if d['source_sha256']:assert sha(L/(d['module'].replace('.','/')+'.lean'))==d['source_sha256']
  accepted[c['module']]=dict(attempt=c['attempt'],source_sha256=c['source_sha256'],object_sha256=c['object_sha256'],dependencies=c['dependencies'])
assert len(attempts)==8
assert [a['exit_status'] for a in attempts]==[0,1,0,1,1,0,0,0]
for name,run in [('Port25ARRAY_Std','lean-001'),('Port25ARRAY_Lane','lean-003')]:
 c=json.loads((R/'evidence/port25array-20261024'/run/'receipt.json').read_text())
 assert sha(L/(name+'.lean'))==c['source_sha256']
 assert sha(Path('/tmp/port25array-20261024-objects')/(name+'.olean'))==c['object_sha256']
 for d in c['dependencies']:
  assert sha(Path(d['object_path']))==d['object_sha256']
  if d['source_sha256']:assert sha(L/(d['module']+'.lean'))==d['source_sha256']
for f in L.glob('Port26ROW_*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',f.read_text())
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000
out=dict(schema='Port26ROW-source-assessment-v1',command='python3 tools/port26row-20261024/Port26ROW_assess.py',
 revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),script_sha256=sha(Path(__file__)),
 exact_array_call=dict(caller=fs[3]['item_meta'],external=fs[14],call=call,expanded_call=call_resolved),
 inherited_native_delegation=hits,source_artifacts={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in [old/'Port23PUSH.llbc',old/'std-source-graph-focused.json',old/'Port23PUSH-generated/Funs.lean.txt',old/'Port23PUSH-generated/FunsExternal_Template.lean.txt']},
 accepted=accepted,not_accepted=['lean-002','lean-004','lean-005'],
 source_revision_qualification='HEAD records repository context; each exact dirty/untracked proof input is the independently hashed source snapshot, not falsely attributed to that HEAD tree.',
 reused='Port23 actual extraction/header adaptation and frame; Port25 Std/Lane and their warm dependencies; inherited sysroot graph. No new native identity/release gate; early Port23 integrity limitations remain.',
 established='complete actual parametric source row and Vec push at the derived content delegation instance; full Result equality, exact carriers, no domain/equality premises',
 remaining=['native ordered primitive effect producer and rejected-prefix semantics','P6 execution association at exact call14 with existing approved collection interpretation','op6 other children/trace observer/source-native release composition'],
 boundary='D157 permits pure called collection content semantics; derives no unsafe internals/panic/allocator policy. No new TrustedStd field or backend registration; raw unused template ABI mismatch is not an obligation to verify all Aeneas.',
 budget=dict(new_lean=8,new_lean_cap=8,known_global_prior=339,known_global_after_this_job=347,global_ceiling=368,prior_port23=13,kani=0,rust=0,extraction=0,backend=0,elf=0,full_manifest=0),
 checks=dict(exit_status=0,wall_seconds=time.monotonic()-start,peak_rss='see command-time.log',swaps='see command-time.log'))
(E/'source-assessment.json').write_text(json.dumps(out,indent=2)+'\n')
manifest=dict(schema='focused-extractor-proof-packet-v1',job='Port26ROW',attempts=attempts,assessment_sha256=sha(E/'source-assessment.json'),budget=out['budget'])
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(accepted=list(accepted),exits=[a['exit_status'] for a in attempts],new_native_identity_gate=False)))
