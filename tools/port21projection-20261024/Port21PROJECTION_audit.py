#!/usr/bin/env python3
"""Exact immutable-source linkage and ordered parent emission, not a proof of effects."""
import hashlib,json,pathlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port21projection-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((E/'Port21PROJECTION.llbc').read_text());assert not p['has_errors'];t=p['translated']
fs={x['def_id']:x for x in t['fun_decls'] if x}
def walk(x):
 if isinstance(x,dict):
  yield x
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
def calls(f):return [x['Call']['call'] for x in walk(f['body']) if 'Call' in x]
def target(c):return c['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')
helper=next(i for i,f in fs.items() if f['item_meta']['source_text'] and f['item_meta']['source_text'].startswith('pub fn filled<'))
parents=[2,3];assert all(helper in [target(c) for c in calls(fs[i])] for i in parents)
ordered={i for d in t['ordered_decls'] for i in ([d['Fun']['NonRec']] if 'Fun' in d and 'NonRec' in d['Fun'] else [])}
assert all(i in ordered for i in parents)
g=(E/'Port21PROJECTION-generated/Funs.lean.txt').read_text()
for name in ['verifier.Accumulator.new','verifier.BatchedWeights.new','verifier.BatchedWeights.new_loop','field.QM31.Insts.CoreCloneClone.clone']:
 assert 'def '+name in g,name
assert 'alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n' in g
assert 'alloc.vec.Vec.resize coremarkerCopyInst.cloneInst out n value' in g
pins=json.loads((E/'source-pins.json').read_text());included=[]
for pin in pins['source_inclusions']:
 data=subprocess.check_output(['git','show','e2747dd63d:'+pin['source']],cwd=R)
 assert hashlib.sha256(data).hexdigest()==pin['whole_sha256']
 span=b''.join(data.splitlines(keepends=True)[pin['start_line']-1:pin['end_line']])
 dest=R/'tools/port21projection-20261024/Port21PROJECTION-native'/pin['destination']
 assert dest.read_bytes()==span+(b'}\n' if dest.name in ['variant.rs','pending.rs'] else b'')
 included.append(dict(**pin,immutable_object_bytes_verified=True))
for i,path in [(helper,'src/r0/heap.rs'),(2,'src/accumulator.rs'),(3,'src/pending.rs')]:
 body=fs[i]['item_meta']['source_text']
 assert body in (R/'tools/port21projection-20261024/Port21PROJECTION-native'/path).read_text()
old=json.loads((R/'evidence/port20alloc-20261024/Port20ALLOC.llbc').read_text())['translated']
old_order={i for d in old['ordered_decls'] for i in ([d['Fun']['NonRec']] if 'Fun' in d and 'NonRec' in d['Fun'] else [])}
assert 2 not in old_order and 3 not in old_order
selected=[]
for i in [0,1,2,3,helper]:
 f=fs[i];selected.append(dict(def_id=i,item_meta=f['item_meta'],signature=f['signature'],generics=f['generics'],src=f['src'],calls=calls(f)))
opaque=[dict(def_id=i,item_meta=f['item_meta'],signature=f['signature']) for i,f in fs.items() if f['body']=='Opaque']
L=R/'docs/research/100bit-spend-path-20261013/lean'
policies={n:dict(sha256=sha(L/(n+'.lean')),bytes=(L/(n+'.lean')).stat().st_size) for n in ['OraclePortStdAllocation','OraclePortJoinSplitStd','Port3_Constructor','OraclePortRuntimeBindingC7','RawRecordedOracleExtractionMassBin','S2X_RuntimeRetention']}
out=dict(schema='Port21PROJECTION-concrete-parent-source-audit-v1',command='python3 tools/port21projection-20261024/Port21PROJECTION_audit.py',
 revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),script_sha256=sha(pathlib.Path(__file__)),
 unchanged_source_inclusions=included,llbc_sha256=sha(E/'Port21PROJECTION.llbc'),options=t['options'],
 old_parent_ids_ordered=False,new_parent_ids_ordered=True,new_parent_bodies_emitted=True,selected=selected,opaque_leaves=opaque,
 policies=policies,generated={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in (E/'Port21PROJECTION-generated').iterdir()},
 exact_reserve_result_controls_branch=True,actual_helper_and_parent_linkage=True,
 native_reserve_content_frame_proved=False,native_primitive_effect_law_proved=False,source_budget_producer=False,
 no_new_primitive_or_allocator_interpretation=True,print_axioms='N/A: source linkage audit; Lean axioms in lean-*/receipt.json')
(E/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['old_parent_ids_ordered','new_parent_ids_ordered','new_parent_bodies_emitted','actual_helper_and_parent_linkage','native_reserve_content_frame_proved','native_primitive_effect_law_proved','source_budget_producer']}))
