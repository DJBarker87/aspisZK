#!/usr/bin/env python3
"""Exact source/emission association only; not native equality or effects."""
import hashlib,json,pathlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port23push-20261024';B=R/'tools/port23push-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
j=json.loads((E/'Port23PUSH.llbc').read_bytes());assert not j['has_errors']; t=j['translated'];fs={f['def_id']:f for f in t['fun_decls'] if f}
def walk(x):
 if isinstance(x,dict):
  yield x
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
def calls(f):return [d['Call']['call'] for d in walk(f['body']) if 'Call' in d]
def target(c):return c['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')
ordered={i for d in t['ordered_decls'] for i in ([d['Fun']['NonRec']] if 'Fun' in d and 'NonRec' in d['Fun'] else [])}
assert {0,1,3,12,13}<=ordered
assert 1 in [target(c) for c in calls(fs[0])]
assert 3 in [target(c) for c in calls(fs[1])]
pins=json.loads((E/'source-pins.json').read_text());included=[]
for pin in pins['source_inclusions']:
 data=subprocess.check_output(['git','show',pins['source_revision']+':'+pin['source']],cwd=R)
 assert sha(data)==pin['whole_sha256']
 span=b''.join(data.splitlines(keepends=True)[pin['start_line']-1:pin['end_line']])
 assert (B/'Port23PUSH-native'/pin['destination']).read_bytes()==span
 included.append(dict(**pin,immutable_source_equal=True))
for i,dest in [(1,'src/lib.rs'),(3,'src/update.rs'),(12,'src/update.rs'),(13,'src/update.rs')]:
 assert fs[i]['item_meta']['source_text'] in (B/'Port23PUSH-native'/dest).read_text()
def generated(name):
 p=E/'Port23PUSH-generated'/name
 if not p.exists(): p=p.with_suffix(p.suffix+'.txt')
 return p.read_text()
f=generated('Funs.lean');external=generated('FunsExternal_Template.lean')
assert 'let back ← verifier.update_residue_row_loop1 iter (fun im => im)' in f
assert 'ok (into_iter_back back)' in f
assert '(core.slice.iter.IterMut T → Array T N)' in external
selected=[dict(def_id=i,item_meta=fs[i]['item_meta'],generics=fs[i]['generics'],signature=fs[i]['signature'],calls=calls(fs[i])) for i in [0,1,3,12,13]]
policies={}
for name in ['Port3_NativeRowFrame','S7Kani2OwnedPush','S7Kani2OwnedRow','S7OwnedP6ScalarExtracted','Port4D_FlushABI','Port17_ReachedSource']:
 p=L/(name+'.lean')
 if p.exists():policies[name]=dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size,source=p.read_text())
out=dict(schema='Port23PUSH-exact-source-audit-v1',command='python3 tools/port23push-20261024/Port23PUSH_audit.py',
 script_sha256=sha(pathlib.Path(__file__).read_bytes()),revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 source_inclusions=included,selected=selected,ordered_declarations=t['ordered_decls'],extraction_options=t['options'],
 opaque=[dict(def_id=i,item_meta=v['item_meta'],signature=v['signature']) for i,v in fs.items() if v['body']=='Opaque'],
 source_functions_recovered=True,actual_mutable_to_owned_equality=False,actual_effect_producer=False,query_child_installed=False,
 incompatible_external_template=dict(template='Result (IterMut T × (IterMut T → Array T N))',caller='back : IterMut U64 → IterMut U64; into_iter_back back',explicit_parameter='Result (IterMut U64 × ((IterMut U64 → IterMut U64) → Array U64 4))',new_native_instance=False),
 prior_source_statements=policies,print_axioms='source-only audit; full Lean statements and axioms in Audit output')
(E/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['source_functions_recovered','actual_mutable_to_owned_equality','actual_effect_producer','query_child_installed']}))
