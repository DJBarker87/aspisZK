#!/usr/bin/env python3
"""Focused emitted-source association audit; never imports external templates."""
import hashlib,json,pathlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port20alloc-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((E/'Port20ALLOC.llbc').read_text()); assert not p['has_errors']
t=p['translated'];fs={x['def_id']:x for x in t['fun_decls'] if x}
def walk(x):
    if isinstance(x,dict):
        yield x
        for v in x.values():yield from walk(v)
    elif isinstance(x,list):
        for v in x:yield from walk(v)
def calls(f):
    return [x['Call']['call'] for x in walk(f['body']) if 'Call' in x]
def target(c):
    return c['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')
def entry(i):
    f=fs[i]
    return dict(def_id=i,name=f['item_meta']['name'],signature=f['signature'],
        source_text=f['item_meta'].get('source_text'),src=f['src'],
        generics=f['generics'],body_kind='opaque' if f['body']=='Opaque' else 'structured',
        calls=[dict(target_id=target(c),target_name=fs[target(c)]['item_meta']['name'] if target(c) is not None else c['func'],args=c['args'],dest=c['dest'],generics=c['func']) for c in calls(f)] if f['body']!='Opaque' else [])
assert fs[4]['item_meta']['source_text']==''.join((R/'crates/aspis-core/src/r0/heap.rs').read_text().splitlines(keepends=True)[4:10]).rstrip('\n')
for i,name in [(2,'Accumulator'),(3,'BatchedWeights')]:
    assert 4 in [target(c) for c in calls(fs[i])],name
assert fs[12]['body']=='Opaque' and fs[13]['body']=='Opaque'
g=(E/'Port20ALLOC-generated/Funs.lean.txt').read_text()
assert 'alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n' in g
assert 'let (r, out) ←' in g
assert 'alloc.vec.Vec.resize coremarkerCopyInst.cloneInst out n value' in g
assert 'ok self' in g
# Explicitly detect the parent omission rather than declaring the whole file
# translated because Charon's has_errors is false.
parent_omitted='def verifier.Accumulator' not in g and 'def verifier.BatchedWeights' not in g
receipts=[]
for q in sorted(E.glob('*/receipt.json')):
    x=json.loads(q.read_text());receipts.append({k:x[k] for k in ['attempt','kind','command','source_revision','exit_status','wall_seconds','peak_aggregate_rss_bytes','peak_observed_swap_bytes','cgroup_memory_peak_bytes','cgroup_swap_current_bytes','time_full','print_axioms']})
L=R/'docs/research/100bit-spend-path-20261013/lean'
interpretations={name:dict(sha256=sha(L/(name+'.lean')),bytes=(L/(name+'.lean')).stat().st_size)
    for name in ['OraclePortStdAllocation','OraclePortJoinSplitStd','OraclePortStdBuilder',
                 'CheckpointBytes3Allocation','Port3_Constructor','Port3_NativePendingBody','Port3_NativePendingInstall']}
native=[]
pins=json.loads((E/'source-pins.json').read_text())
for pin in pins['source_inclusions']:
    f=R/pin['source']; assert sha(f)==pin['whole_sha256']
    data=b''.join(f.read_bytes().splitlines(keepends=True)[pin['start_line']-1:pin['end_line']])
    assert hashlib.sha256(data).hexdigest()==pin['span_sha256']
    dest=R/'tools/port20alloc-20261024/Port20ALLOC-native'/pin['destination']
    assert dest.read_bytes()==data+(b'}\n' if dest.name in ['variant.rs','pending.rs'] else b'')
    old=subprocess.check_output(['git','show','17d459f032:'+pin['source']],cwd=R)
    assert old==f.read_bytes()
    native.append(dict(source=pin['source'],whole_file_unchanged_from_base=True,span_exact=True))
out=dict(schema='Port20ALLOC-focused-source-audit-v1',inspection_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    command='python3 tools/port20alloc-20261024/Port20ALLOC_audit.py',script_sha256=sha(pathlib.Path(__file__)),
    llbc_sha256=sha(E/'Port20ALLOC.llbc'),llbc_bytes=(E/'Port20ALLOC.llbc').stat().st_size,
    options=t['options'],selected_declarations=[entry(i) for i in [2,3,4,12,13,38]],
    full_source_and_dependency_pins='source-pins.json; extract-001.json; extract-002.json; kani-*.json',
    unchanged_source_checks=native,interpretation_source_pins=interpretations,
    new_lean_theorems=[],print_axioms='N/A: no Lean compile; external templates retained only as uncompiled text',
    parent_llbc_bodies_call_actual_helper=True,parent_lean_omitted=parent_omitted,
    result='concrete native reservation/resize def-use association extracted; content/effect join NOT proved',receipts=receipts)
(E/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(parent_llbc_call_association=True,parent_lean_omitted=parent_omitted,
    helper_body_exact=True,actual_reserve_result_retained=True,concrete_clone_operand_retained=True,
    native_content_effect_join=False,receipts=[(r['attempt'],r['exit_status']) for r in receipts])))
