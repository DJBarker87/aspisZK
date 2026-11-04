from pathlib import Path
import json,lzma,copy,sys
sys.dont_write_bytecode=True
from NGI_checks import check,propagate
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text())
a=J(E/'NGI_AUDIT.json');scan=[json.loads(l) for l in (E/'NGI_LOADED_scan.jsonl').read_text().splitlines()];manifest=J(E/'NGI_AUDIT_ROOTS.json');cert=J(E/'NGI_CERT_CHECK.json');inv=json.loads(lzma.decompress((E/'NGI_CERT_INVENTORY.json.xz').read_bytes()));q=J(E/'NGI_DECLARATION_INVENTORY.json');delta=J(E/'NGI_LEDGER_DELTA.json')
args=[a,scan,manifest,cert,inv,q['entries'],q['modules'],delta];assert check(*args)
mutations=[]
def reject(label,index,mutate):
 xs=list(args);xs[index]=copy.deepcopy(xs[index]);mutate(xs[index])
 try:check(*xs)
 except (AssertionError,KeyError,IndexError):mutations.append(label);return
 raise AssertionError('accepted '+label)
reject('nonstandard raw axiom',0,lambda x:x['results'][0]['walked_axioms'].append('Fake.ax'))
reject('omit raw root',0,lambda x:x['results'].pop())
reject('duplicate raw root',0,lambda x:x['results'].append(x['results'][0]))
reject('broken fixture',0,lambda x:x['fixtures'][0].update(equal=False))
reject('dangling reference',1,lambda x:x[0]['dangling'].append({'missing':'fake'}))
reject('incompatible owner',1,lambda x:x[0]['duplicate_owners'].append({'name':'fake'}))
reject('import mismatch',1,lambda x:x[0].update(imports_match=False))
reject('missing occurrence',4,lambda x:x.pop())
reject('omitted theorem records',4,lambda x:x[0]['theorems'].pop())
key=next(iter(q['entries']))
reject('missing declaration',5,lambda x:x[key].update(found=False))
reject('wrong owner',5,lambda x:x[key].update(module_idx=0))
reject('non-theorem substituted',5,lambda x:x[key].update(is_theorem=False))
reject('omitted declaration inventory',5,lambda x:x.pop(key))
reject('new trust row',7,lambda x:x['new_trust_rows'].append('fake'))
reject('invented security conclusion',7,lambda x:x.update(security_target_established=True))
reject('incorrect inventory basis',7,lambda x:x.update(inventory_rows=587))
reject('bypassed selected-callee propagation',7,lambda x:x.update(selected_callee_denial_propagation=False))
# Test the actual baseline's selected-callee graph, not an invented toy edge.
base=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));rows=base['rows'];srows={r['row'] for r in inv}
for r in rows:
 if r['row'] in srows:r['composed_status']='CLOSED'
propagate(rows);assert all(r['composed_status']=='CLOSED' for r in rows if r['row'] in srows)
child=next(r for r in rows if r['row']=='TX2:164');child['composed_status']='QUALIFIED';propagate(rows)
assert next(r for r in rows if r['row']=='TX2:219')['composed_status']=='QUALIFIED'
(E/'NGI_TESTS.json').write_text(json.dumps(dict(positive=True,rejected_mutations=mutations,actual_selected_callee_control='TX2:164 denial propagates to TX2:219',unchanged_historical_builder=J(E/'NGI_REPLAY_NFX_LEDGER.json')['exit_status']==0),indent=1)+'\n')
print('PASS;',len(mutations),'mutations rejected; actual selected-callee denial propagated')
