"""Negative evidence controls: every mutation must be rejected by the same validator."""
from pathlib import Path
import json,copy,sys
sys.dont_write_bytecode=True
from NHP_validate import validate
E=Path(__file__).resolve().parent
rows=[]
def mutate(label,path,change):
 value=json.loads((E/path).read_text());change(value)
 try:validate({path:json.dumps(value).encode()})
 except (AssertionError,KeyError,ValueError):rows.append(dict(test=label,rejected=True));return
 raise AssertionError('Mutation accepted: '+label)
mutate('allowed false with exit zero','NHP_K028-admission.json',lambda x:x['reservation'].update(allowed=False))
mutate('exit78 with allowed true','NHP_K028-admission.json',lambda x:x.update(exit=78))
mutate('swap use','NHP_K028/receipt.json',lambda x:x.update(swaps='1'))
mutate('higher memory cap','NHP_K028/receipt.json',lambda x:x['limits'].update({'memory.max':'17179869184'}))
mutate('graph drift','NHP_K028-graph-check.json',lambda x:x.update(exact_LPm_graph=False))
mutate('lock changed','NHP_K028-lock-check.json',lambda x:x.update(after='0'*64))
mutate('writable static','NHP_K028-rule16-check.json',lambda x:x.update(no_writable_static=False))
mutate('wrong copy patch','NHP_K028.json',lambda x:x.update(copy_patch_sha256='0'*64))
mutate('network enabled','NHP_K028.json',lambda x:x['env'].update(CARGO_NET_OFFLINE='false'))
mutate('compiled source changed','NHP_K028/receipt.json',lambda x:x['source_hashes'].update({'NHP_native.patch':'0'*64}))
mutate('output premise inserted','NHP_GUARD_CERTIFICATE.json',lambda x:x.update(named_hypotheses=['output equality']))
mutate('stronger height domain','NHP_GUARD_CERTIFICATE.json',lambda x:x.update(domain='height=1 only'))
mutate('closed parent root','NHP_LEDGER_DELTA.json',lambda x:x['root_status'].update({'POOL.prefix_to_cpi':'CLOSED'}))
mutate('closed row missing','NHP_CLOSED.json',lambda x:x.update(composed_rows=[]))
mutate('unclassified raw axiom','NHP_audit/batch0/proof0.json',lambda x:x['results'][0].update(walked_axioms=['unreviewedAx']))
mutate('ak route erased','NHP_POOL_ERROR_CERTIFICATE.json',lambda x:x.update(route='unqualified foreign contract'))
mutate('extraction proof bytes changed','NHP_E001_EXTRACTION_PINS.json',lambda x:x['outputs']['NHP_E001_extracted/NHP_StackRef/Funs.lean'].update(sha256='0'*64))
(E/'NHP_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations=rows),indent=2)+'\n');print(json.dumps(dict(status='PASS',rejected=len(rows))))
