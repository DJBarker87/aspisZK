from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';cov=json.loads((D/'resume13/coverage.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=json.loads((O/'receipt-index.json').read_text());passed={r['module']:r for r in receipts if r['exit']==0}
assert 'PV_B3P_TransitionLoan14227'in passed and 'PV_B3P_FrontierIndexedBinding14227'in passed
# This bound count is per reachable body. Complete callback and dependency
# closure are reported separately, never inferred from the count.
for key,cls,note,evidence in [
('frontier#0','reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)','Exact body-token lift with identical lexical resolution; pinned caller extraction and callee-parameter port compiled. fields/Vec dependency and old root conversion law remain explicit.','frontier-binding-chain.json'),
('transition#0','structural own-1','Exact two-arm native source match; returned shared-loan identity and value preserved for every continuation; source/body has no callees, stores or destructor. V370 retained.','transition-native-association.json')]:
 r=next(r for r in cov['rows']if r['family']=='terminal'and r['key']==key);assert not r['bound'];r.update(bound=True,binding_class=cls,remaining=[],note=note,evidence=evidence)
cov.update(bound=41,reclassification_bound=40,own_1_proved_fully_composed=1,own_1_scope='One body only: transition, with no callees. No changed-function or complete callback native closure is inferred.',unbound=38,new_bound=['frontier#0','transition#0'],lexical_identities_without_model_chain=3,unbound_lexical_identities=2,source_revision=passed['PV_B3P_Resume14Focused']['lean_source_revision'] if 'lean_source_revision'in passed['PV_B3P_Resume14Focused']else passed['PV_B3P_Resume14Focused']['source_revision'],credit_policy='Local per-body b3p6-1/own-1 credit only; conservative reachability (79), no pruning; 0/36 changed-function complete native/dependency associations newly closed.',runjoin_op227_discharged=False)
assert sum(r['bound']for r in cov['rows'])==41
(O/'coverage.json').write_text(json.dumps(cov,indent=2)+'\n')
front=json.loads((O/'frontier-binding-chain.json').read_text());outputs=json.loads((O/'extraction/frontier/aeneas-outputs.json').read_text())
for name in ['Funs.lean','Types.lean','translation.json']:
 r=next(r for r in outputs if r['path'].endswith('/'+name));assert sha((O/'frontier-raw'/name).read_bytes())==r['sha256']
inputs=json.loads((O/'extraction/frontier/charon-inputs.json').read_text());snapshot=O/'input-snapshots/lib-before-rounds.rs';path='tools/pv-b3p6-20261028/v244-missing14/lib.rs';assert sha(snapshot.read_bytes())==inputs['input_hashes'][path]
assert front['port']['body_byte_identical']and not front['port']['external_template_compiled']
(O/'coverage-verification.json').write_text(json.dumps(dict(candidates=79,bound=41,reclassification_bound=40,own1_bound=1,newly_bound=2,pruned=0,frontier_raw_outputs_verified=True,frontier_exact_input_snapshot_verified=True,transition_attempt=passed['PV_B3P_TransitionLoan14227']['attempt'],frontier_bridge_attempt=passed['PV_B3P_FrontierIndexedBinding14227']['attempt'],changed_function_native_closed=0,op227_discharged=False),indent=2)+'\n')
print(json.dumps(dict(candidates=79,bound=41,reclassification_bound=40,own1_bound=1,op227_discharged=False)))
