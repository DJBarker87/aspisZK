"""Mutation controls for admission predicates; never mutate retained evidence."""
from copy import deepcopy
import json
from NGU_io import E,read
from NGU_validate import require_caps,require_scan,require_raw,require_delta

passed=[]
def rejected(name,fn):
 try:fn()
 except (AssertionError,KeyError):passed.append(name);return
 raise AssertionError('mutation admitted: '+name)
rc=read(E/'NGU_L035/receipt.json');ad=read(E/'NGU_L035-admission.json');require_caps(rc,ad)
for field,value in [('exit',78)]:
 x=deepcopy(ad);x[field]=value;rejected('admission_exit78',lambda x=x:require_caps(rc,x))
x=deepcopy(ad);x['reservation']['allowed']=False;rejected('allowed_false_exit0',lambda:require_caps(rc,x))
for key,value in [('memory.high','7516192768'),('memory.max','9663676416'),('memory.swap.max','1'),('pids.max','65')]:
 y=deepcopy(rc);y['limits'][key]=value;rejected('changed_cap_'+key,lambda y=y:require_caps(y,ad))
y=deepcopy(rc);y['swaps']='1';rejected('swap_observed',lambda:require_caps(y,ad))
scan=read(E/'NGU_SCAN.json');require_scan(scan)
for k in ['dangling','incompatible_owners','import_mismatches']:
 y=deepcopy(scan);y[k]=1;rejected('scan_'+k,lambda y=y:require_scan(y))
r=[dict(equal=True,walked_axioms=['propext'])];require_raw(r)
y=deepcopy(r);y[0]['equal']=False;rejected('collect_disagreement',lambda:require_raw(y))
y=deepcopy(r);y[0]['walked_axioms']=['Unsound.oracle'];rejected('nonstandard_axiom',lambda:require_raw(y))
d=read(E/'NGU_LEDGER_DELTA.json');require_delta(d)
y=deepcopy(d);y['new_closed_rows']=['TX1:193'];rejected('invent_closed_row',lambda:require_delta(y))
y=deepcopy(d);y['rows'][0]['after']='CLOSED';rejected('promote_qualified_packet',lambda:require_delta(y))
y=deepcopy(d);y['rows'][0]['remaining_hypotheses'].pop();rejected('hide_boundary',lambda:require_delta(y))
y=deepcopy(d);y['rows'][0]['remaining_hypotheses'][0]['status']='DISCHARGED';rejected('fake_native_association',lambda:require_delta(y))
y=deepcopy(d);y['security_target_established']=True;rejected('claim_security_headline',lambda:require_delta(y))
y=deepcopy(d);y['all_other_rows_unchanged']=False;rejected('mutate_unowned_rows',lambda:require_delta(y))
(E/'NGU_TESTS.json').write_text(json.dumps(dict(passed=len(passed),rejected_mutations=passed,full_prover_fixture_controls='Eight actual NEP fixtures in NGU_AUDIT.json, same binary as367 roots'),indent=1)+'\n')
print('rejected mutations',len(passed))
