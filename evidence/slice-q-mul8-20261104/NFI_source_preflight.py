from pathlib import Path
import json,copy,hashlib
from NFI_source_checks import check
E=Path(__file__).resolve().parent
frozen=json.loads((E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json').read_text())
p=json.loads((E/'NFI_LIVE_PAYLOAD.json').read_text());valid=check(p,frozen);tests=[]
def reject(name,mutate):
 q=copy.deepcopy(p);mutate(q)
 try:check(q,frozen)
 except AssertionError:tests.append(name)
 else:raise AssertionError('source mutation accepted: '+name)
k='crates/aspis-r1-cost-probe/src/NFI_dots.rs'
for i in range(8):
 reject('main operand '+str(i),lambda q,i=i:q.__setitem__(k,q[k].replace(f'NFI_product(log, {i}, coefficient[{i}], scalar.0)',f'NFI_product(log, {i}, coefficient[{(i+1)%8}], scalar.0)')))
reject('wrapper slot',lambda q:q.__setitem__(k,q[k].replace('NFI_child(q,g,2,log)','NFI_child(q,g,1,log)')))
k2='crates/aspis-r1-cost-probe/src/NFI_pairing.rs'
reject('public guard',lambda q:q.__setitem__(k2,q[k2].replace('receiver.count >= MAX_TERMS','receiver.count > MAX_TERMS')))
k3='crates/aspis-r1-cost-probe/src/NFI_original.rs'
reject('opening original offset',lambda q:q.__setitem__(k3,q[k3].replace('let at=crate::compact::OFF_OPENINGS+i*crate::compact::OPENING','let at=1+crate::compact::OFF_OPENINGS+i*crate::compact::OPENING')))
out=dict(status='PASS_EXACT_SOURCE_FISSION_ONLY',payload_sha256=hashlib.sha256((E/'NFI_LIVE_PAYLOAD.json').read_bytes()).hexdigest(),checks=valid,mutations_rejected=tests,full_native_execution_instance=False)
(E/'NFI_SOURCE_PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(tests))
