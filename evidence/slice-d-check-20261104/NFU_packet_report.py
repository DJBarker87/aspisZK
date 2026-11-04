"""Describe completed native fragments without promoting any caller."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
pairs=[(0,72,73),(1,74,75),(2,76,77)]+[(g,79+2*i,80+2*i)for i,g in enumerate(list(range(3,8))+list(range(9,14)))]
names={0:'Complete Result mapping from arbitrary push reply',1:'Exact index advance or retention',2:'Exactly one push call',3:'All nine original receiver words',4:'All nine unconstrained successor receiver words',5:'Exact low four value limbs',6:'Exact high four value limbs',7:'Exact four raw scalar limbs',9:'Field then weight then push order',10:'SAME selected field pointer',11:'Selected field length32',12:'Exact field index',13:'SAME selected weight pointer and index'}
observations=[]
for g,p,n in pairs:
 a,b=[json.loads((E/f'NFU_K{i:03}/receipt.json').read_text())for i in [p,n]]
 assert a['exit_status']==0 and b['exit_status']==1 and a['module']==b['module']
 observations.append(dict(observation=names[g],harness=a['module'],positive=a['attempt'],negative=b['attempt'],complete=True,caller_closure=False))
meta=[]
for i in [99,100,51]:
 r=json.loads((E/f'NFU_K{i:03}/receipt.json').read_text());meta.append(dict(attempt=r['attempt'],harness=r['module'],exit=r['exit_status']))
x=dict(status='OPEN caller; no composed credit',frozen_function='crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot',native_domain='j<64; SAME 2048-byte allocation with selected32-byte canonical input;64-element weights with arbitrary raw selected K; arbitrary actual EbyKDot nine-word prestate; valid unique receiver; unconstrained reply and nine-word mutation',observations=observations,missing_canonicality_observation='group8 not launched; groups5/6 identify actual E limbs with the canonical input. No driver-domain proof follows from that input premise.',KMX='Exact adopted patch and generic K024/K025,K040/K041 failing copy controls; per-observation inverted controls above',excluded='K070/K071 helper-placement compile errors; K078 array-equality memcmp-unwind failure, changed to nine explicit equalities in K079 onward; no failure credit',remaining=json.loads((E/'NFU_FINISH_CANDIDATE.json').read_text())['remaining'],metadata_fragments=meta,data_len_domain='All usize Ok(n), Err(AccountBorrowFailed), Err(InvalidAccountData); other ProgramError variants are not covered. Exact clone/error-carrier port and proof that callers establish this restricted error domain remain OPEN.',checkpoint_metadata_domain='Arbitrary32-byte owner/program, metadata flags,writable parameter and all usize lengths, Ok/AccountBorrowFailed only; K051 has NO failing control and earns no packet credit.',metadata_closure=False)
(E/'NFU_NATIVE_FRAGMENTS.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(finish_observations=len(observations),new_composed_credit=0)))
