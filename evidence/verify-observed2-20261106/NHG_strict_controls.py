"""Strengthen matched failures; never rerun an unchanged passing shape."""
from pathlib import Path
import json,hashlib,subprocess,os
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
plans=[(17,3,'crates/aspis-r1-cost-probe/src/NHG_native.rs','NHG_native.rs.txt','NHG_native::NHG_field_append','append'),(18,5,'crates/aspis-r1-cost-probe/src/NHG_native.rs','NHG_native.rs.txt','NHG_native::NHG_field_append','append'),(19,7,'crates/aspis-r1-cost-probe/src/NHG_native.rs','NHG_native.rs.txt','NHG_native::NHG_realloc_window','realloc'),(20,13,'crates/aspis-statement/src/pool_v1/NHG_semantic.rs','NHG_semantic.rs.txt','pool_v1::pair_forest_semantic_terminal::r0::NHG_semantic::NHG_semantic_source','semantic'),(21,15,'crates/aspis-r1-cost-probe/src/NHG_begin.rs','NHG_begin.rs.txt','r1_wire::NHG_begin::NHG_begin_value','begin')]
records=[]
for number,positive,path,local,target,kind in plans:
 source=(E/f'NHG_K{positive:03}/sources/NHG_src'/path).read_text();changed=source
 if kind=='append':
  needle='let old=if j<n{out[j]}else{0};';assert needle in source
  changed=changed.replace(needle,'if cfg!(NHG_invert){kani::assume(value<2147483647);kani::assume(n>=1);kani::assume(j>=n);}\n '+needle)
  why='The negative is forced through canonical append, with a nonempty prior Vec and an observed newly written byte. The existing expected-byte XOR1 is the sole changed assertion. New guards are inactive in the positive configuration.'
 elif kind=='realloc':
  needle='let k:usize=kani::any();kani::assume(k<n);';assert needle in source
  changed=changed.replace(needle,needle+'if cfg!(NHG_invert){kani::assume(i==k);}')
  why='The negative observes the actually copied initialized byte (i=k), rather than an untouched frame byte. The new guard is inactive in the positive configuration.'
 elif kind=='semantic':
  for v in ['p','w']:
   needle=f'result.anchor[j]=={v}.anchor_root[j]';assert needle in source
   changed=changed.replace(needle,f'result.anchor[j].0==({v}.anchor_root[j].0 ^ if cfg!(NHG_invert){{1}}else{{0}})')
  changed=changed.replace('assert!(good!=cfg!(NHG_invert));','assert!(good);')
  why='Corrupt exactly the expected copied anchor limb by XOR1. With invert=false, XOR0 and the tuple M31 PartialEq definition give exactly the original property; the actual callee and all inputs are unchanged.'
 else:
  needle='assert_eq!(t.state[k],after[k]);';assert needle in source
  changed=changed.replace(needle,'assert_eq!(t.state[k],after[k]^if cfg!(NHG_invert){1}else{0});').replace('assert!(correct!=cfg!(NHG_invert));','assert!(correct);')
  why='Corrupt exactly one observed child-produced state byte. The selected child always executes its state assignment before either return. With invert=false, XOR0 and b!=false=b give the original property; all native calls and inputs are unchanged.'
 assert changed!=source
 (E/local).write_text(changed)
 overlay=json.loads((E/'NHG_OVERLAY.json').read_text());(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:sha((E/v).read_bytes())for n,v in overlay.items()},indent=1))
 record=dict(attempt=f'NHG_K{number:03}',positive=f'NHG_K{positive:03}',path=path,positive_sha256=sha(source.encode()),control_sha256=sha(changed.encode()),reason=why,unchanged_positive_configuration=True)
 records.append(record);(E/'NHG_STRICT_CONTROL_PLAN.json').write_text(json.dumps(records,indent=1))
 env=dict(os.environ,NHG_INVERT='1');r=subprocess.run(['python3',str(E/'NHG_run.py'),record['attempt'],'kani',target],env=env)
 log=(E/record['attempt']/'stdout.log').read_text();rc=json.loads((E/record['attempt']/'receipt.json').read_text())
 assert r.returncode==1 and rc['exit_status']==1 and 'VERIFICATION:- FAILED'in log and'timed out'not in log.lower()and'unwinding assertion'not in log.lower(),('STOP review control',record['attempt'])
