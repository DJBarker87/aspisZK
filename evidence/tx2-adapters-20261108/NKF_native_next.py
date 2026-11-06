from NKF_wrappers import *
from NKF_box_shapes import shape
from NKF_ownership import ownership
from NKF_pda import packet
import lzma

def send(a,parent,module,text,target,mode):
 rc=submit(a,target,parent,module,text,mode)
 t=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 record=dict(attempt=a,kind=mode,exit=rc['exit_status'],timeout='CBMC timed out' in t or rc['exit_status']==124,semantic_failure='Failed Checks:' in t and 'CBMC timed out' not in t and 'Failed Checks: unwinding' not in t)
 with (E/'NKF_NATIVE_NEXT_RESULTS.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 return rc

n=44
for kind in ['master','checkpoint']:
 for mode in ['positive','inverse','unimplied','modifies']:
  text=shape(kind,mode);target='shape_unimplied' if mode=='unimplied' else 'shape_contract'
  send('NKF_K'+str(n).zfill(3),P,'NKF_'+kind+'_shape',text,'r1_pool_adapter::NKF_'+kind+'_shape::'+target,'shape_'+mode);n+=1
for kind in ['master','checkpoint']:
 for mode in ['identity','different_allocation','unique','inverse_unique']:
  text=ownership(kind,mode);target='allocation_unique' if 'unique' in mode else 'allocation_identity'
  send('NKF_K'+str(n).zfill(3),P,'NKF_'+kind+'_allocation',text,'r1_pool_adapter::NKF_'+kind+'_allocation::'+target,mode);n+=1
for kind in ['master','checkpoint']:
 text=wrapper(kind,0)
 assert text.count('        raw\n')==1
 text=text.replace('        raw\n','        raw.map(|mut v|{v.bump^=1;v})\n')
 send('NKF_K'+str(n).zfill(3),P,'NKF_'+kind,text,'r1_pool_adapter::NKF_'+kind+'::wrapper_result','corrupt_box_value');n+=1
for site in range(9):
 for mode in ['positive','inverse']:
  text=packet(site)
  send('NKF_K'+str(n).zfill(3),'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NKF_pda',text,'r1_pool_adapter::owned::NKF_pda::stage',mode);n+=1
assert n==80
text=packet(0).replace(' assert!(if cfg!', ' log.bytes[slot]^=1;\n assert!(if cfg!')
send('NKF_K080','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NKF_pda',text,'r1_pool_adapter::owned::NKF_pda::stage','corrupt_seed_frame')
