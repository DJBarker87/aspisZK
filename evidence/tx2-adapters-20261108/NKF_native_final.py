from NKF_wrappers import *
from NKF_box_shapes import shape
from NKF_pda import packet
from NKF_lane import iteration,constructor
import time,lzma
while not (E/'NKF_L015/receipt.json').exists():time.sleep(0.5)
assert json.loads((E/'NKF_L015/receipt.json').read_text())['exit_status']==0

def send(a,parent,module,text,target,mode):
 rc=submit(a,target,parent,module,text,mode)
 t=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 record=dict(attempt=a,kind=mode,exit=rc['exit_status'],timeout='CBMC timed out' in t or rc['exit_status']==124,semantic_failure='Failed Checks:' in t and 'CBMC timed out' not in t and 'Failed Checks: unwinding' not in t)
 with (E/'NKF_NATIVE_NEXT_RESULTS.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 return record
for a,kind in [('NKF_K062','master'),('NKF_K063','checkpoint')]:
 typ=M if kind=='master' else C
 text=shape(kind,'positive').replace('#[kani::stub_verified(shape_probe)]','#[kani::stub(shape_probe,shape_oracle)]')
 text+='\nfn shape_oracle(_seed:u8,scratch:&mut u8)->Result<Box<'+typ+'>,ProgramError>{*scratch=kani::any();if kani::any(){Ok(Box::new(any_'+kind+'()))}else{Err(ProgramError::InvalidAccountData)}}\n'
 send(a,P,'NKF_'+kind+'_shape',text,'r1_pool_adapter::NKF_'+kind+'_shape::shape_unimplied','ak_constructor_unimplied')
for n,part,producer in [(64,'iteration',iteration),(66,'constructor',constructor)]:
 text=producer()
 r=send('NKF_K'+str(n).zfill(3),P,'NKF_lane',text,'r1_pool_adapter::NKF_lane::'+part,'positive')
 if r['timeout']:
  if part=='iteration':text=text.replace('let canonical:bool=kani::any();','let canonical:bool=false;')
  else:text=text.replace('kani::assume(i<32&&level<20&&word<8);','kani::assume(i<32&&level==0&&word==0);')
  mode='isolated_branch_control'
  text=text.replace('if cfg!(NKF_invert){!good}else{good}','!good')
 else:mode='inverse'
 send('NKF_K'+str(n+1).zfill(3),P,'NKF_lane',text,'r1_pool_adapter::NKF_lane::'+part,mode)
for site in range(6):
 for j,mode in enumerate(['positive','inverse']):
  a='NKF_K'+str(68+2*site+j).zfill(3)
  send(a,'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NKF_pda',packet(site),'r1_pool_adapter::owned::NKF_pda::stage',mode)
text=packet(0).replace(' assert!(if cfg!', ' log.bytes[slot]^=1;\n assert!(if cfg!')
send('NKF_K080','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NKF_pda',text,'r1_pool_adapter::owned::NKF_pda::stage','corrupt_seed_frame')
