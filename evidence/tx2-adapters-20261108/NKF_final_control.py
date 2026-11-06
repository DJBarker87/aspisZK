from NKF_wrappers import *
from NKF_box_shapes import shape
from NKF_pda import packet
import re
text=shape('master','positive')
text=re.sub(r'^#\[kani::(?:ensures|modifies)\(.*\)\]\n','',text,flags=re.M)
text=text.replace('#[kani::proof_for_contract(shape_probe)]','#[kani::proof]')
text=text.replace('#[kani::stub_verified(shape_probe)]','#[kani::stub(shape_probe,shape_oracle)]\n#[kani::stub(cp_shape_probe,cp_shape_oracle)]')
text=text.replace('"unimplied boxed bump"','"unimplied boxed master bump"')
old='fn shape_unimplied(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}'
new='fn shape_unimplied(){let choice:u8=kani::any();kani::assume(choice<3);if choice==2{super::owned::NKF_pda::stage();return;}let seed:u8=kani::any();let mut scratch:u8=kani::any();if choice==0{let out=shape_probe(seed,&mut scratch);check(seed,out);}else{let out=cp_shape_probe(seed,&mut scratch);match out{Ok(p)=>assert!(p.bump==seed,"unimplied boxed checkpoint bump"),Err(e)=>assert!(e==ProgramError::InvalidAccountData,"checkpoint error map")}}}'
assert text.count(old)==1;text=text.replace(old,new)
text+='''
fn shape_oracle(_seed:u8,scratch:&mut u8)->Result<Box<PoolV1PairForestMasterV1>,ProgramError>{*scratch=kani::any();if kani::any(){Ok(Box::new(any_master()))}else{Err(ProgramError::InvalidAccountData)}}
fn cp_shape_probe(seed:u8,scratch:&mut u8)->Result<Box<PoolV1PairForestCheckpointV1>,ProgramError>{*scratch=seed;let mut value=any_checkpoint();value.bump=seed;Ok(Box::new(value))}
fn cp_shape_oracle(_seed:u8,scratch:&mut u8)->Result<Box<PoolV1PairForestCheckpointV1>,ProgramError>{*scratch=kani::any();if kani::any(){Ok(Box::new(any_checkpoint()))}else{Err(ProgramError::InvalidAccountData)}}
'''
pda=packet(0).replace('fn stage(){','pub(crate) fn stage(){').replace(' let good=status',' log.bytes[slot]^=1;\n let good=status')
submit('NKF_K081','r1_pool_adapter::NKF_master_shape::shape_unimplied',P,'NKF_master_shape',text,'repaired_ak_and_seed_frame',extra_sidecars=[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NKF_pda',pda)])
