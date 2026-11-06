from NJY_forest_segments import helpers,P
from NJY_native import *
import sys
family=sys.argv[2];mode=sys.argv[3];cp=family=='checkpoint';assert family in ['checkpoint','master']
record='PoolV1PairForestCheckpointV1' if cp else 'PoolV1PairForestMasterV1'
fields='bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),checkpoint_sequence:kani::any(),global_root:digest(),lane_sequences:kani::any()' if cp else 'bump:kani::any(),identity:identity(),verifier_policy:policy(),initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()'
ctor='bump:seed,master:[0;32],deployment_domain:[0;32],checkpoint_sequence:0,global_root:[aspis_core::field::M31(0);8],lane_sequences:[0;8]' if cp else 'bump:seed,identity:I{pool:[0;32],asset_mint:[0;32],token_program:[0;32],asset_id:aspis_core::field::M31(0),deployment_domain:[0;32]},verifier_policy:P{flags:0,registry_program:[0;32],registry_authority:[0;32],policy_binding:[0;32]},initialized_lane_mask:0,has_checkpoint:false,next_checkpoint_sequence:0,last_checkpoint_lane_sequences:[0;8]'
text='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+helpers
text+='impl kani::Arbitrary for '+record+'{fn any()->Self{Self{'+fields+'}}}\nimpl kani::Arbitrary for F{fn any()->Self{match account_reply(){Ok(())=>F::WrongLength,Err(e)=>e}}}\n'
text+='''#[kani::ensures(|r| (r.is_ok()==(seed&1==0))!=cfg!(NJY_invert))]
#[kani::modifies()]
fn shape_probe(seed:u8,scratch:&mut u8)->Result<RECORD,F>{if WRITE{*scratch=seed;}if seed&1==0{Ok(RECORD{CTOR})}else{Err(F::WrongMagic)}}
fn check(seed:u8,out:Result<RECORD,F>){match out{Ok(p)=>assert!(p.bump==seed,"unimplied record bump"),Err(e)=>assert!(e==F::WrongMagic,"unimplied record error")}}
#[kani::proof_for_contract(shape_probe)]
#[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_contract(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
#[kani::proof]
#[kani::stub_verified(shape_probe)]
#[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_unimplied(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
'''.replace('RECORD',record).replace('CTOR',ctor).replace('WRITE','true' if mode=='modifies' else 'false')
module='NJY_'+family+'_shape';(E/(module+'_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/'+str(Path(P).parent/(module+'.rs'))+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines()))
submit(sys.argv[1],'pool_v1::pair_forest_accounts::'+module+'::'+('shape_unimplied' if mode=='unimplied' else 'shape_contract'),P,module,text,mode)
