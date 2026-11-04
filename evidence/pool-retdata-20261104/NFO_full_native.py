"""Direct frozen generic Pool caller on a ready account fixture; no decoder is reached."""
from pathlib import Path
import subprocess,difflib,json,sys
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
negative=len(sys.argv)>1 and sys.argv[1]=='negative'
source=r'''use super::*;
fn decode_not_reached(_: &[u8])->Result<PoolV1PairForestTerminalResultV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>{panic!("decoder must not be called for a wrong program")}
struct Runtime{calls:u8,reply:Option<(Pubkey,Vec<u8>)>,returned:Option<(Pubkey,Vec<u8>)>,selected:Pubkey}
impl PairForestVerifierRuntimeV1 for Runtime{
 fn clear_return_data(&mut self){assert!(self.calls==0);self.calls=1;self.returned=None;}
 fn invoke(&mut self,instruction:&Instruction,infos:&[AccountInfo<'_>])->ProgramResult{
  assert!(self.calls==1&&instruction.program_id==self.selected&&instruction.accounts.len()==7&&infos.len()==8);self.calls=2;self.returned=self.reply.take();Ok(())}
 fn get_return_data(&mut self)->Option<(Pubkey,Vec<u8>)>{assert!(self.calls==2);self.calls=3;self.returned.take()}
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_result_v1,decode_not_reached)]
fn association(){
 let selected=Pubkey::new_from_array(kani::any());let returned=Pubkey::new_from_array(kani::any());kani::assume(returned!=selected);
 let base=selected.to_bytes();
 let loader=bpf_loader::id();let owner=Pubkey::new_from_array(kani::any());
'''
# verifier=0, proof=1, verifierCP=2, master=3, forestCP=4, lane=5, registry=6, entry=7.
for i in range(8):
 source+=f' let mut key{i}=base;key{i}[0]^={i};let key{i}=Pubkey::new_from_array(key{i});let mut lam{i}:u64=kani::any();let mut data{i}=[];\n'
 own='&loader' if i==0 else '&selected' if i==2 else '&owner'
 signer='false' if i in [0,1,2] else 'kani::any()';writable=signer;executable='true' if i==0 else 'false' if i in [1,2] else 'kani::any()'
 source+=f' let info{i}=AccountInfo::new(&key{i},{signer},{writable},&mut lam{i},&mut data{i},{own},{executable},kani::any());\n'
source+=r'''
 let raw:[u8;792]=kani::any();let boxed:Box<[u8]>=Box::new(raw);let bytes=boxed.into_vec();
 let request:[u8;320]=kani::any();let boxed:Box<[u8]>=Box::new(request);
 let plan=PlannedPairForestDispatchV1{selected_verifier:selected,request_bytes:boxed.into_vec()};
 let mut runtime=Runtime{calls:0,reply:Some((returned,bytes)),returned:None,selected};
 let actual=invoke_pair_forest_terminal_with_runtime_v1(plan,&info1,&info3,&info4,&info5,&[info6,info7],&info0,Some(&info2),&mut runtime);
 assert!(runtime.calls==3);
 assert!(matches!(actual,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnProgram.into()));
}
'''
if negative:source=source.replace('assert!(matches!(actual,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnProgram.into()));','assert!(actual.is_ok());')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 if p.endswith('pair_forest_dispatch.rs'):hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n'
 else:hook='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFO_native.patch').write_text(patch);(E/'NFO_CURRENT.json').write_text(json.dumps(dict(mode='full-negative' if negative else 'full-positive',source=source,classification='DIRECT actual frozen caller; ready fixture keys distinct by xor, empty account data and raw320 request. Diagnostic subset, not full PacketDomain; poison decoder proved unreached'),indent=1)+'\n')
