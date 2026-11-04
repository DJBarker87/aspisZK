"""Direct frozen generic Pool caller on a ready account fixture; no decoder is reached."""
from pathlib import Path
import subprocess,difflib,json,sys
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1] if len(sys.argv)>1 else 'program'
assert mode in ['program','negative','cpi','cpi-negative','missing','missing-negative','length','length-negative','args','args-request','args-meta','args-flags','args-infos']
negative=mode.endswith('negative') or mode=='negative'
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
if mode.startswith('args'):
 import re
 for i in range(1,8):source=source.replace(f'let mut key{i}=base;key{i}[0]^={i};',f'let key{i}:[u8;32]=kani::any();')
 at=' let raw:[u8;792]=kani::any();'
 constraints=' kani::assume(key1!=selected&&key2!=selected&&key2!=key1&&key2!=key3&&key2!=key4&&key2!=key5&&key2!=key6&&key2!=key7);\n'
 source=source.replace(at,constraints+at)
 source=source.replace('let loader=bpf_loader::id();','let loader=match kani::any::<u8>()%3{0=>bpf_loader::id(),1=>bpf_loader_upgradeable::id(),_=>loader_v4::id()};')
 source=source.replace('selected:Pubkey}', 'selected:Pubkey,request:*const u8,request_byte:u8,j:usize,keys:[[u8;32];7],meta:usize}')
 check='assert!(instruction.data.len()==320&&core::ptr::eq(instruction.data.as_ptr(),self.request)&&instruction.data[self.j]==self.request_byte);assert!(instruction.accounts[self.meta].pubkey.to_bytes()==self.keys[self.meta]&&!instruction.accounts[self.meta].is_signer&&!instruction.accounts[self.meta].is_writable);assert!(infos[self.meta].key.to_bytes()==self.keys[self.meta]&&infos[7].key==&self.selected);'
 source=source.replace('self.calls=2;self.returned',check+'self.calls=2;self.returned')
 source=source.replace('let plan=PlannedPairForestDispatchV1', 'let request_ptr=boxed.as_ptr();let j:usize=kani::any();kani::assume(j<320);let request_byte=boxed[j];let meta:usize=kani::any();kani::assume(meta<7);let keys=[key1.to_bytes(),key3.to_bytes(),key4.to_bytes(),key5.to_bytes(),key6.to_bytes(),key7.to_bytes(),key2.to_bytes()];\n let plan=PlannedPairForestDispatchV1')
 source=source.replace('returned:None,selected}', 'returned:None,selected,request:request_ptr,request_byte,j,keys,meta}')
 if mode=='args-request':source=source.replace('instruction.data[self.j]==self.request_byte','instruction.data[self.j]==(self.request_byte^1)')
 if mode=='args-meta':source=source.replace('self.keys[self.meta]&&!instruction', '{let mut wrong=self.keys[self.meta];wrong[0]^=1;wrong}&&!instruction')
 if mode=='args-flags':source=source.replace('&&!instruction.accounts[self.meta].is_writable','&&instruction.accounts[self.meta].is_writable')
 if mode=='args-infos':source=source.replace('infos[7].key==&self.selected','infos[7].key.to_bytes()==self.keys[6]')
if mode.startswith('cpi'):
 source=source.replace('kani::assume(returned!=selected);','')
 source=source.replace('selected:Pubkey}', 'selected:Pubkey,code:u64}')
 source=source.replace('self.returned=self.reply.take();Ok(())', 'Err(ProgramError::from(self.code))')
 source=source.replace('let selected=Pubkey::new_from_array(kani::any());', 'let code:u64=kani::any();kani::assume(code!=0);let selected=Pubkey::new_from_array(kani::any());')
 source=source.replace('returned:None,selected}', 'returned:None,selected,code}')
 source=source.replace('runtime.calls==3','runtime.calls==2')
 source=source.replace('PoolV1ProgramError::InvalidVerifierReturnProgram.into()', 'ProgramError::from(code)')
if mode.startswith('missing'):
 source=source.replace('kani::assume(returned!=selected);','')
 source=source.replace('reply:Some((returned,bytes))','reply:None')
 source=source.replace('PoolV1ProgramError::InvalidVerifierReturnProgram.into()', 'PoolV1ProgramError::MissingVerifierReturnData.into()')
if mode.startswith('length'):
 source=source.replace('kani::assume(returned!=selected);', 'let returned=selected;let length:usize=kani::any();kani::assume(length<=1024&&length!=792);')
 source=source.replace('let raw:[u8;792]', 'let raw:[u8;1024]')
 source=source.replace('let bytes=boxed.into_vec();','let mut bytes=boxed.into_vec();bytes.truncate(length);')
 source=source.replace('PoolV1ProgramError::InvalidVerifierReturnProgram.into()', 'PoolV1ProgramError::InvalidVerifierReturnData.into()')
if negative:
 import re
 source=re.sub(r'assert!\(matches!\(actual,Err\(e\) if e==[^;]+;','assert!(actual.is_ok());',source)
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 if p.endswith('pair_forest_dispatch.rs'):hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n'
 else:hook='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFO_native.patch').write_text(patch);(E/'NFO_CURRENT.json').write_text(json.dumps(dict(mode='full-'+mode,source=source,classification='DIRECT actual frozen caller; ready fixture keys distinct by xor, empty account data and raw320 request. Diagnostic subset, not full PacketDomain; poison decoder proved unreached'),indent=1)+'\n')
