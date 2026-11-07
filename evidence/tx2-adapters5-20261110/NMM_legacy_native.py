from NMM_native import *
from NMM_registry_native import common
import re
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
F='PoolV1VerifierRegistryFormatError'
def constructors(version=1):
 raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/verifier_registry.rs'],text=True)
 out=''
 for name in ['VerifierRegistryV'+str(version),'VerifierRegistryEntryV'+str(version)]:
  body=raw.split('pub struct '+name+' {',1)[1].split('}',1)[0]
  fields=re.findall(r'^\s*pub (\w+): (.*),$',body,re.M)
  values=[]
  for field,t in fields:
   value='NMM_status()' if t=='VerifierEntryStatusV1' else 'kani::any()'
   values.append(field+':'+value)
  out+='fn NMM_any_'+name+'()->'+name+'{'+name+'{'+','.join(values)+'}}\n'
 body=raw.split('pub enum '+F+' {',1)[1].split('}',1)[0]
 variants=re.findall(r'^\s*(\w+),',body,re.M);assert len(variants)>3
 out+='fn NMM_format_error()->'+F+'{let tag:u8=kani::any();kani::assume(tag<'+str(len(variants))+');match tag{'+','.join(str(i)+'=>'+F+'::'+v for i,v in enumerate(variants[:-1]))+',_=>'+F+'::'+variants[-1]+'}}\n'
 variants=re.findall(r'^\s*(\w+)\s*(?:=\s*\d+)?\s*,',raw.split('pub enum VerifierEntryStatusV1 {',1)[1].split('}',1)[0],re.M)
 assert len(variants)==4
 out+='fn NMM_status()->VerifierEntryStatusV1{let t:u8=kani::any();kani::assume(t<4);match t{'+','.join(str(i)+'=>VerifierEntryStatusV1::'+v for i,v in enumerate(variants[:-1]))+',_=>VerifierEntryStatusV1::'+variants[-1]+'}}\n'
 return out
HELP='''
use core::cell::UnsafeCell;
type Reg=Result<VerifierRegistryV1,PoolV1VerifierRegistryFormatError>;
type Ent=Result<VerifierRegistryEntryV1,PoolV1VerifierRegistryFormatError>;
#[derive(Clone)]
struct NMM_Pda {count:usize,len:Option<usize>,byte:Option<u8>,program:u8,reply:Result<Pubkey,solana_program::pubkey::PubkeyError>}
#[repr(C)]
struct NMM_Ctx {
 account:OwnedAccount,image:[u8;320],extent:usize,probe_seed:usize,probe_byte:usize,
 data:UnsafeCell<Option<*const OwnedAccount>>,
 reg:UnsafeCell<Option<(*const u8,usize,Reg)>>,
 ent:UnsafeCell<Option<(*const u8,usize,Ent)>>,
 pda:UnsafeCell<[Option<NMM_Pda>;2]>,nw:UnsafeCell<usize>,nr:UnsafeCell<usize>
}
fn NMM_ctx(a:&OwnedAccount)->&NMM_Ctx {unsafe{&*(a as *const OwnedAccount as *const NMM_Ctx)}}
fn NMM_from_bytes(bytes:&[u8])->&NMM_Ctx{unsafe{&*(bytes.as_ptr().sub(core::mem::offset_of!(NMM_Ctx,image)) as *const NMM_Ctx)}}
fn NMM_from_seeds<'a>(seeds:&'a[&'a[u8]])->&'a NMM_Ctx{
 assert!(seeds.len()==3||seeds.len()==5,"actual legacy seed arity");
 assert!(seeds[1].len()==32,"master key seed extent");
 unsafe{&*(seeds[1].as_ptr().sub(core::mem::offset_of!(OwnedAccount,key)) as *const NMM_Ctx)}
}
fn NMM_data_cut(a:&OwnedAccount)->Result<&[u8],ProgramError>{
 let c=NMM_ctx(a);unsafe{assert!((*c.data.get()).is_none(),"data occurrence unique");c.data.get().write(Some(a as *const _));}
 Ok(&c.image[..c.extent])
}
fn NMM_data_replay(a:&OwnedAccount)->Result<&[u8],ProgramError>{
 let c=NMM_ctx(a);let arg=unsafe{(*c.data.get()).take()};assert!(arg==Some(a as *const _),"exact data argument");Ok(&c.image[..c.extent])
}
fn NMM_reg_cut(bytes:&[u8])->Reg{
 let out=if kani::any(){Ok(NMM_any_VerifierRegistryV1())}else{Err(NMM_format_error())};let c=NMM_from_bytes(bytes);
 unsafe{assert!((*c.reg.get()).is_none(),"registry occurrence unique");c.reg.get().write(Some((bytes.as_ptr(),bytes.len(),out)));}out
}
fn NMM_reg_replay(bytes:&[u8])->Reg{
 let c=NMM_from_bytes(bytes);let record=unsafe{(*c.reg.get()).take()};assert!(record.is_some(),"registry reply present");
 match record{Some((p,n,r))=>{assert!(p==bytes.as_ptr()&&n==bytes.len(),"exact registry arguments");r},None=>Err(PoolV1VerifierRegistryFormatError::WrongLength)}
}
fn NMM_ent_cut(bytes:&[u8])->Ent{
 let out=if kani::any(){Ok(NMM_any_VerifierRegistryEntryV1())}else{Err(NMM_format_error())};let c=NMM_from_bytes(bytes);
 unsafe{assert!((*c.ent.get()).is_none(),"entry occurrence unique");c.ent.get().write(Some((bytes.as_ptr(),bytes.len(),out)));}out
}
fn NMM_ent_replay(bytes:&[u8])->Ent{
 let c=NMM_from_bytes(bytes);let record=unsafe{(*c.ent.get()).take()};assert!(record.is_some(),"entry reply present");
 match record{Some((p,n,r))=>{assert!(p==bytes.as_ptr()&&n==bytes.len(),"exact entry arguments");r},None=>Err(PoolV1VerifierRegistryFormatError::WrongLength)}
}
fn NMM_pda_cut(seeds:&[&[u8]],program:&Pubkey)->Result<Pubkey,solana_program::pubkey::PubkeyError>{
 use solana_program::pubkey::PubkeyError::*;
 let tag:u8=kani::any();kani::assume(tag<4);let out=match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(MaxSeedLengthExceeded),2=>Err(InvalidSeeds),_=>Err(IllegalOwner)};
 let c=NMM_from_seeds(seeds);let i=c.probe_seed;let j=c.probe_byte;assert!(i<5&&j<32,"probe bounds");
 for seed in seeds {assert!(seed.len()<=32,"runtime seed extent domain");}
 let len=if i<seeds.len(){Some(seeds[i].len())}else{None};
 let byte=if i<seeds.len()&&j<seeds[i].len(){Some(seeds[i][j])}else{None};
 let r=NMM_Pda{count:seeds.len(),len,byte,program:program.to_bytes()[j],reply:out.clone()};unsafe{let n=*c.nw.get();assert!(n<2,"legacy PDA prefix bound");(*c.pda.get())[n]=Some(r);*c.nw.get()=n+1;}out
}
fn NMM_pda_replay(seeds:&[&[u8]],program:&Pubkey)->Result<Pubkey,solana_program::pubkey::PubkeyError>{
 let c=NMM_from_seeds(seeds);let record=unsafe{let n=*c.nr.get();assert!(n<2,"replayed PDA prefix bound");*c.nr.get()=n+1;(*c.pda.get())[n].take()};
 assert!(record.is_some(),"same PDA reply present");match record{Some(r)=>{let i=c.probe_seed;let j=c.probe_byte;let len=if i<seeds.len(){Some(seeds[i].len())}else{None};let byte=if i<seeds.len()&&j<seeds[i].len(){Some(seeds[i][j])}else{None};assert!(r.count==seeds.len()&&r.program==program.to_bytes()[j],"exact PDA program window and arity");assert!(r.len==len&&r.byte==byte,"exact PDA seed length and byte window");r.reply},None=>Err(solana_program::pubkey::PubkeyError::InvalidSeeds)}
}
fn NMM_account<const N:usize>()->NMM_Ctx{
 let original:[u8;N]=kani::any();let bytes:Box<[u8]>=Box::new(original);let bytes=bytes.into_vec();
 NMM_Ctx{account:OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(N),bytes:Ok(bytes)},image:kani::any(),extent:N,probe_seed:0,probe_byte:0,data:UnsafeCell::new(None),reg:UnsafeCell::new(None),ent:UnsafeCell::new(None),pda:UnsafeCell::new([None,None]),nw:UnsafeCell::new(0),nr:UnsafeCell::new(0)}
}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(super::OwnedAccount::data,NMM_data_cut)]
#[kani::stub(aspis_statement::pool_v1::decode_verifier_registry_v1,NMM_reg_cut)]
#[kani::stub(aspis_statement::pool_v1::decode_verifier_registry_entry_v1,NMM_ent_cut)]
#[kani::stub(solana_program::pubkey::Pubkey::create_program_address,NMM_pda_cut)]
'''
def attempt(a,mode,branch="all",version="1"):
 version=int(version)
 ref=(E/'NMM_FROZEN_234.rs').read_text().replace('fn authenticate_invariant_release_registry(','fn NMM_reference(',1)
 for x in ['registry_account','entry_account']:ref=ref.replace(x+'.data()','NMM_data_replay('+x+')')
 ref=ref.replace('decode_verifier_registry_v'+str(version)+'(','NMM_reg_replay(').replace('decode_verifier_registry_entry_v'+str(version)+'(','NMM_ent_replay(').replace('Pubkey::create_program_address(','NMM_pda_replay(')
 text=common()+constructors(version)+HELP+ref+ANN+'''fn stage(){
 let mut master=any_master();master.verifier_policy.flags &= !POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT;
 let mut ma=NMM_account::<1>();ma.probe_seed=kani::any();ma.probe_byte=kani::any();kani::assume(ma.probe_seed<5&&ma.probe_byte<32);let reg=NMM_account::<128>();let ent=NMM_account::<192>();
 let verifier=Pubkey::new_from_array(kani::any());let pool=Pubkey::new_from_array(kani::any());let slot:u64=kani::any();
 let obs:usize=kani::any();kani::assume(obs<128);let before=reg.account.bytes.as_ref().unwrap()[obs];
 let native=authenticate_invariant_release_registry(&verifier,&pool,&ma.account,&master,&reg.account,&ent.account,slot);
 let reference=NMM_reference(&verifier,&pool,&ma.account,&master,&reg.account,&ent.account,slot);
 assert!(native==reference,"complete legacy outcome with same typed replies");
 assert!(reg.account.bytes.as_ref().unwrap()[obs]==before,"original immutable byte frame");
 unsafe{assert!((*reg.data.get()).is_none()&&(*ent.data.get()).is_none()&&(*reg.reg.get()).is_none()&&(*ent.ent.get()).is_none(),"no unmatched data or decoder call");assert!(*ma.nw.get()==*ma.nr.get(),"exact PDA prefix length");}
}
'''
 if version==2:
  text=text.replace('VerifierRegistryV1','VerifierRegistryV2').replace('VerifierRegistryEntryV1','VerifierRegistryEntryV2')
  text=text.replace('decode_verifier_registry_v1,NMM_reg_cut','decode_verifier_registry_v2,NMM_reg_cut').replace('decode_verifier_registry_entry_v1,NMM_ent_cut','decode_verifier_registry_entry_v2,NMM_ent_cut')
  text=text.replace('master.verifier_policy.flags &= !POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT;','master.verifier_policy.flags |= POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT;')
  text=text.replace('let reg=NMM_account::<128>();let ent=NMM_account::<192>();','let reg=NMM_account::<256>();let ent=NMM_account::<320>();').replace('kani::assume(obs<128);','kani::assume(obs<256);')
 if branch=='first_error':
  old='let tag:u8=kani::any();kani::assume(tag<4);let out=match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(MaxSeedLengthExceeded),2=>Err(InvalidSeeds),_=>Err(IllegalOwner)};'
  new='let tag:u8=kani::any();kani::assume(tag<3);let out=match tag{0=>Err(MaxSeedLengthExceeded),1=>Err(InvalidSeeds),_=>Err(IllegalOwner)};'
  assert old in text;text=text.replace(old,new)
  text=text.replace('r.reply},None=>Err(solana_program::pubkey::PubkeyError::InvalidSeeds)', 'match r.reply{Err(e)=>Err(e),Ok(_)=>{assert!(false,"selected first PDA error arm");Err(solana_program::pubkey::PubkeyError::InvalidSeeds)}}},None=>Err(solana_program::pubkey::PubkeyError::InvalidSeeds)')
 if branch in ['second_error','all_ok']:
  assert version==1,'V2 second call has no local argument channel; never launch this shape'
  old='let tag:u8=kani::any();kani::assume(tag<4);let out=match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(MaxSeedLengthExceeded),2=>Err(InvalidSeeds),_=>Err(IllegalOwner)};'
  if branch=='second_error':
   new='let c=NMM_from_seeds(seeds);let first=unsafe{*c.nw.get()==0};let tag:u8=kani::any();kani::assume(tag<3);let out=if first{Ok(Pubkey::new_from_array(kani::any()))}else{match tag{0=>Err(MaxSeedLengthExceeded),1=>Err(InvalidSeeds),_=>Err(IllegalOwner)}};'
  else:new='let out=Ok(Pubkey::new_from_array(kani::any()));'
  assert old in text;text=text.replace(old,new)
 if mode=='reply':text=text.replace('Some((p,n,r))=>{assert!(p==bytes.as_ptr()&&n==bytes.len(),"exact registry arguments");r}', 'Some((p,n,r))=>{assert!(p==bytes.as_ptr()&&n==bytes.len(),"exact registry arguments");r.map(|mut value|{value.bump=0;value})}')
 if mode=='argument':text=text.replace('&master,&reg.account,&ent.account,slot);','&master,&ent.account,&reg.account,slot);',1)
 if mode=='footprint':text=text.replace('let byte=if i<seeds.len()&&j<seeds[i].len(){Some(seeds[i][j])}else{None};','let byte=None;',1)
 if mode=='copy':text=text.replace('assert!(native==reference,','let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/NMM_legacy.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::NMM_legacy::stage',P,'NMM_legacy',text,mode)
if __name__=='__main__':
 import sys
 r=attempt(*sys.argv[1:]);sys.exit(r['exit_status'])
