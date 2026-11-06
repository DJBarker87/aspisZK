from pathlib import Path
E=Path(__file__).resolve().parent
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log { account:*const OwnedAccount, owner:*const Pubkey, writable:bool, calls:u8, failed:bool, kind:u8 }
fn any_account()->OwnedAccount { let borrowed:bool=kani::any();OwnedAccount { key:Pubkey::new_from_array(kani::any()), owner:Pubkey::new_from_array(kani::any()), is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:if !borrowed{Ok(kani::any())}else{Err(ProgramError::AccountBorrowFailed)},bytes:Err(if borrowed{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData}) } }
fn expected(a:&OwnedAccount,p:&Pubkey,kind:u8,w:bool)->ProgramResult {
 match kind {
  0=>if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())},
  1=>if a.owner()!=p||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())},
  _=>{if a.owner()!=p||a.is_signer||a.executable||a.is_writable!=w{return Err(ProgramError::InvalidAccountData)};if a.data_len()?!=1768{return Err(ProgramError::InvalidAccountData)};Ok(())}
 }
}
fn logged_guard(a:&OwnedAccount,p:&Pubkey,kind:u8,w:bool,l:&mut Log)->ProgramResult {
 l.account=a;l.owner=p;l.writable=w;l.kind=kind;l.calls+=1;
 let failed:bool=kani::any();let borrowed:bool=kani::any();
 let reply=if failed{if borrowed{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)}}else{Ok(())};
 // Complete packet law on the SAME arguments. Only this helper's reachable errors.
 kani::assume(reply==expected(a,p,kind,w));l.failed=failed;reply
}
fn cut(a:&OwnedAccount,p:&Pubkey,kind:u8,w:bool,l:&mut Log)->ProgramResult {
 logged_guard(a,p,kind,w,l)?;
 Ok(())
}
fn run<const KIND:u8,const WRITABLE:bool,const WRONG:bool>(){
 let a=any_account();let p=Pubkey::new_from_array(kani::any());
 let before=(a.key.to_bytes(),a.owner.to_bytes(),a.is_signer,a.is_writable,a.executable,a.data_len());
 let mut l=Log{account:core::ptr::null(),owner:core::ptr::null(),writable:kani::any(),calls:0,failed:kani::any(),kind:kani::any()};
 let reply=expected(&a,&p,KIND,WRITABLE);let out=cut(&a,&p,KIND,WRITABLE,&mut l);
 let j:usize=kani::any();kani::assume(j<32);
 let good=out==reply&&l.account==&a as *const OwnedAccount&&l.owner==&p as *const Pubkey&&l.writable==WRITABLE&&l.kind==KIND&&l.calls==1&&l.failed==out.is_err()&&a.key.to_bytes()[j]==before.0[j]&&a.owner.to_bytes()[j]==before.1[j]&&a.is_signer==before.2&&a.is_writable==before.3&&a.executable==before.4&&a.data_len()==before.5;
 assert!(good!=WRONG,"NJD guard cut arguments complete reply and frame");
}
'''
rows=[('s1_readonly_proof',0,False,'TX1:345','proof_account'),('s1_readonly_public',0,False,'TX1:345','public_account'),('s1_checkpoint',2,True,'TX1:345','checkpoint_account'),('auth_readonly_proof',0,False,'TX2:233','proof_account'),('auth_checkpoint',2,False,'TX2:233','verifier_checkpoint'),('auth_readonly_master',1,False,'TX2:233','master_account'),('auth_readonly_checkpoint',1,False,'TX2:233','checkpoint_account'),('auth_readonly_lane',1,False,'TX2:233','lane_account')]
for name,k,w,_,_ in rows:
 for bad in [False,True]:
  s+='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn '''+name+('_wrong' if bad else '')+'(){run::<'+str(k)+','+str(w).lower()+','+str(bad).lower()+'>()}\n'
p='programs/r1-cost-probe/src/NJD_stages.rs'
(E/'NJD_guards.patch').write_text('--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l for l in s.splitlines(True)))
import json
(E/'NJD_GUARD_CUTS.json').write_text(json.dumps([dict(name=n,kind=k,writable=w,row=r,argument=a,scope='metadata/length producer; bytes deferred Err only, full byte-carrier frame remains OPEN') for n,k,w,r,a in rows],indent=1))
