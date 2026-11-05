from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());adapter=I[P+'r1_pool_adapter.rs'];owned=I[P+'r1_pool_adapter_owned.rs']
# The proposed zero cut is redundant with the already CLOSED NFU_ZeroPort; remove it.
z=json.loads((E/'NGL_ZERO_SOURCE_ERASURE.json').read_text());owned=owned.replace(z['instrumented_body'],z['frozen_body'])
attrs={
 'fn readonly_meta_ok(':'#[cfg_attr(kani,kani::ensures(|r| (*r == NGL_adapter::metadata_ref(owner,expected,is_signer,is_writable,executable)) != cfg!(NGL_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n',
 'fn require_readonly_account(account: &OwnedAccount, owner: &Pubkey) -> ProgramResult {':'#[cfg_attr(kani,kani::ensures(|r| (*r == NGL_owned::readonly_ref(account,owner)) != cfg!(NGL_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n',
 '    fn data_len(&self) -> Result<usize, ProgramError> {':'    #[cfg_attr(kani,kani::requires(NGL_owned::length_domain(&self.length)))]\n    #[cfg_attr(kani,kani::ensures(|r| (*r == self.length) != cfg!(NGL_invert)))]\n    #[cfg_attr(kani,kani::modifies())]\n',
 'fn require_verifier_checkpoint(account: &OwnedAccount, program_id: &Pubkey, writable: bool) -> ProgramResult {':'#[cfg_attr(kani,kani::requires(NGL_owned::checkpoint_domain(account)))]\n#[cfg_attr(kani,kani::ensures(|r| (*r == NGL_owned::checkpoint_ref(account,program_id,writable)) != cfg!(NGL_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n'
}
for sig,attr in attrs.items():
 target=adapter if sig.startswith('fn readonly_meta') else owned
 assert target.count(sig)==1
 target=target.replace(sig,attr+sig,1)
 if sig.startswith('fn readonly_meta'):adapter=target
 else:owned=target
h=I[P+'NGL_adapter.rs'];h+='''
pub(super) fn metadata_ref(owner:&Pubkey,expected:&Pubkey,s:bool,w:bool,e:bool)->ProgramResult{if owner!=expected||s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())}}
#[kani::proof_for_contract(readonly_meta_ok)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn metadata_contract(){let a=Pubkey::new_from_array(kani::any());let b=Pubkey::new_from_array(kani::any());let _=readonly_meta_ok(&a,&b,kani::any(),kani::any(),kani::any());}
'''
g=I[P+'NGL_owned.rs'];g+='''
pub(super) fn length_domain(r:&Result<usize,ProgramError>)->bool{matches!(r,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData))}
pub(super) fn checkpoint_domain(a:&OwnedAccount)->bool{matches!(a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed))}
pub(super) fn readonly_ref(a:&OwnedAccount,k:&Pubkey)->ProgramResult{if a.owner!=*k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())}}
pub(super) fn checkpoint_ref(a:&OwnedAccount,k:&Pubkey,w:bool)->ProgramResult{if a.owner!=*k||a.is_signer||a.executable||a.is_writable!=w{Err(ProgramError::InvalidAccountData)}else{match a.length{Err(ProgramError::AccountBorrowFailed)=>Err(ProgramError::AccountBorrowFailed),Ok(1768)=>Ok(()),_=>Err(ProgramError::InvalidAccountData)}}}
#[kani::proof_for_contract(require_readonly_account)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_contract(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let _=require_readonly_account(&a,&k);}
#[kani::proof_for_contract(OwnedAccount::data_len)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_contract(){let mut a=core::mem::ManuallyDrop::new(account());let tag:u8=kani::any();kani::assume(tag<3);a.length=match tag{0=>Ok(kani::any()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};let _=a.data_len();}
#[kani::proof_for_contract(require_verifier_checkpoint)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_contract(){let mut a=core::mem::ManuallyDrop::new(account());a.length=if kani::any(){Ok(kani::any())}else{Err(ProgramError::AccountBorrowFailed)};let k=Pubkey::new_from_array(kani::any());let _=require_verifier_checkpoint(&a,&k,kani::any());}
'''
update({P+'r1_pool_adapter.rs':adapter,P+'r1_pool_adapter_owned.rs':owned,P+'NGL_adapter.rs':h,P+'NGL_owned.rs':g},'actual_contracts')
(E/'NGL_CONTRACT_ANNOTATIONS.json').write_text(json.dumps(attrs,indent=1)+'\n')
