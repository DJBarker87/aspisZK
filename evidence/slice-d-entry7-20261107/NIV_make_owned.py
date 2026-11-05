from pathlib import Path
E=Path(__file__).resolve().parent
s=''.join(l[1:] for l in (E/'NIV_forward.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
reply=s[s.index('fn reply('):s.index('fn log_child')].replace('fn reply(','fn full_reply(')
t='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
'''+reply+'''fn err(p:&Pubkey)->ProgramError{match full_reply(p){Ok(())=>ProgramError::Custom(0),Err(e)=>e}}
fn owned()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:false,is_writable:false,executable:false,length:Ok(kani::any()),bytes:Err(ProgramError::InvalidAccountData)}}
fn no_decode(_: &[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{panic!("decoder past selected prefix")}
fn distinct3<const N:usize>(a:&[&OwnedAccount;N])->ProgramResult{assert_eq!(N,3);if a[0].key()==a[1].key()||a[0].key()==a[2].key()||a[1].key()==a[2].key(){Err(ProgramError::InvalidArgument)}else{Ok(())}}
fn check<const G:usize>(wrong:bool){
 let p=Pubkey::new_from_array(kani::any());let seed=Pubkey::new_from_array(kani::any());let mut a=[owned(),owned(),owned()];
 kani::assume(a[0].key!=a[1].key&&a[0].key!=a[2].key&&a[1].key!=a[2].key);
 a[2].owner=p;a[2].is_writable=true;a[2].length=Ok(1768);
 let mut expected=ProgramError::InvalidAccountData;
 match G {
  0=>{a[1].key=a[0].key;expected=ProgramError::InvalidArgument;},
  1=>a[0].is_writable=true,2=>a[0].is_signer=true,3=>a[0].executable=true,
  4=>a[1].is_writable=true,5=>a[1].is_signer=true,6=>a[1].executable=true,
  7=>{kani::assume(seed!=p);a[2].owner=seed;},8=>a[2].is_signer=true,9=>a[2].executable=true,10=>a[2].is_writable=false,
  11=>{a[2].length=Err(ProgramError::AccountBorrowFailed);a[2].bytes=Err(ProgramError::AccountBorrowFailed);expected=ProgramError::AccountBorrowFailed;},
  12=>{let n:usize=kani::any();kani::assume(n!=1768);a[2].length=Ok(n);},
  13=>{a[2].bytes=Err(ProgramError::InvalidAccountData);expected=ProgramError::InvalidAccountData;},
  14=>{a[2].bytes=Ok(Vec::new());a[1].bytes=Err(err(&seed));expected=err(&seed);},
  _=>unreachable!()
 }
 let a=core::mem::ManuallyDrop::new(a);let data=[3,if kani::any(){10}else{11}];
 let r=stage1_owned(&p,&a[..],&data);
 let good=match r{Err(e)=>e==expected,Ok(_)=>false};assert!(good!=wrong,"ordered owned rejection prefix and full error reply");
}
'''
for i in range(15):
 for neg in [False,True]:
  t+='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(super::require_distinct_accounts::<3>,distinct3)]\n#[kani::stub(crate::r1_pool_adapter::decode_public_statement_box,no_decode)]\nfn guard_'+str(i)+('_wrong' if neg else '')+'(){check::<'+str(i)+'>('+str(neg).lower()+');}\n'
p='programs/r1-cost-probe/src/NIV_owned.rs';(E/'NIV_owned.patch').write_text('--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(t.splitlines()))+' @@\n'+''.join('+'+l for l in t.splitlines(True)))
