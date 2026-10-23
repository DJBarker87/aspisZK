#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
rev='b2727acd3abf79315d18b754a260f58f4b1c6326';p='programs/r1-cost-probe/src/r1_pool_adapter.rs'
source=subprocess.check_output(['git','-C',str(R),'show',rev+':'+p],text=True)
def cut(n):
 a=source.index('fn '+n);e=source.index('{',a)+1;d=1
 while d:d+=(source[e]=='{')-(source[e]=='}');e+=1
 return source[a:e]
prefix=cut('stage1');prefix=prefix[:prefix.index('    if checkpoint_data.iter().any')]+'''    drop(checkpoint_data);
    Ok(())
}
'''
s='''#![allow(dead_code,unused_mut)]
use solana_program::{account_info::AccountInfo,program_error::ProgramError,entrypoint::ProgramResult,pubkey::Pubkey};
enum Variant {S2}
mod verifier {pub fn checkpoint_size(_:super::Variant)->usize{1768}}
'''+ '\n'.join(cut(n) for n in ['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts'])+'\n'+prefix+r'''
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof]
#[kani::unwind(40)]
fn actual_sdk_prefix_guard_order() {
 let program=Pubkey::new_from_array(kani::any());let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owner=Pubkey::new_from_array(kani::any());let readonly0:bool=kani::any();let readonly1:bool=kani::any();
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();
 let mut lamports=[0u64;3];let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 let mut proof=[];let mut public=[];let mut cp=[0u8;1768];let cp_len:usize=kani::any();kani::assume(cp_len<=1768);
 let a0=AccountInfo::new(&keys[0],!readonly0,false,l0,&mut proof,&owner,false,0);
 let a1=AccountInfo::new(&keys[1],false,!readonly1,l1,&mut public,&owner,false,0);
 let a2=AccountInfo::new(&keys[2],signer,writable,l2,&mut cp[..cp_len],&owner,executable,0);
 let accounts=[a0,a1,a2];
 let held_shared=if kani::any(){Some(accounts[2].try_borrow_data().unwrap())}else{None};
 let held_exclusive=if held_shared.is_none() && kani::any(){Some(accounts[2].try_borrow_mut_data().unwrap())}else{None};
 let bytes:[u8;3]=kani::any();let data_len:usize=kani::any();kani::assume(data_len<=3);
 let accounts_len:usize=kani::any();kani::assume(accounts_len<=3);
 let data=&bytes[..data_len];
 let actual=stage1(&program,&accounts[..accounts_len],data);
 let expected=if !(data==[3,10]||data==[3,11]) || accounts_len!=3 {0}
  else if keys[0]==keys[1]||keys[0]==keys[2]||keys[1]==keys[2]{1}
  else if !readonly0||!readonly1||owner!=program||signer||executable||!writable{2}
  else if held_exclusive.is_some(){3}
  else if cp_len!=1768{2}
  else if held_shared.is_some(){3}
  else{4};
 assert!(matches!((&actual,expected),(Err(ProgramError::InvalidInstructionData),0)|(Err(ProgramError::InvalidArgument),1)|(Err(ProgramError::InvalidAccountData),2)|(Err(ProgramError::AccountBorrowFailed),3)|(Ok(()),4)));
 drop(held_shared);drop(held_exclusive);assert!(accounts[2].try_borrow_mut_data().is_ok());
 kani::cover!(expected==0,"instruction reject");kani::cover!(expected==1,"duplicate reject");kani::cover!(expected==2,"metadata reject");kani::cover!(expected==3,"borrow reject");kani::cover!(expected==4,"prefix succeeds");
}
}
'''
(O/'src/lib.rs').write_text(s);(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-prefix-guards"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=rev,path=p,prefix=prefix,source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification='Exact stage1 prefix through the checkpoint exclusive acquisition. Replaced suffix by drop+Ok at modular exit. Domain data/account lengths 0..3, CP length0..1768; longer lengths reject at the same initial equality/length tests but are not separately model checked. Proof/public readonly errors represented by one metadata bit each; full individual metadata guards separately certified. Initial checkpoint shared/exclusive guards exercise both RefCell error positions.'),indent=2)+'\n')
