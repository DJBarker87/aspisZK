from pathlib import Path
import json,difflib,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent; I=E.parent/'pool-b3-20261106'
sys.path.insert(0,str(E))
from NIO_frozen_identity import frozen,apply
def stage(path,source,kind,mode,domain,remaining,extra=None):
 files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((I/'NHP_INCLUDES.json').read_text()).items()})
 apply(files,(I/'NHP_KMX_copy_stubs.patch').read_text())
 original=files[path].decode();after=original+'\n#[cfg(kani)]\nmod NIO_native {\n'+source+'\n}\n'
 root='programs/aspis-pool/src/lib.rs'
 root_before=files[root].decode();root_after='#![cfg_attr(kani, feature(allocator_api))]\n'+root_before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n#[cfg(kani)]\npub use KMX_stubs as NIO_KMX;\n'
 root_patch=''.join(difflib.unified_diff(root_before.splitlines(True),root_after.splitlines(True),fromfile='a/'+root,tofile='b/'+root))
 patch=root_patch+''.join(difflib.unified_diff(original.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 (E/'NIO_native.patch').write_text(patch)
 x=dict(kind=kind,mode=mode,domain=domain,source=source,modifies=[],production_credit=False,remaining=remaining)
 if extra:x.update(extra)
 (E/'NIO_CURRENT.json').write_text(json.dumps(x,indent=2)+'\n')

def attrs():
 return '\n'.join(json.loads((E/'NIO_KMX_ATTRIBUTES.json').read_text())).replace('NHP_KMX','NIO_KMX')


def account_setup(n):
 s='use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};\n'
 for i in range(n):
  s+=f'let k{i}=Pubkey::new_from_array(kani::any()); let mut l{i}:u64=kani::any(); let mut d{i}=[kani::any::<u8>()]; let a{i}=AccountInfo::new(&k{i},false,true,&mut l{i},&mut d{i},&k{i},false,0);\n'
 return s

def infos(which,j,negative):
 function='exact_transfer_account_infos_v1' if which=='deposit' else 'exact_withdrawal_transfer_account_infos_v1'
 mapping=[1,0,3,2,4] if which=='deposit' else [1,0,2,3,4]
 s=account_setup(6)
 s+='kani::assume(k0!=k1 && k0!=k2 && k0!=k3 && k0!=k4 && k1!=k2 && k1!=k3 && k1!=k4 && k2!=k3 && k2!=k4 && k3!=k4);\n'
 # Guarded key is arbitrary, disjoint from every token key: exact cut precondition, not derived here.
 s+='kani::assume(k5!=k0 && k5!=k1 && k5!=k2 && k5!=k3 && k5!=k4); let _held=a5.try_borrow_mut_data().unwrap();\n'
 s+='let accounts=[a0,a1,a2,a3,a4]; let result=super::'+function+'(&accounts).unwrap();\n'
 s+=f'let observed=&result[{j}]; let expected=&accounts[{mapping[j]}];\n'
 if negative:s+='let observed=&a5;\n'
 s+='assert!(observed.key==expected.key); assert!(alloc::rc::Rc::ptr_eq(&observed.data,&expected.data)); assert!(alloc::rc::Rc::ptr_eq(&observed.lamports,&expected.lamports)); assert!(observed.key!=a5.key);\n'
 callee='exact_five_accounts' if which=='deposit' else 'exact_five_withdrawal_accounts'
 stub="fn NIO_five<'s,'i>(accounts:&'s [solana_program::account_info::AccountInfo<'i>])->Result<[&'s solana_program::account_info::AccountInfo<'i>;5],solana_program::program_error::ProgramError>{ match accounts { [a,b,c,d,e]=>Ok([a,b,c,d,e]), _=>Err(if accounts.len()<5 {solana_program::program_error::ProgramError::NotEnoughAccountKeys} else {solana_program::program_error::ProgramError::InvalidArgument}) } }\n"
 return stub+attrs()+'\n#[kani::stub(super::'+callee+',NIO_five)]\n#[kani::proof]\nfn certificate(){'+s+'}\n' 


def close_account(mode,negative):
 stub="""
fn NIO_assign<'a:'a>(a:&solana_program::account_info::AccountInfo<'a>,_owner:&solana_program::pubkey::Pubkey){
 assert!(a.try_borrow_mut_data().is_ok()); assert!(a.try_borrow_mut_lamports().is_ok());
}
fn NIO_resize<'a:'a>(a:&solana_program::account_info::AccountInfo<'a>,n:usize)->solana_program::entrypoint::ProgramResult{
 assert!(n==0); assert!(a.try_borrow_mut_data().is_ok()); assert!(a.try_borrow_mut_lamports().is_ok());
 if kani::any::<bool>() {Ok(())}else{Err(solana_program::program_error::ProgramError::InvalidRealloc)}
}
"""
 body=account_setup(2)
 body+='kani::assume(k0!=k1); let before0=a0.lamports(); let before1=a1.lamports(); let data_before=a0.try_borrow_data().unwrap()[0];\n'
 if mode==1:body+='let ambient=a0.try_borrow_data().unwrap();\n'
 if mode==2:body+='let ambient=a1.try_borrow_lamports().unwrap();\n'
 if mode==3:body+='let ambient=a0.try_borrow_lamports().unwrap();\n'
 body+='let result=super::close_program_account_v1(&a0,&a1,&k0,1);\n'
 if mode:
  body+='assert!(result==Err(ProgramError::AccountBorrowFailed)); assert!(a0.lamports()==before0); assert!(a1.lamports()==before1);\n'
 else:
  body+='match before1.checked_add(before0) {None=>{assert!(result==Err(crate::error::PoolV1ProgramError::ArithmeticOverflow.into())); assert!(a0.lamports()==before0);assert!(a1.lamports()==before1);},Some(sum)=>{assert!(result==Ok(()) || result==Err(ProgramError::InvalidRealloc));assert!(a0.lamports()==0);assert!(a1.lamports()==sum);}}\n'
 if mode==1:body+='assert!(a0.try_borrow_data().unwrap()[0]==data_before);\n'
 else:body+='assert!(a0.try_borrow_data().unwrap()[0]==0xff);\n'
 if mode:body+='drop(ambient);\n'
 if negative:body+='let _unreleased=a1.try_borrow_mut_data().unwrap();\n'
 body+='assert!(a0.try_borrow_mut_data().is_ok());assert!(a1.try_borrow_mut_data().is_ok());assert!(a0.try_borrow_mut_lamports().is_ok());assert!(a1.try_borrow_mut_lamports().is_ok());\n'
 return stub+attrs()+"\n#[kani::stub(solana_program::account_info::AccountInfo::assign,NIO_assign)]\n#[kani::stub(solana_program::account_info::AccountInfo::resize,NIO_resize)]\n#[kani::proof]\nfn certificate(){"+body+'}\n'



def meta_cut(which,j,negative):
 text=frozen()['programs/aspis-pool/src/vault.rs'].decode()
 pieces=text.split('    let instruction = Instruction {')[1:]
 literal='let instruction = Instruction {'+pieces[0 if which=='deposit' else 1].split('    };',1)[0]+'    };\n'
 # Actual constructor bytes are committed once, and reused unchanged per window.
 pin=E/'NIO_META_CUTS.json';cuts=json.loads(pin.read_text()) if pin.exists() else {}
 import hashlib
 cuts[which]=dict(source_sha256=hashlib.sha256(text.encode()).hexdigest(),literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),literal=literal,domain='Actual arbitrary constructor pre-state; keys inherited from prior exact-five validation; payload Vec carried opaquely.')
 pin.write_text(json.dumps(cuts,indent=2)+'\n')
 body='use super::*;\n'+account_setup(6)
 body+='kani::assume(k5!=k0 && k5!=k1 && k5!=k2 && k5!=k3 && k5!=k4);let _held=a5.try_borrow_mut_data().unwrap();\n'
 if which=='deposit':
  body+='let mint_account=&a0;let source_account=&a1;let source_authority=&a2;let vault_account=&a3;\n';perm=[1,0,3,2]
 else:
  body+='let mint_account=&a0;let vault_account=&a1;let destination_account=&a2;let vault_authority=&a3;\n';perm=[1,0,2,3]
 body+='let data=alloc::vec![kani::any::<u8>()];\n'+literal
 body+=f'let observed=&instruction.accounts[{j}];assert!(instruction.accounts.len()==4);assert!(instruction.program_id==super::LEGACY_SPL_TOKEN_PROGRAM_ID);\n'
 if negative:body+='let observed=&solana_program::instruction::AccountMeta::new(*a5.key,false);\n'
 body+=f'assert!(observed.pubkey==k{perm[j]});assert!(observed.pubkey!=k5);assert!(observed.is_writable=='+str(j in [0,2]).lower()+');assert!(observed.is_signer=='+str(j==3).lower()+');\n'
 return attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
if __name__=='__main__':
 which,j,neg=sys.argv[1:]; negative=neg=='negative'
 if which in ['meta_deposit','meta_withdrawal']:
  source=meta_cut(which.removeprefix('meta_'),int(j),negative)
  stage('programs/aspis-pool/src/vault.rs',source,'unchanged actual CPI-meta constructor cut',neg,'Arbitrary constructor keys and opaque carried payload; guarded key outside all source keys.','Actual caller reaches this constructor on that state; physical entry interpretation; remaining child frames.',dict(member=which,index=int(j),expected_verdict='FAIL' if negative else 'PASS'))
 elif which=='close':
  source=close_account(int(j),negative)
  stage('programs/aspis-pool/src/processor.rs',source,'actual close caller with assign/resize cut oracles',neg,'Arbitrary scalar balances/keys and one arbitrary data byte; free or one live shared data/destination-lamport/source-lamport guard. Actual source/refund keys distinct.','Arbitrary byte-length frame and arbitrary incoming counter interpretation; actual assign/resize packet laws remain OPEN.',dict(member='close_program_account_v1',case=int(j),expected_verdict='FAIL' if negative else 'PASS'))
 else:
  source=infos(which,int(j),negative)
  stage('programs/aspis-pool/src/vault.rs',source,'actual CPI-info helper',neg,'Five pairwise-distinct arbitrary token keys; arbitrary sixth guarded key distinct from them; data/lamport carriers retained by actual Rc clones.','Caller layout/metadata, arbitrary ambient counters, physical entry interpretation and callback/callee frames are not instantiated.',dict(member=which,index=int(j),expected_verdict='FAIL' if negative else 'PASS'))
