from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='programs/r1-cost-probe/src/'
def frozen(n):return subprocess.check_output(['git','show',F+':'+n],text=True)
def update(files,label):
 old=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());old.update(files);(E/'NGL_NATIVE_INPUTS.json').write_text(json.dumps(old,indent=1)+'\n');pins=json.loads((E/'NGL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NGL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');patch=[]
 for n,s in old.items():
  r=subprocess.run(['git','show',F+':'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),s.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
 (E/'NGL_COMPLETE.patch').write_text(''.join(patch))
if __name__=='__main__':
 lib=frozen(P+'lib.rs');adapter=frozen(P+'r1_pool_adapter.rs');owned=frozen(P+'r1_pool_adapter_owned.rs')
 lib='#![cfg_attr(kani,feature(allocator_api))]\n'+lib+'\n#[cfg(kani)]\n#[path="NGL_entry.rs"]\nmod NGL_entry;\n'
 adapter+='\n#[cfg(kani)]\n#[path="NGL_adapter.rs"]\nmod NGL_adapter;\n'
 owned+='\n#[cfg(kani)]\n#[path="NGL_owned.rs"]\nmod NGL_owned;\n'
 entry='''use super::*;
#[kani::proof] #[kani::unwind(6)]
fn rejected_entry2(){let key=Pubkey::new_from_array([0;32]);let data:[u8;2]=kani::any();kani::assume(data!=[3,10]&&data!=[3,11]);let r=process_r1_cost_probe_instruction(&key,&[],&data);assert!((r==Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}
'''
 helper='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_meta(){let owner:[u8;32]=kani::any();let expected:[u8;32]=kani::any();let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let r=readonly_meta_ok(&Pubkey::new_from_array(owner),&Pubkey::new_from_array(expected),s,w,e);let v=if owner!=expected||s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==v) != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn key_copy(){let x:[u8;32]=kani::any();let k=Pubkey::new_from_array(x);let j:usize=kani::any();kani::assume(j<32);assert!((k.as_ref()[j]==x[j]) != cfg!(NGL_invert));}
'''
 owned_h='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) != cfg!(NGL_invert));}
'''
 update({P+'lib.rs':lib,P+'r1_pool_adapter.rs':adapter,P+'r1_pool_adapter_owned.rs':owned,P+'NGL_entry.rs':entry,P+'NGL_adapter.rs':helper,P+'NGL_owned.rs':owned_h},'stage1')
