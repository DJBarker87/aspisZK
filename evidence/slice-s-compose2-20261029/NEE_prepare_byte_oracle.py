"""Small frozen byte/lane caller certificates with exact arbitrary child replies."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
case,control=sys.argv[1:];assert case in {'first','lane'} and control in {'positive','negative'}
path='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
module='''#![allow(non_snake_case)]
use super::*;
use aspis_core::field::M31;
pub(super) static mut LOG:usize=0;
pub(super) static mut EARG:Digest=[M31(0);8];
pub(super) static mut D:[u8;32]=[0;32];
pub(super) static mut Q:bool=false;
pub(super) static mut B:u8=0;
fn d()->Digest {[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
fn same(input:&Digest){let j:usize=kani::any();kani::assume(j<8);unsafe{assert!(input[j].0==EARG[j].0,"NEE exact byte/lane argument");}}
fn encoded(input:&Digest)->[u8;32]{same(input);unsafe{assert!(LOG==0);LOG+=1;D}}
fn canonical(input:&Digest)->bool{same(input);unsafe{assert!(LOG==0);LOG+=1;Q}}
fn first(input:&Digest)->u8{same(input);unsafe{assert!(LOG==1);LOG+=1;B}}
pub(super) fn expected_first()->u8 {unsafe{D[0]^CORRUPT}}
pub(super) fn expected_lane()->Result<u8,PoolV1PairForestAccountErrorV1> {unsafe{
 if Q{Ok((B^CORRUPT)&7)}else{Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)}
}}
const CORRUPT:u8=CONTROL;
'''.replace('CONTROL','1' if control=='negative' else '0')
if case=='first':
 needle='fn first_canonical_byte(';arg='digest';fn='first_canonical_byte'
 expected='*r==NEE_byte_oracle::expected_first() && NEE_byte_oracle::LOG==1'
 stubs='#[kani::stub(crate::atomic_statement::encode_digest_canonical,encoded)]\n'
else:
 needle='pub fn pool_v1_pair_forest_output_lane_v1(';arg='nullifier';fn='pool_v1_pair_forest_output_lane_v1'
 expected='*r==NEE_byte_oracle::expected_lane() && NEE_byte_oracle::LOG==if NEE_byte_oracle::Q{2}else{1}'
 stubs='#[kani::stub(digest_is_canonical,canonical)]\n#[kani::stub(first_canonical_byte,first)]\n'
attrs='''#[cfg_attr(kani,kani::requires(unsafe {NEE_byte_oracle::LOG==0 && NEE_byte_oracle::EARG==*'''+arg+'''}))]
#[cfg_attr(kani,kani::modifies(unsafe {&mut NEE_byte_oracle::LOG}))]
#[cfg_attr(kani,kani::ensures(|r| unsafe {'''+expected+'''}))]
'''
module+='#[kani::proof_for_contract('+fn+')]\n'+stubs+'''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn byte_oracle(){let input=d();unsafe{EARG=input;LOG=0;D=kani::any();Q=kani::any();B=kani::any();}let _=FUNCTION(&input);}
'''.replace('FUNCTION',fn)
assert frozen.count(needle)==1
changed=frozen.replace(needle,attrs+needle);assert changed.replace(attrs,'')==frozen
changed+='\n#[cfg(kani)]\n#[path="NEE_byte_oracle.rs"]\nmod NEE_byte_oracle;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
name='crates/aspis-statement/src/pool_v1/NEE_byte_oracle.rs'
patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
base,hook=oracle_parts()
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(base.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in base.splitlines())+hook)
(E/('NEE_'+case+'_ORACLE_'+control+'.json')).write_text(json.dumps(dict(case=case,control=control,actual_function=fn,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),cfg_erasure_exact=True,domain='every typed Digest, exact ghost input snapshot; arbitrary full Bool/U8/32-byte replies',modifies='ordered ghost call log only; input and all external state unchanged',patch_sha256=hashlib.sha256(patch.encode()).hexdigest()),indent=1)+'\n')
print('pool_v1::pair_forest_accounts::NEE_byte_oracle::byte_oracle')
