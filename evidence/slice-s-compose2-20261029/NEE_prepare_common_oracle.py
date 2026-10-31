"""Actual encode_common: arbitrary cached digest replies, indexed full prestate/frame."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
control=sys.argv[1];assert control in {'positive','reply-negative','frame-negative'}
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
module='''#![allow(non_snake_case)]
use super::*;
pub(super) static mut J:usize=0;
pub(super) static mut OLD:u8=0;
pub(super) static mut LOG:usize=0;
static mut D0:[u8;32]=[0;32];
static mut D1:[u8;32]=[0;32];
static mut E0:Digest=[M31(0);8];
static mut E1:Digest=[M31(0);8];
fn d()->Digest {[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
pub(super) fn digest_reply(d:&Digest)->[u8;32] {unsafe{
 let k:usize=kani::any();kani::assume(k<8);assert!(LOG<2);
 let expected=if LOG==0{E0[k].0}else{E1[k].0};assert!(d[k].0==expected,"NEE same digest call argument");
 let reply=if LOG==0{D0}else{D1};LOG+=1;reply
}}
pub(super) fn byte(magic:[u8;4],kind:PoolV1TransitionKind,c:CommonPublicV1,j:usize)->u8 {unsafe{
 let b=match j {0..=3=>magic[j],4=>1,5=>kind as u8,6=>1,7=>OLD,
 8..=39=>c.pool[j-8],40..=71=>c.deployment_domain[j-40],
 72..=79=>c.anchor_sequence.to_le_bytes()[j-72],80..=111=>D0[j-80],
 112..=143=>D1[j-112],144..=147=>c.asset_id.0.to_le_bytes()[j-144],_=>OLD};
 if CORRUPT && j>=80&&j<112{b^1}else{b}
}}
const CORRUPT:bool=CONTROL;
#[kani::proof_for_contract(encode_common)]
#[kani::stub(crate::atomic_statement::encode_digest_canonical,digest_reply)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn common_oracle(){
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:d(),nullifier:d(),asset_id:M31(kani::any())};
 let mut output:[u8;216]=kani::any();let magic:[u8;4]=kani::any();
 let kind=if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};
 let j:usize=kani::any();kani::assume(j<216);
 unsafe{J=j;OLD=output[j];LOG=0;D0=kani::any();D1=kani::any();E0=c.anchor_root;E1=c.nullifier;}
 encode_common(&mut output,magic,kind,c);
}
'''.replace('CONTROL','true' if control=='reply-negative' else 'false')
frame='&mut output[..147]' if control=='frame-negative' else 'output'
attrs='''#[cfg_attr(kani,kani::requires(unsafe {NEE_common_oracle::J<216 && NEE_common_oracle::LOG==0 && NEE_common_oracle::OLD==output[NEE_common_oracle::J]}))]
#[cfg_attr(kani,kani::modifies('''+frame+''', unsafe {&mut NEE_common_oracle::LOG}))]
#[cfg_attr(kani,kani::ensures(|_| unsafe {NEE_common_oracle::LOG==2 && output[NEE_common_oracle::J]==NEE_common_oracle::byte(magic,kind,common,NEE_common_oracle::J)}))]
'''
needle='fn encode_common(';assert frozen.count(needle)==1
changed=frozen.replace(needle,attrs+needle)
assert changed.replace(attrs,'')==frozen
changed+='\n#[cfg(kani)]\n#[path="NEE_common_oracle.rs"]\nmod NEE_common_oracle;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
name='crates/aspis-statement/src/pool_v1/NEE_common_oracle.rs'
patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
base,hook=oracle_parts()
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(base.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in base.splitlines())+hook)
(E/('NEE_COMMON_ORACLE_'+control+'.json')).write_text(json.dumps(dict(control=control,actual_function='encode_common',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),cfg_erasure_exact=True,observation_domain='arbitrary complete CommonPublicV1, magic, both typed kinds, arbitrary 216-byte mutable prestate, index j<216; two unconstrained full [u8;32] replies',modifies='caller mutable output array and ghost two-call log only; indexed postcondition preserves byte7 and bytes148..216',patch_sha256=hashlib.sha256(patch.encode()).hexdigest()),indent=1)+'\n')
print('pool_v1::payment_relation::NEE_common_oracle::common_oracle')
