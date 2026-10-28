from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 out={}
 for name,prefix,fun in [('pool_v1/pair_forest_semantic_terminal.rs','semantic','lift_m31'),('pool_v1/pair_forest_copy_terminal.rs','copy','lift_m31'),('state_only_poseidon.rs','poseidon','extension_limbs')]:
  n='crates/aspis-statement/src/'+name
  s=subprocess.check_output(['git','show',REV+':'+n],text=True)
  prop='NDE_native::to_native(NDE_native::reference::lift_ref(value.0))' if fun=='lift_m31' else 'NDE_native::reference::extension_limbs_ref(NDE_native::to_ref(value))'
  attr='#[cfg_attr(kani, kani::ensures(|r| (*r == '+prop+') != cfg!(NDE_invert))) ]\n'
  s=s.replace('fn '+fun+'(',attr+'fn '+fun+'(',1)
  if prefix=='poseidon':
   pre='#[cfg_attr(kani, kani::requires(limbs[0] < (1u64<<62) && limbs[1] < (1u64<<62) && limbs[2] < (1u64<<62) && limbs[3] < (1u64<<62)))]\n'
   post='#[cfg_attr(kani, kani::ensures(|r| (*r == NDE_native::to_native(NDE_native::reference::extension_raw_ref(limbs))) != cfg!(NDE_invert)))]\n'
   s=s.replace('fn extension_from_raw_limbs(',pre+post+'fn extension_from_raw_limbs(',1)
  if prefix=='semantic':
   for fn,pre,prop in [
    ('initial_variant_selectors','NDE_native::canonical(high27)&&NDE_native::canonical(high28)&&NDE_native::canonical(high29)','NDE_native::native_initial(variant,high27,high28,high29)'),
    ('scalar_lanes','NDE_native::canonical(output_scalar)&&NDE_native::canonical(private_transfer_term)&&NDE_native::canonical(withdrawal_term)','NDE_native::native_scalar(variant,withdrawal_amount_present,input_asset,output_scalar,private_transfer_term,withdrawal_term)'),
    ('copy_variant','true','if NDE_native::reference::copy_variant_ref(variant==CompiledVariant::Withdrawal){PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer}')]:
    attrs='#[cfg_attr(kani,kani::requires('+pre+'))]\n#[cfg_attr(kani,kani::ensures(|r|(*r==('+prop+')) != cfg!(NDE_invert)))]\n'
    s=s.replace('fn '+fn+'(',attrs+'fn '+fn+'(',1)
  if prefix=='copy':
   pre='#[cfg_attr(kani,kani::requires(link.weight_kind<=4 && (link.weight_kind<3 || link.weight_level<64)))]\n'
   post='#[cfg_attr(kani,kani::ensures(|r|(r.0==NDE_native::reference::link_weight_ref(link.weight_kind,link.weight_level,append_index,variant==PoolV1PairForestCompiledVariantV1::Withdrawal)) != cfg!(NDE_invert)))]\n'
   s=s.replace('fn link_weight(',pre+post+'fn link_weight(',1)
  if prefix=='semantic':
   attrs='#[cfg_attr(kani,kani::requires(point<3&&column<28))]\n#[cfg_attr(kani,kani::ensures(|r|(*r==NDE_native::claim_reference::claim_ref(claims,point,column)) != cfg!(NDE_invert)))]\n'
   s=s.replace('fn selected_claim(',attrs+'fn selected_claim(',1)
  module='NDE_'+prefix
  s+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod NDE_native;\n'
  out[n]=s
  dirname='pool_v1/' if name.startswith('pool_v1/') else ''
  harness='''use super::*;
#[path="NDE_reference.rs"] pub(super) mod reference;
pub(super) fn to_ref(v:QM31)->reference::Q { reference::Q { c0:reference::C{a:v.c0.a.0,b:v.c0.b.0},c1:reference::C{a:v.c1.a.0,b:v.c1.b.0} } }
pub(super) fn to_native(v:reference::Q)->QM31 {QM31 {c0:CM31{a:M31(v.c0.a),b:M31(v.c0.b)},c1:CM31{a:M31(v.c1.a),b:M31(v.c1.b)}}}
'''
  if fun=='lift_m31':
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::lift_m31)]\nfn NDE_contract(){let v:u32=kani::any();let _=super::lift_m31(M31(v));}\n'
  else:
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::extension_limbs)]\nfn NDE_contract(){let v:[u32;4]=kani::any();let _=super::extension_limbs(to_native(reference::Q{c0:reference::C{a:v[0],b:v[1]},c1:reference::C{a:v[2],b:v[3]}}));}\n'
  if prefix=='poseidon':
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::extension_from_raw_limbs)]\nfn NDE_raw_contract(){let v:[u64;4]=kani::any();kani::assume(v[0]<(1u64<<62)&&v[1]<(1u64<<62)&&v[2]<(1u64<<62)&&v[3]<(1u64<<62));let _=super::extension_from_raw_limbs(v); }\n'
  if prefix=='semantic':
   harness+=(E/'NDE_semantic_extra.rs').read_text()+(E/'NDE_semantic_index.rs').read_text()
   out['crates/aspis-statement/src/pool_v1/NDE_claim_reference.rs']=(E/'NDE_claim_reference.rs').read_text()
  if prefix=='copy':
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::link_weight)]\nfn NDE_link(){let k:u8=kani::any();let l:u8=kani::any();kani::assume(k<=4&&(k<3||l<64));let i:u64=kani::any();let v=if kani::any(){PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer};let ep=CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()};let link=CompiledPoolV1PairForestLink{tag:kani::any(),weight_kind:k,weight_level:l,producer:ep,consumer:CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()}};let _=super::link_weight(link,i,v); }\n'
  out['crates/aspis-statement/src/'+dirname+module+'.rs']=harness
  out['crates/aspis-statement/src/'+dirname+'NDE_reference.rs']=(E/'NDE_reference.rs').read_text()
 # Root allocator feature required by exact KMX code.
 n='crates/aspis-statement/src/lib.rs';s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 s='#![cfg_attr(kani, feature(allocator_api))]\n'+s+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\nmod NDE_kmx;\n'
 out[n]=s
 patch=''
 for n,s in out.items():
  old=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True)
  patch+=''.join(difflib.unified_diff(old.stdout.splitlines(True),s.splitlines(True),fromfile='a/'+n if old.returncode==0 else '/dev/null',tofile='b/'+n))
 (E/'NDE_harness.patch').write_text(patch)
 return out
if __name__=='__main__':files()
