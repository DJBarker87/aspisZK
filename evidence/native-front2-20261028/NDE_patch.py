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
  if prefix=='copy':
   s=s.replace('fn selected_binary_weight(', '#[cfg_attr(kani,kani::ensures(|r| (*r==NDE_native::reference::selected_binary_ref(high,QM31::ZERO,weight.0)) != cfg!(NDE_simple_invert)))]\nfn selected_binary_weight(',1)
  if prefix=='semantic':
   s=s.replace('fn variant_expected_output(', '#[cfg_attr(kani,kani::ensures(|r| (r.0==NDE_native::reference::variant_output_ref(variant==CompiledVariant::Withdrawal)) != cfg!(NDE_simple_invert)))]\nfn variant_expected_output(',1)
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
  if prefix=='semantic':
   begin='fn bounded_append_carry(mut index: u64) -> usize {\n    let mut carry = 0usize;'
   assert begin in s
   s=s.replace(begin,begin+'\n    #[cfg(all(kani,NDE_carry_step))]\n    let mut carry = unsafe{NDE_native::NDE_CARRY};',1)
   point='        carry += 1;\n    }\n    carry'
   assert point in s
   s=s.replace(point,'        carry += 1;\n        #[cfg(all(kani,NDE_carry_step))]\n        {NDE_native::carry_record(index); return carry;}\n    }\n    carry',1)
  if prefix=='semantic':
   for fn,check in [('private_public','private_matches'),('withdrawal_public','withdrawal_matches')]:
    attrs='#[cfg_attr(kani,kani::requires(unsafe{NDE_native::NDE_PUBLIC_INDEX<32}))]\n#[cfg_attr(kani,kani::ensures(|r|NDE_native::'+check+'(r,public,transition) != cfg!(NDE_invert)))]\n'
    s=s.replace("fn "+fn+"<'a>(",attrs+"fn "+fn+"<'a>(",1)
  if prefix=='semantic':
   attrs='#[cfg_attr(kani,kani::requires(level<21&&unsafe{NDE_native::NDE_ROOT_INDEX<8}))]\n#[cfg_attr(kani,kani::ensures(|r|(r[unsafe{NDE_native::NDE_ROOT_INDEX}].0==NDE_native::reference::empty_root_ref(level)[unsafe{NDE_native::NDE_ROOT_INDEX}]) != cfg!(NDE_invert)))]\n'
   s=s.replace('fn empty_root(',attrs+'fn empty_root(',1)
  if prefix=='semantic':
   begin='fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {\n    let mut sum = QM31::ZERO;'
   assert begin in s
   s=s.replace(begin,begin+'\n    #[cfg(all(kani,NDE_sum_step))]\n    let mut sum=unsafe{NDE_native::NDE_SUM_PRE};',1)
   point='            sum = sum.add(selectors.high[block]);'
   assert point in s
   s=s.replace(point,point+'\n            #[cfg(all(kani,NDE_sum_step))]\n            {unsafe{NDE_native::NDE_SUM_STEPPED=true;}return sum;}',1)
   point='.fold(view[9], |acc, bit| acc.add(acc).add(*bit))'
   assert point in s
   s=s.replace(point,".fold(view[9], |acc, bit| {\n            #[cfg(all(kani,NDE_reconstruct_step))]\n            if unsafe{NDE_native::NDE_RECON_DONE}{return acc;}\n            let out=acc.add(acc).add(*bit);\n            #[cfg(all(kani,NDE_reconstruct_step))]\n            unsafe{NDE_native::NDE_RECON_DONE=true;}\n            out\n        })",1)
  if prefix=='poseidon':
   a=s.index('fn external_local_packed_raw(');b=s.index('\n#[inline(always)]\nfn external_local_packed(',a)
   raw=s[a:b]
   point='        core::array::from_fn(|limb| {\n            let a ='
   assert point in raw
   raw=raw.replace(point,'        core::array::from_fn(|limb| {\n            #[cfg(all(kani,any(NDE_scan_step,NDE_packed_after)))]\n            return 0;\n            #[cfg(all(kani,NDE_matrix_step))]\n            if output!=unsafe{NDE_native::NDE_PACKED_ROW} || limb!=unsafe{NDE_native::NDE_PACKED_LIMB}{return 0;}\n            let a =',1)
   raw=raw.replace('            match output {','            let cell=match output {',1)
   point='                _ => unreachable!(),\n            }\n        })'
   assert point in raw
   raw=raw.replace(point,'                _ => unreachable!(),\n            };\n            #[cfg(all(kani,NDE_matrix_step))]\n            unsafe{NDE_native::NDE_MATRIX_REPLY=cell;NDE_native::NDE_MATRIX_COUNT+=1;}\n            cell\n        })',1)
   point='    let mut all_local_limbs_bounded = true;'
   raw=raw.replace(point,'    #[cfg(all(kani,NDE_matrix_step))]\n    return [0;4];\n    #[cfg(all(kani,any(NDE_scan_step,NDE_packed_after)))]\n    let local=unsafe{NDE_native::NDE_PACKED_TABLE};\n'+point+'\n    #[cfg(all(kani,NDE_scan_step))]\n    let mut all_local_limbs_bounded=unsafe{NDE_native::NDE_PACKED_FLAG};',1)
   point='    let mut output = 0usize;'
   raw=raw.replace(point,point+'\n    #[cfg(all(kani,NDE_scan_step))]\n    let mut output=unsafe{NDE_native::NDE_PACKED_ROW};\n    #[cfg(all(kani,NDE_packed_after))]\n    let mut output=4usize;',1)
   point='        let mut limb = 0usize;'
   raw=raw.replace(point,point+'\n        #[cfg(all(kani,NDE_scan_step))]\n        let mut limb=unsafe{NDE_native::NDE_PACKED_LIMB};',1)
   point='            limb += 1;'
   raw=raw.replace(point,point+'\n            #[cfg(all(kani,NDE_scan_step))]\n            {unsafe{NDE_native::NDE_SCAN_REPLY=(all_local_limbs_bounded,output,limb,false);}return [0;4];}',1)
   point='        output += 1;'
   raw=raw.replace(point,point+'\n        #[cfg(all(kani,NDE_scan_step))]\n        {unsafe{NDE_native::NDE_SCAN_REPLY=(all_local_limbs_bounded,output,limb,true);}return [0;4];}',1)
   s=s[:a]+raw+s[b:]
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
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::variant_expected_output)]\nfn NDE_expected(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let _=super::variant_expected_output(v);}\n'
   harness+=(E/'NDE_semantic_extra.rs').read_text()+(E/'NDE_semantic_index.rs').read_text()+(E/'NDE_carry_native.rs').read_text()+(E/'NDE_public_native.rs').read_text()+(E/'NDE_root_native.rs').read_text()+(E/'NDE_linear_native.rs').read_text()
   out['crates/aspis-statement/src/pool_v1/NDE_claim_reference.rs']=(E/'NDE_claim_reference.rs').read_text()
  if prefix=='copy':
   harness+=(E/'NDE_row_native.rs').read_text()
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::selected_binary_weight)]\nfn NDE_binary(){let high:QM31=kani::any();let weight:u32=kani::any();let _=super::selected_binary_weight(high,M31(weight));}\n'
   harness+='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]\n#[kani::proof_for_contract(super::link_weight)]\nfn NDE_link(){let k:u8=kani::any();let l:u8=kani::any();kani::assume(k<=4&&(k<3||l<64));let i:u64=kani::any();let v=if kani::any(){PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer};let ep=CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()};let link=CompiledPoolV1PairForestLink{tag:kani::any(),weight_kind:k,weight_level:l,producer:ep,consumer:CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()}};let _=super::link_weight(link,i,v); }\n'
  if prefix=='poseidon':harness+=(E/'NDE_packed_native.rs').read_text()
  out['crates/aspis-statement/src/'+dirname+module+'.rs']=harness
  out['crates/aspis-statement/src/'+dirname+'NDE_reference.rs']=(E/'NDE_reference.rs').read_text()
 # Root allocator feature required by exact KMX code.
 n='crates/aspis-statement/src/lib.rs';s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 s='#![cfg_attr(kani, feature(allocator_api))]\n'+s+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\nmod NDE_kmx;\n'
 s+='\n#[cfg(kani)]\nmod NDE_field;\n'
 out[n]=s
 out['crates/aspis-statement/src/NDE_field.rs']=(E/'NDE_field.rs').read_text()
 n='crates/aspis-core/src/lib.rs';s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 out[n]=s+'\n#[cfg(kani)]\nmod NDE_arbitrary;\n'
 out['crates/aspis-core/src/NDE_arbitrary.rs']=(E/'NDE_arbitrary.rs').read_text()
 n='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 out[n]=s+'\n#[cfg(kani)]\n#[path="NDE_terminal.rs"]\nmod NDE_terminal;\n'
 out['crates/aspis-statement/src/pool_v1/NDE_terminal.rs']=(E/'NDE_terminal_native.rs').read_text()
 patch=''
 for n,s in out.items():
  old=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True)
  patch+=''.join(difflib.unified_diff(old.stdout.splitlines(True),s.splitlines(True),fromfile='a/'+n if old.returncode==0 else '/dev/null',tofile='b/'+n))
 (E/'NDE_harness.patch').write_text(patch)
 return out
if __name__=='__main__':files()
