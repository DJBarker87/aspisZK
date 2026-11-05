from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=src[src.index('fn internal_linear_lazy('):src.index('\n#[inline(never)]\nfn full_round(',src.index('fn internal_linear_lazy('))]
shifts=body[body.index('    const SHIFTS:'):body.index('\n    let old_zero')]
acc='''            part_sum[limb] += u64::from(limbs[limb]);
            limb += 1;''';assert acc in body
full='part_sum[limb] + u64::from(old_zero[limb])';assert full in body
zero=body[body.index('    state[0] ='):body.index('\n    for lane in 1..')]
lane=body[body.index('    for lane in 1..'):body.rindex('\n}')];cut=lane.replace('for lane in 1..POSEIDON2_WIDTH {','if let Some(lane)=iter.next() {')
assert cut.replace('if let Some(lane)=iter.next() {','for lane in 1..POSEIDON2_WIDTH {')==lane
out='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{extension_limbs(q)}
fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn canonical()->QM31{let w:[u32;4]=kani::any();kani::assume(w[0]<P&&w[1]<P&&w[2]<P&&w[3]<P);q(w)}
fn part()->[u64;4]{let w:[u64;4]=kani::any();kani::assume(w[0]<61*u64::from(P)&&w[1]<61*u64::from(P)&&w[2]<61*u64::from(P)&&w[3]<61*u64::from(P));w}
fn fullsum()->[u64;4]{let w:[u64;4]=kani::any();kani::assume(w[0]<62*u64::from(P)&&w[1]<62*u64::from(P)&&w[2]<62*u64::from(P)&&w[3]<62*u64::from(P));w}
fn NIH_acc_cut(mut part_sum:[u64;4],limbs:[u32;4],mut limb:usize)->([u64;4],usize){if limb<4{
'''+acc+'''
}(part_sum,limb)}
fn NIH_full_cut(part_sum:[u64;4],old_zero:[u32;4],limb:usize)->u64{'''+full+'''}
fn NIH_zero_cut(state:&mut[QM31;16],part_sum:[u64;4],old_zero:[u32;4]){
'''+zero+'''
}
fn NIH_lane_cut(state:&mut[QM31;16],full_sum:[u64;4],iter:&mut core::ops::Range<usize>){
'''+shifts+'\n'+cut+'''
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_internal_acc(){let before=part();let limbs=words(canonical());let i:usize=kani::any();kani::assume(i<=4);let (after,next)=NIH_acc_cut(before,limbs,i);let j:usize=kani::any();kani::assume(j<4);assert_eq!(next,if i<4{i+1}else{i});let expected=if j==i{before[j]+u64::from(limbs[j])}else{before[j]};assert_eq!(after[j],expected ^ if cfg!(NIH_invert){1}else{0});assert!(after[j]<62*u64::from(P));}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_internal_full(){let part_sum=part();let old_zero=words(canonical());let j:usize=kani::any();kani::assume(j<4);let out=NIH_full_cut(part_sum,old_zero,j);assert_eq!(out,part_sum[j]+u64::from(old_zero[j]) ^ if cfg!(NIH_invert){1}else{0});assert!(out<62*u64::from(P));}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_internal_zero(){let mut state:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let before=state;let part_sum=part();let old_zero=words(canonical());NIH_zero_cut(&mut state,part_sum,old_zero);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);let raw=part_sum[k]+u64::from(P)-u64::from(old_zero[k]);assert!(raw<4611686018427387904);let expected=if j==0{(raw%u64::from(P)) as u32}else{words(before[j])[k]};assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_internal_lane(){let mut state:[QM31;16]=core::array::from_fn(|_|canonical());let before=state;let full=fullsum();let start:usize=kani::any();kani::assume(start>=1&&start<=16);let mut iter=start..16;NIH_lane_cut(&mut state,full,&mut iter);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);let shifts=[0u8,1,2,3,4,5,6,7,8,10,12,13,14,15,16];let expected=if start<16&&j==start{let raw=full[k]+(u64::from(words(before[start])[k])<<shifts[start-1]);assert!(raw<4611686018427387904);(raw%u64::from(P)) as u32}else{words(before[j])[k]};assert_eq!(iter.start,if start<16{start+1}else{16});assert_eq!(iter.end,16);assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
'''
(E/'NIH_internal.rs.txt').write_text(out)
(E/'NIH_INTERNAL_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),acc=acc,full=full,zero=zero,lane=lane,cut=cut,shifts=shifts,reverse_erasure=True,domains={'part':'all four words<61*P, exactly JGj_InternalPrepare.success','full':'all four words<62*P, exactly JGj_InternalPrepare.success','old':'four canonical U32','lane':'1<=start<=16; arbitrary canonical state; arbitrary selected frame index'},modifies='acc selected limb and cursor; zero only state0; lane only selected state cell and Range cursor; all borrowed input arrays immutable'),indent=2)+'\n')
