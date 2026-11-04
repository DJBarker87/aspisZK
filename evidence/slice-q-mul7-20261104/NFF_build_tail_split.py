from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFF_PUBLIC_FIXED_PAYLOAD.json').read_text());s=p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']
s+='''
fn NFF_log()->NFF_PublicLog {NFF_PublicLog{calls:0,half:[99;2],receiver:[0;2],before:[[0;4];2],left:[[0;4];2],right:[[0;4];2],replies:kani::any()}}
fn NFF_tail_chain(values:[E;3],scalars:[QM31;3],logs:&mut[NFF_PublicLog;3])->EbyKDot {
 let mut tail=EbyKDot::new();
 NFF_public_push(&mut tail,values[0],scalars[0],&mut logs[0]).unwrap();
 NFF_public_push(&mut tail,values[1],scalars[1],&mut logs[1]).unwrap();
 NFF_public_push(&mut tail,values[2],scalars[2],&mut logs[2]).unwrap();tail
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn tail_chain_window() {
 let values:[E;3]=kani::any();let scalars:[QM31;3]=kani::any();
 for scalar in scalars {for word in super::super::limbs_of(scalar){kani::assume(word<P);}}
 let mut logs=[NFF_log(),NFF_log(),NFF_log()];let tail=NFF_tail_chain(values,scalars,&mut logs);
 let call:usize=kani::any();let half:usize=kani::any();let lane:usize=kani::any();
 kani::assume(call<3 && half<2 && lane<4);
 assert_eq!(tail.count,3);assert_eq!((logs[0].calls,logs[1].calls,logs[2].calls),(2,2,2));
 assert_eq!(logs[call].left[half][lane],values[call].to_limbs()[half*4+lane]);
 assert_eq!(logs[call].right[half][lane],super::super::limbs_of(scalars[call])[lane]);
 let before=if call==0{0}else{logs[call-1].replies[half][lane]};
 assert_eq!(logs[call].before[half][lane],before);
 let observed=if half==0{tail.c0.sums[lane]}else{tail.c1.sums[lane]};
 let expected=logs[2].replies[half][lane];
 assert_eq!(observed,if cfg!(NFF_wrong_tail_chain){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn tail_selected_finish_add() {
 let old:[u64;8]=kani::any();let count:usize=kani::any();let head:E=kani::any();
 for word in head.to_limbs(){kani::assume(word<P);}
 let receiver=EbyKDot{c0:Dot{sums:[old[0],old[1],old[2],old[3]]},c1:Dot{sums:[old[4],old[5],old[6],old[7]]},count};
 let out=head.add(receiver.finish());
 let lane:usize=kani::any();kani::assume(lane<8);
 let sum=head.to_limbs()[lane]+reduce(old[lane]);let expected=if sum>=P{sum-P}else{sum};
 assert_eq!(out.to_limbs()[lane],if cfg!(NFF_wrong_tail_finish_add){expected^1}else{expected});
 assert!(out.to_limbs()[lane]<P);
}
'''
p['crates/aspis-r1-cost-probe/src/NFF_pairing.rs']=s;(E/'NFF_TAIL_SPLIT_PAYLOAD.json').write_text(json.dumps(p));(E/'NFF_pairing.rs.txt').write_text(s)
