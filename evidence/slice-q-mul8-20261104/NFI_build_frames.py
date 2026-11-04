from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=json.loads((E/'NFI_PAYLOAD.json').read_text()); key='crates/aspis-r1-cost-probe/src/NFI_dots.rs'
s=p[key]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
s+='''
// Adjacent native cuts share the actual records. No complete-loop harness.
'''
s+=attr+'''fn entry_to_inner_frame(){
 let limbs=[0u64;WideExact::LIMB_COUNT];
 let mut outer=(0..26).step_by(4);let start=outer.next().unwrap();
 let sums=[0u64;WideExact::LIMB_COUNT];
 let inner=start..core::cmp::min(start+4,26);
 let lane:usize=kani::any();kani::assume(lane<8);
 assert_eq!(limbs[lane],0);assert_eq!(sums[lane],0);assert_eq!(inner.end,4);
 assert_eq!(inner.start,if cfg!(NFI_wrong_entry){1}else{0});
}
'''
s+=attr+'''fn cursor_to_product_frame(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let start:usize=kani::any();let end:usize=kani::any();
 let lane:usize=kani::any();let observed:usize=kani::any();let gi:usize=kani::any();let gl:usize=kani::any();
 kani::assume(slot<4 && start<end && end<=26 && lane<8 && observed<608 && gi<29 && gl<8);
 let at=slot*120+start*4;let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8{kani::assume(sums[i]<=3*NFI_BOUND);kani::assume(replies[i]<=NFI_BOUND);}
 let before=sums[lane];let byte=q[observed];let coeff=g[gi].to_limbs()[gl];
 let qp=q.as_ptr() as usize;let gp=g.as_ptr() as usize;
 let mut iter=start..end;let term=iter.next().unwrap();
 let mut log=NFI_Log{replies,left:[0;8],right:[0;8],calls:[0;8],order:[99;8],next:0};
 NFI_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(iter.start,start+1);assert_eq!(iter.end,end);
 assert_eq!(log.left[lane],g[start].to_limbs()[lane]);assert_eq!(log.right[lane],scalar);assert_eq!(log.calls[lane],1);
 assert_eq!(q.as_ptr() as usize,qp);assert_eq!(g.as_ptr() as usize,gp);
 assert_eq!(q[observed],byte);assert_eq!(g[gi].to_limbs()[gl],coeff);
 assert_eq!(sums[lane],if cfg!(NFI_wrong_cursor_product){(before+replies[lane])^1}else{before+replies[lane]});
}
'''
s+=attr+'''fn exhausted_inner_to_fold_frame(){
 let cursor:usize=kani::any();kani::assume(cursor<=26);
 let mut iter=cursor..cursor;
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8{kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];
 assert_eq!(iter.next(),None);
 NFI_fold(sums,&mut limbs);
 assert_eq!(iter.start,cursor);assert_eq!(iter.end,cursor);
 let expected=before+(sums[lane]&0x7fffffff)+(sums[lane]>>31);
 assert_eq!(limbs[lane],if cfg!(NFI_wrong_exhaust_fold){expected^1}else{expected});
}
'''
s+=attr+'''fn fold_to_next_outer_frame(){
 let start:usize=kani::any();kani::assume(start<26 && start%4==0);
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8{kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];
 let mut outer=(start..26).step_by(4);assert_eq!(outer.next(),Some(start));
 NFI_fold(sums,&mut limbs);
 let after=limbs[lane];let next=outer.next();
 assert_eq!(after,before+(sums[lane]&0x7fffffff)+(sums[lane]>>31));
 let expected=if start+4<26{Some(start+4)}else{None};
 assert_eq!(next,if cfg!(NFI_wrong_fold_next){Some(99)}else{expected});
 assert_eq!(limbs[lane],after);
}
'''
p[key]=s
(E/'NFI_FRAME_PAYLOAD.json').write_text(json.dumps(p))
(E/'NFI_dots.rs.txt').write_text(s)
