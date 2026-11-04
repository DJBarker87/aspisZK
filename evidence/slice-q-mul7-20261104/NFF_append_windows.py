from pathlib import Path
import json
E=Path(__file__).resolve().parent
s=(E/'NFF_dots.rs.txt').read_text()
f=json.loads((E/'NFF_FROZEN.json').read_text())['crates/aspis-r1-cost-probe/src/fast_dots.rs']
a=f.index('            limbs[0] +=');b=f.index('\n        }',a);fold=f[a:b]
s+='''
fn NFF_fold(sums:[u64;8],limbs:&mut[u64;8]) {
'''+fold+'''
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn outer_fold_window() {
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(limbs[i]<=6*(1u64<<33));}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];let selected=sums[lane];
 NFF_fold(sums,&mut limbs);
 let expected=before+(selected&0x7fff_ffff)+(selected>>31);
 assert_eq!(limbs[lane],if cfg!(NFF_wrong_fold){expected^1}else{expected});
 assert!(limbs[lane]<=7*(1u64<<33));
}
struct NFF_ChildLog { calls:usize,slots:[usize;4],qptr:[usize;4],gptr:[usize;4],replies:[WideExact;4] }
fn NFF_child(q:&[u8;608],g:&[WideExact;29],slot:usize,log:&mut NFF_ChildLog)->WideExact {
 let at=log.calls;log.calls+=1;log.slots[at]=slot;
 log.qptr[at]=q.as_ptr() as usize;log.gptr[at]=g.as_ptr() as usize;
 log.replies[at]
}
fn NFF_four(q:&[u8],g:&[WideExact;29],log:&mut NFF_ChildLog)->[WideExact;4] {
 let q:&[u8;608]=q[..608].try_into().unwrap();
 [NFF_child(q,g,0,log),NFF_child(q,g,1,log),NFF_child(q,g,2,log),NFF_child(q,g,3,log)]
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn wrapper_calls_window() {
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();
 let replies:[WideExact;4]=kani::any();
 let mut log=NFF_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let out=NFF_four(&q,&g,&mut log);
 let at:usize=kani::any();let lane:usize=kani::any();kani::assume(at<4 && lane<8);
 assert_eq!(log.calls,4);assert_eq!(log.slots[at],at);
 assert_eq!(log.qptr[at],q.as_ptr() as usize);assert_eq!(log.gptr[at],g.as_ptr() as usize);
 let expected=replies[at].to_limbs()[lane];
 assert_eq!(out[at].to_limbs()[lane],if cfg!(NFF_wrong_wrapper){expected^1}else{expected});
}
'''
(E/'NFF_dots.rs.txt').write_text(s)
p=json.loads((E/'NFF_PAYLOAD.json').read_text());p['crates/aspis-r1-cost-probe/src/NFF_dots.rs']=s;(E/'NFF_NEXT_PAYLOAD.json').write_text(json.dumps(p))
(E/'NFF_FOLD_FISSION.json').write_text(json.dumps(dict(original=fold,abstracted=fold,reverse_equal=True)))
