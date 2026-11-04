from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFI_CONTEXT_PAYLOAD.json').read_text());k='crates/aspis-r1-cost-probe/src/NFI_dots.rs';s=p[k]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
s+=attr+'''fn outer_reentry_live_frame(){
 let limbs:[u64;8]=kani::any();let lane:usize=kani::any();let start:usize=kani::any();
 kani::assume(lane<8 && start<22 && start%4==0);let before=limbs[lane];
 let mut outer=(start..26).step_by(4);assert_eq!(outer.next(),Some(start));
 // One running-state transition, observing the same iterator through clones.
 let before_len=outer.len();let before_peek=outer.clone().next();
 assert_eq!(before_peek,Some(start+4));let returned=outer.next();
 assert_eq!(returned,before_peek);assert_eq!(outer.len()+1,before_len);
 let peek=outer.clone().next();let expected=if start+8<26{Some(start+8)}else{None};
 assert_eq!(peek,if cfg!(NFI_wrong_reentry_frame){Some(99)}else{expected});
 assert_eq!(limbs[lane],before);
}
'''
s+=attr+'''fn inner_cursor_live_frame(){
 let limbs:[u64;8]=kani::any();let lane:usize=kani::any();let start:usize=kani::any();let end:usize=kani::any();
 kani::assume(lane<8 && start<=end && end<=26);let before=limbs[lane];
 let mut inner=start..end;let returned=inner.next();
 assert_eq!(returned,if start<end{Some(start)}else{None});
 assert_eq!(inner.start,if start<end{start+1}else{start});assert_eq!(inner.end,end);
 assert_eq!(limbs[lane],if cfg!(NFI_wrong_inner_live_frame){before^1}else{before});
}
'''
s+=attr+'''fn tail_decoder_head_frame(){
 let q:[u8;16]=kani::any();let head:WideExact=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 let before=head.to_limbs()[lane];let out=QM31::from_le_bytes(&q);
 if let Some(v)=out{assert!(v.c0.a.0<2147483647);}
 assert_eq!(head.to_limbs()[lane],if cfg!(NFI_wrong_tail_head_frame){before^1}else{before});
}
'''
s+=attr+'''fn wrapper_return_to_caller_frame(){
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();let replies:[WideExact;4]=kani::any();
 let byte:usize=kani::any();let slot:usize=kani::any();let lane:usize=kani::any();
 kani::assume(byte<609 && slot<4 && lane<8);let original=q[byte];
 let mut log=NFI_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let out=NFI_four(&q,&g,&mut log);let returned=out;
 assert_eq!(q[byte],original);assert_eq!(log.qptr[slot],q.as_ptr() as usize);assert_eq!(log.gptr[slot],g.as_ptr() as usize);
 let expected=replies[slot].to_limbs()[lane];
 assert_eq!(returned[slot].to_limbs()[lane],if cfg!(NFI_wrong_wrapper_return_frame){expected^1}else{expected});
}
'''
p[k]=s;(E/'NFI_LIVE_PAYLOAD.json').write_text(json.dumps(p))
s=(E/'NFI_queue2.py').read_text();a=s.index('jobs=');b=s.index('for i,h,wrong in jobs:',a)
s=s[:a]+'''jobs=[(91,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(92,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('outer_reentry_live_frame','NFI_wrong_reentry_frame'),('inner_cursor_live_frame','NFI_wrong_inner_live_frame'),('tail_decoder_head_frame','NFI_wrong_tail_head_frame'),('wrapper_return_to_caller_frame','NFI_wrong_wrapper_return_frame')]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((93+2*i+j,'fast_dots::NFI_dots::'+h,w))
'''+s[b:];s=s.replace("'NFI_TAIL_CALL_PAYLOAD.json'","'NFI_LIVE_PAYLOAD.json','NFI_KANI_BASE':'NFI_ORIGINAL_BASE.json'");(E/'NFI_queue9.py').write_text(s)
