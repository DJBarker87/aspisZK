from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFM_REJECT_PAYLOAD.json').read_text());k='crates/aspis-r1-cost-probe/src/NFM_dots.rs';s=p[k]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
'''
s+=attr+'''fn wrapper_original_opening(){
 let q:[u8;832]=kani::any();let g:[WideExact;29]=kani::any();let replies:[WideExact;4]=kani::any();
 let mut log=NFM_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let slot:usize=kani::any();let lane:usize=kani::any();let byte:usize=kani::any();
 kani::assume(slot<4 && lane<8 && byte<832);let saved=q[byte];let coeff=g[28].to_limbs()[lane];
 let out=NFM_four(&q,&g,&mut log);
 assert_eq!(log.calls,4);assert_eq!(log.slots[slot],slot);
 assert_eq!(log.qptr[slot],q.as_ptr() as usize);assert_eq!(log.gptr[slot],g.as_ptr() as usize);
 assert_eq!(q[byte],saved);assert_eq!(g[28].to_limbs()[lane],coeff);
 let expected=replies[slot].to_limbs()[lane];
 assert_eq!(out[slot].to_limbs()[lane],if cfg!(NFM_wrong_original_wrapper){expected^1}else{expected});
}
'''
p[k]=s;(E/'NFM_WRAPPER_PAYLOAD.json').write_text(json.dumps(p))
