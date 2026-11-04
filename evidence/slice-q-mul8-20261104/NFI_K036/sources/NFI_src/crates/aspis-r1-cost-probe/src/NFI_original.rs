use aspis_core::field::WideExact;
fn NFI_opening(proof:&[u8],i:usize)->&[u8]{
 let at=crate::compact::OFF_OPENINGS+i*crate::compact::OPENING;
 &proof[at..at+crate::compact::OPENING]
}
struct NFI_Log{qplace:usize,gplace:usize,byte:u8,reply:WideExact,calls:usize}
fn NFI_selected_call(q:&[u8;608],g:&[WideExact;29],j:usize,log:&mut NFI_Log)->WideExact{
 log.qplace=q.as_ptr() as usize;log.gplace=g.as_ptr() as usize;log.byte=q[j];log.calls+=1;log.reply
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn original_proof_one_cell(){
 // ONE symbolic cell; all other cells are a fixed frame. Lean composes
 // arbitrary frames from the exact read-only slice footprint, not a whole-buffer SAT gate.
 let mut proof=[0u8;57607];let i:usize=kani::any();let j:usize=kani::any();
 let lane:usize=kani::any();kani::assume(i<22 && j<608 && lane<8);
 let at=crate::compact::OFF_OPENINGS+i*832;
 let original:u8=kani::any();proof[at+j]=original;
 let g:[WideExact;29]=kani::any();let reply:WideExact=kani::any();
 let coefficient=g[0].to_limbs()[lane];let root=proof.as_ptr() as usize;
 let q=NFI_opening(&proof,i);let fixed:&[u8;608]=q[..608].try_into().unwrap();
 let mut log=NFI_Log{qplace:0,gplace:0,byte:0,reply,calls:0};
 let out=NFI_selected_call(fixed,&g,j,&mut log);
 assert_eq!(q.len(),832);assert_eq!(log.calls,1);
 assert_eq!(log.qplace,root+at);assert_eq!(log.gplace,g.as_ptr() as usize);
 assert_eq!(log.byte,original);assert_eq!(proof[at+j],original);assert_eq!(g[0].to_limbs()[lane],coefficient);
 let expected=reply.to_limbs()[lane];
 assert_eq!(out.to_limbs()[lane],if cfg!(NFI_wrong_original_cell){expected^1}else{expected});
}
