#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_columns_stop(){
 let weights=core::array::from_fn(|_|NKG_q());
 let c0:[u32;16]=kani::any();let c1:[u32;16]=kani::any();let c2:[u32;16]=kani::any();
 let mut out:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let mut lane:usize=kani::any();kani::assume(lane>=16);let initial=lane;
 let k:usize=kani::any();kani::assume(k<16);let before=NKG_words(out[k]);
 let mut log=NKG_ColumnLog{args:[[0;6];4],replies:kani::any(),calls:0};
 NKG_column_step(weights,c0,c1,c2,&mut out,&mut lane,&mut log);
 if cfg!(NKG_bad_output){out[k].c0.a.0^=1;}
 assert_eq!(lane,initial);assert_eq!(log.calls,0);assert_eq!(NKG_words(out[k]),before);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_columns_initial(){
 let mut output = [QM31::ZERO; POSEIDON2_WIDTH];
 let lane = 0usize;
 let k:usize=kani::any();kani::assume(k<16);
 if cfg!(NKG_bad_output){output[k].c0.a.0^=1;}
 assert_eq!(lane,0);assert_eq!(NKG_words(output[k]),[0;4]);
}
