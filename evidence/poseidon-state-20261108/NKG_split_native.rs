fn NKG_empty_group_log()->NKG_GroupLog{
 let p=aspis_core::field::NKG_prepared_from_words([[0;3];3]);
 NKG_GroupLog{pack_inputs:[[QM31::ZERO;4];2],pack_replies:[QM31::ZERO;2],pack_calls:0,sub_args:[[QM31::ZERO;2];3],sub_replies:[QM31::ZERO;3],sub_calls:0,sum_weights:[p;3],sum_right:[QM31::ZERO;3],sum_reply:QM31::ZERO,sum_calls:0,mul_left:p,mul_right:QM31::ZERO,mul_reply:QM31::ZERO,mul_calls:0}
}
fn NKG_pack_segment(log:&mut NKG_GroupLog,succ:&[QM31;16],internal:&[QM31;16],group:usize)->(QM31,QM31){
 let start=4*group;
 let target=NKG_pack(log,&succ[start..start+4]);
 let internal=NKG_pack(log,&internal[start..start+4]);
 (target,internal)
}
fn NKG_sub_segment(log:&mut NKG_GroupLog,target:QM31,internal:QM31,leading:&[QM31;4],full:&[QM31;4],group:usize)->[QM31;3]{
 let d0=NKG_sub(log,target,leading[group]);let d1=NKG_sub(log,target,full[group]);let d2=NKG_sub(log,target,internal);[d0,d1,d2]
}
fn NKG_sum_segment(log:&mut NKG_GroupLog,p:&[PreparedQm31Multiplier;3],differences:&[QM31;3])->QM31{NKG_sum(log,p,differences)}
fn NKG_mul_segment(log:&mut NKG_GroupLog,p:PreparedQm31Multiplier,sum:QM31)->QM31{NKG_pmul(log,p,sum)}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_pack_segment_cut(){
 let succ:[QM31;16]=core::array::from_fn(|_|NKG_q());let internal:[QM31;16]=core::array::from_fn(|_|NKG_q());let replies:[QM31;2]=core::array::from_fn(|_|NKG_q());
 let mut log=NKG_empty_group_log();log.pack_replies=replies;
 let g:usize=kani::any();let k:usize=kani::any();kani::assume(g<4&&k<4);
 let mut out=NKG_pack_segment(&mut log,&succ,&internal,g);
 if cfg!(NKG_bad_output){out.0.c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.pack_inputs[0][k].c0.a.0^=1;}
 assert_eq!(log.pack_calls,2);assert_eq!(NKG_words(log.pack_inputs[0][k]),NKG_words(succ[4*g+k]));assert_eq!(NKG_words(log.pack_inputs[1][k]),NKG_words(internal[4*g+k]));assert_eq!(NKG_words(out.0),NKG_words(replies[0]));assert_eq!(NKG_words(out.1),NKG_words(replies[1]));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_sub_segment_cut(){
 let target=NKG_q();let internal=NKG_q();let lead:[QM31;4]=core::array::from_fn(|_|NKG_q());let full:[QM31;4]=core::array::from_fn(|_|NKG_q());let replies:[QM31;3]=core::array::from_fn(|_|NKG_q());
 let mut log=NKG_empty_group_log();log.sub_replies=replies;
 let g:usize=kani::any();let j:usize=kani::any();kani::assume(g<4&&j<3);
 let mut out=NKG_sub_segment(&mut log,target,internal,&lead,&full,g);
 if cfg!(NKG_bad_output){out[j].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.sub_args[j][0].c0.a.0^=1;}
 assert_eq!(log.sub_calls,3);assert_eq!(NKG_words(log.sub_args[j][0]),NKG_words(target));assert_eq!(NKG_words(log.sub_args[j][1]),NKG_words(if j==0{lead[g]}else if j==1{full[g]}else{internal}));assert_eq!(NKG_words(out[j]),NKG_words(replies[j]));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_sum_segment_cut(){
 let prepared:[PreparedQm31Multiplier;3]=core::array::from_fn(|_|NKG_p());let differences:[QM31;3]=core::array::from_fn(|_|NKG_q());let reply=NKG_q();
 let mut log=NKG_empty_group_log();log.sum_reply=reply;
 let j:usize=kani::any();let a:usize=kani::any();let b:usize=kani::any();kani::assume(j<3&&a<3&&b<3);
 let mut out=NKG_sum_segment(&mut log,&prepared,&differences);
 if cfg!(NKG_bad_output){out.c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.sum_right[j].c0.a.0^=1;}
 assert_eq!(log.sum_calls,1);assert_eq!(aspis_core::field::NKG_prepared_words(log.sum_weights[j])[a][b],aspis_core::field::NKG_prepared_words(prepared[j])[a][b]);assert_eq!(NKG_words(log.sum_right[j]),NKG_words(differences[j]));assert_eq!(NKG_words(out),NKG_words(reply));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_mul_segment_cut(){
 let prepared=NKG_p();let sum=NKG_q();let reply=NKG_q();let mut log=NKG_empty_group_log();log.mul_reply=reply;
 let a:usize=kani::any();let b:usize=kani::any();kani::assume(a<3&&b<3);
 let mut out=NKG_mul_segment(&mut log,prepared,sum);
 if cfg!(NKG_bad_output){out.c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.mul_right.c0.a.0^=1;}
 assert_eq!(log.mul_calls,1);assert_eq!(aspis_core::field::NKG_prepared_words(log.mul_left)[a][b],aspis_core::field::NKG_prepared_words(prepared)[a][b]);assert_eq!(NKG_words(log.mul_right),NKG_words(sum));assert_eq!(NKG_words(out),NKG_words(reply));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_prepared_factory(){
 let words:[[u32;3];3]=kani::any();let p=aspis_core::field::NKG_prepared_from_words(words);let mut actual=aspis_core::field::NKG_prepared_words(p);
 let a:usize=kani::any();let b:usize=kani::any();kani::assume(a<3&&b<3);
 if cfg!(NKG_bad_output){actual[a][b]^=1;}
 assert_eq!(actual[a][b],words[a][b]);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_leading_selector_read(){
 let selectors=StateOnlyPoseidonSelectors{local:core::array::from_fn(|_|NKG_q()),block:NKG_q()};
 let mut leading_low=selectors.local[0];
 if cfg!(NKG_bad_output){leading_low.c0.a.0^=1;}
 assert_eq!(NKG_words(leading_low),NKG_words(selectors.local[0]));
}
struct NKG_LowControl{rows:[usize;10],calls:usize}
fn NKG_control_add(log:&mut NKG_LowControl,row:usize)->QM31{let k=log.calls;assert!(k<10);log.rows[k]=row;log.calls+=1;QM31::ZERO}
// (ad) control ONLY. The replacement arithmetic body carries no value/frame credit.
fn NKG_low_controller(selectors:&StateOnlyPoseidonSelectors,log:&mut NKG_LowControl){
 let leading_low=selectors.local[0];
 let full_low=[1usize,9,10].into_iter().fold(QM31::ZERO,|_sum,row|NKG_control_add(log,row));
 let internal_low=(2usize..=8).fold(QM31::ZERO,|_sum,row|NKG_control_add(log,row));
 let _=(leading_low,full_low,internal_low);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_low_control_order(){
 let selectors=StateOnlyPoseidonSelectors{local:core::array::from_fn(|_|NKG_q()),block:NKG_q()};let mut log=NKG_LowControl{rows:[0;10],calls:0};NKG_low_controller(&selectors,&mut log);
 let k:usize=kani::any();kani::assume(k<10);
 if cfg!(NKG_bad_argument){log.rows[k]^=1;}
 assert_eq!(log.calls,10);assert_eq!(log.rows[k],if k==0{1}else if k==1{9}else if k==2{10}else{k-1});
}
