fn NKG_p()->PreparedQm31Multiplier{aspis_core::field::NKG_prepared_from_words(kani::any())}
struct NKG_LowLog{args:[QM31;2],reply:QM31,calls:usize}
fn NKG_low_add(log:&mut NKG_LowLog,x:QM31,y:QM31)->QM31{assert_eq!(log.calls,0);log.args=[x,y];log.calls=1;log.reply}
// One source fold callback. The seven-term fold is composed by Lean induction.
fn NKG_low_step(log:&mut NKG_LowLog,local:&[QM31;16],acc:QM31,row:usize)->QM31{NKG_low_add(log,acc,local[row])}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_low_iteration(){
 let local:[QM31;16]=core::array::from_fn(|_|NKG_q());let acc=NKG_q();let reply=NKG_q();let row:usize=kani::any();kani::assume(row<16);
 let mut log=NKG_LowLog{args:[QM31::ZERO;2],reply,calls:0};let mut out=NKG_low_step(&mut log,&local,acc,row);
 if cfg!(NKG_bad_output){out.c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.args[1].c0.a.0^=1;}
 assert_eq!(log.calls,1);assert_eq!(NKG_words(log.args[0]),NKG_words(acc));assert_eq!(NKG_words(log.args[1]),NKG_words(local[row]));assert_eq!(NKG_words(out),NKG_words(reply));
}
struct NKG_PrepLog{inputs:[QM31;4],replies:[PreparedQm31Multiplier;4],calls:usize}
fn NKG_prepare(log:&mut NKG_PrepLog,value:QM31)->PreparedQm31Multiplier{let k=log.calls;assert!(k<4);log.inputs[k]=value;log.calls+=1;log.replies[k]}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_prepared_stage(){
 let values:[QM31;3]=core::array::from_fn(|_|NKG_q());let block=NKG_q();let replies:[PreparedQm31Multiplier;4]=core::array::from_fn(|_|NKG_p());
 let mut log=NKG_PrepLog{inputs:[QM31::ZERO;4],replies,calls:0};
 let prepared_weights=values.map(|v|NKG_prepare(&mut log,v));let mut prepared_block=NKG_prepare(&mut log,block);
 let k:usize=kani::any();let a:usize=kani::any();let b:usize=kani::any();kani::assume(k<3&&a<3&&b<3);
 if cfg!(NKG_bad_output){let mut words=aspis_core::field::NKG_prepared_words(prepared_block);words[0][0]^=1;prepared_block=aspis_core::field::NKG_prepared_from_words(words);}
 if cfg!(NKG_bad_argument){log.inputs[k].c0.a.0^=1;}
 assert_eq!(log.calls,4);assert_eq!(NKG_words(log.inputs[k]),NKG_words(values[k]));assert_eq!(NKG_words(log.inputs[3]),NKG_words(block));assert_eq!(aspis_core::field::NKG_prepared_words(prepared_weights[k])[a][b],aspis_core::field::NKG_prepared_words(replies[k])[a][b]);assert_eq!(aspis_core::field::NKG_prepared_words(prepared_block)[a][b],aspis_core::field::NKG_prepared_words(replies[3])[a][b]);
}
struct NKG_GroupLog{pack_inputs:[[QM31;4];2],pack_replies:[QM31;2],pack_calls:usize,sub_args:[[QM31;2];3],sub_replies:[QM31;3],sub_calls:usize,sum_weights:[PreparedQm31Multiplier;3],sum_right:[QM31;3],sum_reply:QM31,sum_calls:usize,mul_left:PreparedQm31Multiplier,mul_right:QM31,mul_reply:QM31,mul_calls:usize}
fn NKG_pack(log:&mut NKG_GroupLog,values:&[QM31])->QM31{let k=log.pack_calls;assert!(k<2);assert_eq!(values.len(),4);log.pack_inputs[k]=core::array::from_fn(|i|values[i]);log.pack_calls+=1;log.pack_replies[k]}
fn NKG_sub(log:&mut NKG_GroupLog,x:QM31,y:QM31)->QM31{let k=log.sub_calls;assert!(k<3);log.sub_args[k]=[x,y];log.sub_calls+=1;log.sub_replies[k]}
fn NKG_sum(log:&mut NKG_GroupLog,p:&[PreparedQm31Multiplier;3],r:&[QM31;3])->QM31{assert_eq!(log.sum_calls,0);log.sum_weights=*p;log.sum_right=*r;log.sum_calls=1;log.sum_reply}
fn NKG_pmul(log:&mut NKG_GroupLog,p:PreparedQm31Multiplier,r:QM31)->QM31{assert_eq!(log.mul_calls,0);log.mul_left=p;log.mul_right=r;log.mul_calls=1;log.mul_reply}
fn NKG_group(log:&mut NKG_GroupLog,succ:&[QM31;16],internal:&[QM31;16],leading:&[QM31;4],full:&[QM31;4],prepared_weights:&[PreparedQm31Multiplier;3],prepared_block:PreparedQm31Multiplier,group:usize)->QM31{
 let start=4*group;
 let target=NKG_pack(log,&succ[start..start+4]);
 let internal=NKG_pack(log,&internal[start..start+4]);
 let d0=NKG_sub(log,target,leading[group]);let d1=NKG_sub(log,target,full[group]);let d2=NKG_sub(log,target,internal);
 let sum=NKG_sum(log,prepared_weights,&[d0,d1,d2]);NKG_pmul(log,prepared_block,sum)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_group_iteration(){
 let succ:[QM31;16]=core::array::from_fn(|_|NKG_q());let internal:[QM31;16]=core::array::from_fn(|_|NKG_q());let leading:[QM31;4]=core::array::from_fn(|_|NKG_q());let full:[QM31;4]=core::array::from_fn(|_|NKG_q());
 let prepared_weights:[PreparedQm31Multiplier;3]=core::array::from_fn(|_|NKG_p());let prepared_block=NKG_p();
 let pack_replies:[QM31;2]=core::array::from_fn(|_|NKG_q());let sub_replies:[QM31;3]=core::array::from_fn(|_|NKG_q());let sum_reply=NKG_q();let mul_reply=NKG_q();
 let mut log=NKG_GroupLog{pack_inputs:[[QM31::ZERO;4];2],pack_replies,pack_calls:0,sub_args:[[QM31::ZERO;2];3],sub_replies,sub_calls:0,sum_weights:core::array::from_fn(|_|NKG_p()),sum_right:[QM31::ZERO;3],sum_reply,sum_calls:0,mul_left:NKG_p(),mul_right:QM31::ZERO,mul_reply,mul_calls:0};
 let group:usize=kani::any();let k:usize=kani::any();let j:usize=kani::any();kani::assume(group<4&&k<4&&j<3);
 let mut out=NKG_group(&mut log,&succ,&internal,&leading,&full,&prepared_weights,prepared_block,group);
 if cfg!(NKG_bad_output){out.c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.pack_inputs[0][k].c0.a.0^=1;}
 assert_eq!(log.pack_calls,2);assert_eq!(log.sub_calls,3);assert_eq!(log.sum_calls,1);assert_eq!(log.mul_calls,1);
 assert_eq!(NKG_words(log.pack_inputs[0][k]),NKG_words(succ[4*group+k]));assert_eq!(NKG_words(log.pack_inputs[1][k]),NKG_words(internal[4*group+k]));
 assert_eq!(NKG_words(log.sub_args[j][0]),NKG_words(pack_replies[0]));assert_eq!(NKG_words(log.sub_args[j][1]),NKG_words(if j==0{leading[group]}else if j==1{full[group]}else{pack_replies[1]}));
 assert_eq!(aspis_core::field::NKG_prepared_words(log.sum_weights[j]),aspis_core::field::NKG_prepared_words(prepared_weights[j]));assert_eq!(NKG_words(log.sum_right[j]),NKG_words(sub_replies[j]));assert_eq!(aspis_core::field::NKG_prepared_words(log.mul_left),aspis_core::field::NKG_prepared_words(prepared_block));assert_eq!(NKG_words(log.mul_right),NKG_words(sum_reply));assert_eq!(NKG_words(out),NKG_words(mul_reply));
}
struct NKG_FromFnLog{replies:[QM31;4],indices:[usize;4],calls:usize}
fn NKG_output(log:&mut NKG_FromFnLog,g:usize)->QM31{let k=log.calls;assert!(k<4);log.indices[k]=g;log.calls+=1;log.replies[g]}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_output_constructor(){
 let replies:[QM31;4]=core::array::from_fn(|_|NKG_q());let mut log=NKG_FromFnLog{replies,indices:[0;4],calls:0};
 let mut out:[QM31;4]=core::array::from_fn(|group|NKG_output(&mut log,group));let k:usize=kani::any();kani::assume(k<4);
 if cfg!(NKG_bad_output){out[k].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.indices[k]^=1;}
 assert_eq!(log.calls,4);assert_eq!(log.indices[k],k);assert_eq!(NKG_words(out[k]),NKG_words(replies[k]));
}
struct NKG_PrefixLog{opening:StateOnlyPoseidonOpenings,full_state:[QM31;16],full_local:[QM31;16],internal_state:[QM31;16],internal_local:[QM31;16],lead_reply:[QM31;4],full_reply:[QM31;4],internal_reply:[QM31;16],calls:usize}
fn NKG_lead(log:&mut NKG_PrefixLog,o:&StateOnlyPoseidonOpenings)->[QM31;4]{assert_eq!(log.calls,0);log.opening=*o;log.calls=1;log.lead_reply}
fn NKG_full_child(log:&mut NKG_PrefixLog,s:[QM31;16],l:&[QM31;16])->[QM31;4]{assert_eq!(log.calls,1);log.full_state=s;log.full_local=*l;log.calls=2;log.full_reply}
fn NKG_internal_child(log:&mut NKG_PrefixLog,s:[QM31;16],l:&[QM31;16])->[QM31;16]{assert_eq!(log.calls,2);log.internal_state=s;log.internal_local=*l;log.calls=3;log.internal_reply}
fn NKG_prefix(o:&StateOnlyPoseidonOpenings,s:&StateOnlyPoseidonSelectors,log:&mut NKG_PrefixLog)->([QM31;4],[QM31;4],[QM31;16]){
 let leading=NKG_lead(log,o);let full=NKG_full_child(log,o.z,&s.local);let internal=NKG_internal_child(log,o.z,&s.local);(leading,full,internal)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_prefix_children(){
 let z=core::array::from_fn(|_|NKG_q());let succ_z=core::array::from_fn(|_|NKG_q());let xor12_z=core::array::from_fn(|_|NKG_q());let o=StateOnlyPoseidonOpenings{z,succ_z,xor12_z};let local=core::array::from_fn(|_|NKG_q());let s=StateOnlyPoseidonSelectors{local,block:NKG_q()};
 let lead_reply:[QM31;4]=core::array::from_fn(|_|NKG_q());let full_reply:[QM31;4]=core::array::from_fn(|_|NKG_q());let internal_reply:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let mut log=NKG_PrefixLog{opening:StateOnlyPoseidonOpenings{z:[QM31::ZERO;16],succ_z:[QM31::ZERO;16],xor12_z:[QM31::ZERO;16]},full_state:[QM31::ZERO;16],full_local:[QM31::ZERO;16],internal_state:[QM31::ZERO;16],internal_local:[QM31::ZERO;16],lead_reply,full_reply,internal_reply,calls:0};
 let k:usize=kani::any();let g:usize=kani::any();kani::assume(k<16&&g<4);let mut out=NKG_prefix(&o,&s,&mut log);
 if cfg!(NKG_bad_output){out.2[k].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.full_local[k].c0.a.0^=1;}
 assert_eq!(log.calls,3);
 assert_eq!(NKG_words(log.opening.z[k]),NKG_words(o.z[k]));assert_eq!(NKG_words(log.opening.succ_z[k]),NKG_words(o.succ_z[k]));assert_eq!(NKG_words(log.opening.xor12_z[k]),NKG_words(o.xor12_z[k]));
 assert_eq!(NKG_words(log.full_state[k]),NKG_words(o.z[k]));assert_eq!(NKG_words(log.internal_state[k]),NKG_words(o.z[k]));assert_eq!(NKG_words(log.full_local[k]),NKG_words(s.local[k]));assert_eq!(NKG_words(log.internal_local[k]),NKG_words(s.local[k]));
 assert_eq!(NKG_words(out.0[g]),NKG_words(lead_reply[g]));assert_eq!(NKG_words(out.1[g]),NKG_words(full_reply[g]));assert_eq!(NKG_words(out.2[k]),NKG_words(internal_reply[k]));
}
