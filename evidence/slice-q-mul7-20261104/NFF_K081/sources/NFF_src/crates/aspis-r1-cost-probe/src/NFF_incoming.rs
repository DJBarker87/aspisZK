use super::*;
struct NFF_Call {calls:usize,q:usize,g:usize,reply:[E;4]}
fn NFF_dots(q:&[u8;832],g:&[E;29],log:&mut NFF_Call)->[E;4]{log.calls+=1;log.q=q.as_ptr() as usize;log.g=g.as_ptr() as usize;log.reply}
fn NFF_prefix(queries:&[u32;22],next:usize,q:&[u8;832],g:&[E;29],log:&mut NFF_Call)->(usize,usize,[E;4]){
 let i=next;let u=queries[i] as usize;let dots=NFF_dots(q,g,log);(i,u,dots)
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_prefix_same_inputs(){
 let queries:[u32;22]=kani::any();let next:usize=kani::any();kani::assume(next<22);
 let q:[u8;832]=kani::any();let g:[E;29]=kani::any();let reply:[E;4]=kani::any();
 let mut log=NFF_Call{calls:0,q:0,g:0,reply};let (i,u,dots)=NFF_prefix(&queries,next,&q,&g,&mut log);
 assert_eq!(i,next);assert_eq!(u,queries[next] as usize);assert_eq!(log.calls,1);
 assert_eq!(log.q,q.as_ptr() as usize);assert_eq!(log.g,g.as_ptr() as usize);
 let at:usize=kani::any();let word:usize=kani::any();kani::assume(at<4 && word<8);
 let expected=reply[at].to_limbs()[word];assert_eq!(dots[at].to_limbs()[word],if cfg!(NFF_wrong_query_prefix){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_field_window(){
 let bytes:[u8;128]=kani::any();let s:usize=kani::any();kani::assume(s<4);
 for j in 0..8{let at=s*32+j*4;kani::assume(u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])<2147483647);}
 let value=crate::weights::field(&bytes,s);let lane:usize=kani::any();kani::assume(lane<8);let at=s*32+lane*4;
 let expected=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);
 assert_eq!(value.to_limbs()[lane],if cfg!(NFF_wrong_query_field){expected^1}else{expected});
}
fn NFF_guard(folded:E,values:[E;4],u:usize,reply:E,calls:&mut usize)->Result<E,Error>{
 if folded!=values[u%4]{return Err(Error::Query);}
 *calls+=1;Ok(reply)
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_guard_continuation(){
 let folded:E=kani::any();let values:[E;4]=kani::any();let reply:E=kani::any();let u:usize=kani::any();let mut calls=0;
 let out=NFF_guard(folded,values,u,reply,&mut calls);
 if folded!=values[u%4]{assert!(matches!(out,Err(Error::Query)));assert_eq!(calls,0);}else{
 assert_eq!(calls,1);let lane:usize=kani::any();kani::assume(lane<8);let expected=reply.to_limbs()[lane];
 assert_eq!(out.unwrap().to_limbs()[lane],if cfg!(NFF_wrong_query_guard){expected^1}else{expected});}
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_geometry_association(){
 let inverses:[[M31;5];22]=kani::any();let line_z:[M31;22]=kani::any();
 let start:usize=kani::any();let index:usize=kani::any();kani::assume(start<=index && index<22);
 let geometry=QueryGeometry{start,inverses:inverses.to_vec(),line_z:line_z.to_vec()};
 let inverse=geometry.for_query(index);let j:usize=kani::any();kani::assume(j<5);
 assert_eq!(inverse.as_ptr(),geometry.inverses[index-start].as_ptr());
 assert_eq!(inverse[j].0,inverses[index-start][j].0);
 let expected=line_z[index-start].0;assert_eq!(geometry.line_z[index-start].0,if cfg!(NFF_wrong_query_geometry){expected^1}else{expected});
}
struct NFF_Product {left:u32,right:u32,calls:usize,reply:M31}
fn NFF_mul(a:M31,b:M31,log:&mut NFF_Product)->M31{log.left=a.0;log.right=b.0;log.calls+=1;log.reply}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_node_product_continuation(){
 let z:M31=kani::any();let reply:M31=kani::any();kani::assume(z.0<2147483647 && reply.0<2147483647);
 let mut log=NFF_Product{left:0,right:0,calls:0,reply};let node=NFF_mul(z,z,&mut log).double().sub(M31::ONE);
 assert_eq!(log.left,z.0);assert_eq!(log.right,z.0);assert_eq!(log.calls,1);
 let sum=reply.0+reply.0;let doubled=if sum>=2147483647{sum-2147483647}else{sum};
 let expected=if doubled==0{2147483646}else{doubled-1};
 assert_eq!(node.0,if cfg!(NFF_wrong_query_node){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn opening_address_window(){
 let i:usize=kani::any();kani::assume(i<22);
 let at=crate::compact::OFF_OPENINGS+i*crate::compact::OPENING;let end=at+crate::compact::OPENING;
 assert!(end<=crate::compact::PROOF_BYTES);assert_eq!(end-at,832);
 assert_eq!(at,if cfg!(NFF_wrong_opening_address){crate::compact::OFF_OPENINGS+(i+1)*832}else{crate::compact::OFF_OPENINGS+i*832});
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_folded_subslice(){
 let q:[u8;832]=kani::any();let s=&q[672..800];let k:usize=kani::any();kani::assume(k<128);
 assert_eq!(s.as_ptr(),q[672..].as_ptr());assert_eq!(s.len(),128);
 assert_eq!(s[k],if cfg!(NFF_wrong_folded_subslice){q[672+k]^1}else{q[672+k]});
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_child_input_frame(){
 let q:[u8;832]=kani::any();let g:[E;29]=kani::any();let queries:[u32;22]=kani::any();let next:usize=kani::any();kani::assume(next<22);
 let at:usize=kani::any();let coefficient:usize=kani::any();let lane:usize=kani::any();kani::assume(at<832 && coefficient<29 && lane<8);
 let byte=q[at];let word=g[coefficient].to_limbs()[lane];let mut log=NFF_Call{calls:0,q:0,g:0,reply:kani::any()};
 let _=NFF_prefix(&queries,next,&q,&g,&mut log);
 assert_eq!(g[coefficient].to_limbs()[lane],word);assert_eq!(q[at],if cfg!(NFF_wrong_query_frame){byte^1}else{byte});
}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn query_slot_partition(){
 let slot:usize=kani::any();let term:usize=kani::any();let tail:usize=kani::any();kani::assume(slot<4 && term<26 && tail<2);
 let base=slot*120+term*4;let first=slot*120+104;let later=480+slot*32+tail*16;
 assert!(base+4<=first && first+16<=480 && later>=480 && later+16<=608);
 assert_eq!(later,if cfg!(NFF_wrong_partition){480+slot*32+(1-tail)*16}else{480+slot*32+tail*16});
}
