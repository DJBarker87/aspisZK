use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}


struct FrontierLog{window:usize,calls:usize,fail:bool,error:Error,observe:usize,word:usize,seen:bool,vec_place:*const alloc::vec::Vec<u8>,row:*const M31,value:u32,before_len:usize,before_byte:u8,after_len:usize,after_byte:u8,after_ptr:*const u8}
fn NHG_fields_cut(out:&mut alloc::vec::Vec<u8>,values:&[M31],log:&mut FrontierLog)->Result<(),Error>{
 let j=log.calls;assert!(j<20);assert_eq!(values.len(),8);assert!(out.len()>=1&&out.len()+32<=1880);log.calls+=1;
 if j==log.window{
  log.seen=true;log.vec_place=out;log.row=values.as_ptr();log.value=values[log.word].0;log.before_len=out.len();log.before_byte=if log.observe<out.len(){out[log.observe]}else{0};
  let length:usize=kani::any();kani::assume(length>=out.len()&&length<=out.len()+32);
  let delta=length-out.len();let suffix:[u8;32]=kani::any();
  if cfg!(NHG_invert){kani::assume(delta>0);kani::assume(log.observe>=out.len());kani::assume(log.observe<length);}
  out.extend_from_slice(&suffix[..delta]);
  log.after_len=length;log.after_byte=if log.observe<length{out[log.observe]}else{0};log.after_ptr=out.as_ptr();
  if log.fail{return Err(log.error)}
 }
 Ok(())
}
fn NHG_frontier_control(out:&mut alloc::vec::Vec<u8>,values:&[Digest;20],log:&mut FrontierLog)->Result<(),Error>
{
                NHG_fields_cut(out, &values[0], log)?;
                NHG_fields_cut(out, &values[1], log)?;
                NHG_fields_cut(out, &values[2], log)?;
                NHG_fields_cut(out, &values[3], log)?;
                NHG_fields_cut(out, &values[4], log)?;
                NHG_fields_cut(out, &values[5], log)?;
                NHG_fields_cut(out, &values[6], log)?;
                NHG_fields_cut(out, &values[7], log)?;
                NHG_fields_cut(out, &values[8], log)?;
                NHG_fields_cut(out, &values[9], log)?;
                NHG_fields_cut(out, &values[10], log)?;
                NHG_fields_cut(out, &values[11], log)?;
                NHG_fields_cut(out, &values[12], log)?;
                NHG_fields_cut(out, &values[13], log)?;
                NHG_fields_cut(out, &values[14], log)?;
                NHG_fields_cut(out, &values[15], log)?;
                NHG_fields_cut(out, &values[16], log)?;
                NHG_fields_cut(out, &values[17], log)?;
                NHG_fields_cut(out, &values[18], log)?;
                NHG_fields_cut(out, &values[19], log)?;
                Ok(())
            }
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
fn NHG_frontier_value(){
 let values:[Digest;20]=core::array::from_fn(|_|digest());let window:usize=kani::any();kani::assume(window<20);
 let n:usize=kani::any();kani::assume(n>=1&&n<=1240+32*window);
 let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);let place=&out as *const alloc::vec::Vec<u8>;
 let observe:usize=kani::any();kani::assume(observe<1880);let word:usize=kani::any();kani::assume(word<8);let old_byte=if observe<n{out[observe]}else{0};let fail:bool=kani::any();let error=any_error();
 let mut log=FrontierLog{window,calls:0,fail,error,observe,word,seen:false,vec_place:core::ptr::null(),row:core::ptr::null(),value:0,before_len:0,before_byte:0,after_len:0,after_byte:0,after_ptr:core::ptr::null()};
 let got=NHG_frontier_control(&mut out,&values,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{20});
 assert_eq!(log.vec_place,place);assert_eq!(log.row,values[window].as_ptr());assert_eq!(log.value,values[window][word].0);assert_eq!(log.before_len,n);if observe<n{assert_eq!(log.before_byte,old_byte);}
 assert_eq!(out.len(),log.after_len);assert_eq!(out.as_ptr(),log.after_ptr);assert_eq!(got,if fail{Err(error)}else{Ok(())});
 if cfg!(NHG_invert){kani::assume(observe<out.len());}
 if observe<out.len(){assert_eq!(out[observe],log.after_byte^if cfg!(NHG_invert){1}else{0});}
}
