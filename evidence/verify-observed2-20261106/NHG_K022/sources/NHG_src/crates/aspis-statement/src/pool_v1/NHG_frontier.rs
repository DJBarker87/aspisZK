use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}

struct FrontierLog{calls:usize,fail_at:usize,error:Error,observe:usize,word:usize,vec_places:[*const alloc::vec::Vec<u8>;20],rows:[*const M31;20],words:[u32;20],before_len:[usize;20],before_byte:[u8;20],after_len:[usize;20],after_byte:[u8;20],after_ptr:[*const u8;20]}
fn NHG_fields_cut(out:&mut alloc::vec::Vec<u8>,values:&[M31],log:&mut FrontierLog)->Result<(),Error>{
 let j=log.calls;assert!(j<20);assert_eq!(values.len(),8);assert!(out.len()>=1&&out.len()+32<=1880);
 log.calls+=1;log.vec_places[j]=out;log.rows[j]=values.as_ptr();log.words[j]=values[log.word].0;log.before_len[j]=out.len();log.before_byte[j]=if log.observe<out.len(){out[log.observe]}else{0};
 let length:usize=kani::any();kani::assume(length>=out.len()&&length<=out.len()+32);
 let mut reply=kani::vec::exact_vec::<u8,1884>();reply.truncate(length);
 log.after_len[j]=length;log.after_byte[j]=if log.observe<length{reply[log.observe]}else{0};log.after_ptr[j]=reply.as_ptr();*out=reply;
 if j==log.fail_at{Err(log.error)}else{Ok(())}
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
fn NHG_frontier_value(){
 let values:[Digest;20]=core::array::from_fn(|_|digest());let n:usize=kani::any();kani::assume(n>=1&&n<=1240);
 let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);let place=&out as *const alloc::vec::Vec<u8>;
 let observe:usize=kani::any();kani::assume(observe<1880);let word:usize=kani::any();kani::assume(word<8);let old_byte=if observe<n{out[observe]}else{0};
 let fail_at:usize=kani::any();kani::assume(fail_at<=20);let error=any_error();
 let mut log=FrontierLog{calls:0,fail_at,error,observe,word,vec_places:[core::ptr::null();20],rows:[core::ptr::null();20],words:[0;20],before_len:[0;20],before_byte:[0;20],after_len:[0;20],after_byte:[0;20],after_ptr:[core::ptr::null();20]};
 let got=NHG_frontier_control(&mut out,&values,&mut log);let count=if fail_at<20{fail_at+1}else{20};assert_eq!(log.calls,count);
 let j:usize=kani::any();kani::assume(j<count);assert_eq!(log.vec_places[j],place);assert_eq!(log.rows[j],values[j].as_ptr());assert_eq!(log.words[j],values[j][word].0);
 assert_eq!(log.before_len[j],if j==0{n}else{log.after_len[j-1]});if observe<log.before_len[j]{assert_eq!(log.before_byte[j],if j==0{old_byte}else{log.after_byte[j-1]});}
 assert_eq!(out.len(),log.after_len[count-1]);assert_eq!(out.as_ptr(),log.after_ptr[count-1]);assert_eq!(got,if fail_at<20{Err(error)}else{Ok(())});
 if cfg!(NHG_invert){kani::assume(fail_at==20);kani::assume(observe<out.len());}
 if observe<out.len(){assert_eq!(out[observe],log.after_byte[count-1]^if cfg!(NHG_invert){1}else{0});}
}
