// Independent per-field replacements for the retired whole-carrier windows.
struct ViewWindowLog<'a,const PART:usize>{proof:&'a[u8],inactive:E,reply:Result<(),Error>,calls:usize}
impl<const PART:usize> ViewWindowLog<'_,PART>{fn finish(&mut self,v:&View)->Result<(),Error>{
 self.calls+=1;assert!(v.variant==Variant::S2);assert!(v.semantic.is_empty());assert!(v.y1.is_empty());assert!(v.query_bytes.is_empty());assert!(v.folded_root.is_none());assert_eq!(v.inactive,self.inactive);
 assert_eq!(v.round0.as_ptr(),self.proof.as_ptr().wrapping_add(7527));assert_eq!(v.round0.len(),224);assert_eq!(v.round1.as_ptr(),self.proof.as_ptr().wrapping_add(7783));assert_eq!(v.round1.len(),224);assert_eq!(v.final_message.as_ptr(),self.proof.as_ptr().wrapping_add(8007));assert_eq!(v.final_message.len(),2048);
 if PART==0{let i=kani::any::<u8>() as usize;kani::assume(i<224);assert_eq!(v.round0[i],self.proof[7527+i]^(if cfg!(NKE_invert){1}else{0}));}
 if PART==1{let i=kani::any::<u8>() as usize;kani::assume(i<224);assert_eq!(v.round1[i],self.proof[7783+i]^(if cfg!(NKE_invert){1}else{0}));}
 if PART==2{let i=(kani::any::<u16>()&2047) as usize;assert_eq!(v.final_message[i],self.proof[8007+i]^(if cfg!(NKE_invert){1}else{0}));}
 self.reply
}}
fn view_window<const PART:usize>(){
 let proof:[u8;57607]=kani::any();let proof=&proof[..];let inactive=any_e();let reply=if kani::any(){Ok(())}else{Err(error(kani::any()))};let mut log=ViewWindowLog::<PART>{proof,inactive,reply,calls:0};
 let v=View{variant:Variant::S2,semantic:&[],y1:&[],inactive,round0:&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],folded_root:None,round1:&proof[compact::OFF_ROUND1..compact::OFF_FINAL],final_message:&proof[compact::OFF_FINAL..compact::OFF_OPENINGS],query_bytes:&[]};
 let out=log.finish(&v);assert_eq!(log.calls,1);assert_eq!(out,reply);
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn view_round0(){view_window::<0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn view_round1(){view_window::<1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn view_final(){view_window::<2>();}

// Full SAME-reader native call and Try prefix for K and E. Only cursor mutates.
struct ReaderLog<'a,T:Copy>{bytes:&'a[u8],cursor:usize,post:usize,value:T,err:Option<Error>,seen:Option<&'a[u8]>,calls:usize}
impl<'a,T:Copy> ReaderLog<'a,T>{fn read(&mut self,r:&mut Reader<'a>)->Result<T,Error>{
 self.calls+=1;self.seen=Some(r.bytes);assert_eq!(r.at,self.cursor);r.at=self.post;match self.err{Some(e)=>Err(e),None=>Ok(self.value)}
}}
fn read_stage<'a,T:Copy>(bytes:&'a[u8],at:usize,log:&mut ReaderLog<'a,T>)->Result<(T,usize),Error>{
 let mut r=Reader{bytes,at};let value=log.read(&mut r)?;Ok((value,r.at))
}
fn reader_window<const WIDE:bool>(){
 let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let post:usize=kani::any();let words:[u32;8]=kani::any();let err=if kani::any(){Some(error(kani::any()))}else{None};
 let mut log=ReaderLog{bytes:&bytes,cursor:at,post,value:if WIDE{E::new(k([words[0],words[1],words[2],words[3]]),k([words[4],words[5],words[6],words[7]]))}else{E::new(k([words[0],words[1],words[2],words[3]]),K::ZERO)},err,seen:None,calls:0};
 let out=read_stage(&bytes,at,&mut log);assert_eq!(log.calls,1);let seen=log.seen.unwrap();assert_eq!(seen.as_ptr(),bytes.as_ptr());assert_eq!(seen.len(),1768);let i=(kani::any::<u16>()&2047) as usize;kani::assume(i<1768);assert_eq!(seen[i],bytes[i]);
 match out{Err(e)=>{assert_eq!(Some(e),err);assert!(!cfg!(NKE_invert));},Ok((value,cursor))=>{assert!(err.is_none());assert_eq!(cursor,post);let got=value.to_limbs();let i:usize=kani::any();kani::assume(i<(if WIDE{8}else{4}));assert_eq!(got[i],words[i]^(if cfg!(NKE_invert){1}else{0}));}}
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn reader_e_call(){reader_window::<true>();}
// K has a distinct full return type; do not cite an E-shaped cut for it.
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn reader_k_call(){
 let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let post:usize=kani::any();let words:[u32;4]=kani::any();let value=k(words);let err=if kani::any(){Some(error(kani::any()))}else{None};let mut log=ReaderLog{bytes:&bytes,cursor:at,post,value,err,seen:None,calls:0};let out=read_stage(&bytes,at,&mut log);assert_eq!(log.calls,1);let seen=log.seen.unwrap();assert_eq!(seen.as_ptr(),bytes.as_ptr());assert_eq!(seen.len(),1768);let i=(kani::any::<u16>()&2047) as usize;kani::assume(i<1768);assert_eq!(seen[i],bytes[i]);
 match out{Err(e)=>{assert_eq!(Some(e),err);assert!(!cfg!(NKE_invert));},Ok((v,cursor))=>{assert!(err.is_none());assert_eq!(cursor,post);assert_eq!(v.c0.a.0,words[0]^(if cfg!(NKE_invert){1}else{0}));assert_eq!(v.c0.b.0,words[1]);assert_eq!(v.c1.a.0,words[2]);assert_eq!(v.c1.b.0,words[3]);}}
}
struct ValidateLog{queries:[u32;22],reply:Result<(),Error>,calls:usize}
impl ValidateLog{fn validate(&mut self,queries:&[u32;22])->Result<(),Error>{self.calls+=1;assert_eq!(*queries,self.queries);self.reply}}
fn validate_stage(queries:&[u32;22],log:&mut ValidateLog)->Result<(),Error>{log.validate(queries)?;Ok(())}
#[kani::proof]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn validate_call(){let queries:[u32;22]=kani::any();let reply=if kani::any(){Ok(())}else{Err(error(kani::any()))};let mut log=ValidateLog{queries,reply,calls:0};let out=validate_stage(&queries,&mut log);assert_eq!(log.calls,1);assert_eq!(out,if cfg!(NKE_invert){match reply{Ok(())=>Err(Error::Parse),Err(_)=>Ok(())}}else{reply});assert_eq!(queries,log.queries);}

struct PowersLog{gamma:E,reply:[E;29],calls:usize}
impl PowersLog{fn powers(&mut self,gamma:E)->[E;29]{self.calls+=1;assert_eq!(gamma,self.gamma);self.reply}}
fn powers_stage(gamma:E,log:&mut PowersLog)->[E;29]{let g=log.powers(gamma);g}
#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn powers_call(){let gamma=any_e();let words:[[u32;8];29]=kani::any();let reply=words.map(|w|E::new(k([w[0],w[1],w[2],w[3]]),k([w[4],w[5],w[6],w[7]])));let mut log=PowersLog{gamma,reply,calls:0};let out=powers_stage(gamma,&mut log);assert_eq!(log.calls,1);let i=(kani::any::<u8>()&31) as usize;kani::assume(i<29);let j=(kani::any::<u8>()&7) as usize;assert_eq!(out[i].to_limbs()[j],words[i][j]^(if cfg!(NKE_invert){1}else{0}));}
