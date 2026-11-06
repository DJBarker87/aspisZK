use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Full caller bound: MAX_BATCH * LEAF_BITS * digest bytes = 9216.
// Every byte is arbitrary, including all coordinates outside the selected view.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_sibling_window() {
 let nodes:[u8;9216]=kani::any();let len:usize=kani::any();let at:usize=kani::any();let j:usize=kani::any();
 kani::assume(len<=9216&&at<=9216&&j<32);
 if cfg!(NJP_payload_only){kani::assume(at+32<=len);}
 let part=nodes[..len].get(at..at+32);
 match part {
  Some(sibling)=>{
   assert!(at+32<=len);assert_eq!(sibling.len(),32);assert_eq!(sibling.as_ptr(),unsafe{nodes.as_ptr().add(at)});
   if cfg!(NJP_bad_argument){assert_eq!(sibling[j],nodes[at+j]^1)}else{assert_eq!(sibling[j],nodes[at+j])}
  },
  None=>{if cfg!(NJP_bad_argument){assert!(at+32<=len)}else{assert!(len<at+32)}}
 }
}

// Full-range branch cuts imported from NJE, revalidated on full-range buffers.
struct NJP_RowLog {reply:[u8;32],calls:usize,kind:usize,left:bool,i:usize,len:usize,ptr:*const u8,coordinate:usize,byte:usize,observed:u8,first:u8,second:u8}
fn NJP_row_occupied(log:&mut NJP_RowLog,val:&[[u8;32];16],i:usize)->[u8;32]{
 assert_eq!(val[log.coordinate][log.byte],log.observed);
 log.first=val[i][log.byte];log.second=val[i+1][log.byte];log.calls+=1;log.kind=1;log.i=i;log.ptr=val.as_ptr() as *const u8;log.len=16;
 log.reply
}
fn NJP_row_sibling(log:&mut NJP_RowLog,val:&[[u8;32];16],i:usize,sibling:&[u8],left:bool)->[u8;32]{
 assert_eq!(val[log.coordinate][log.byte],log.observed);
 log.first=val[i][log.byte];log.second=sibling[log.byte];log.calls+=1;log.kind=2;log.i=i;log.ptr=sibling.as_ptr();log.len=sibling.len();log.left=left;
 log.reply
}
fn NJP_binary_row(log:&mut NJP_RowLog,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],i:&mut usize,w:&mut usize,at:&mut usize)->bool{
 if *i<n {
 let parent=super::index_at(idx,*i)>>super::Arity::Two.bits();
 let digest=if *i+1<n&&super::index_at(idx,*i+1)==super::index_at(idx,*i)^1 {
 let d=NJP_row_occupied(log,val,*i);*i+=2;d
 }else{
 let Some(sibling)=nodes.get(*at..*at+32)else{return false};
 *at+=32;
 let d=NJP_row_sibling(log,val,*i,sibling,super::index_at(idx,*i)&1==0);
 *i+=1;d
 };
 idx[*w]=parent;val[*w]=digest;*w+=1;
 }
 true
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_binary_row_window(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let nodes:[u8;9216]=kani::any();
 let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut at:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();
 kani::assume(0<n&&n<=16&&i<n&&w<=i&&at<=9216&&len<=9216&&k<16&&h<32);
 let paired=i+1<n&&idx[i+1]==idx[i]^1;
 if cfg!(NJP_pair_class){kani::assume(paired);}else{kani::assume(!paired&&at+32<=len);}
 let oldi=i;let oldw=w;let oldat=at;let beforeidx=idx[k];let beforeval=val[k][h];let parent=idx[i]>>1;let left=idx[i]&1==0;
 let first=val[i][h];let second=if paired{val[i+1][h]}else{nodes[at+h]};
 let reply:[u8;32]=kani::any();let expectedreply=reply[h];let base=nodes.as_ptr();let valuebase=val.as_ptr() as *const u8;
 let mut log=NJP_RowLog{reply,calls:0,kind:0,left:false,i:0,len:0,ptr:core::ptr::null(),coordinate:k,byte:h,observed:beforeval,first:0,second:0};
 let theorem:usize=if cfg!(NJP_row_0){0}else if cfg!(NJP_row_1){1}else if cfg!(NJP_row_2){2}else if cfg!(NJP_row_3){3}else if cfg!(NJP_row_4){4}else if cfg!(NJP_row_5){5}else if cfg!(NJP_row_6){6}else if cfg!(NJP_row_7){7}else if cfg!(NJP_row_8){8}else{9};
 if theorem==8{kani::assume(k==oldw);}
 if theorem==9{kani::assume(k!=oldw);}
 let succeeded=NJP_binary_row(&mut log,&mut idx,&mut val,n,&nodes[..len],&mut i,&mut w,&mut at);
 macro_rules! assert_eq {($a:expr,$b:expr)=>{assert!(if cfg!(NJP_bad_argument){$a!=$b}else{$a==$b})}}
 if theorem==0{assert_eq!(succeeded,true);}
 if theorem==1{assert_eq!(log.calls,1);}
 if theorem==2{assert_eq!(log.kind,if paired{1}else{2});assert_eq!(log.i,oldi);assert_eq!(log.ptr,if paired{valuebase}else{unsafe{base.add(oldat)}});assert_eq!(log.len,if paired{16}else{32});}
 if theorem==3{assert_eq!(log.first,first);assert_eq!(log.second,second);if !paired{assert_eq!(log.left,left);}}
 if theorem==4{assert_eq!(i,oldi+if paired{2}else{1});}
 if theorem==5{assert_eq!(w,oldw+1);}
 if theorem==6{assert_eq!(at,oldat+if paired{0}else{32});}
 if theorem==7{assert_eq!(idx[k],if k==oldw{parent}else{beforeidx});}
 if theorem==8{assert_eq!(val[k][h],expectedreply);}
 if theorem==9{assert_eq!(val[k][h],beforeval);}
}
