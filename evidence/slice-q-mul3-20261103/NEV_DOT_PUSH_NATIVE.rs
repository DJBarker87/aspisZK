// Receipt-only replay source; compiled solely from cfg(kani) scratch module.
struct NEV_RawLog { a:[u32;4],b:[u32;4],reply:[u64;4],calls:u8 }
impl NEV_RawLog {
 fn call(&mut self,a:Q,b:Q)->[u64;4] {self.a=a.0;self.b=b.0;self.calls+=1;self.reply}
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dot_push_iteration() {
 let before:[u64;4]=kani::any();let left:[u32;4]=kani::any();let right:[u32;4]=kani::any();
 for k in 0..4 {kani::assume(left[k]<P && right[k]<P);}
 let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<4 && observed<4);
 let reply:[u64;4]=kani::any();let mut log=NEV_RawLog{a:[0;4],b:[0;4],reply,calls:0};
 let mut dot=Dot{sums:before};let raw=log.call(Q(left),Q(right));
 let mut cursor=index..4;let j=cursor.next().unwrap();
 // Literal native ONE-iteration body; raw arithmetic is an opaque owned call.
 dot.sums[j]=dot.sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));
 assert_eq!(cursor.start,index+1);assert_eq!(cursor.end,4);
 assert_eq!(log.calls,1);assert_eq!(log.a,left);assert_eq!(log.b,right);
 let expected=if observed==index {before[observed].wrapping_add((reply[observed]&u64::from(P)).wrapping_add(reply[observed]>>31u32))}else{before[observed]};
 assert_eq!(dot.sums[observed],if cfg!(NEV_wrong_dot_iteration){expected^1}else{expected});
}
