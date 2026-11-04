// Receiver/window fission of the row call. The CLOSED NEI push law supplies
// the selected returned row; this native context quantifies ANY such row.
struct NEV_ReceiverLog {
 called:bool,receiver:usize,data:usize,len:usize,capacity:usize,terms:usize,
 index:usize,power:[u32;4],basis:u32,old:[u64;4],reply:[u64;4],
}
impl NEV_ReceiverLog {
 fn call(&mut self,target:&mut BatchedWeights,index:usize,power:QM31,basis:M31) {
  assert!(!self.called);self.called=true;
  self.receiver=target as *mut BatchedWeights as usize;
  self.data=target.raw.as_ptr() as usize;self.len=target.raw.len();
  self.capacity=target.raw.capacity();self.terms=target.terms;
  self.index=index;self.power=NEV_qwords(power);self.basis=basis.0;
  self.old=target.raw[index];target.raw[index]=self.reply;
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn accumulate_row_receiver() {
 let mut b=BatchedWeights {raw:kani::vec::exact_vec::<[u64;4],64>(),terms:kani::any()};
 kani::assume(b.terms<22);
 let index:usize=kani::any();let observed:usize=kani::any();let lane:usize=kani::any();
 kani::assume(index<64 && observed<64 && lane<4);
 let power=NEV_any_qm();let basis=M31(kani::any());kani::assume(basis.0<2147483647);
 let receiver=&mut b as *mut BatchedWeights as usize;
 let pointer=b.raw.as_ptr() as usize;let capacity=b.raw.capacity();let terms=b.terms;
 let old=b.raw[index];let window=b.raw[observed][lane];
 let mut log=NEV_ReceiverLog {called:false,receiver:0,data:0,len:0,capacity:0,terms:0,index:0,power:[0;4],basis:0,old:[0;4],reply:kani::any()};
 log.call(&mut b,index,power,basis);
 assert!(log.called && log.receiver==receiver && log.data==pointer && log.len==64 && log.capacity==capacity && log.terms==terms);
 assert!(log.index==index && log.power==NEV_qwords(power) && log.basis==basis.0 && log.old==old);
 assert!(b.raw.len()==64 && b.raw.capacity()==capacity && b.raw.as_ptr() as usize==pointer && b.terms==terms);
 let expected=if observed==index{log.reply[lane]}else{window};
 assert_eq!(b.raw[observed][lane],if cfg!(NEV_wrong_receiver){expected^1}else{expected});
}
