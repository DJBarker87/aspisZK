use core::fmt::Write;
struct NBP_Writer { index:usize, seen:usize, expected:&'static str }
impl Write for NBP_Writer {
 fn write_str(&mut self,s:&str)->core::fmt::Result {
  let n=s.len();
  if self.index>=self.seen && self.index-self.seen<n {
   assert!(s.as_bytes()[self.index-self.seen]==self.expected.as_bytes()[self.index]);
  }
  self.seen+=n;
  Ok(())
 }
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Parse() {
 let i:usize=kani::any();kani::assume(i<5);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Parse"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Parse).is_ok());
 assert!(w.seen==5);
 kani::cover!(i==4);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Parse() {
 let i:usize=kani::any();kani::assume(i<14);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Parse"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Parse).is_ok());
 assert!(w.seen==14);
 kani::cover!(i==13);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Semantic() {
 let i:usize=kani::any();kani::assume(i<8);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Semantic"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Semantic).is_ok());
 assert!(w.seen==8);
 kani::cover!(i==7);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Semantic() {
 let i:usize=kani::any();kani::assume(i<17);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Semantic"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Semantic).is_ok());
 assert!(w.seen==17);
 kani::cover!(i==16);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Transcript() {
 let i:usize=kani::any();kani::assume(i<10);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Transcript"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Transcript).is_ok());
 assert!(w.seen==10);
 kani::cover!(i==9);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Transcript() {
 let i:usize=kani::any();kani::assume(i<19);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Transcript"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Transcript).is_ok());
 assert!(w.seen==19);
 kani::cover!(i==18);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Relation() {
 let i:usize=kani::any();kani::assume(i<8);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Relation"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Relation).is_ok());
 assert!(w.seen==8);
 kani::cover!(i==7);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Relation() {
 let i:usize=kani::any();kani::assume(i<17);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Relation"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Relation).is_ok());
 assert!(w.seen==17);
 kani::cover!(i==16);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Merkle() {
 let i:usize=kani::any();kani::assume(i<6);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Merkle"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Merkle).is_ok());
 assert!(w.seen==6);
 kani::cover!(i==5);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Merkle() {
 let i:usize=kani::any();kani::assume(i<15);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Merkle"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Merkle).is_ok());
 assert!(w.seen==15);
 kani::cover!(i==14);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Query() {
 let i:usize=kani::any();kani::assume(i<5);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Query"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Query).is_ok());
 assert!(w.seen==5);
 kani::cover!(i==4);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Query() {
 let i:usize=kani::any();kani::assume(i<14);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Query"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Query).is_ok());
 assert!(w.seen==14);
 kani::cover!(i==13);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Checkpoint() {
 let i:usize=kani::any();kani::assume(i<10);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Checkpoint"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Checkpoint).is_ok());
 assert!(w.seen==10);
 kani::cover!(i==9);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Checkpoint() {
 let i:usize=kani::any();kani::assume(i<19);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Checkpoint"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Checkpoint).is_ok());
 assert!(w.seen==19);
 kani::cover!(i==18);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_debug_Allocation() {
 let i:usize=kani::any();kani::assume(i<10);
 let mut w=NBP_Writer{index:i,seen:0,expected:"Allocation"};
 assert!(write!(&mut w,"{:?}",aspis_r1_cost_probe::verifier::Error::Allocation).is_ok());
 assert!(w.seen==10);
 kani::cover!(i==9);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_message_Allocation() {
 let i:usize=kani::any();kani::assume(i<19);
 let mut w=NBP_Writer{index:i,seen:0,expected:"r1:error:Allocation"};
 assert!(write!(&mut w,"r1:error:{:?}",aspis_r1_cost_probe::verifier::Error::Allocation).is_ok());
 assert!(w.seen==19);
 kani::cover!(i==18);
}
