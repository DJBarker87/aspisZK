//! Finite native validation of the concrete equality dictionary, not a proof.
use aspis_r1_cost_probe::r1_wire::Error;
fn reference(a:Error,b:Error)->bool{
 match (a,b) {
 (Error::Allocation,Error::Allocation)|(Error::InvalidRow,Error::InvalidRow)|
 (Error::Terminal,Error::Terminal)|(Error::EqualCirclePoints,Error::EqualCirclePoints)|
 (Error::TrailingBytes,Error::TrailingBytes)|(Error::Public,Error::Public)|
 (Error::ActivePole,Error::ActivePole)=>true,
 (Error::RowOrder{expected:a,actual:b},Error::RowOrder{expected:c,actual:d})=>a==c&&b==d,
 (Error::Tag{row:a},Error::Tag{row:b})|(Error::Length{row:a},Error::Length{row:b})=>a==b,
 (Error::NonCanonical{row:a,value:b},Error::NonCanonical{row:c,value:d})=>a==c&&b==d,
 (Error::Boundary{round:a},Error::Boundary{round:b})=>a==b,
 _=>false,
 }
}
fn main(){
 let mut v=vec![Error::Allocation,Error::InvalidRow,Error::Terminal,Error::EqualCirclePoints,Error::TrailingBytes,Error::Public,Error::ActivePole];
 for b in [0u8,1,127,255] {
  v.push(Error::Tag{row:b});v.push(Error::Length{row:b});
  for c in [0u8,1,127,255] {v.push(Error::RowOrder{expected:b,actual:c});}
  for n in [0usize,1,usize::MAX/2,usize::MAX] {v.push(Error::NonCanonical{row:b,value:n});}
 }
 for n in [0usize,1,usize::MAX/2,usize::MAX] {v.push(Error::Boundary{round:n});}
 let mut n=0;
 for &a in &v {for &b in &v {assert_eq!(a==b,reference(a,b));n+=1;}}
 assert_eq!(Error::ActivePole,Error::ActivePole);
 println!("{{\"comparisons\":{n},\"inputs\":{}}}",v.len());
}
