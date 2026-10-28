#[derive(Debug, PartialEq)] enum Error { WrongField }
fn validate_zero_tail(limbs:&[u32;8],mut i:usize)->Result<(),Error> {
    while i<8 {if limbs[i]!=0 {return Err(Error::WrongField);}i+=1;}
    Ok(())
}
#[derive(Debug,PartialEq)] enum Event { Loop(usize,bool), Read(usize), Zero(usize,bool) }
fn instrumented(limbs:&[u32;8],mut i:usize)->(Result<(),Error>,Vec<Event>) {
 let mut t=Vec::new();
 loop {
  t.push(Event::Loop(i,i<8));
  if i>=8 {return (Ok(()),t);}
  t.push(Event::Read(i));t.push(Event::Zero(i,limbs[i]==0));
  if limbs[i]!=0 {return (Err(Error::WrongField),t);}
  i+=1;
 }
}
fn reference(i:usize,xs:&[u32])->(Result<(),Error>,Vec<Event>) {
 match xs.split_first() {
  None=>(Ok(()),vec![Event::Loop(i,false)]),
  Some((&x,rest))=>{
   let mut t=vec![Event::Loop(i,true),Event::Read(i),Event::Zero(i,x==0)];
   if x!=0 {(Err(Error::WrongField),t)} else {
    let (out,trace)=reference(i+1,rest);t.extend(trace);(out,t)
   }
  }
 }
}
fn check(a:[u32;8],first:usize)->usize {
 let native=validate_zero_tail(&a,first);let (out,trace)=instrumented(&a,first);
 assert_eq!(native,out);assert_eq!((out,trace),reference(first,&a[first..]));1
}
fn main(){
 let mut checks=0;
 for mask in 0..256 {
  for x in [1,2,0x7fff_ffff,0xffff_ffff] {
   let a=std::array::from_fn(|i|if mask&(1<<i)!=0 {x} else {0});
   for first in 0..=8 {checks+=check(a,first);}
  }
 }
 let mut state=0x9234_5678_9abc_def0u64;
 for _ in 0..10000 {
  let a=std::array::from_fn(|_| {state^=state<<13;state^=state>>7;state^=state<<17;state as u32});
  for first in [1,4] {checks+=check(a,first);}
 }
 // Nonvacuity: arbitrary in-field limbs pass, first excluded nonzero fails.
 assert_eq!(validate_zero_tail(&[17,0,0,0,0,0,0,0],1),Ok(()));
 assert_eq!(validate_zero_tail(&[19,0,0,0,0,0,0,0],1),Ok(()));
 assert_eq!(validate_zero_tail(&[0,1,0,0,0,0,0,0],1),Err(Error::WrongField));
 println!("{{\"checks\":{},\"failed\":0}}",checks);
}
