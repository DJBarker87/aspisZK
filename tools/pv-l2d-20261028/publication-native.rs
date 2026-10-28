fn publication_indices(queries:&[u32;22],begin:usize,end:usize,folded:bool)->Vec<u32> {
    let mut out=Vec::with_capacity(end-begin);
    let mut i=begin;
    while i<end {
        let value=if folded {queries[i]/4} else {queries[i]};
        let mut at=0;
        while at<out.len() && out[at]<value {at+=1;}
        if at==out.len() || out[at]!=value {out.insert(at,value);}
        i+=1;
    }
    out
}

fn obs(tag:u8,b:bool,t:&mut Vec<(u8,usize)>)->bool {t.push((tag,b as usize));b}
fn ix(tag:u8,i:usize,t:&mut Vec<(u8,usize)>)->usize {t.push((tag,i));i}
fn instrumented(queries:&[u32;22],begin:usize,end:usize,folded:bool)->(Vec<u32>,Vec<(u8,usize)>) {
    let mut trace=vec![];let mut out=Vec::with_capacity(end-begin);
    let mut i=begin;
    while obs(0,i<end,&mut trace) {
        let value=if obs(1,folded,&mut trace) {queries[ix(2,i,&mut trace)]/4} else {queries[ix(2,i,&mut trace)]};
        let mut at=0;
        while obs(3,at<out.len(),&mut trace) && obs(4,out[ix(5,at,&mut trace)]<value,&mut trace) {at+=1;}
        if obs(6,at==out.len(),&mut trace) || obs(7,out[ix(8,at,&mut trace)]!=value,&mut trace) {out.insert(ix(9,at,&mut trace),value);}
        i+=1;
    }
    (out,trace)
}
fn check(q:&[u32;22],begin:usize,end:usize,folded:bool)->usize {
 let native=publication_indices(q,begin,end,folded);
 let (value,trace)=instrumented(q,begin,end,folded);assert_eq!(native,value);
 let mut expected:Vec<u32>=q[begin..end].iter().map(|&x|if folded {x/4} else {x}).collect();
 expected.sort();expected.dedup();assert_eq!(native,expected);
 assert!(trace.iter().filter(|(tag,_)|[2,5,8,9].contains(tag)).all(|(_,i)|*i<=22));
 1
}
fn main(){
 let mut checks=0;let mut state=0x5a5a_1234_5678_9abcu64;
 for case in 0..256 {
  let q=std::array::from_fn(|i|match case {
   0=>0,1=>i as u32,2=>(21-i) as u32,3=>(i%4) as u32,
   _=>{state^=state<<13;state^=state>>7;state^=state<<17;(state as u32)&((1<<18)-1)}
  });
  for begin in 0..=22 {for end in begin..=22 {for folded in [false,true] {checks+=check(&q,begin,end,folded);}}}
 }
 let q=std::array::from_fn(|i|i as u32);let reversed=std::array::from_fn(|i|(21-i) as u32);
 assert_eq!(publication_indices(&q,0,22,false),publication_indices(&reversed,0,22,false));
 assert_ne!(instrumented(&q,0,22,false).1,instrumented(&reversed,0,22,false).1);
 println!("{{\"checks\":{},\"same_set_different_control\":true,\"failed\":0}}",checks);
}
