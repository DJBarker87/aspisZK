pub type Word=[u32;8];
pub type Reply=Result<Word,u8>;
pub struct Replies {pub round0:Reply,pub round1:Reply,pub weights:Result<(),u8>,pub pair:Reply,pub dot:Reply}
pub struct Observed {pub result:Result<(),u8>,pub events:[u8;7],pub len:usize}
fn event(o:&mut Observed,tag:u8){o.events[o.len]=tag;o.len+=1;}
pub fn finish_ref(two:bool,next:usize,rhs:Word,r:Replies)->Observed {
 let mut o=Observed{result:Ok(()),events:[255;7],len:0};
 event(&mut o,0);
 let mut claim=match r.round0 {Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if two {event(&mut o,1);claim=match r.round1 {Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};}
 event(&mut o,2);if let Err(e)=r.weights{o.result=Err(e);return o;}
 event(&mut o,3);let pair=match r.pair{Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if pair!=claim{o.result=Err(3);return o;}
 event(&mut o,4);event(&mut o,5);
 let actual=match r.dot{Ok(x)=>x,Err(e)=>{o.result=Err(e);return o;}};
 if next!=22||actual!=rhs{o.result=Err(5);return o;}
 event(&mut o,6);o
}
