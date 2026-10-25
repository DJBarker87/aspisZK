// Proof-local source slice from multiproof.rs. No crate/program is edited.
// generate's control is retained; only event pushes and a trace argument are
// inserted. Std internal comparison/allocation costs remain OPEN.
#[derive(Clone, Copy)] enum Arity { Two }
impl Arity {
    fn bits(self)->u32 { 1 }
    fn width(self)->usize { 2 }
    fn levels(self)->u32 { 18 }
}
const LEAF_BITS:u32=18;
const MAX_BATCH:usize=16;
fn well_formed(indices:&[u32])->bool {
    !indices.is_empty() && indices.len() <= MAX_BATCH
    && indices.windows(2).all(|w| w[0] < w[1])
    && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}
fn index_at(indices:&[u32;MAX_BATCH],index:usize)->u32 { indices[index] }
fn node_count(arity:Arity,indices:&[u32])->Option<usize> {
    if !well_formed(indices) { return None; }
    let mut level=[0u32;MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n=indices.len(); let mut count=0;
    for _ in 0..arity.levels() {
        let mut w=0; let mut i=0;
        while i<n {
            let parent=index_at(&level,i)>>arity.bits();
            let mut j=i;
            while j<n && index_at(&level,j)>>arity.bits()==parent { j+=1; }
            count+=arity.width()-(j-i);level[w]=parent;w+=1;i=j;
        }
        n=w;
    }
    Some(count)
}
#[derive(Debug, PartialEq, Eq)]
enum Event { Allocate(usize), Level(u32), Visit(usize), Slot(u32),
    Occupied(bool), Read(u32,u32), Extend(usize,usize), Push(usize,usize), Done(bool) }
fn generate(arity:Arity,indices:&[u32],mut node:impl FnMut(u32,u32)->[u8;32],trace:&mut Vec<Event>)->Option<Vec<u8>> {
    let count=node_count(arity,indices)?;
    trace.push(Event::Allocate(32*count));
    let mut out=Vec::with_capacity(32*count);
    trace.push(Event::Allocate(indices.len()));
    let mut level:Vec<u32>=indices.to_vec();
    for depth in 0..arity.levels() {
        trace.push(Event::Level(depth));
        let mut next=Vec::new();
        let mut i=0;
        while i<level.len() {
            trace.push(Event::Visit(i));
            let parent=level[i]>>arity.bits();
            for slot in 0..arity.width() as u32 {
                trace.push(Event::Slot(slot));
                let child=(parent<<arity.bits())|slot;
                trace.push(Event::Occupied(i<level.len() && level[i]==child));
                if i<level.len() && level[i]==child { i+=1; }
                else {
                    trace.push(Event::Read(depth,child));
                    out.extend_from_slice(&node(depth,child));
                    trace.push(Event::Extend(out.len(),out.capacity()));
                }
            }
            next.push(parent);
            trace.push(Event::Push(next.len(),next.capacity()));
        }
        level=next;
    }
    trace.push(Event::Done(out.len()==32*count));
    (out.len()==32*count).then_some(out)
}
#[kani::proof]
#[kani::unwind(20)]
fn L2Leaf_multiproof_payload_two_run() {
    // Two arbitrary distinct sorted leaves, all 18 levels, independent node
    // payloads. This does not claim the 16-leaf bound or std internal costs.
    let mut indices:[u32;2]=kani::any();
    kani::assume(indices[0] < indices[1]);
    kani::assume(indices[1] < (1<<18));
    let witness_left:[u8;32]=kani::any();
    let witness_right:[u8;32]=kani::any();
    let mut a=Vec::new(); let mut b=Vec::new();
    let x=generate(Arity::Two,&indices,|_,_| witness_left,&mut a);
    let y=generate(Arity::Two,&indices,|_,_| witness_right,&mut b);
    assert_eq!(a,b);
    assert_eq!(x.as_ref().map(Vec::len),y.as_ref().map(Vec::len));
}
