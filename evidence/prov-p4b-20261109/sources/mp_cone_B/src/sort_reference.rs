//! Owned atomic insertion state and two row recurrences for the frozen sort.
#[derive(Clone,Copy)]
pub enum InsertStep { Done([u64;16]), Next([u64;16],usize) }
pub fn insert_step(mut keys:[u64;16],at:usize)->InsertStep {
    if at==0 {return InsertStep::Done(keys);}
    let left=keys[at-1];let right=keys[at];
    if left<=right {return InsertStep::Done(keys);}
    keys[at-1]=right;keys[at]=left;
    InsertStep::Next(keys,at-1)
}
pub fn insert_rows(keys:[u64;16],at:usize)->[u64;16] {
    match insert_step(keys,at) {
        InsertStep::Done(done)=>done,
        InsertStep::Next(next,at)=>insert_rows(next,at),
    }
}
pub fn sort_rows(keys:[u64;16],at:usize,n:usize)->[u64;16] {
    if at>=n {return keys;}
    let next=insert_rows(keys,at);
    sort_rows(next,at+1,n)
}
