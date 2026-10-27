const STATE_ONLY_POSEIDON_TRACE_ROWS:usize=1024;const STATE_ONLY_HIDING_C1_COLUMNS:usize=16;const MAX_BATCH:usize=16;
mod verifier{#[derive(Debug)]pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    /// Host prover only (LOG D38.3): this attempt's challenges fail the public
    /// P_R1 check. Carries no challenge and no conjunct.
    #[cfg(feature="prover")] Rejected,
    /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
    #[cfg(feature="prover")] AttemptsExhausted,
    /// Host prover only: the operating-system entropy source failed.
    #[cfg(feature="prover")] Entropy }}
fn active_rows(rows: &[u16]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
    let mut i=0;
    while i<rows.len() {active[usize::from(rows[i])]=true;i+=1;}
    active
}
fn source_active_flags(masks:&[u16;64])->[bool;STATE_ONLY_POSEIDON_TRACE_ROWS] {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    let mut active=[false;STATE_ONLY_POSEIDON_TRACE_ROWS];let mut row=0;
    while row<rows {
        active[row]=masks[row>>4]&(1<<(row&15))!=0;row+=1;
    }
    active
}
fn mask_dependent_step(mut dependents:[Option<usize>;STATE_ONLY_HIDING_C1_COLUMNS],column:usize,row:usize,active:bool)->[Option<usize>;STATE_ONLY_HIDING_C1_COLUMNS] {
    if !active {dependents[column]=Some(row);}
    dependents
}
fn count_level(mut level:[u32;MAX_BATCH],n:usize)->([u32;MAX_BATCH],usize,usize) {
    let mut i=0;let mut w=0;let mut missing=0;
    while i<n {
        let (parent,take)=count_parent(&level,i,n);
        level[w]=parent;w+=1;i+=take;missing+=2-take;
    }
    (level,w,missing)
}
fn count_parent(level:&[u32;MAX_BATCH],i:usize,n:usize)->(u32,usize) {
    let parent=level[i]>>1;
    let take=if i+1<n && level[i+1]>>1==parent {2} else {1};
    (parent,take)
}
fn query_contains(accepted:&[u32;22],n:usize,candidate:u32)->bool {
    let mut i=0;
    while i<n {if accepted[i]==candidate {return true;} i+=1;}
    false
}
fn scan_query_words(blocks:&[[u8;32];8],advances:&[[u8;32];8],mut accepted:[u32;22],n:usize,draws:usize)->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    if draws==64 {
        return if n==22 {Ok((accepted,advances[7]))} else {Err(crate::verifier::Error::Transcript)};
    }
    let k=draws/8;
    if n==22 {return Ok((accepted,advances[k]));}
    let at=4*(draws%8);
    let candidate=u32::from_le_bytes([blocks[k][at],blocks[k][at+1],blocks[k][at+2],blocks[k][at+3]])&0x3ffff;
    if query_contains(&accepted,n,candidate) {
        scan_query_words(blocks,advances,accepted,n,draws+1)
    } else {
        accepted[n]=candidate;
        scan_query_words(blocks,advances,accepted,n+1,draws+1)
    }
}
fn main(){println!("active {:?}",&active_rows(&[1,3,7])[..8]);println!("flags {:?}",&source_active_flags(&[1;64])[..32]);println!("dependent {:?}",mask_dependent_step([None;16],3,7,false)[3]);let mut a=[0;16];a[..3].copy_from_slice(&[1,2,3]);println!("count {:?}",count_level(a,3));let mut b=[0;32];b[0]=2;println!("scan {:?}",scan_query_words(&[b;8],&[[7;32];8],[1;22],21,0).unwrap());}
