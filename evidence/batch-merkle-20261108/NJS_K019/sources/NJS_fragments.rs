// Mechanically selected frozen candidate.rs loop94..98 body; wrapper only exposes the pre-state.
fn key_iteration(queries:&[u32;22],lo:usize,n:usize,tree:usize,mut keys:[u64;16],start:usize)->([u64;16],usize,bool){
 let mut iter=start..n;let next=iter.next();
 if let Some(j)=next {

        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
    
 (keys,iter.start,true)
 }else{(keys,iter.start,false)}
}
