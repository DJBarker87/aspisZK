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

fn sort_iteration(mut keys:[u64;16],mut j:usize)->([u64;16],usize,bool){
 if j > 0 && batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {

            keys.swap(j - 1, j);
            j -= 1;
        
 (keys,j,true)
 }else{(keys,j,false)}
}
