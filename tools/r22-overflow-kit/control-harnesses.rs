#[cfg(kani)] #[kani::proof] #[kani::unwind(20)]
fn parent_group_all_frontiers() {
    let mut level:[u32;16]=kani::any();
    let n:usize=kani::any();let i:usize=kani::any();
    kani::assume(n<=16);kani::assume(i<n);
    // Only the live prefix is constrained. Dead suffix entries are arbitrary.
    for k in 0..16 {if k<n {kani::assume(level[k]<(1<<18));if k>0 {kani::assume(level[k-1]<level[k]);}}}
    let arity=if kani::any() {Arity::Two}else{Arity::Eight};
    // Exact frozen node_count inner group (source-pins.json).
    let parent = index_at(&level, i) >> arity.bits();
    let mut j = i;
    while j < n && index_at(&level, j) >> arity.bits() == parent {
        j += 1;
    }
    assert!(i<j && j<=n && j-i<=arity.width());
    let siblings=arity.width()-(j-i);assert!(siblings<=8);
    // Output writes use a separate w<=i invariant, never sorting alone.
    let w:usize=kani::any();kani::assume(w<=i);
    level[w]=parent;let next_w=w+1;
    assert!(next_w<=j && next_w<=16);
}
#[cfg(kani)] #[kani::proof]
fn binary_frontier_step() {
    let i:usize=kani::any();let n:usize=kani::any();let w:usize=kani::any();
    kani::assume(n<=16);kani::assume(i<n);kani::assume(w<=i);
    let paired:bool=kani::any();
    let mut next_i=i;
    if paired && i+1<n {next_i+=2;} else {next_i+=1;}
    let next_w=w+1;
    assert!(next_w<=next_i && next_i<=n && next_w<=16);
    assert!(n-next_i<n-i);
    // Arbitrary digest contents do not occur in these scalar expressions.
}
#[cfg(kani)] #[kani::proof]
fn sibling_cursor_step() {
    let used:usize=kani::any();kani::assume(used<=2304);
    let at=32*used;let end=at+32;assert!(end<=73760);
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(20)]
fn insertion_inner_all_positions() {
    let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();
    let i:usize=kani::any();kani::assume(i<16);
    // Exact frozen sort_dedup inner insertion body (source-pins.json).
    let mut j = i;
    while j > 0 && idx[j - 1] > idx[j] {
        idx.swap(j - 1, j);
        val.swap(j - 1, j);
        j -= 1;
    }
    assert!(j<=i);
}
#[cfg(kani)]
fn dedup_step(idx:&mut[u32;16],val:&mut[[u8;32];16],i:usize,mut w:usize)->Option<usize> {
    // Exact frozen sort_dedup branch, with the enclosing loop split away.
    if idx[i] == idx[w - 1] {
        if val[i] != val[w - 1] {
            return None;
        }
    } else {
        idx[w] = idx[i];
        val[w] = val[i];
        w += 1;
    }
    Some(w)
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(34)]
fn dedup_step_all_positions() {
    let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();
    let i:usize=kani::any();let w:usize=kani::any();
    kani::assume(i<16);kani::assume(w>0 && w<=i);
    if let Some(next)=dedup_step(&mut idx,&mut val,i,w) {assert!(next>0 && next<=i+1 && next<=16);}
}
