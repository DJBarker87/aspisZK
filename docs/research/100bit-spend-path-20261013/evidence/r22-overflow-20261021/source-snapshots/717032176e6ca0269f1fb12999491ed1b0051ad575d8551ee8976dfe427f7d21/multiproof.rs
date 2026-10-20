pub const MAX_BATCH:usize=16; const LEAF_BITS:u32=18;
#[derive(Clone,Copy)] enum Arity {Two,Eight}
impl Arity {
pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }
pub const fn width(self) -> usize {
        1 << self.bits()
    }
pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}
fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}
fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}
pub fn node_count(arity: Arity, indices: &[u32]) -> Option<usize> {
    if !well_formed(indices) {
        return None;
    }
    let mut level = [0u32; MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
            count += arity.width() - (j - i);
            level[w] = parent;
            w += 1;
            i = j;
        }
        n = w;
    }
    Some(count)
}
pub fn sort_dedup(idx: &mut [u32], val: &mut [[u8; 32]]) -> Option<usize> {
    let n = idx.len();
    if n != val.len() || n == 0 || n > MAX_BATCH {
        return None;
    }
    // Insertion sort: n <= 16.
    for i in 1..n {
        let mut j = i;
        while j > 0 && idx[j - 1] > idx[j] {
            idx.swap(j - 1, j);
            val.swap(j - 1, j);
            j -= 1;
        }
    }
    let mut w = 1;
    for i in 1..n {
        if idx[i] == idx[w - 1] {
            if val[i] != val[w - 1] {
                return None;
            }
        } else {
            idx[w] = idx[i];
            val[w] = val[i];
            w += 1;
        }
    }
    Some(w)
}
// Selected exact frozen functions. These harnesses assert arithmetic/ranges,
// not hash correctness, and do not involve a digest backend.
#[cfg(kani)]
fn sorted_indices<const N:usize>()->[u32;N] {
    let a:[u32;N]=kani::any();
    for i in 0..N {kani::assume(a[i]<(1<<18));if i>0 {kani::assume(a[i-1]<a[i]);}}
    a
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(20)]
fn node_count_single() {
    let a=sorted_indices::<1>();
    assert_eq!(node_count(Arity::Two,&a),Some(18));
    assert_eq!(node_count(Arity::Eight,&a),Some(42));
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(20)]
fn node_count_pair() {
    let a=sorted_indices::<2>();
    assert!(node_count(Arity::Two,&a).unwrap()<=36);
    assert!(node_count(Arity::Eight,&a).unwrap()<=84);
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(18)]
fn sort_dedup_four() {
    let mut a:[u32;4]=kani::any();let mut values=[[0;32];4];
    let n=sort_dedup(&mut a,&mut values).unwrap();
    assert!(n>0 && n<=4);
    for i in 1..n {assert!(a[i-1]<a[i]);}
}

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
