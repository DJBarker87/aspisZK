const MAX_BATCH:usize=16; const LEAF_BITS:u32=18;
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
