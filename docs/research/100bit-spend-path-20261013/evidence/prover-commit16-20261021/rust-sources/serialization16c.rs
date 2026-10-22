// Ordered slicing and tree-key projection cut, before std sort/dedup.
#[cfg(kani)]
mod serialization16c {
    use super::*;
    #[kani::proof]
    #[kani::unwind(32)]
    fn ordered_projection() {
        let queries: [u32;22] = kani::any();
        let batch: usize = kani::any();
        let t: usize = kani::any();
        kani::assume(batch < 2 && t < 3);
        let range = if batch==0 {0..SPLIT} else {SPLIT..22};
        let idx:Vec<u32>=queries[range.clone()].iter().map(|&u|if t==2 {u/4} else {u}).collect();
        assert_eq!(idx.len(), if batch==0 {10} else {12});
        let ordinal: usize = kani::any();
        kani::assume(ordinal < idx.len());
        let u = queries[range.start+ordinal];
        assert_eq!(idx[ordinal], if t==2 {u/4} else {u});
    }
}
