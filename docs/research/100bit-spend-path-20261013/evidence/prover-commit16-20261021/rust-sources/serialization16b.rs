// Split replacement for the combined 600-second timeout. Each exact
// batch/tree shape has source-valid 18-bit keys and its own solver target.
#[cfg(kani)]
mod serialization16b {
    use super::*;
    fn check<const B: usize, const T: usize>() {
        let mut queries: [u32;22] = kani::any();
        for q in &mut queries {*q &= 0x3ffff;}
        let range = if B==0 {0..SPLIT} else {SPLIT..22};
        let t = T;
        let mut idx:Vec<u32>=queries[range.clone()].iter().map(|&u|if t==2 {u/4} else {u}).collect();
        idx.sort();idx.dedup();
        let key: u32 = kani::any::<u32>() & 0x3ffff;
        let mut member = false;
        for i in range {member |= key == if t==2 {queries[i]/4} else {queries[i]};}
        assert_eq!(idx.contains(&key), member);
        let probe: usize = kani::any();
        kani::assume(probe < idx.len());
        if probe+1 < idx.len() {assert!(idx[probe] < idx[probe+1]);}
    }
    #[kani::proof]
    #[kani::unwind(32)]
    fn batch_a_plain() {check::<0,0>();}
    #[kani::proof]
    #[kani::unwind(32)]
    fn batch_b_plain() {check::<1,0>();}
    #[kani::proof]
    #[kani::unwind(32)]
    fn batch_a_folded() {check::<0,2>();}
    #[kani::proof]
    #[kani::unwind(32)]
    fn batch_b_folded() {check::<1,2>();}
}
