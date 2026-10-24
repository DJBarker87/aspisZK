#[cfg(kani)]
#[kani::proof]
fn range_loop_contract() {
 let mut count=0usize;
 #[kani::loop_invariant(count==kani::index())]
 for _i in 0usize..6usize {count+=1;}
 assert_eq!(count,6);
}
