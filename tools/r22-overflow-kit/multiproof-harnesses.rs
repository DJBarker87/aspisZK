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
