#[cfg(kani)] #[kani::proof] #[kani::unwind(8)]
fn all_compact_slots() {
    let s:usize=kani::any();kani::assume(s<6);
    let begin=compact::slot_offset(s);let end=compact::slot_offset(s+1);
    assert!(begin<end && end<=compact::PROOF_BYTES);
    let proof=[0u8;compact::PROOF_BYTES];assert_eq!(slot(&proof,s).len(),end-begin);
}
#[cfg(kani)] #[kani::proof]
fn all_compact_openings() {
    let i:usize=kani::any();kani::assume(i<22);
    let proof=[0u8;compact::PROOF_BYTES];assert_eq!(opening(&proof,i).len(),OPENING);
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(20)]
fn batch_key_ranges() {
    let q:[u32;22]=kani::any();
    for i in 0..22 {kani::assume(q[i]<(1<<18));}
    let lo:usize=kani::any();let n:usize=kani::any();let tree:usize=kani::any();
    kani::assume(lo<=22 && n<=16);kani::assume(lo+n<=22);
    let keys=batch_keys(&q,lo,n,tree);
    for j in 0..n {assert!(keys[j]<(1<<26));assert_eq!(keys[j]&255,j as u64);}
}
#[cfg(kani)]
fn reader_case<const N:usize>() {
    let bytes=[0u8;4880];let at:usize=kani::any();kani::assume(at<=4880-N);
    let mut r=Reader{bytes:&bytes,at};let out=r.raw::<N>();
    assert_eq!(r.at,at+N);assert_eq!(out,[0;N]);
}
#[cfg(kani)] #[kani::proof]
fn checkpoint_reader_4() {reader_case::<4>();}
#[cfg(kani)] #[kani::proof]
fn checkpoint_reader_16() {reader_case::<16>();}
#[cfg(kani)] #[kani::proof]
fn checkpoint_reader_32() {reader_case::<32>();}
