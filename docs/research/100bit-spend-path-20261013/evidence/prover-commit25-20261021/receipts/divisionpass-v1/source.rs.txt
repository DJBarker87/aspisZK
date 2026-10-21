const P: u32 = 2147483647;
fn iterator_pass(mut quotient: [u32;8]) -> ([u32;8],u32) {
        let mut remainder = 0u64;
        for limb in quotient.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
    (quotient,remainder as u32)
}
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}
#[kani::proof]
#[kani::unwind(10)]
fn pass_iterator_equals_indexed() {
 let words: [u32;8] = kani::any();
 let (a,ra) = iterator_pass(words);
 let (b,rb) = qm31_div_pass(words);
 assert_eq!(ra,rb);
 for i in 0..8 { assert_eq!(a[i],b[i]); }
}
