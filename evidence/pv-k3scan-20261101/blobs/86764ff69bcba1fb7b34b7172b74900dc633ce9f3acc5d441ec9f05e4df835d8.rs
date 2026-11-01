use aspis_core::field::P;
pub fn actual(word:u32,mut remainder:u64)->(u32,u64) {
 let mut rank=[word];let j=0;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
 (rank[0],remainder)
}
