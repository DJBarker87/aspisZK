const P:u32=2147483647;
#[derive(Clone,Copy)] struct M31(pub u32);
#[derive(Clone,Copy)] struct CM31 { a:M31,b:M31 }
#[derive(Clone,Copy)] struct QM31 { c0:CM31,c1:CM31 }
impl M31 {    pub fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }}
impl CM31 {    pub fn write_le_bytes(self, out: &mut [u8]) {
        out[0..4].copy_from_slice(&self.a.to_le_bytes());
        out[4..8].copy_from_slice(&self.b.to_le_bytes());
    }}
impl QM31 {    pub fn write_le_bytes(self, out: &mut [u8]) {
        self.c0.write_le_bytes(&mut out[0..8]);
        self.c1.write_le_bytes(&mut out[8..16]);
    }}
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
fn qm31_digits(block: &[u8; 32]) -> [u32; 4] {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }
    let mut digits = [0u32; 4];
    let mut i = 0usize;
    while i < 4 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    digits
}
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut quotient: [u32; 8] =
        core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let digits = core::array::from_fn(|_| {
        let mut remainder = 0u64;
        for limb in quotient.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        remainder as u32
    });

    // After eight divisions, the quotient is at most 256 and fits in u32.
    debug_assert!(quotient[1..].iter().all(|&limb| limb == 0));
    debug_assert!(quotient[0] <= 256);
    (digits, quotient[0])
}
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
    }
    debug_assert!(addend <= 1);
    addend != 0
}
fn main() {
 let q=QM31{c0:CM31{a:M31(1),b:M31(2)},c1:CM31{a:M31(3),b:M31(4)}};
 let mut out=[255;20];q.write_le_bytes(&mut out);println!("op72 {:?}",out);
 for (label,n) in [("zero",0u32),("P",P),("P+1",P+1)] {
  let mut b=[0u8;32];b[..4].copy_from_slice(&n.to_le_bytes());
  println!("low {label} {:?}",low_base_p_digits(&b));
  println!("qm31 {label} {:?}",qm31_digits(&b));
 }
 println!("low ff {:?}",low_base_p_digits(&[255;32]));
 println!("qm31 ff {:?}",qm31_digits(&[255;32]));
 let mut d=[P-1;8];println!("add carry {:?}",(add_small_base_p(&mut d,1),d));
 let mut d=[0;8];println!("add one {:?}",(add_small_base_p(&mut d,1),d));
}
