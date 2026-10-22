// Paired exact source cells. The callee contract is relational, not an
// arithmetic axiom. Prove it first, then use only its verified stub.
const P: u32 = 2147483647;
#[kani::requires(ra == rb && wa == wb)]
#[kani::ensures(|out: &((u32,u64),(u32,u64))|
    out.0.0 == out.1.0 && out.0.1 == out.1.1)]
fn paired_cell(ra: u64, wa: u32, rb: u64, wb: u32) -> ((u32,u64),(u32,u64)) {
    let da = (ra << 32) | u64::from(wa);
    let qa = (da / u64::from(P)) as u32;
    let ra = da % u64::from(P);
    let db = (rb << 32) | u64::from(wb);
    let qb = (db / u64::from(P)) as u32;
    let rb = db % u64::from(P);
    ((qa,ra),(qb,rb))
}
#[kani::proof_for_contract(paired_cell)]
fn arithmetic_cell() {
    paired_cell(kani::any(),kani::any(),kani::any(),kani::any());
}
// Product execution: original reverse iterator and reference decrementing
// index take one step each, using the already-verified relational callee.
#[kani::proof]
#[kani::stub_verified(paired_cell)]
#[kani::unwind(10)]
fn limb_induction_step() {
    let words: [u32;8] = kani::any();
    let mut a=words; let mut b=words;
    let mut ra=0u64; let mut rb=0u64; let mut j=8usize;
    for limb in a.iter_mut().rev() {
        j-=1;
        let ((qa,na),(qb,nb))=paired_cell(ra,*limb,rb,b[j]);
        *limb=qa;ra=na;b[j]=qb;rb=nb;
    }
    assert_eq!(j,0);
    assert_eq!(ra,rb);
    for i in 0..8 {assert_eq!(a[i],b[i]);}
}

fn same(a: &[u32;8],b: &[u32;8]) -> bool {
    a[0]==b[0] && a[1]==b[1] && a[2]==b[2] && a[3]==b[3] &&
    a[4]==b[4] && a[5]==b[5] && a[6]==b[6] && a[7]==b[7]
}
#[kani::requires(same(&a,&b))]
#[kani::ensures(|out: &(([u32;8],u32),([u32;8],u32))|
    same(&out.0.0,&out.1.0) && out.0.1==out.1.1)]
fn paired_pass(mut a: [u32;8],mut b: [u32;8]) -> (([u32;8],u32),([u32;8],u32)) {
    let mut ra=0u64;let mut rb=0u64;let mut j=8usize;
    for limb in a.iter_mut().rev() {
        j-=1;
        let ((qa,na),(qb,nb))=paired_cell(ra,*limb,rb,b[j]);
        *limb=qa;ra=na;b[j]=qb;rb=nb;
    }
    ((a,ra as u32),(b,rb as u32))
}
#[kani::proof_for_contract(paired_pass)]
#[kani::stub_verified(paired_cell)]
#[kani::unwind(10)]
fn pass_contract() { paired_pass(kani::any(),kani::any()); }
#[kani::proof]
#[kani::stub_verified(paired_pass)]
#[kani::unwind(10)]
fn digits_composition() {
    let block: [u8;32]=kani::any();
    let mut a: [u32;8]=core::array::from_fn(|i|
        u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()));
    let mut b=[0u32;8];let mut i=0;
    while i<8 {let start=4*i;b[i]=u32::from_le_bytes([
        block[start],block[start+1],block[start+2],block[start+3]]);i+=1;}
    let mut da=[0u32;8];let mut db=[0u32;8];
    for i in 0..8 {
        let ((qa,ra),(qb,rb))=paired_pass(a,b);
        a=qa;b=qb;da[i]=ra;db[i]=rb;
    }
    for i in 0..8 {assert_eq!(da[i],db[i]);assert_eq!(a[i],b[i]);}
}
