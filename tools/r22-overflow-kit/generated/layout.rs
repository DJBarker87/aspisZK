use crate::multiproof;
mod compact {
pub const MAGIC: &[u8; 8] = b"R1P3CB18";
pub const HEADER: usize = 16;
pub const SPLIT: usize = 10;
pub const QUERIES: usize = 22;
pub const SEMANTIC_ROWS: u8 = 27;
pub const LOGICAL_SEMANTIC: usize = crate::verifier::SEMANTIC_BYTES;
pub const SEMANTIC_COMPACT_VALUES: usize = 1 + 10 * 28 + (87 + 29) + 29;
pub const COMPACT_SEMANTIC: usize = LOGICAL_SEMANTIC - 16 * SEMANTIC_COMPACT_VALUES;
pub const COMPACT_Y1: usize = 29 * 16;
pub const LOGICAL_Y1: usize = 29 * 32;
pub const OPENING: usize = 480 + 128 + 32 + 32 + 128 + 32;
pub const OFF_SEMANTIC: usize = HEADER;
pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;
pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;
pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;
pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;
pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;
pub const OFF_FINAL: usize = OFF_ROUND1 + 224;
pub const FINAL_LEN: usize = 64;
pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;
pub const OFF_NODES: usize = OFF_OPENINGS + QUERIES * OPENING;
pub const FIXED: usize = OFF_NODES;
pub const MAX_NODES: usize = 2 * (146 + 172) + (128 + 150);
pub const MAX_PROOF: usize = FIXED + 32 * MAX_NODES;
pub const SLOT_NODES: [usize; 6] = [146, 146, 128, 172, 172, 150];
pub const PROOF_BYTES: usize = MAX_PROOF;
pub const fn slot_offset(slot: usize) -> usize {
    let mut at = OFF_NODES;
    let mut i = 0;
    while i < slot {
        at += 32 * SLOT_NODES[i];
        i += 1;
    }
    at
}
}
fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}
fn slot(proof: &[u8], s: usize) -> &[u8] {
    &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)]
}
fn batch_keys(queries: &[u32; 22], lo: usize, n: usize, tree: usize) -> [u64; multiproof::MAX_BATCH] {
    let mut keys = [0u64; multiproof::MAX_BATCH];
    for j in 0..n {
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
    }
    keys
}
const OPENING:usize=compact::OPENING;
struct Reader<'a>{bytes:&'a[u8],at:usize}
impl Reader<'_> {
fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
}
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
#[cfg(kani)] #[kani::proof] #[kani::unwind(24)]
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
fn checkpoint_reader_32() {
    let bytes=[0u8;4880];let at:usize=kani::any();kani::assume(at<=4880-32);
    let mut r=Reader{bytes:&bytes,at};let _out=r.raw::<32>();
    assert_eq!(r.at,at+32);
}

#[cfg(kani)]
fn dynamic_reader<const N:usize>() {
    let bytes=[0u8;4880];let len:usize=kani::any();let at:usize=kani::any();
    kani::assume(len<=4880);kani::assume(at<=len);kani::assume(N<=len-at);
    let mut r=Reader{bytes:&bytes[..len],at};let _out=r.raw::<N>();
    assert_eq!(r.at,at+N);assert!(r.at<=len);
}
#[cfg(kani)] #[kani::proof]
fn dynamic_checkpoint_reader4() {dynamic_reader::<4>();}
#[cfg(kani)] #[kani::proof]
fn dynamic_checkpoint_reader16() {dynamic_reader::<16>();}
#[cfg(kani)] #[kani::proof]
fn dynamic_checkpoint_reader32() {dynamic_reader::<32>();}
