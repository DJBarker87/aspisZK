//! Aspis translatability pass, construct probe m03: the final candidate shapes (scan with the slots written out and the
//! limb loop in its own helper; the lane frontier with a `const` table as in the source; the seven-account
//! comparison; the mutable-array conversion by `match`). Stand-in types; none of this is Aspis code.
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error { Parse, Allocation }
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PErr { InvalidArgument, InvalidAccountData }
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct M31(pub u32);
pub const P: u32 = 0x7fff_ffff;
impl M31 {
    pub const ZERO: M31 = M31(0);
    #[inline(always)]
    pub fn from_le_bytes(b: [u8; 4]) -> Option<M31> { let x = u32::from_le_bytes(b); if x < P { Some(M31(x)) } else { None } }
}
#[derive(Clone, Copy)]
pub struct K(pub [u32; 4]);
impl K {
    #[inline(never)]
    pub fn from_le_bytes(b: &[u8]) -> Option<K> { if b.len() == 16 && b[3] < 0x80 { Some(K([b[0] as u32; 4])) } else { None } }
}
#[inline(never)]
pub fn echeck(b: &[u8], k: bool) -> Result<(), Error> { if b.len() % 32 == 0 && !k { Ok(()) } else { Err(Error::Parse) } }
pub const OPENING: usize = 832;
#[inline(always)]
fn opening(proof: &[u8], i: usize) -> &[u8] { let at = 64 + i * OPENING; &proof[at..at + OPENING] }

// ---- canonical_scan, form `unrolled2` ----
fn scan_slot_base(q: &[u8], s: usize) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    Ok(())
}
fn scan_slot(q: &[u8], s: usize) -> Result<(), Error> {
    scan_slot_base(q, s)?;
    K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]).ok_or(Error::Parse)?;
    Ok(())
}
fn scan_opening(q: &[u8]) -> Result<(), Error> {
    scan_slot(q, 0)?;
    scan_slot(q, 1)?;
    scan_slot(q, 2)?;
    scan_slot(q, 3)?;
    echeck(&q[672..800], false)
}
pub fn canonical_scan(proof: &[u8]) -> Result<(), Error> {
    echeck(&proof[0..32], false)?;
    echeck(&proof[32..64], false)?;
    for i in 0..22 {
        scan_opening(opening(proof, i))?;
    }
    Ok(())
}

// ---- the lane frontier, with the table as a `const` (as in the source) ----
pub type Digest = [M31; 8];
pub const EMPTY: [Digest; 21] = [[M31(7); 8]; 21];
#[inline(never)]
pub fn decode_digest(b: &[u8; 32]) -> Result<Digest, Error> { if b[3] < 0x80 { Ok([M31(b[0] as u32); 8]) } else { Err(Error::Parse) } }
/// The first batch's loop (the tools rejected the real one at the `if`).
pub fn frontier_first(tree: &[u8], next: u64, root: Digest) -> Result<[Digest; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let start = 48 + 32 * level;
        match decode_digest(tree[start..start + 32].try_into().map_err(|_| PErr::InvalidAccountData)?) {
            Ok(node) => {
                if (next >> level) & 1 == 0 && node != EMPTY[level] { ok = false; }
                frontier[level] = node;
            }
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    if next == 0 && root != EMPTY[20] { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// One node, both checks, every branch ends the function (the candidate).
fn node_all_tails(tree: &[u8], level: usize, next: u64) -> Result<Digest, PErr> {
    let start = 48 + 32 * level;
    let node = decode_digest(tree[start..start + 32].try_into().map_err(|_| PErr::InvalidAccountData)?).map_err(|_| PErr::InvalidAccountData)?;
    if (next >> level) & 1 == 0 {
        if node != EMPTY[level] { Err(PErr::InvalidAccountData) } else { Ok(node) }
    } else {
        Ok(node)
    }
}
/// The candidate loop followed by the pinned root line (an `&&` with the table on its right, then more code).
pub fn frontier_candidate(tree: &[u8], next: u64, root: Digest) -> Result<[Digest; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_all_tails(tree, level, next) {
            Ok(node) => frontier[level] = node,
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    if next == 0 && root != EMPTY[20] { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// The candidate loop alone (no root line after it).
pub fn frontier_candidate_loop_only(tree: &[u8], next: u64) -> Result<[Digest; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_all_tails(tree, level, next) {
            Ok(node) => frontier[level] = node,
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// The pinned root line alone, with code after it.
pub fn root_line_pinned(next: u64, root: Digest, x: u32) -> Result<u32, PErr> {
    if next == 0 && root != EMPTY[20] { return Err(PErr::InvalidAccountData); }
    Ok(x.wrapping_add(1))
}
/// The comparison with the table made on every level, before the test of the index bit.
pub fn frontier_always(tree: &[u8], next: u64) -> Result<[Digest; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let start = 48 + 32 * level;
        match decode_digest(tree[start..start + 32].try_into().map_err(|_| PErr::InvalidAccountData)?) {
            Ok(node) => {
                let empty = node == EMPTY[level];
                if (next >> level) & 1 == 0 && !empty { ok = false; }
                frontier[level] = node;
            }
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}

// ---- the seven-account comparison ----
pub struct Acc { pub key: [u8; 32] }
impl Acc { fn key(&self) -> &[u8; 32] { &self.key } }
pub fn distinct_seven(a: &[&Acc; 7]) -> Result<(), PErr> {
    if a[0].key() == a[1].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[2].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[2].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[3].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[3].key() { return Err(PErr::InvalidArgument); }
    if a[2].key() == a[3].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[4].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[4].key() { return Err(PErr::InvalidArgument); }
    if a[2].key() == a[4].key() { return Err(PErr::InvalidArgument); }
    if a[3].key() == a[4].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[5].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[5].key() { return Err(PErr::InvalidArgument); }
    if a[2].key() == a[5].key() { return Err(PErr::InvalidArgument); }
    if a[3].key() == a[5].key() { return Err(PErr::InvalidArgument); }
    if a[4].key() == a[5].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    if a[2].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    if a[3].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    if a[4].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    if a[5].key() == a[6].key() { return Err(PErr::InvalidArgument); }
    Ok(())
}
pub fn distinct_caller(x: &[Acc]) -> Result<u8, PErr> {
    if x.len() != 7 { return Err(PErr::InvalidArgument); }
    let a = &x[0]; let b = &x[1]; let c = &x[2]; let d = &x[3]; let e = &x[4]; let f = &x[5]; let g = &x[6];
    distinct_seven(&[a, b, c, d, e, f, g])?;
    Ok(a.key()[0])
}

// ---- the mutable slice to mutable array reference ----
#[inline(never)]
fn accumulate(acc: &mut [u64; 16], x: &[u8]) -> Result<(), Error> { acc[0] = acc[0].wrapping_add(x.len() as u64); Ok(()) }
fn filled(n: usize, v: u64) -> Result<Vec<u64>, Error> { let mut out = Vec::new(); out.resize(n, v); Ok(out) }
/// Through `map_err` and `?` (translates, the emitted Lean does not elaborate).
pub fn lanes_map_err(x: &[u8]) -> Result<u64, Error> {
    let mut acc = filled(16, 0u64).map_err(|_| Error::Allocation)?;
    {
        let acc: &mut [u64; 16] = (&mut acc[..]).try_into().map_err(|_| Error::Allocation)?;
        accumulate(acc, x)?;
    }
    Ok(acc[0])
}
/// Through a `match` (the candidate).
pub fn lanes_match(x: &[u8]) -> Result<u64, Error> {
    let mut acc = filled(16, 0u64).map_err(|_| Error::Allocation)?;
    {
        let acc: &mut [u64; 16] = match (&mut acc[..]).try_into() {
            Ok(array) => array,
            Err(_) => return Err(Error::Allocation),
        };
        accumulate(acc, x)?;
    }
    Ok(acc[0])
}
