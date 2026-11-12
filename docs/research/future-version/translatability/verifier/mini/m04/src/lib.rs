//! Aspis translatability pass, construct probe m04: the lane frontier loop with an error type that owns a string, as
//! the SDK's `ProgramError` does (`BorshIoError(String)`). Stand-in types; none of this is Aspis code.
#![no_std]
extern crate alloc;
use alloc::string::String;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgErr { Custom(u32), InvalidAccountData, BorshIoError(String) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtErr { NonCanonicalDigest }
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct M31(pub u32);
impl M31 { pub const ZERO: M31 = M31(0); }
pub type Digest = [M31; 8];
pub const EMPTY: [Digest; 21] = [[M31(7); 8]; 21];
#[inline(never)]
pub fn decode_digest(b: &[u8; 32]) -> Result<Digest, StmtErr> { if b[3] < 0x80 { Ok([M31(b[0] as u32); 8]) } else { Err(StmtErr::NonCanonicalDigest) } }

/// First batch: flag loop, `match` on the decode with the SDK error, `if` with the table in one branch.
pub fn frontier_first(tree: &[u8], next: u64) -> Result<[Digest; 20], ProgErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_result_plain(tree, level) {
            Ok(node) => {
                if (next >> level) & 1 == 0 && node != EMPTY[level] { ok = false; }
                frontier[level] = node;
            }
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(ProgErr::InvalidAccountData); }
    Ok(frontier)
}
fn node_result_plain(tree: &[u8], level: usize) -> Result<Digest, ProgErr> {
    let start = 48 + 32 * level;
    decode_digest(tree[start..start + 32].try_into().map_err(|_| ProgErr::InvalidAccountData)?).map_err(|_| ProgErr::InvalidAccountData)
}
/// Second form: helper returns `Result<_, ProgErr>` with both checks; `match` in the loop stores or flags.
fn node_result(tree: &[u8], level: usize, next: u64) -> Result<Digest, ProgErr> {
    let start = 48 + 32 * level;
    let node = decode_digest(tree[start..start + 32].try_into().map_err(|_| ProgErr::InvalidAccountData)?).map_err(|_| ProgErr::InvalidAccountData)?;
    if (next >> level) & 1 == 0 {
        if node != EMPTY[level] { Err(ProgErr::InvalidAccountData) } else { Ok(node) }
    } else {
        Ok(node)
    }
}
pub fn frontier_second(tree: &[u8], next: u64) -> Result<[Digest; 20], ProgErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_result(tree, level, next) {
            Ok(node) => frontier[level] = node,
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(ProgErr::InvalidAccountData); }
    Ok(frontier)
}
/// Third form (the candidate): helper returns a flag and the node; the loop body is straight-line.
fn node_flag(tree: &[u8], level: usize, next: u64) -> (bool, Digest) {
    let start = 48 + 32 * level;
    let bytes: [u8; 32] = match tree[start..start + 32].try_into() {
        Ok(bytes) => bytes,
        Err(_) => return (false, [M31::ZERO; 8]),
    };
    match decode_digest(&bytes) {
        Ok(node) => {
            if (next >> (level as u32)) & 1 == 0 {
                if node != EMPTY[level] { (false, node) } else { (true, node) }
            } else {
                (true, node)
            }
        }
        Err(_) => (false, [M31::ZERO; 8]),
    }
}
pub fn frontier_third(tree: &[u8], next: u64, root: Digest) -> Result<[Digest; 20], ProgErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let (acceptable, node) = node_flag(tree, level, next);
        frontier[level] = node;
        ok &= acceptable;
        level += 1;
    }
    if !ok { return Err(ProgErr::InvalidAccountData); }
    if next == 0 && root != EMPTY[20] { return Err(ProgErr::InvalidAccountData); }
    Ok(frontier)
}
/// Third form with the bytes taken by reference from the conversion result.
fn node_flag_ref(tree: &[u8], level: usize, next: u64) -> (bool, Digest) {
    let start = 48 + 32 * level;
    let bytes: &[u8; 32] = match tree[start..start + 32].try_into() {
        Ok(bytes) => bytes,
        Err(_) => return (false, [M31::ZERO; 8]),
    };
    match decode_digest(bytes) {
        Ok(node) => {
            if (next >> (level as u32)) & 1 == 0 {
                if node != EMPTY[level] { (false, node) } else { (true, node) }
            } else {
                (true, node)
            }
        }
        Err(_) => (false, [M31::ZERO; 8]),
    }
}
pub fn frontier_third_ref(tree: &[u8], next: u64) -> Result<[Digest; 20], ProgErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let (acceptable, node) = node_flag_ref(tree, level, next);
        frontier[level] = node;
        ok &= acceptable;
        level += 1;
    }
    if !ok { return Err(ProgErr::InvalidAccountData); }
    Ok(frontier)
}
