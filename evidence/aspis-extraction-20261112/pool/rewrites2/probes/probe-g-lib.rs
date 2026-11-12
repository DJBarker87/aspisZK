//! X2b reproducers, probe g: optional account references (trigger isolation) and class g shapes.
#![no_std]
extern crate alloc;
use alloc::{boxed::Box, vec::Vec};
use core::convert::TryInto;
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

/// H1: Option<&AccountInfo> parameter, match, read key.
pub fn h1(c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> { match c { Some(c) => Ok(*c.key), None => Err(ProgramError::NotEnoughAccountKeys) } }
/// H2: as H1, read owner.
pub fn h2(c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> { match c { Some(c) => Ok(*c.owner), None => Err(ProgramError::NotEnoughAccountKeys) } }
/// H3: as H1, read a bool field.
pub fn h3(c: Option<&AccountInfo<'_>>) -> Result<bool, ProgramError> { match c { Some(c) => Ok(c.is_signer), None => Err(ProgramError::NotEnoughAccountKeys) } }
/// H4: two account references and the option, value comparisons (c5 without the early return).
pub fn h4(v: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<bool, ProgramError> { match c { Some(c) => Ok(*c.owner == *v.key), None => Err(ProgramError::NotEnoughAccountKeys) } }
/// H5: as H4 with an early return.
pub fn h5(v: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> {
    let c = match c { Some(c) => c, None => return Err(ProgramError::NotEnoughAccountKeys) };
    if *c.owner != *v.key { return Err(ProgramError::InvalidArgument); }
    Ok(*v.key)
}
/// H6: index instead of the option (accounts + Option<usize>).
pub fn h6(v: &AccountInfo<'_>, accounts: &[AccountInfo<'_>], c: Option<usize>) -> Result<Pubkey, ProgramError> {
    let i = match c { Some(i) => i, None => return Err(ProgramError::NotEnoughAccountKeys) };
    let c = &accounts[i];
    if *c.owner != *v.key || c.is_signer { return Err(ProgramError::InvalidArgument); }
    Ok(*v.key)
}
/// H7: the option built from an index by a closure (frozen terminal shape) and passed on.
pub fn h7(accounts: &[AccountInfo<'_>], idx: Option<usize>) -> Result<Pubkey, ProgramError> { h1(idx.map(|i| &accounts[i])) }
/// H8: the option built by an explicit match.
pub fn h8(accounts: &[AccountInfo<'_>], idx: Option<usize>) -> Result<Pubkey, ProgramError> {
    let c = match idx { Some(i) => Some(&accounts[i]), None => None }; h1(c)
}

/// G1 (require_alias_free frozen shape): loop with any() over previous accounts.
pub fn g1(m: &AccountInfo<'_>, lanes: &[AccountInfo<'_>], c: &AccountInfo<'_>) -> Result<(), ProgramError> {
    if m.key == c.key { return Err(ProgramError::InvalidArgument); }
    for (i, l) in lanes.iter().enumerate() {
        if l.key == m.key || l.key == c.key || lanes[..i].iter().any(|p| p.key == l.key) { return Err(ProgramError::InvalidArgument); }
    }
    Ok(())
}
const LANES: usize = 8;
fn alias_scan(m: &Pubkey, lanes: &[Pubkey; LANES], count: usize, c: &Pubkey) -> bool {
    let mut alias = *m == *c;
    let mut i = 0;
    while !alias && i < count {
        alias = lanes[i] == *m || lanes[i] == *c;
        let mut p = 0;
        while !alias && p < i { alias = lanes[p] == lanes[i]; p += 1; }
        i += 1;
    }
    alias
}
/// G2: keys copied out by indexing (written out), the scan over plain keys.
pub fn g2(m: &AccountInfo<'_>, lanes: &[AccountInfo<'_>], c: &AccountInfo<'_>) -> Result<(), ProgramError> {
    let count = lanes.len();
    if count > LANES { return Err(ProgramError::InvalidArgument); }
    let mut keys = [Pubkey::new_from_array([0u8; 32]); LANES];
    if count > 0 { keys[0] = *lanes[0].key; }
    if count > 1 { keys[1] = *lanes[1].key; }
    if count > 2 { keys[2] = *lanes[2].key; }
    if count > 3 { keys[3] = *lanes[3].key; }
    if count > 4 { keys[4] = *lanes[4].key; }
    if count > 5 { keys[5] = *lanes[5].key; }
    if count > 6 { keys[6] = *lanes[6].key; }
    if count > 7 { keys[7] = *lanes[7].key; }
    if alias_scan(m.key, &keys, count, c.key) { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
/// G3 (encode_lane frozen shape): early return inside a loop over plain data.
pub fn g3(next: u64, f: &[[u32; 8]; 20], e: &[[u32; 8]; 21]) -> Result<u8, ProgramError> {
    for (level, node) in f.iter().enumerate() { if (next >> level) & 1 == 0 && *node != e[level] { return Err(ProgramError::InvalidAccountData); } }
    Ok(1)
}
/// G4: while loop with a flag, error after the loop.
pub fn g4(next: u64, f: &[[u32; 8]; 20], e: &[[u32; 8]; 21]) -> Result<u8, ProgramError> {
    let mut ok = true; let mut level = 0;
    while ok && level < 20 { ok = (next >> level) & 1 != 0 || f[level] == e[level]; level += 1; }
    if !ok { return Err(ProgramError::InvalidAccountData); }
    Ok(1)
}
#[derive(Clone, Copy)]
pub struct St { pub a: [u32; 8], pub n: u64 }
fn dec(acc: &AccountInfo<'_>, i: u8) -> Result<St, ProgramError> {
    let d = match acc.try_borrow_data() { Ok(d) => d, Err(e) => return Err(e) };
    if d.len() < 8 { return Err(ProgramError::InvalidAccountData); }
    Ok(St { a: [i as u32; 8], n: d[0] as u64 })
}
/// G5 (decode_checkpoint_lanes_box frozen shape): loop with ? pushing into a Vec, then a boxed array.
pub fn g5(accs: &[AccountInfo<'_>]) -> Result<Box<[St; 4]>, ProgramError> {
    let mut v = Vec::with_capacity(4);
    for i in 0..4 { v.push(dec(&accs[i], i as u8)?); }
    v.into_boxed_slice().try_into().map_err(|_| ProgramError::InvalidAccountData)
}
/// G6: the pushes written out with explicit matches.
pub fn g6(accs: &[AccountInfo<'_>]) -> Result<Box<[St; 4]>, ProgramError> {
    let mut v = Vec::with_capacity(4);
    match dec(&accs[0], 0) { Ok(s) => v.push(s), Err(e) => return Err(e) }
    match dec(&accs[1], 1) { Ok(s) => v.push(s), Err(e) => return Err(e) }
    match dec(&accs[2], 2) { Ok(s) => v.push(s), Err(e) => return Err(e) }
    match dec(&accs[3], 3) { Ok(s) => v.push(s), Err(e) => return Err(e) }
    match v.into_boxed_slice().try_into() { Ok(b) => Ok(b), Err(_) => Err(ProgramError::InvalidAccountData) }
}
/// G7: closure inside a function holding accounts (require_checkpoint_distinct shape) vs plain keys.
pub fn g7(c: &AccountInfo<'_>, reg: &[AccountInfo<'_>]) -> bool { reg.iter().any(|a| a.key == c.key) }
pub fn g8(c: &AccountInfo<'_>, reg: &[AccountInfo<'_>]) -> bool {
    if reg.len() != 2 { return false; }
    *reg[0].key == *c.key || *reg[1].key == *c.key
}
