//! X2b reproducers, probe b: class 1 (account-data borrows), class 2 (binder named like a module), and the
//! Option/Result combinators of class 9. One function per shape; the name says the shape.
#![no_std]
extern crate alloc;
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

pub mod vault { pub fn pool_v1_vault_tag() -> u8 { 3 } }

fn first(d: &[u8]) -> Result<u8, ProgramError> { if d.is_empty() { Err(ProgramError::InvalidAccountData) } else { Ok(d[0]) } }
fn all_zero(d: &[u8]) -> bool { let mut i = 0; let mut ok = true; while ok && i < d.len() { ok = d[i] == 0; i += 1; } ok }
fn put8(d: &mut [u8], v: u64) { d[0..8].copy_from_slice(&v.to_le_bytes()) }
fn decode32(d: &[u8]) -> Result<[u8; 32], ProgramError> {
    if d.len() < 32 { return Err(ProgramError::InvalidAccountData); }
    let mut o = [0u8; 32]; o.copy_from_slice(&d[0..32]); Ok(o)
}

/// Q0 (frozen shape, rejected natively): `?` on the borrow, guard held.
pub fn q0_question(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> { let d = acc.try_borrow_data()?; first(&d) }
/// Q1: explicit match with early return, guard held, pure read.
pub fn q1_match_len(acc: &AccountInfo<'_>) -> Result<usize, ProgramError> {
    let d = match acc.try_borrow_data() { Ok(d) => d, Err(e) => return Err(e) };
    Ok(d.len())
}
/// Q2: explicit match, guard passed to a fallible pure helper, its `?` after the match.
pub fn q2_match_first(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> {
    let d = match acc.try_borrow_data() { Ok(d) => d, Err(e) => return Err(e) };
    let x = first(&d)?;
    Ok(x.wrapping_add(1))
}
/// Q3: helper that confines the borrow and returns a copied value; the caller uses `?` on a plain Result.
fn read_first(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> {
    match acc.try_borrow_data() { Ok(d) => first(&d), Err(e) => Err(e) }
}
pub fn q3_helper_copy(acc: &AccountInfo<'_>, k: &Pubkey) -> Result<u8, ProgramError> {
    if *acc.owner != *k { return Err(ProgramError::IllegalOwner); }
    let x = read_first(acc)?;
    Ok(x.wrapping_add(1))
}
/// Q4: helper returning a predicate over the bytes (loop in a plain-data helper).
fn data_all_zero(acc: &AccountInfo<'_>) -> Result<bool, ProgramError> {
    match acc.try_borrow_data() { Ok(d) => Ok(all_zero(&d)), Err(e) => Err(e) }
}
pub fn q4_zero(acc: &AccountInfo<'_>, n: usize) -> Result<(), ProgramError> {
    if acc.data_len() != n { return Err(ProgramError::InvalidAccountData); }
    if !data_all_zero(acc)? { return Err(ProgramError::AccountAlreadyInitialized); }
    Ok(())
}
/// Q5: helper decoding a 32-byte value (copy of a small header) from the guard.
fn read_key(acc: &AccountInfo<'_>) -> Result<[u8; 32], ProgramError> {
    match acc.try_borrow_data() { Ok(d) => decode32(&d), Err(e) => Err(e) }
}
pub fn q5_decode(acc: &AccountInfo<'_>) -> Result<[u8; 32], ProgramError> { let k = read_key(acc)?; Ok(k) }
/// Q6: mutable guard by match, write through a plain-data helper.
pub fn q6_write(acc: &AccountInfo<'_>, v: u64) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    put8(&mut d, v);
    Ok(())
}
/// Q7: two mutable guards acquired first, an SDK call on a third account in between, then two writes
/// (the deposit/terminal write path: borrows held across the CPI).
pub fn q7_two_guards(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, v: u64) -> Result<(), ProgramError> {
    let mut da = match a.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let mut db = match b.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    if c.data_len() != 8 { return Err(ProgramError::InvalidAccountData); }
    put8(&mut da, v);
    put8(&mut db, v.wrapping_add(1));
    Ok(())
}
/// Q8: copy_from_slice directly on the guard (the frozen write).
pub fn q8_copy_from_slice(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    d.copy_from_slice(img.as_ref());
    Ok(())
}
/// Q9: write helper that confines the mutable borrow.
fn write_image(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    match acc.try_borrow_mut_data() { Ok(mut d) => { d.copy_from_slice(img.as_ref()); Ok(()) } Err(e) => Err(e) }
}
pub fn q9_write_helper(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> { write_image(acc, img)?; Ok(()) }
/// Q10: indexing a range of the guard and converting (pair_forest 2562 shape).
pub fn q10_index(acc: &AccountInfo<'_>) -> Result<u64, ProgramError> {
    let d = match acc.try_borrow_data() { Ok(d) => d, Err(e) => return Err(e) };
    if d.len() < 72 { return Err(ProgramError::InvalidAccountData); }
    let mut b = [0u8; 8]; b.copy_from_slice(&d[64..72]);
    Ok(u64::from_le_bytes(b))
}

/// N0 (frozen shape): a local named like the module `vault`.
pub fn n0_shadow(vault: &AccountInfo<'_>) -> u8 { if vault.is_signer { vault::pool_v1_vault_tag() } else { 0 } }
/// N1: the binder renamed.
pub fn n1_renamed(vault_account: &AccountInfo<'_>) -> u8 { if vault_account.is_signer { vault::pool_v1_vault_tag() } else { 0 } }

/// O0 (frozen shape): ok_or then `?`.
pub fn o0_ok_or(x: Option<u8>) -> Result<u8, ProgramError> { let v = x.ok_or(ProgramError::InvalidArgument)?; Ok(v) }
/// O1: explicit match with the same error value.
pub fn o1_match(x: Option<u8>) -> Result<u8, ProgramError> { let v = match x { Some(v) => v, None => return Err(ProgramError::InvalidArgument) }; Ok(v) }
/// O2: ok_or_else.
pub fn o2_ok_or_else(x: Option<u8>) -> Result<u8, ProgramError> { let v = x.ok_or_else(|| ProgramError::InvalidArgument)?; Ok(v) }
/// O3: Option::map.
pub fn o3_option_map(x: Option<u8>) -> Option<u16> { x.map(|v| v as u16) }
/// O4: Result::map_err then `?`.
pub fn o4_map_err(x: Result<u8, ()>) -> Result<u8, ProgramError> { let v = x.map_err(|_| ProgramError::InvalidArgument)?; Ok(v) }
/// O5: Option::and_then.
pub fn o5_and_then(x: Option<u8>) -> Option<u8> { x.and_then(|v| v.checked_add(1)) }
/// O6: Result::map.
pub fn o6_result_map(x: Result<u8, ProgramError>) -> Result<u16, ProgramError> { x.map(|v| v as u16) }
/// O7: `?` on a plain Result (no borrow inside).
pub fn o7_question(x: Result<u8, ProgramError>) -> Result<u8, ProgramError> { let v = x?; Ok(v) }
/// O8: checked arithmetic then ok_or (Pool's overflow guards).
pub fn o8_checked(a: u64, b: u64) -> Result<u64, ProgramError> { a.checked_add(b).ok_or(ProgramError::ArithmeticOverflow) }
/// O9: explicit match on the checked result.
pub fn o9_checked_match(a: u64, b: u64) -> Result<u64, ProgramError> { match a.checked_add(b) { Some(v) => Ok(v), None => Err(ProgramError::ArithmeticOverflow) } }
