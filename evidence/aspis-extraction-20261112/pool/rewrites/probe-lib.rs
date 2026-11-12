//! X2 stage 2 reproducers (class a: AccountInfo borrows). One function per shape.
#![no_std]
use solana_program::{account_info::AccountInfo, program_error::ProgramError};

fn first(d: &[u8]) -> Result<u8, ProgramError> { d.first().copied().ok_or(ProgramError::InvalidAccountData) }

/// A1: data_len alone
pub fn a1(acc: &AccountInfo<'_>) -> usize { acc.data_len() }
/// A2: data_len inside a short-circuit chain after field reads
pub fn a2(acc: &AccountInfo<'_>, n: usize) -> bool { acc.is_signer || acc.data_len() != n }
/// A3: guard held to the end of the function (the shape that translates in the Pool)
pub fn a3(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> { let d = acc.try_borrow_data()?; first(&d) }
/// A4: temporary guard in an argument, then more code
pub fn a4(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> { let x = first(&acc.try_borrow_data()?)?; Ok(x.wrapping_add(1)) }
/// A5: guard in an inner block, then more code
pub fn a5(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> { let x = { let d = acc.try_borrow_data()?; first(&d)? }; Ok(x.wrapping_add(1)) }
/// A6: data_is_empty alone
pub fn a6(acc: &AccountInfo<'_>) -> bool { acc.data_is_empty() }
/// A7: guard held to the end, after a branch on a field
pub fn a7(acc: &AccountInfo<'_>, k: &solana_program::pubkey::Pubkey) -> Result<u8, ProgramError> {
    if acc.owner == k { let d = acc.try_borrow_data()?; first(&d) } else { Err(ProgramError::InvalidArgument) }
}
/// A8: guard dropped explicitly before more code
pub fn a8(acc: &AccountInfo<'_>) -> Result<u8, ProgramError> { let d = acc.try_borrow_data()?; let x = first(&d)?; drop(d); Ok(x.wrapping_add(1)) }
/// A9: data_len then data_is_empty sequence (no chain)
pub fn a9(acc: &AccountInfo<'_>) -> bool { let n = acc.data_len(); let e = acc.data_is_empty(); n == 0 && e }

use solana_program::pubkey::Pubkey;
fn k() -> Pubkey { Pubkey::new_from_array([7u8; 32]) }
const KC: Pubkey = Pubkey::new_from_array([9u8; 32]);
/// B1: field comparison against a temporary, then an SDK call in the same && chain (plan_fresh_program_pda tail)
pub fn b1(acc: &AccountInfo<'_>) -> bool { acc.owner == &k() && acc.data_is_empty() }
/// B2: as B1 with the deref comparison (*field == value)
pub fn b2(acc: &AccountInfo<'_>) -> bool { *acc.owner == k() && acc.data_is_empty() }
/// B3: as B1, the comparison bound to a local first
pub fn b3(acc: &AccountInfo<'_>) -> bool { let o = acc.owner == &k(); o && acc.data_is_empty() }
/// B4: as B1, nested if
pub fn b4(acc: &AccountInfo<'_>) -> bool { if acc.owner == &k() { acc.data_is_empty() } else { false } }
/// B5: field comparisons in an || chain ending in data_len (require_forest_mint_account)
pub fn b5(acc: &AccountInfo<'_>, n: usize) -> bool { acc.owner != &KC || acc.executable || acc.data_len() != n }
/// B6: B5 with deref comparisons
pub fn b6(acc: &AccountInfo<'_>, n: usize) -> bool { *acc.owner != KC || acc.executable || acc.data_len() != n }
/// B7: key compared with a reference parameter, then a guard (plan_fresh_program_pda head)
pub fn b7(acc: &AccountInfo<'_>, e: &Pubkey, p: &Pubkey) -> Result<u8, ProgramError> {
    if acc.key != e || acc.is_signer { return Err(ProgramError::InvalidArgument); }
    if acc.owner == p { let d = acc.try_borrow_data()?; first(&d) } else { Err(ProgramError::InvalidArgument) }
}
/// B8: two accounts from a slice pattern, comparisons, then a guard on one (validate_exact_deposit_delta_v1)
pub fn b8(accs: &[AccountInfo<'_>], m: &Pubkey) -> Result<u8, ProgramError> {
    let [a, b] = accs else { return Err(ProgramError::NotEnoughAccountKeys) };
    if a.key != m || b.key != m { return Err(ProgramError::InvalidArgument); }
    let x = { let d = b.try_borrow_data()?; first(&d)? };
    Ok(x)
}
/// B9: as B8 with indexing instead of a slice pattern
pub fn b9(accs: &[AccountInfo<'_>], m: &Pubkey) -> Result<u8, ProgramError> {
    if accs.len() != 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    let a = &accs[0]; let b = &accs[1];
    if a.key != m || b.key != m { return Err(ProgramError::InvalidArgument); }
    let x = { let d = b.try_borrow_data()?; first(&d)? };
    Ok(x)
}

/// C1: B7 with value comparisons (*field != *param)
pub fn c1(acc: &AccountInfo<'_>, e: &Pubkey, p: &Pubkey) -> Result<u8, ProgramError> {
    if *acc.key != *e || acc.is_signer { return Err(ProgramError::InvalidArgument); }
    if *acc.owner == *p { let d = acc.try_borrow_data()?; first(&d) } else { Err(ProgramError::InvalidArgument) }
}
/// C2: B7 with only the key comparison changed
pub fn c2(acc: &AccountInfo<'_>, e: &Pubkey, p: &Pubkey) -> Result<u8, ProgramError> {
    if *acc.key != *e || acc.is_signer { return Err(ProgramError::InvalidArgument); }
    if acc.owner == p { let d = acc.try_borrow_data()?; first(&d) } else { Err(ProgramError::InvalidArgument) }
}
/// C3: B9 with value comparisons
pub fn c3(accs: &[AccountInfo<'_>], m: &Pubkey) -> Result<u8, ProgramError> {
    if accs.len() != 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    let a = &accs[0]; let b = &accs[1];
    if *a.key != *m || *b.key != *m { return Err(ProgramError::InvalidArgument); }
    let x = { let d = b.try_borrow_data()?; first(&d)? };
    Ok(x)
}
/// C4: B8 (slice pattern) with value comparisons
pub fn c4(accs: &[AccountInfo<'_>], m: &Pubkey) -> Result<u8, ProgramError> {
    let [a, b] = accs else { return Err(ProgramError::NotEnoughAccountKeys) };
    if *a.key != *m || *b.key != *m { return Err(ProgramError::InvalidArgument); }
    let x = { let d = b.try_borrow_data()?; first(&d)? };
    Ok(x)
}
/// C5: slice pattern returning the element references only
pub fn c5<'s, 'i>(accs: &'s [AccountInfo<'i>]) -> Result<[&'s AccountInfo<'i>; 2], ProgramError> {
    let [a, b] = accs else { return Err(ProgramError::NotEnoughAccountKeys) };
    Ok([a, b])
}
/// C6: the same by length check and indexing
pub fn c6<'s, 'i>(accs: &'s [AccountInfo<'i>]) -> Result<[&'s AccountInfo<'i>; 2], ProgramError> {
    if accs.len() != 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    Ok([&accs[0], &accs[1]])
}

// ---- class b: loop shapes
/// D0: the frozen shape (nested for, return inside)
pub fn d0(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    for l in 0..a.len() { for r in l + 1..a.len() { if a[l].key == a[r].key { return Err(ProgramError::InvalidArgument); } } }
    Ok(())
}
/// D1: nested while, a flag in both conditions, value comparison
pub fn d1(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    let n = a.len(); let mut dup = false; let mut l = 0;
    while l < n && !dup { let mut r = l + 1; while r < n && !dup { if *a[l].key == *a[r].key { dup = true; } r += 1; } l += 1; }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
fn repeats_after(a: &[AccountInfo<'_>], l: usize) -> bool {
    let mut r = l + 1; let mut dup = false;
    while r < a.len() && !dup { if *a[l].key == *a[r].key { dup = true; } r += 1; }
    dup
}
/// D2: inner loop in a helper, outer while with a flag
pub fn d2(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    let mut l = 0; let mut dup = false;
    while l < a.len() && !dup { dup = repeats_after(a, l); l += 1; }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
/// D3: for loops with a plain break from the inner loop only, flag checked by the outer
pub fn d3(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    let mut dup = false;
    for l in 0..a.len() { for r in l + 1..a.len() { if *a[l].key == *a[r].key { dup = true; break; } } if dup { break; } }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
fn canon(b: &[u8]) -> Result<(), ()> { if b[0] == 0xff { Err(()) } else { Ok(()) } }
/// E0: the frozen shape of validate_root_page_bytes' loop (? inside for)
pub fn e0(d: &[u8], filled: usize) -> Result<u8, ProgramError> {
    for s in 0..filled { let st = 64 + s * 32; canon(&d[st..st + 32]).map_err(|_| ProgramError::InvalidAccountData)?; }
    Ok(1)
}
/// E1: while with an ok flag in the condition, error returned after the loop
pub fn e1(d: &[u8], filled: usize) -> Result<u8, ProgramError> {
    let mut s = 0; let mut ok = true;
    while s < filled && ok { let st = 64 + s * 32; if canon(&d[st..st + 32]).is_err() { ok = false; } s += 1; }
    if !ok { return Err(ProgramError::InvalidAccountData); }
    Ok(1)
}

// ---- class b with AccountInfo slices: keep AccountInfo out of the loop body
fn key_of<'b>(x: &'b AccountInfo<'_>) -> &'b Pubkey { x.key }
fn same_key_at(a: &[AccountInfo<'_>], l: usize, r: usize) -> bool { *a[l].key == *a[r].key }
/// F1: while + flag, comparison in a loop-free helper taking the slice and two indices
pub fn f1(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    let n = a.len(); let mut dup = false; let mut l = 0;
    while l < n && !dup { let mut r = l + 1; while r < n && !dup { if same_key_at(a, l, r) { dup = true; } r += 1; } l += 1; }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
/// F2: while + flag over an array of key references built before the loop (fixed five)
pub fn f2(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, d: &AccountInfo<'_>, e: &AccountInfo<'_>) -> Result<(), ProgramError> {
    let keys: [&Pubkey; 5] = [a.key, b.key, c.key, d.key, e.key];
    let mut dup = false; let mut l = 0;
    while l < 5 && !dup { let mut r = l + 1; while r < 5 && !dup { if *keys[l] == *keys[r] { dup = true; } r += 1; } l += 1; }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
/// F3: as F1 with key_of
pub fn f3(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    let n = a.len(); let mut dup = false; let mut l = 0;
    while l < n && !dup { let mut r = l + 1; while r < n && !dup { if *key_of(&a[l]) == *key_of(&a[r]) { dup = true; } r += 1; } l += 1; }
    if dup { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
/// F4: fixed five, unrolled comparisons, no loop
pub fn f4(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, d: &AccountInfo<'_>, e: &AccountInfo<'_>) -> bool {
    *a.key == *b.key || *a.key == *c.key || *a.key == *d.key || *a.key == *e.key || *b.key == *c.key
        || *b.key == *d.key || *b.key == *e.key || *c.key == *d.key || *c.key == *e.key || *d.key == *e.key
}

// ---- class b, variable-length account slices
fn dup_inner(a: &[AccountInfo<'_>], l: usize, r: usize) -> bool {
    if r >= a.len() { false } else if *a[l].key == *a[r].key { true } else { dup_inner(a, l, r + 1) }
}
fn dup_outer(a: &[AccountInfo<'_>], l: usize) -> bool {
    if l >= a.len() { false } else if dup_inner(a, l, l + 1) { true } else { dup_outer(a, l + 1) }
}
/// G1: recursion instead of loops (no loop in any function that holds an AccountInfo)
pub fn g1(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> {
    if dup_outer(a, 0) { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
fn keys_repeat(keys: &[Pubkey]) -> bool {
    let n = keys.len(); let mut dup = false; let mut l = 0;
    while l < n && !dup { let mut r = l + 1; while r < n && !dup { if keys[l] == keys[r] { dup = true; } r += 1; } l += 1; }
    dup
}
/// G2: keys copied out (fixed five), the loop in a helper that sees only [Pubkey]
pub fn g2(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, d: &AccountInfo<'_>, e: &AccountInfo<'_>) -> Result<(), ProgramError> {
    let keys = [*a.key, *b.key, *c.key, *d.key, *e.key];
    if keys_repeat(&keys) { return Err(ProgramError::InvalidArgument); }
    Ok(())
}
