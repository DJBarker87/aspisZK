//! X2b reproducers, probe c: writes through the account-data guard `RefMut<&mut [u8]>` (class 1, mutable side),
//! and the loop shapes proposed for class 9. One function per shape.
#![no_std]
use core::cell::RefMut;
use core::ops::DerefMut;
use solana_program::{account_info::AccountInfo, program_error::ProgramError};

fn borrow_mut<'b, 'a>(acc: &'b AccountInfo<'a>) -> Result<RefMut<'b, &'a mut [u8]>, ProgramError> {
    match acc.try_borrow_mut_data() { Ok(d) => Ok(d), Err(e) => Err(e) }
}

/// W1: helper generic over the guard type (DerefMut with the borrowed-slice target).
fn write_w1<'a, D: DerefMut<Target = &'a mut [u8]>>(d: &mut D, img: &[u8]) { d.deref_mut().copy_from_slice(img) }
pub fn w1(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_w1(&mut d, img.as_ref());
    Ok(())
}
/// W2: helper generic over the guard's content type, bounded by AsMut<[u8]>.
fn write_w2<T: AsMut<[u8]>>(d: &mut RefMut<'_, T>, img: &[u8]) { d.deref_mut().as_mut().copy_from_slice(img) }
pub fn w2(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_w2(&mut d, img.as_ref());
    Ok(())
}
/// W3: helper generic over the content type with a local trait for the slice view.
pub trait BytesMut { fn bytes_mut(&mut self) -> &mut [u8]; }
impl<'a> BytesMut for &'a mut [u8] { fn bytes_mut(&mut self) -> &mut [u8] { self } }
fn write_w3<T: BytesMut>(d: &mut RefMut<'_, T>, img: &[u8]) { d.deref_mut().bytes_mut().copy_from_slice(img) }
pub fn w3(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_w3(&mut d, img.as_ref());
    Ok(())
}
/// W4: RefMut::map to a guard over the unsized slice, then a write through it.
pub fn w4(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let mut s = RefMut::map(d, |x| &mut **x);
    s.copy_from_slice(img.as_ref());
    Ok(())
}
/// W5: generic plain-content helper (T: ?Sized + AsMut<[u8]>) taking `&mut T` reached by a generic deref.
fn deref_w5<'b, 'c, T>(d: &'b mut RefMut<'c, T>) -> &'b mut T { d.deref_mut() }
pub fn w5(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let s: &mut &mut [u8] = deref_w5(&mut d);
    s.copy_from_slice(img.as_ref());
    Ok(())
}
/// W6: W2 with two guards held across a call on a third account (the deposit write path), writes after.
pub fn w6(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut da = match a.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let mut db = match b.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    if c.data_len() != 8 { return Err(ProgramError::InvalidAccountData); }
    write_w2(&mut da, img.as_ref());
    write_w2(&mut db, img.as_ref());
    Ok(())
}
/// W7: W2 through the borrow helper.
pub fn w7(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let mut d = match borrow_mut(acc) { Ok(d) => d, Err(e) => return Err(e) };
    write_w2(&mut d, img.as_ref());
    Ok(())
}
/// W8: W2 with a plain-data writer taking &mut [u8] (write_new_page_unchecked shape).
fn put_header(d: &mut [u8], v: u64) { d[0..8].copy_from_slice(&v.to_le_bytes()) }
fn write_w8<T: AsMut<[u8]>>(d: &mut RefMut<'_, T>, v: u64) { put_header(d.deref_mut().as_mut(), v) }
pub fn w8(acc: &AccountInfo<'_>, v: u64) -> Result<(), ProgramError> {
    let mut d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_w8(&mut d, v);
    Ok(())
}

/// L1: for over a range with a flag (no early return).
pub fn l1(d: &[u8]) -> bool { let mut any = false; for i in 0..d.len() { if d[i] != 0 { any = true; } } any }
/// L2: while with index and flag in the condition.
pub fn l2(d: &[u8]) -> bool { let mut i = 0; let mut z = true; while z && i < d.len() { z = d[i] == 0; i += 1; } z }
/// L3: for over slice.iter().
pub fn l3(d: &[u8]) -> u64 { let mut s = 0u64; for b in d.iter() { s = s.wrapping_add(*b as u64); } s }
/// L4: for over a fixed array by value index, writing a local array (map replacement).
pub fn l4(x: [u32; 8]) -> [u64; 8] { let mut o = [0u64; 8]; let mut i = 0; while i < 8 { o[i] = x[i] as u64; i += 1; } o }
/// L5: for over a range writing a mutable array (iter_mut replacement).
pub fn l5(x: &mut [u32; 8], k: u32) { for i in 0..8 { x[i] = x[i].wrapping_add(k); } }
/// L6: for over a range with break.
pub fn l6(d: &[u8]) -> Option<usize> { let mut f = None; for i in 0..d.len() { if d[i] == 1 { f = Some(i); break; } } f }
/// L7: wrapping_shl with a u32 amount from a usize.
pub fn l7(x: u64, s: usize) -> u64 { x.wrapping_shl(s as u32) }
/// L8: wrapping_shl with a literal amount.
pub fn l8(x: u32) -> u32 { x.wrapping_shl(8u32) }
