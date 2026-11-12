//! X2b reproducers, probe d: account-data writes with the guard moved by value into a generic writer and a local
//! trait whose methods on the borrowed slice return unit.
#![no_std]
use core::cell::RefMut;
use solana_program::{account_info::AccountInfo, program_error::ProgramError};

fn put_header(d: &mut [u8], v: u64) { d[0..8].copy_from_slice(&v.to_le_bytes()) }

pub trait AccountBytesMut {
    fn copy_image(&mut self, src: &[u8]);
    fn put_header(&mut self, v: u64);
}
impl<'a> AccountBytesMut for &'a mut [u8] {
    fn copy_image(&mut self, src: &[u8]) { self.copy_from_slice(src) }
    fn put_header(&mut self, v: u64) { put_header(self, v) }
}
/// D1: guard moved into a generic writer; the write goes through the trait method (auto-deref, generic T).
fn write_image<T: AccountBytesMut>(mut g: RefMut<'_, T>, src: &[u8]) { g.copy_image(src) }
fn write_header<T: AccountBytesMut>(mut g: RefMut<'_, T>, v: u64) { g.put_header(v) }
pub fn d1(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_image(d, img.as_ref());
    Ok(())
}
/// D2: as D1 with the plain-data writer behind the trait.
pub fn d2(acc: &AccountInfo<'_>, v: u64) -> Result<(), ProgramError> {
    let d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_header(d, v);
    Ok(())
}
/// D3: two guards acquired, a call on a third account, then both moved into writers (deposit write path).
pub fn d3(a: &AccountInfo<'_>, b: &AccountInfo<'_>, c: &AccountInfo<'_>, img: &[u8; 16], v: u64) -> Result<(), ProgramError> {
    let da = match a.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let db = match b.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    if c.data_len() != 8 { return Err(ProgramError::InvalidAccountData); }
    write_image(da, img.as_ref());
    write_header(db, v);
    Ok(())
}
/// D4: generic writer over the deref'd content by explicit DerefMut call on the moved guard.
fn write_image4<T: AccountBytesMut>(mut g: RefMut<'_, T>, src: &[u8]) { let t: &mut T = &mut *g; t.copy_image(src) }
pub fn d4(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let d = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_image4(d, img.as_ref());
    Ok(())
}
/// D5: the reader with `?` on a plain helper result after a guard-confining read helper (control).
fn read8(acc: &AccountInfo<'_>) -> Result<u64, ProgramError> {
    let d = match acc.try_borrow_data() { Ok(d) => d, Err(e) => return Err(e) };
    if d.len() < 8 { return Err(ProgramError::InvalidAccountData); }
    let mut b = [0u8; 8]; b.copy_from_slice(&d[0..8]); Ok(u64::from_le_bytes(b))
}
pub fn d5(acc: &AccountInfo<'_>) -> Result<u64, ProgramError> { let x = read8(acc)?; Ok(x) }
