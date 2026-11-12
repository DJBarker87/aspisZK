//! X2b reproducers, probe e: account-data writes with the borrowed slice moved out of the guard and put back.
#![no_std]
use core::cell::RefMut;
use solana_program::{account_info::AccountInfo, program_error::ProgramError};

/// E1: generic split of a moved guard into (guard, content) and the join back; the concrete caller writes through
/// a single-level `&mut [u8]`.
fn split_guard<'g, T: Default>(mut g: RefMut<'g, T>) -> (RefMut<'g, T>, T) { let s = core::mem::take(&mut *g); (g, s) }
fn join_guard<'g, T>(mut g: RefMut<'g, T>, s: T) -> RefMut<'g, T> { *g = s; g }
pub fn e1(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let g = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    let (g, s) = split_guard(g);
    s.copy_from_slice(img.as_ref());
    let _g = join_guard(g, s);
    Ok(())
}
/// E3: trait whose method moves the slice in and out (Self by value, returns Self), generic writer with take.
pub trait IntoWritten: Sized { fn written_with_image(self, src: &[u8]) -> Self; }
impl<'a> IntoWritten for &'a mut [u8] { fn written_with_image(self, src: &[u8]) -> Self { self.copy_from_slice(src); self } }
fn write_e3<T: IntoWritten + Default>(mut g: RefMut<'_, T>, src: &[u8]) { let s = core::mem::take(&mut *g); *g = s.written_with_image(src); }
pub fn e3(acc: &AccountInfo<'_>, img: &[u8; 16]) -> Result<(), ProgramError> {
    let g = match acc.try_borrow_mut_data() { Ok(d) => d, Err(e) => return Err(e) };
    write_e3(g, img.as_ref());
    Ok(())
}
/// E4: trait with a unit method taking Self by value (consumes the slice), generic writer with take and a re-borrow
/// is impossible; instead the write is done on a copy of the moved slice reference: not used (control for the impl
/// signature only).
pub trait WriteInto { fn write_image_into(self, src: &[u8]); }
impl<'a> WriteInto for &'a mut [u8] { fn write_image_into(self, src: &[u8]) { self.copy_from_slice(src) } }
pub fn e4(s: &mut [u8], img: &[u8; 16]) { s.write_image_into(img.as_ref()) }
