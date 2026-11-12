//! X2b reproducers, probe f: class c (account arrays, optional account references), class d (function items as
//! closure values), class e (settlement entry generic over callables with elided lifetimes).
#![no_std]
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

fn five<'s, 'i>(a: &'s [AccountInfo<'i>]) -> Result<[&'s AccountInfo<'i>; 5], ProgramError> {
    if a.len() != 5 { return Err(ProgramError::NotEnoughAccountKeys); }
    Ok([&a[0], &a[1], &a[2], &a[3], &a[4]])
}
/// C0 (frozen shape): array pattern over the array of references, clones into an array.
pub fn c0<'a>(a: &[AccountInfo<'a>]) -> Result<[AccountInfo<'a>; 5], ProgramError> {
    let [m, s, au, v, t] = five(a)?;
    Ok([(*s).clone(), (*m).clone(), (*v).clone(), (*au).clone(), (*t).clone()])
}
/// C1: index the array of references.
pub fn c1<'a>(a: &[AccountInfo<'a>]) -> Result<[AccountInfo<'a>; 5], ProgramError> {
    let r = match five(a) { Ok(r) => r, Err(e) => return Err(e) };
    Ok([r[1].clone(), r[0].clone(), r[3].clone(), r[2].clone(), r[4].clone()])
}
/// C2: check through the helper, then clone from the slice by index.
pub fn c2<'a>(a: &[AccountInfo<'a>]) -> Result<[AccountInfo<'a>; 5], ProgramError> {
    if let Err(e) = five(a) { return Err(e); }
    Ok([a[1].clone(), a[0].clone(), a[3].clone(), a[2].clone(), a[4].clone()])
}
/// C3: clone one account (control).
pub fn c3<'a>(a: &AccountInfo<'a>) -> AccountInfo<'a> { a.clone() }
/// C4: Option<&AccountInfo> parameter, ok_or then field checks (proof_transport_verifier shape, value comparisons).
pub fn c4(v: &AccountInfo<'_>, p: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> {
    let c = c.ok_or(ProgramError::NotEnoughAccountKeys)?;
    if *p.key == *v.key || *c.owner != *v.key || c.is_signer { return Err(ProgramError::InvalidArgument); }
    Ok(*v.key)
}
/// C5: Option<&AccountInfo> parameter, explicit match.
pub fn c5(v: &AccountInfo<'_>, p: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> {
    let c = match c { Some(c) => c, None => return Err(ProgramError::NotEnoughAccountKeys) };
    if *p.key == *v.key || *c.owner != *v.key || c.is_signer { return Err(ProgramError::InvalidArgument); }
    Ok(*v.key)
}
/// C6: Option<&AccountInfo> passed through to C5.
pub fn c6(v: &AccountInfo<'_>, p: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<Pubkey, ProgramError> { c5(v, p, c) }
/// C7: Option<&AccountInfo> built by slice get.
pub fn c7(v: &AccountInfo<'_>, a: &[AccountInfo<'_>]) -> Result<Pubkey, ProgramError> { c5(v, &a[0], a.get(1)) }
/// C8: account reference by first()/get() with ok_or (terminal handler head).
pub fn c8<'a>(a: &'a [AccountInfo<'a>]) -> Result<&'a AccountInfo<'a>, ProgramError> {
    let m = a.first().ok_or(ProgramError::NotEnoughAccountKeys)?; Ok(m)
}
/// C9: as C8 with a length check and indexing.
pub fn c9<'a>(a: &'a [AccountInfo<'a>]) -> Result<&'a AccountInfo<'a>, ProgramError> {
    if a.is_empty() { return Err(ProgramError::NotEnoughAccountKeys); } Ok(&a[0])
}

fn hash2(x: u32, y: &[u32]) -> u32 { x.wrapping_add(if y.is_empty() { 0 } else { y[0] }) }
fn with_h<H: FnMut(u32, &[u32]) -> u32>(a: u32, h: &mut H) -> u32 { h(a, &[a]) }
/// D0 (frozen shape): function item passed as an FnMut value.
pub fn d0(a: u32) -> u32 { with_h(a, &mut hash2) }
/// D1: direct call.
pub fn d1(a: u32) -> u32 { hash2(a, &[a]) }
/// D2: Result::map with a path function (decode_with_empty_roots shape).
fn inner(x: (u32, u32)) -> u32 { x.0 }
pub fn d2(r: Result<(u32, u32), ProgramError>) -> Result<u32, ProgramError> { r.map(inner) }
/// D3: explicit match.
pub fn d3(r: Result<(u32, u32), ProgramError>) -> Result<u32, ProgramError> { match r { Ok(v) => Ok(inner(v)), Err(e) => Err(e) } }

/// E0 (frozen shape): entry generic over callables whose argument types have elided lifetimes.
pub fn e0<'info, V, S>(a: &[AccountInfo<'info>], v: V, s: S) -> Result<(), ProgramError>
where V: FnOnce(&Pubkey, &AccountInfo<'info>, Option<&AccountInfo<'info>>) -> Result<u64, ProgramError>, S: FnOnce(&[u8]) {
    if a.len() < 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    let x = v(a[0].key, &a[0], a.get(1))?;
    s(&x.to_le_bytes());
    Ok(())
}
fn verify_prod(_p: &Pubkey, a: &AccountInfo<'_>, c: Option<&AccountInfo<'_>>) -> Result<u64, ProgramError> {
    match c { Some(c) => Ok(if *a.key == *c.key { 1 } else { 2 }), None => Err(ProgramError::NotEnoughAccountKeys) }
}
pub fn e0_call(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> { e0(a, verify_prod, solana_program::program::set_return_data) }
/// E1: a local trait for the two host calls; production impl calls the functions directly.
pub trait TerminalHost<'info> {
    fn verify(&mut self, p: &Pubkey, a: &AccountInfo<'info>, c: Option<&AccountInfo<'info>>) -> Result<u64, ProgramError>;
    fn set_return_data(&mut self, d: &[u8]);
}
pub struct ProdHost;
impl<'info> TerminalHost<'info> for ProdHost {
    fn verify(&mut self, p: &Pubkey, a: &AccountInfo<'info>, c: Option<&AccountInfo<'info>>) -> Result<u64, ProgramError> { verify_prod(p, a, c) }
    fn set_return_data(&mut self, d: &[u8]) { solana_program::program::set_return_data(d) }
}
pub fn e1<'info, H: TerminalHost<'info>>(a: &[AccountInfo<'info>], h: &mut H) -> Result<(), ProgramError> {
    if a.len() < 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    let x = match h.verify(a[0].key, &a[0], a.get(1)) { Ok(x) => x, Err(e) => return Err(e) };
    h.set_return_data(&x.to_le_bytes());
    Ok(())
}
pub fn e1_call(a: &[AccountInfo<'_>]) -> Result<(), ProgramError> { let mut h = ProdHost; e1(a, &mut h) }
/// E2: as E1 with the host taken by value.
pub trait TerminalHostOnce<'info> {
    fn verify_once(&mut self, p: &Pubkey, a: &AccountInfo<'info>, c: Option<&AccountInfo<'info>>) -> Result<u64, ProgramError>;
}
impl<'info> TerminalHostOnce<'info> for ProdHost {
    fn verify_once(&mut self, p: &Pubkey, a: &AccountInfo<'info>, c: Option<&AccountInfo<'info>>) -> Result<u64, ProgramError> { verify_prod(p, a, c) }
}
pub fn e2<'info, H: TerminalHostOnce<'info>>(a: &[AccountInfo<'info>], mut h: H) -> Result<u64, ProgramError> {
    if a.len() < 2 { return Err(ProgramError::NotEnoughAccountKeys); }
    h.verify_once(a[0].key, &a[0], a.get(1))
}
pub fn e2_call(a: &[AccountInfo<'_>]) -> Result<u64, ProgramError> { e2(a, ProdHost) }
