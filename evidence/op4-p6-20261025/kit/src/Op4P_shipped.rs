// Verbatim shipped bodies; nominal Error reduced to its sole reached variant.
use aspis_core::field::{M31,QM31 as K,WideExact as E};
use super::Op4P_reference::Error;
const OPENING:usize=832;
mod compact {
use aspis_core::field::QM31;
#[derive(Clone,Copy,Debug)] pub enum CodecError {NonCanonical}
pub const OFF_Y1:usize=7031;
pub const OFF_INACTIVE:usize=7495;
pub const OFF_ROUND0:usize=7527;
pub const OFF_FOLDED_ROOT:usize=7751;
pub const OFF_ROUND1:usize=7783;
pub const OFF_OPENINGS:usize=10055;
pub fn check_values(compact: &[u8]) -> Result<(), CodecError> {
    for c in compact.chunks_exact(16) {
        QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical)?;
    }
    Ok(())
}
}
impl From<compact::CodecError> for Error {fn from(_:compact::CodecError)->Self{Self::Parse}}
fn echeck(b:&[u8],k:bool)->Result<(),Error> {
    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}
    Ok(())
}
fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}
pub fn canonical_scan(proof: &[u8]) -> Result<(), Error> {
    compact::check_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE])?;
    echeck(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE + 32], false)?;
    echeck(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT], false)?;
    echeck(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS], false)?;
    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
            }
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            for l in 0..2 {
                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
            }
        }
        echeck(&q[672..800], false)?;
    }
    Ok(())
}
