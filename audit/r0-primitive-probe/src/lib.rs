//! Local SBF primitive calibration. No proof verification or network action.
#![allow(unexpected_cfgs)]
use aspis_core::{
    field::{WideExact as E, M31, QM31},
    r0::CodeField,
};
use core::hint::black_box;
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, hash::hashv, log::sol_log_compute_units,
    program_error::ProgramError, pubkey::Pubkey,
};
#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process);
pub fn process(_: &Pubkey, _: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data.len() != 70 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let op = data[0];
    let empty = data[1] != 0;
    let n = u32::from_le_bytes(data[2..6].try_into().unwrap());
    if n > 8192 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let x = E::from_le_bytes(&data[6..38]).ok_or(ProgramError::InvalidInstructionData)?;
    let y = E::from_le_bytes(&data[38..70]).ok_or(ProgramError::InvalidInstructionData)?;
    let (k, f) = (y.c0(), M31(y.to_limbs()[0]));
    // Each branch has its own matching empty loop on the same value type.
    macro_rules! run {
        ($x:expr,$v:ident,$work:expr,$encode:expr) => {{
            let mut $v = $x;
            if empty {
                for _ in 0..n {
                    $v = black_box($v);
                }
            } else {
                for _ in 0..n {
                    $v = black_box($work);
                }
            }
            ($encode)($v)
        }};
    }
    sol_log_compute_units();
    let out: [u8; 32] = match op {
        0 => run!(x, v, v.add(black_box(y)), E::to_le_bytes),
        1 => run!(x, v, v.sub(black_box(y)), E::to_le_bytes),
        2 => run!(x, v, v.neg(), E::to_le_bytes),
        3 => run!(x, v, v.mul(black_box(y)), E::to_le_bytes),
        4 => run!(x, v, v.square(), E::to_le_bytes),
        5 => run!(x, v, v.mul_qm31(black_box(k)), E::to_le_bytes),
        6 => run!(x, v, v.mul_m31(black_box(f)), E::to_le_bytes),
        7 => run!(x, v, v.try_inv().unwrap(), E::to_le_bytes),
        8 => run!(x, v, <E as CodeField>::try_inv(v).unwrap(), E::to_le_bytes),
        9 => run!(x.c0(), v, v.add(black_box(k)), encode_k),
        10 => run!(x.c0(), v, v.sub(black_box(k)), encode_k),
        11 => run!(x.c0(), v, v.neg(), encode_k),
        12 => run!(x.c0(), v, v.mul(black_box(k)), encode_k),
        13 => run!(x.c0(), v, v.square(), encode_k),
        14 => run!(x.c0(), v, v.mul_m31(black_box(f)), encode_k),
        15 => run!(x.c0(), v, v.mul_cm31(black_box(k.c0)), encode_k),
        16 => run!(x.c0(), v, v.try_inv().unwrap(), encode_k),
        17 => run!(
            x.c0(),
            v,
            <QM31 as CodeField>::try_inv(v).unwrap(),
            encode_k
        ),
        18 => run!(M31(x.to_limbs()[0]), v, v.add(black_box(f)), encode_f),
        19 => run!(M31(x.to_limbs()[0]), v, v.sub(black_box(f)), encode_f),
        20 => run!(M31(x.to_limbs()[0]), v, v.neg(), encode_f),
        21 => run!(M31(x.to_limbs()[0]), v, v.mul(black_box(f)), encode_f),
        22 => run!(M31(x.to_limbs()[0]), v, v.inv(), encode_f),
        23 => run!(
            M31(x.to_limbs()[0]),
            v,
            <M31 as CodeField>::try_inv(v).unwrap(),
            encode_f
        ),
        24 => run!(M31(x.to_limbs()[0]), v, v.half(), encode_f),
        25 => run!(
            M31(x.to_limbs()[0]),
            v,
            v.mul_pow2(black_box((f.0 % 30) as u8)),
            encode_f
        ),
        26 => run!(
            x.to_le_bytes(),
            v,
            hashv(&[black_box(&v)]).to_bytes(),
            |v| v
        ),
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    sol_log_compute_units();
    solana_program::program::set_return_data(&out);
    Ok(())
}
fn encode_k(k: QM31) -> [u8; 32] {
    let mut out = [0; 32];
    k.write_le_bytes(&mut out[..16]);
    out
}
fn encode_f(f: M31) -> [u8; 32] {
    let mut out = [0; 32];
    out[..4].copy_from_slice(&f.0.to_le_bytes());
    out
}
