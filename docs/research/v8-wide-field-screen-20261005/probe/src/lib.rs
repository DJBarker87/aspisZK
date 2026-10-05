//! Wide-field cost screen probe.  Kernel timing and authentication only.
//! Acceptance here is never Aspis proof acceptance.
extern crate aspis_core as corelib;
use corelib::field::{CM31, M31, QM31};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};
solana_program::entrypoint!(entry);

type K6 = [CM31; 3];
type K8 = [QM31; 2];

#[inline(always)]
fn mul_by_r(x: CM31) -> CM31 {
    // (2 + i)(a + bi)
    CM31::new(x.a.double().sub(x.b), x.a.add(x.b.double()))
}
#[inline(always)]
fn mul_by_u(x: QM31) -> QM31 {
    // (c0 + c1 u) u = (2 + i) c1 + c0 u
    QM31 { c0: mul_by_r(x.c1), c1: x.c0 }
}
#[inline(always)]
fn k8_mul(a: K8, b: K8) -> K8 {
    let m0 = a[0].mul(b[0]);
    let m1 = a[1].mul(b[1]);
    let m2 = a[0].add(a[1]).mul(b[0].add(b[1]));
    [m0.add(mul_by_u(m1)), m2.sub(m0).sub(m1)]
}
#[inline(always)]
fn k8_inv(a: K8) -> K8 {
    let norm = a[0].square().sub(mul_by_u(a[1].square()));
    let n = norm.inv();
    [a[0].mul(n), a[1].neg().mul(n)]
}
#[inline(always)]
fn k6_mul(a: K6, b: K6) -> K6 {
    let v0 = a[0].mul(b[0]);
    let v1 = a[1].mul(b[1]);
    let v2 = a[2].mul(b[2]);
    let t12 = a[1].add(a[2]).mul(b[1].add(b[2])).sub(v1).sub(v2);
    let t01 = a[0].add(a[1]).mul(b[0].add(b[1])).sub(v0).sub(v1);
    let t02 = a[0].add(a[2]).mul(b[0].add(b[2])).sub(v0).sub(v2);
    [v0.add(mul_by_r(t12)), t01.add(mul_by_r(v2)), t02.add(v1)]
}

fn word(bytes: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(bytes.get(at..at + 4)?.try_into().ok()?))
}
fn m31(bytes: &[u8], at: usize) -> Option<M31> {
    let value = word(bytes, at)?;
    (value < 2_147_483_647).then_some(M31(value))
}
fn cm31(bytes: &[u8], at: usize) -> Option<CM31> {
    Some(CM31::new(m31(bytes, at)?, m31(bytes, at + 4)?))
}
fn qm31(bytes: &[u8], at: usize) -> Option<QM31> {
    Some(QM31 { c0: cm31(bytes, at)?, c1: cm31(bytes, at + 8)? })
}
fn k6(bytes: &[u8], at: usize) -> Option<K6> {
    Some([cm31(bytes, at)?, cm31(bytes, at + 8)?, cm31(bytes, at + 16)?])
}
fn k8(bytes: &[u8], at: usize) -> Option<K8> {
    Some([qm31(bytes, at)?, qm31(bytes, at + 16)?])
}

fn kernels(op: u8, n: u32, p: &[u8]) -> Option<bool> {
    Some(match op {
        1 => {
            let (mut x, y, want) = (qm31(p, 0)?, qm31(p, 16)?, qm31(p, 32)?);
            for _ in 0..n { x = x.mul(y); }
            x == want
        }
        2 => {
            let (mut x, y, want) = (k6(p, 0)?, k6(p, 24)?, k6(p, 48)?);
            for _ in 0..n { x = k6_mul(x, y); }
            x == want
        }
        3 => {
            let (mut x, y, want) = (k8(p, 0)?, k8(p, 32)?, k8(p, 64)?);
            for _ in 0..n { x = k8_mul(x, y); }
            x == want
        }
        4 => {
            let (mut x, s, want) = (qm31(p, 0)?, m31(p, 16)?, qm31(p, 20)?);
            for _ in 0..n { x = x.mul_m31(s); }
            x == want
        }
        5 => {
            let (mut x, s, want) = (k6(p, 0)?, m31(p, 24)?, k6(p, 28)?);
            for _ in 0..n { x = [x[0].mul_m31(s), x[1].mul_m31(s), x[2].mul_m31(s)]; }
            x == want
        }
        6 => {
            let (mut x, s, want) = (k8(p, 0)?, m31(p, 32)?, k8(p, 36)?);
            for _ in 0..n { x = [x[0].mul_m31(s), x[1].mul_m31(s)]; }
            x == want
        }
        7 => {
            let (mut x, y, want) = (qm31(p, 0)?, qm31(p, 16)?, qm31(p, 32)?);
            for _ in 0..n { x = x.inv().add(y); }
            x == want
        }
        8 => {
            let (mut x, y, want) = (k8(p, 0)?, k8(p, 32)?, k8(p, 64)?);
            for _ in 0..n {
                let inverse = k8_inv(x);
                x = [inverse[0].add(y[0]), inverse[1].add(y[1])];
            }
            x == want
        }
        _ => return None,
    })
}

type Digest = [u8; 26];
fn digest(parts: &[&[u8]]) -> Digest {
    let full = solana_program::hash::hashv(parts).to_bytes();
    let mut out = [0u8; 26];
    out.copy_from_slice(&full[..26]);
    out
}

/// Two eight-way depth-six trees with shared topology; leaf inputs are hashed
/// here.  Same walk as the R101 arity-8 pilot, with the entry limit at 32.
fn authenticate(q: usize, p: &[u8]) -> Option<bool> {
    const ARITY: usize = 8;
    const DEPTH: u32 = 6;
    let (w1, w2, nodes) = (word(p, 0)? as usize, word(p, 4)? as usize, word(p, 8)? as usize);
    let root1: Digest = p.get(12..38)?.try_into().ok()?;
    let root2: Digest = p.get(38..64)?.try_into().ok()?;
    let record = 4 + w1 + w2;
    if q == 0 || q > 32 || p.len() != 64 + q * record + 52 * nodes {
        return Some(false);
    }
    let mut level: Vec<(u32, Digest, Digest)> = Vec::with_capacity(q);
    for k in 0..q {
        let at = 64 + k * record;
        level.push((
            word(p, at)?,
            digest(&[&p[at + 4..at + 4 + w1]]),
            digest(&[&p[at + 4 + w1..at + record]]),
        ));
    }
    if level.windows(2).any(|pair| pair[0].0 >= pair[1].0) || level[q - 1].0 >= 1 << 18 {
        return Some(false);
    }
    let start = 64 + q * record;
    let (f1, f2) = (&p[start..start + 26 * nodes], &p[start + 26 * nodes..]);
    let tag = [0x18u8];
    let mut at = 0usize;
    for _ in 0..DEPTH {
        let (mut read, mut write) = (0usize, 0usize);
        while read < level.len() {
            let parent = level[read].0 >> 3;
            let first = parent << 3;
            let mut p1: [&[u8]; 9] = [&[]; 9];
            let mut p2 = p1;
            p1[0] = &tag;
            p2[0] = &tag;
            for slot in 0..ARITY {
                if read < level.len() && level[read].0 == first + slot as u32 {
                    p1[slot + 1] = &level[read].1;
                    p2[slot + 1] = &level[read].2;
                    read += 1;
                } else {
                    if at + 26 > f1.len() { return Some(false); }
                    p1[slot + 1] = &f1[at..at + 26];
                    p2[slot + 1] = &f2[at..at + 26];
                    at += 26;
                }
            }
            let (h1, h2) = (digest(&p1), digest(&p2));
            level[write] = (parent, h1, h2);
            write += 1;
        }
        level.truncate(write);
    }
    Some(at == f1.len() && level.len() == 1 && level[0].0 == 0 && level[0].1 == root1 && level[0].2 == root2)
}

fn entry(program: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if account.owner != program || account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    let bytes = account.try_borrow_data()?;
    if bytes.len() < 12 || &bytes[..4] != b"SCRN" {
        return Err(ProgramError::InvalidAccountData);
    }
    let op = bytes[4];
    let n = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let ok = if op == 10 { authenticate(n as usize, &bytes[12..]) } else { kernels(op, n, &bytes[12..]) };
    match ok {
        Some(true) => Ok(()),
        Some(false) => Err(ProgramError::Custom(2)),
        None => Err(ProgramError::Custom(1)),
    }
}
