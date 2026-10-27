//! Prover-local public byte carrier and selected terminal wrapper.
use alloc::vec::Vec;
use aspis_core::{
    field::{M31, QM31},
    state_only_prefix::r0::{Challenges, Error},
};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
#[derive(Clone, Copy)]
pub struct OwnedPublic {
    pub withdrawal: bool,
    pub anchor: [u32; 8],
    pub nullifier: [u32; 8],
    pub asset_id: u32,
    pub recipient: [u32; 8],
    pub change: [u32; 8],
    pub withdrawal_amount: u32,
    pub next_pair_index: u64,
    pub frontier: [[u32; 8]; 20],
    pub next_root: [u32; 8],
    pub next_frontier: [[u32; 8]; 20],
}
#[inline(never)]
fn canonical(v: u32) -> Option<u32> {
    if v < 2147483647 {
        Some(v)
    } else {
        None
    }
}
#[inline(never)]
fn field_byte(v: u32, j: usize) -> Result<u8, Error> {
    let v = match canonical(v) {
        Some(v) => v,
        None => return Err(Error::Public),
    };
    Ok((v >> (8u32 * (j as u32))) as u8)
}
#[inline(never)]
fn byte_at(p: OwnedPublic, i: usize) -> Result<u8, Error> {
    if i == 0 {
        return Ok(if p.withdrawal { 1 } else { 0 });
    }
    if i < 33 {
        return field_byte(p.anchor[(i - 1) / 4], (i - 1) % 4);
    }
    if i < 65 {
        return field_byte(p.nullifier[(i - 33) / 4], (i - 33) % 4);
    }
    if i < 69 {
        return field_byte(p.asset_id, i - 65);
    }
    if i == 69 {
        return Ok(if p.withdrawal { 0 } else { 1 });
    }
    let change = if p.withdrawal { 70 } else { 102 };
    if i < change {
        return field_byte(p.recipient[(i - 70) / 4], (i - 70) % 4);
    }
    if i < change + 32 {
        return field_byte(p.change[(i - change) / 4], (i - change) % 4);
    }
    if i == change + 32 {
        return Ok(if p.withdrawal { 1 } else { 0 });
    }
    let index = if p.withdrawal { 107 } else { 135 };
    if i < index {
        return field_byte(p.withdrawal_amount, i - (change + 33));
    }
    if i < index + 8 {
        return Ok((p.next_pair_index >> (8u32 * ((i - index) as u32))) as u8);
    }
    let front = index + 8;
    if i < front + 640 {
        let j = i - front;
        return field_byte(p.frontier[j / 32][(j % 32) / 4], j % 4);
    }
    if i < front + 672 {
        let j = i - front - 640;
        return field_byte(p.next_root[j / 4], j % 4);
    }
    let j = i - front - 672;
    field_byte(p.next_frontier[j / 32][(j % 32) / 4], j % 4)
}
pub fn encode_owned(p: OwnedPublic) -> Result<([u8; 1455], usize), Error> {
    let n = if p.withdrawal { 1427 } else { 1455 };
    let mut out = [0u8; 1455];
    let mut i = 0usize;
    while i < n {
        out[i] = byte_at(p, i)?;
        i += 1;
    }
    Ok((out, n))
}

pub fn project(public: Public<'_>) -> OwnedPublic {
    let (withdrawal, anchor, nullifier, asset_id, recipient, change, withdrawal_amount, transition) =
        match public {
            Public::Transfer(p, t) => (
                false,
                p.anchor_root,
                p.nullifier,
                p.asset_id,
                p.recipient_commitment,
                p.change_commitment,
                0,
                *t,
            ),
            Public::Withdrawal(p, t) => (
                true,
                p.anchor_root,
                p.nullifier,
                p.asset_id,
                [M31::ZERO; 8],
                p.change_commitment,
                p.amount,
                *t,
            ),
        };
    let mut out = OwnedPublic {
        withdrawal,
        anchor: [0; 8],
        nullifier: [0; 8],
        asset_id: asset_id.0,
        recipient: [0; 8],
        change: [0; 8],
        withdrawal_amount,
        next_pair_index: transition.live_snapshot.next_pair_index,
        frontier: [[0; 8]; 20],
        next_root: [0; 8],
        next_frontier: [[0; 8]; 20],
    };
    let mut i = 0usize;
    while i < 8 {
        out.anchor[i] = anchor[i].0;
        out.nullifier[i] = nullifier[i].0;
        out.recipient[i] = recipient[i].0;
        out.change[i] = change[i].0;
        out.next_root[i] = transition.candidate_afterstate.next_root[i].0;
        i += 1;
    }
    let mut level = 0usize;
    while level < 20 {
        let mut i = 0usize;
        while i < 8 {
            out.frontier[level][i] = transition.live_snapshot.frontier[level][i].0;
            out.next_frontier[level][i] = transition.candidate_afterstate.next_frontier[level][i].0;
            i += 1;
        }
        level += 1;
    }
    out
}
pub fn public_bytes(public: Public<'_>) -> Result<([u8; 1455], usize), Error> {
    encode_owned(project(public))
}
pub fn materialize_public_bytes(public: Public<'_>) -> Result<Vec<u8>, Error> {
    let (bytes, len) = public_bytes(public)?;
    Ok(bytes[..len].to_vec())
}
pub fn terminal_qm31(
    public: Public<'_>,
    claims: &[[QM31; 29]; 3],
    alpha: &[QM31; 10],
    c: &Challenges,
) -> Result<QM31, Error> {
    let p = match public {
        Public::Transfer(p, t) => crate::host_terminal::r0::Public::Transfer(p, t),
        Public::Withdrawal(p, t) => crate::host_terminal::r0::Public::Withdrawal(p, t),
    };
    p.terminal_qm31(claims, alpha, c)
}
