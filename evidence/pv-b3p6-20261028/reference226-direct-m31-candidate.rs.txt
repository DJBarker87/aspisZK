//! Proof-only owned public-byte reference; never compiled into a release program.
//! Root and chunks have no loops or mutable-borrow output continuations.
use aspis_core::{state_only_prefix::r0::Error, field::M31};
use aspis_statement::pool_v1::{
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
    pair_tree_profile::PoolV1PairLatePublicStatementV1,
};

#[derive(Clone, Copy)]
pub enum Source {
    Transfer(PoolV1PrivateTransferPublicV1, PoolV1PairLatePublicStatementV1),
    Withdrawal(PoolV1WithdrawalPublicV1, PoolV1PairLatePublicStatementV1),
}
#[derive(Clone, Copy)]
pub struct OwnedPublic {
    pub withdrawal: bool,
    pub anchor: [M31; 8],
    pub nullifier: [M31; 8],
    pub asset_id: M31,
    pub recipient: [M31; 8],
    pub change: [M31; 8],
    pub withdrawal_amount: u32,
    pub next_pair_index: u64,
    pub frontier: [[M31; 8]; 20],
    pub next_root: [M31; 8],
    pub next_frontier: [[M31; 8]; 20],
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
fn field_byte(v: M31, j: usize) -> Result<u8, Error> {
    let v = match canonical(v.0) {
        Some(v) => v,
        None => return Err(Error::Public),
    };
    Ok((v >> (8u32 * (j as u32))) as u8)
}
#[inline(never)]
fn byte_at(p: OwnedPublic, i: usize) -> Result<u8, Error> {
    let n = if p.withdrawal { 1427 } else { 1455 };
    if i >= n { return Ok(0); }
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
        return field_byte(M31(p.withdrawal_amount), i - (change + 33));
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

#[inline(never)]
fn chunk8(p: OwnedPublic, base: usize) -> Result<[u8;8], Error> {
    Ok([
        byte_at(p, base + 0)?,
        byte_at(p, base + 1)?,
        byte_at(p, base + 2)?,
        byte_at(p, base + 3)?,
        byte_at(p, base + 4)?,
        byte_at(p, base + 5)?,
        byte_at(p, base + 6)?,
        byte_at(p, base + 7)?,
    ])
}
#[inline(never)]
fn chunk(p: OwnedPublic, base: usize) -> Result<[u8;64], Error> {
    let a0 = chunk8(p, base + 0)?;
    let a1 = chunk8(p, base + 8)?;
    let a2 = chunk8(p, base + 16)?;
    let a3 = chunk8(p, base + 24)?;
    let a4 = chunk8(p, base + 32)?;
    let a5 = chunk8(p, base + 40)?;
    let a6 = chunk8(p, base + 48)?;
    let a7 = chunk8(p, base + 56)?;
    Ok([
        a0[0], a0[1], a0[2], a0[3], a0[4], a0[5], a0[6], a0[7],
        a1[0], a1[1], a1[2], a1[3], a1[4], a1[5], a1[6], a1[7],
        a2[0], a2[1], a2[2], a2[3], a2[4], a2[5], a2[6], a2[7],
        a3[0], a3[1], a3[2], a3[3], a3[4], a3[5], a3[6], a3[7],
        a4[0], a4[1], a4[2], a4[3], a4[4], a4[5], a4[6], a4[7],
        a5[0], a5[1], a5[2], a5[3], a5[4], a5[5], a5[6], a5[7],
        a6[0], a6[1], a6[2], a6[3], a6[4], a6[5], a6[6], a6[7],
        a7[0], a7[1], a7[2], a7[3], a7[4], a7[5], a7[6], a7[7],
    ])
}

pub fn encode_owned(p: OwnedPublic) -> Result<([[u8;64];23], usize), Error> {
    let n = if p.withdrawal { 1427 } else { 1455 };
    Ok(([
        chunk(p, 0)?,
        chunk(p, 64)?,
        chunk(p, 128)?,
        chunk(p, 192)?,
        chunk(p, 256)?,
        chunk(p, 320)?,
        chunk(p, 384)?,
        chunk(p, 448)?,
        chunk(p, 512)?,
        chunk(p, 576)?,
        chunk(p, 640)?,
        chunk(p, 704)?,
        chunk(p, 768)?,
        chunk(p, 832)?,
        chunk(p, 896)?,
        chunk(p, 960)?,
        chunk(p, 1024)?,
        chunk(p, 1088)?,
        chunk(p, 1152)?,
        chunk(p, 1216)?,
        chunk(p, 1280)?,
        chunk(p, 1344)?,
        chunk(p, 1408)?,
    ], n))
}

pub fn project(public: Source) -> OwnedPublic {
    let (withdrawal, anchor, nullifier, asset_id, recipient, change, withdrawal_amount, transition) =
        match public {
            Source::Transfer(p, t) => (
                false,
                p.anchor_root,
                p.nullifier,
                p.asset_id,
                p.recipient_commitment,
                p.change_commitment,
                0,
                t,
            ),
            Source::Withdrawal(p, t) => (
                true,
                p.anchor_root,
                p.nullifier,
                p.asset_id,
                [M31::ZERO; 8],
                p.change_commitment,
                p.amount,
                t,
            ),
        };
    OwnedPublic {
        withdrawal, anchor, nullifier, asset_id, recipient, change,
        withdrawal_amount,
        next_pair_index: transition.live_snapshot.next_pair_index,
        frontier: transition.live_snapshot.frontier,
        next_root: transition.candidate_afterstate.next_root,
        next_frontier: transition.candidate_afterstate.next_frontier,
    }
}


pub fn public_bytes(source: Source) -> Result<([[u8;64];23], usize), Error> {
    encode_owned(project(source))
}
