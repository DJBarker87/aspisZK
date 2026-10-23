//! Extraction-friendly copies of the honest builder's Poseidon-block writers
//! (t2b2b/DESIGN-BUILDER-MODEL.txt §10), with the permutation ABSTRACT: every
//! writer takes the eleven odd-round outputs of its permutation (`rounds`) as
//! an input instead of computing them.  Production originals (read-only,
//! origin/codex/100bit-spend-path-20261013):
//!   write_permutation   crates/aspis-statement/src/pool_v1/pair_trace.rs:268-302
//!   write_sponge        crates/aspis-statement/src/pool_v1/pair_trace.rs:304-354
//!   write_node          crates/aspis-statement/src/pool_v1/pair_trace.rs:356-366
//!   write_forest_node   crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:161-195
//!   trace_digest / node_left / node_right (relocation read-back)
//!                       crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:120-140
//!   M31 add/sub         crates/aspis-core/src/field.rs:62-119 (non-audit branches)
//! A block is 16 rows x 16 lanes, row-major (index = local_row * 16 + lane):
//! row 0 = pre-absorption state, rows 1..11 = odd-round outputs, row 12 =
//! absorption (lanes the writer does not touch stay 0), rows 13..15 = 0.
#![no_std]

pub const P: u32 = 0x7fff_ffff;
pub const TWEAK: u32 = 0x4153_1005;
pub const BLOCK_CELLS: usize = 256;

/// M31 addition on canonical inputs.
pub fn m31_add(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= P {
        s - P
    } else {
        s
    }
}

/// M31 subtraction on canonical inputs.
pub fn m31_sub(a: u32, b: u32) -> u32 {
    let s = a + P - b;
    if s >= P {
        s - P
    } else {
        s
    }
}

/// Rows 1..11: the odd-round outputs.
pub fn write_block_rounds(block: [u32; BLOCK_CELLS], rounds: &[[u32; 16]; 11]) -> [u32; BLOCK_CELLS] {
    let mut block = block;
    let mut r: usize = 0;
    while r < 11 {
        let mut lane: usize = 0;
        while lane < 16 {
            block[(r + 1) * 16 + lane] = rounds[r][lane];
            lane += 1;
        }
        r += 1;
    }
    block
}

/// Rows 0 and 12: pre-state and absorption.
pub fn write_block_ends(block: [u32; BLOCK_CELLS], pre: &[u32; 16], absorb: &[u32; 16]) -> [u32; BLOCK_CELLS] {
    let mut block = block;
    let mut lane: usize = 0;
    while lane < 16 {
        block[lane] = pre[lane];
        block[192 + lane] = absorb[lane];
        lane += 1;
    }
    block
}

/// write_permutation's cells for one block.
pub fn write_block(pre: &[u32; 16], absorb: &[u32; 16], rounds: &[[u32; 16]; 11]) -> [u32; BLOCK_CELLS] {
    let block = write_block_ends([0u32; BLOCK_CELLS], pre, absorb);
    write_block_rounds(block, rounds)
}

/// write_node's pre-state: [0^8, right[0..7), right[7] + tweak].
pub fn node_pre(right: &[u32; 8]) -> [u32; 16] {
    let mut pre = [0u32; 16];
    let mut lane: usize = 0;
    while lane < 8 {
        pre[8 + lane] = right[lane];
        lane += 1;
    }
    pre[15] = m31_add(right[7], TWEAK);
    pre
}

/// write_node's absorption: the left child in lanes 0..7.
pub fn node_absorb(left: &[u32; 8]) -> [u32; 16] {
    let mut absorb = [0u32; 16];
    let mut lane: usize = 0;
    while lane < 8 {
        absorb[lane] = left[lane];
        lane += 1;
    }
    absorb
}

/// write_node / write_forest_node.
pub fn write_node(left: &[u32; 8], right: &[u32; 8], rounds: &[[u32; 16]; 11]) -> [u32; BLOCK_CELLS] {
    write_block(&node_pre(right), &node_absorb(left), rounds)
}

/// hash_fields_with_trace's initial state: lane 8 = domain, lane 9 = length.
pub fn sponge_init(domain: u32, len: u32) -> [u32; 16] {
    let mut state = [0u32; 16];
    state[8] = domain;
    state[9] = len;
    state
}

/// write_sponge's absorption for one chunk of `len` (<= 8) words.
pub fn sponge_absorb(chunk: &[u32; 8], len: usize) -> [u32; 16] {
    let mut absorb = [0u32; 16];
    let mut lane: usize = 0;
    while lane < 8 {
        if lane < len {
            absorb[lane] = chunk[lane];
        }
        lane += 1;
    }
    absorb
}

/// write_sponge for one permutation: the pre-state is the running state
/// (transition.input minus the absorbed chunk, pair_trace.rs:329-335).
pub fn write_sponge_block(state: &[u32; 16], chunk: &[u32; 8], len: usize, rounds: &[[u32; 16]; 11]) -> [u32; BLOCK_CELLS] {
    write_block(state, &sponge_absorb(chunk, len), rounds)
}

/// Words 8p..8p+7 of the (zero-padded) sponge input.
pub fn sponge_chunk(input: &[u32; 24], p: usize) -> [u32; 8] {
    let mut chunk = [0u32; 8];
    let mut lane: usize = 0;
    while lane < 8 {
        chunk[lane] = input[8 * p + lane];
        lane += 1;
    }
    chunk
}

/// Place one 256-cell block at block offset p of a 3-block buffer.
pub fn place_block(out: [u32; 3 * BLOCK_CELLS], p: usize, block: &[u32; BLOCK_CELLS]) -> [u32; 3 * BLOCK_CELLS] {
    let mut out = out;
    let mut i: usize = 0;
    while i < BLOCK_CELLS {
        out[p * BLOCK_CELLS + i] = block[i];
        i += 1;
    }
    out
}

/// write_sponge (pair_trace.rs:304-354) for 1 <= len <= 24 input words:
/// ceil(len/8) consecutive blocks; the running state after permutation p is
/// its final odd-round output rounds[p][10] (the permutation is abstract).
pub fn write_sponge(domain: u32, input: &[u32; 24], len: usize, rounds: &[[[u32; 16]; 11]; 3]) -> [u32; 3 * BLOCK_CELLS] {
    let mut out = [0u32; 3 * BLOCK_CELLS];
    let mut state = sponge_init(domain, len as u32);
    let perms = (len + 7) / 8;
    let mut p: usize = 0;
    while p < perms {
        let chunk = sponge_chunk(input, p);
        let clen = if len - 8 * p < 8 { len - 8 * p } else { 8 };
        let block = write_sponge_block(&state, &chunk, clen, &rounds[p]);
        out = place_block(out, p, &block);
        state = rounds[p][10];
        p += 1;
    }
    out
}

/// The relocation read-back of one level (pair_forest_trace.rs:216-224):
/// current = previous block row 11 lanes 0..7, left = node row 12 lanes 0..7,
/// right = node row 0 lanes 8..15 with the tweak removed from lane 7.
pub fn read_back(prev_row11: &[u32; 16], node_row0: &[u32; 16], node_row12: &[u32; 16]) -> ([u32; 8], [u32; 8], [u32; 8]) {
    let mut current = [0u32; 8];
    let mut left = [0u32; 8];
    let mut right = [0u32; 8];
    let mut lane: usize = 0;
    while lane < 8 {
        current[lane] = prev_row11[lane];
        left[lane] = node_row12[lane];
        right[lane] = if lane == 7 { m31_sub(node_row0[15], TWEAK) } else { node_row0[8 + lane] };
        lane += 1;
    }
    (current, left, right)
}
