//! Native differential tests for the Poseidon-block writer copies
//! (refine/blockwriters): the copies take the permutation's odd-round outputs
//! as an input; here they are produced by the production permutation
//! `permute_optimized_with_trace` (the abstract Poseidon parameter, instantiated).
use aspis_core::field::{M31, P};
use aspis_r0_block_writer_copies as bw;
use aspis_statement::{
    poseidon2::{permute_optimized_with_trace, Digest},
    pool_v1::{
        pair_forest_trace::diff_write_forest_node,
        pair_trace::{diff_write_node, diff_write_permutation, diff_write_sponge},
    },
};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn m31(&mut self) -> u32 {
        (self.next() % P as u64) as u32
    }
    fn digest(&mut self) -> Digest {
        core::array::from_fn(|_| M31(self.m31()))
    }
    fn state(&mut self) -> [M31; 16] {
        core::array::from_fn(|_| M31(self.m31()))
    }
}

fn empty() -> [Vec<M31>; 16] {
    core::array::from_fn(|_| vec![M31(0); 1024])
}

fn raw8(d: &Digest) -> [u32; 8] {
    core::array::from_fn(|i| d[i].0)
}

fn raw16(s: &[M31; 16]) -> [u32; 16] {
    core::array::from_fn(|i| s[i].0)
}

/// The abstract Poseidon parameter, instantiated by production: the eleven
/// odd-round outputs of permuting `input`, and the final state.
fn rounds_of(input: [M31; 16]) -> ([[u32; 16]; 11], [M31; 16]) {
    let mut state = input;
    let mut out = [[0u32; 16]; 11];
    permute_optimized_with_trace(&mut state, |t| {
        if t.round & 1 == 1 {
            out[usize::from(t.round) / 2] = raw16(&t.output);
        }
    });
    (out, state)
}

fn block_matches(cols: &[Vec<M31>; 16], block: usize, cells: &[u32]) -> bool {
    for r in 0..16 {
        for c in 0..16 {
            if cols[c][block * 16 + r].0 != cells[r * 16 + c] {
                return false;
            }
        }
    }
    true
}

fn add(a: [M31; 16], b: &[u32; 16]) -> [M31; 16] {
    core::array::from_fn(|i| a[i].add(M31(b[i])))
}

#[test]
fn m31_ops_match() {
    let mut rng = Rng(0x2468_ace0_1357_9bdf);
    let edge = [0u32, 1, P - 1, bw::TWEAK, P - bw::TWEAK, 1 << 30];
    for i in 0..1_000_000u64 {
        let (a, b) = if i < 36 { (edge[(i % 6) as usize], edge[(i / 6) as usize]) } else { (rng.m31(), rng.m31()) };
        assert_eq!(M31(a).add(M31(b)).0, bw::m31_add(a, b));
        assert_eq!(M31(a).sub(M31(b)).0, bw::m31_sub(a, b));
    }
    println!("m31_ops_match: 1000000 pairs");
}

#[test]
fn permutation_writer_matches() {
    let mut rng = Rng(0x1111_2222_3333_4444);
    for _ in 0..20_000u64 {
        let block = (rng.next() % 54) as usize;
        let pre = rng.state();
        let absorption: [M31; 8] = core::array::from_fn(|_| M31(rng.m31()));
        let mut cols = empty();
        diff_write_permutation(&mut cols, block, pre, absorption).unwrap();
        let mut abs16 = [0u32; 16];
        for i in 0..8 {
            abs16[i] = absorption[i].0;
        }
        let (rounds, _) = rounds_of(add(pre, &abs16));
        let cells = bw::write_block(&raw16(&pre), &abs16, &rounds);
        assert!(block_matches(&cols, block, &cells));
    }
    println!("permutation_writer_matches: 20000 cases");
}

#[test]
fn node_writers_match() {
    let mut rng = Rng(0x5555_6666_7777_8888);
    for i in 0..20_000u64 {
        let (l, r) = (rng.digest(), rng.digest());
        let mut cols = empty();
        let forest = i % 2 == 1;
        let block = if forest { 54 + (rng.next() % 3) as usize } else { (rng.next() % 54) as usize };
        let digest = if forest {
            diff_write_forest_node(&mut cols, block, l, r).unwrap()
        } else {
            diff_write_node(&mut cols, block, l, r).unwrap()
        };
        let pre = bw::node_pre(&raw8(&r));
        let abs = bw::node_absorb(&raw8(&l));
        let input: [M31; 16] = core::array::from_fn(|k| M31(pre[k]).add(M31(abs[k])));
        let (rounds, fin) = rounds_of(input);
        let cells = bw::write_node(&raw8(&l), &raw8(&r), &rounds);
        assert!(block_matches(&cols, block, &cells));
        assert_eq!(raw8(&digest), core::array::from_fn::<u32, 8, _>(|k| fin[k].0));
        // read-back of the relocation: the previous block's digest, left, right
        let prev: [u32; 16] = core::array::from_fn(|_| rng.m31());
        let row0: [u32; 16] = core::array::from_fn(|c| cols[c][block * 16].0);
        let row12: [u32; 16] = core::array::from_fn(|c| cols[c][block * 16 + 12].0);
        let (cur, left, right) = bw::read_back(&prev, &row0, &row12);
        assert_eq!(cur, core::array::from_fn::<u32, 8, _>(|k| prev[k]));
        assert_eq!(left, raw8(&l));
        assert_eq!(right, raw8(&r));
    }
    println!("node_writers_match: 20000 cases (half forest), read_back included");
}

#[test]
fn sponge_writer_matches() {
    let mut rng = Rng(0x9999_aaaa_bbbb_cccc);
    for i in 0..20_000u64 {
        let len = 1 + (i % 24) as usize;
        let domain = rng.m31();
        let words: Vec<M31> = (0..len).map(|_| M31(rng.m31())).collect();
        let start = (rng.next() % 52) as usize;
        let mut cols = empty();
        let digest = diff_write_sponge(&mut cols, start, M31(domain), &words).unwrap();
        // the abstract permutation, instantiated as in hash_fields_with_trace
        let mut input = [0u32; 24];
        for k in 0..len {
            input[k] = words[k].0;
        }
        let mut rounds = [[[0u32; 16]; 11]; 3];
        let mut state = [M31(0); 16];
        state[8] = M31(domain);
        state[9] = M31(len as u32);
        let perms = len.div_ceil(8);
        for p in 0..perms {
            for k in 0..8 {
                if 8 * p + k < len {
                    state[k] = state[k].add(M31(input[8 * p + k]));
                }
            }
            let (r, fin) = rounds_of(state);
            rounds[p] = r;
            state = fin;
        }
        let cells = bw::write_sponge(domain, &input, len, &rounds);
        for p in 0..3 {
            assert!(block_matches(&cols, start + p, &cells[p * 256..(p + 1) * 256]));
        }
        assert_eq!(raw8(&digest), core::array::from_fn::<u32, 8, _>(|k| state[k].0));
    }
    println!("sponge_writer_matches: 20000 cases, len 1..24");
}
