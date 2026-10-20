//! Kani-only, same-crate reference of records; compiled only by proof builds.
use super::*;
use super::super::{
    pair_trace::PoolV1PairInputNoteWitnessV1,
    pair_tree_profile::PoolV1PairLeafWitnessV1,
    payment_relation::PoolV1MembershipWitnessV1,
};

fn records_reference(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
    let input = *input;
    let chg = *chg;
    let snapshot = *snapshot;
    let rec = rec.copied();
    let pair = input.pair;
    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
    let mut bits = [0u32; 24];
    let mut sibs = [[0u32; 8]; 24];
    for level in 0..24 {
        let (bit, sib) = if level == 0 {
            (u32::from(pair.selected_second), other)
        } else if level <= 20 {
            (((pair.membership.index >> (level - 1)) & 1) as u32, pair.membership.siblings[level - 1])
        } else {
            (u32::from(input.super_root_directions[level - 21]), input.super_root_siblings[level - 21])
        };
        bits[level] = bit;
        sibs[level] = raw(&sib);
    }
    let empty = pair_empty_roots();
    let w = RW {
        input_value: pair.value,
        output_value: out,
        change_value: chg.value,
        sk: raw(&pair.nullifier_key),
        salt: raw(&pair.salt),
        bits,
        sibs,
        pair_first: raw(&pair.pair_leaf.first_commitment),
        pair_occupied: pair.pair_leaf.second_occupied.0,
        pair_second: raw(&pair.pair_leaf.second_commitment),
        pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
        recipient_owner: rec.map(|r| raw(&r.owner_key)).unwrap_or(ZERO8),
        recipient_salt: rec.map(|r| raw(&r.salt)).unwrap_or(ZERO8),
        change_owner: raw(&chg.owner_key),
        change_salt: raw(&chg.salt),
    };
    let p = RP {
        transfer: rec.is_some(),
        asset: asset.0,
        next_pair_index: snapshot.next_pair_index,
        frontier: core::array::from_fn(|l| raw(&snapshot.frontier[l])),
        empty: core::array::from_fn(|l| raw(&empty[l])),
    };
    (w, p)
}

fn any_digest() -> Digest { kani::any::<[u32; 8]>().map(M31) }
fn any_output() -> PoolV1OutputNoteWitnessV1 {
    PoolV1OutputNoteWitnessV1 { owner_key: any_digest(), salt: any_digest(), value: kani::any() }
}

#[kani::proof]
#[kani::unwind(25)]
fn records_equal_copied_reference() {
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: any_digest(), salt: any_digest(), value: kani::any(),
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: any_digest(), second_occupied: M31(kani::any()),
                second_commitment: any_digest(), second_occupancy_inverse: M31(kani::any()),
            },
            selected_second: kani::any(),
            membership: PoolV1MembershipWitnessV1 {
                siblings: kani::any::<[[u32; 8]; 20]>().map(|d| d.map(M31)), index: kani::any(),
            },
        },
        super_root_siblings: kani::any::<[[u32; 8]; 3]>().map(|d| d.map(M31)),
        super_root_directions: kani::any(),
    };
    let recipient = if kani::any() { Some(any_output()) } else { None };
    let change = any_output();
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
        next_pair_index: kani::any(), current_root: any_digest(),
        frontier: kani::any::<[[u32; 8]; 20]>().map(|d| d.map(M31)),
    };
    let out = kani::any(); let asset = M31(kani::any());
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = records_reference(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    assert_eq!(w.input_value, v.input_value);
    assert_eq!(w.output_value, v.output_value);
    assert_eq!(w.change_value, v.change_value);
    assert_eq!(w.sk, v.sk);
    assert_eq!(w.salt, v.salt);
    assert_eq!(w.bits, v.bits);
    assert_eq!(w.sibs, v.sibs);
    assert_eq!(w.pair_first, v.pair_first);
    assert_eq!(w.pair_occupied, v.pair_occupied);
    assert_eq!(w.pair_second, v.pair_second);
    assert_eq!(w.pair_inverse, v.pair_inverse);
    assert_eq!(w.recipient_owner, v.recipient_owner);
    assert_eq!(w.recipient_salt, v.recipient_salt);
    assert_eq!(w.change_owner, v.change_owner);
    assert_eq!(w.change_salt, v.change_salt);
    assert_eq!(p.transfer, q.transfer);
    assert_eq!(p.asset, q.asset);
    assert_eq!(p.next_pair_index, q.next_pair_index);
    assert_eq!(p.frontier, q.frontier);
    assert_eq!(p.empty, q.empty);
}

// Relational abstraction: both mappers call the identical pure, zero-argument
// helper. One shared arbitrary return table covers every possible normal
// result, so this harness checks the mapper without unrolling fixed hashes.
static mut SHARED_ROOTS: [Digest; 21] = [[M31::ZERO; 8]; 21];
fn shared_roots() -> [Digest; 21] { unsafe { SHARED_ROOTS } }

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_equal_parametric_roots() {
    unsafe { SHARED_ROOTS = kani::any::<[[u32; 8]; 21]>().map(|d| d.map(M31)); }
    records_equal_copied_reference();
}
