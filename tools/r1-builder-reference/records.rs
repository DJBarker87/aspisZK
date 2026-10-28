//! Kani-only, same-crate reference of records; compiled only by proof builds.
use super::*;
use super::super::{
    pair_trace::PoolV1PairInputNoteWitnessV1,
    pair_tree_profile::PoolV1PairLeafWitnessV1,
    payment_relation::PoolV1MembershipWitnessV1,
};

// P6 proof-only compatibility: shipped records now takes the empty-root table explicitly.
// Preserve the historical proof helper convention without changing any shipped body.
fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
    super::records(input, out, rec, chg, snapshot, asset, pair_empty_roots())
}

fn records_reference(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
    super::records_reference::records_reference_with_roots(*input, out, rec.copied(), *chg, *snapshot, asset, pair_empty_roots())
}

fn any_digest() -> Digest { [M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any())] }

fn any_digests_3() -> [Digest; 3] { [any_digest(), any_digest(), any_digest()] }
fn any_digests_20() -> [Digest; 20] { [any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest()] }
fn any_digests_21() -> [Digest; 21] { [any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest(), any_digest()] }
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
                siblings: any_digests_20(), index: kani::any(),
            },
        },
        super_root_siblings: any_digests_3(),
        super_root_directions: kani::any(),
    };
    let recipient = if kani::any() { Some(any_output()) } else { None };
    let change = any_output();
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
        next_pair_index: kani::any(), current_root: any_digest(),
        frontier: any_digests_20(),
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
    unsafe { SHARED_ROOTS = any_digests_21(); }
    records_equal_copied_reference();
}

// Continuation 3: small universal projections, replacing the whole-record jobs.
fn arbitrary_records() -> (RW, RP, RW, RP) {
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: any_digest(), salt: any_digest(), value: kani::any(),
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: any_digest(), second_occupied: M31(kani::any()),
                second_commitment: any_digest(), second_occupancy_inverse: M31(kani::any()),
            },
            selected_second: kani::any(),
            membership: PoolV1MembershipWitnessV1 {
                siblings: any_digests_20(), index: kani::any(),
            },
        },
        super_root_siblings: any_digests_3(),
        super_root_directions: kani::any(),
    };
    let recipient = if kani::any() { Some(any_output()) } else { None };
    let change = any_output();
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
        next_pair_index: kani::any(), current_root: any_digest(),
        frontier: any_digests_20(),
    };
    let out = kani::any(); let asset = M31(kani::any());
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = records_reference(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    (w, p, v, q)
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_path_bit() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); kani::assume(level < 24);
    assert_eq!(w.bits[level], v.bits[level]);
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_path_sibling() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 24 && lane < 8);
    assert_eq!(w.sibs[level][lane], v.sibs[level][lane]);
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_scalars() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    assert_eq!(w.input_value, v.input_value);
    assert_eq!(w.output_value, v.output_value);
    assert_eq!(w.change_value, v.change_value);
    assert_eq!(w.pair_occupied, v.pair_occupied);
    assert_eq!(w.pair_inverse, v.pair_inverse);
    assert_eq!(p.transfer, q.transfer);
    assert_eq!(p.asset, q.asset);
    assert_eq!(p.next_pair_index, q.next_pair_index);
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_digest_cell() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let lane: usize = kani::any(); kani::assume(lane < 8);
    assert_eq!(w.sk[lane], v.sk[lane]);
    assert_eq!(w.salt[lane], v.salt[lane]);
    assert_eq!(w.pair_first[lane], v.pair_first[lane]);
    assert_eq!(w.pair_second[lane], v.pair_second[lane]);
    assert_eq!(w.recipient_owner[lane], v.recipient_owner[lane]);
    assert_eq!(w.recipient_salt[lane], v.recipient_salt[lane]);
    assert_eq!(w.change_owner[lane], v.change_owner[lane]);
    assert_eq!(w.change_salt[lane], v.change_salt[lane]);
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
fn records_public_cell() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    assert_eq!(p.frontier[level][lane], q.frontier[level][lane]);
    assert_eq!(p.empty[level][lane], q.empty[level][lane]);
}

// Exact callee replacement, proved separately before use in caller proofs.
fn raw_reference(d: &Digest) -> [u32; 8] {
    [d[0].0, d[1].0, d[2].0, d[3].0, d[4].0, d[5].0, d[6].0, d[7].0]
}

#[kani::proof]
#[kani::unwind(9)]
fn raw_shipped_equals_reference() {
    let d = any_digest();
    let lane: usize = kani::any();
    kani::assume(lane < 8);
    assert_eq!(raw(&d)[lane], raw_reference(&d)[lane]);
}

// These static projections split the timed-out symbolic-index path proof.
// The raw stub is the exact implementation established by the preceding leaf.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_selected_bit() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, _, v, _) = arbitrary_records();
    assert_eq!(w.bits[0], v.bits[0]);
}

fn arbitrary_inputs() -> (PoolV1PairForestInputNoteWitnessV1, u32, Option<PoolV1OutputNoteWitnessV1>, PoolV1OutputNoteWitnessV1, PoolV1PairLiveSnapshotV1, M31) {
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: any_digest(), salt: any_digest(), value: kani::any(),
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: any_digest(), second_occupied: M31(kani::any()),
                second_commitment: any_digest(), second_occupancy_inverse: M31(kani::any()),
            },
            selected_second: kani::any(),
            membership: PoolV1MembershipWitnessV1 {
                siblings: any_digests_20(), index: kani::any(),
            },
        },
        super_root_siblings: any_digests_3(),
        super_root_directions: kani::any(),
    };
    let recipient = if kani::any() { Some(any_output()) } else { None };
    let change = any_output();
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
        next_pair_index: kani::any(), current_root: any_digest(),
        frontier: any_digests_20(),
    };
    let out = kani::any(); let asset = M31(kani::any());
    (input, out, recipient, change, snapshot, asset)
}

#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_selected_bit_direct_small_inputs() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    let (w, _) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    assert_eq!(w.bits[0], u32::from(input.pair.selected_second));
}


// Scalar projection on the extracted owned reference, with straight-line arbitrary inputs.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_path_bit_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); kani::assume(level < 24);
    assert_eq!(w.bits[level], v.bits[level]);
}


// Scalar projection on the extracted owned reference, with straight-line arbitrary inputs.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_path_sibling_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 24 && lane < 8);
    assert_eq!(w.sibs[level][lane], v.sibs[level][lane]);
}


// Scalar projection on the extracted owned reference, with straight-line arbitrary inputs.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_scalars_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    assert_eq!(w.input_value, v.input_value);
    assert_eq!(w.output_value, v.output_value);
    assert_eq!(w.change_value, v.change_value);
    assert_eq!(w.pair_occupied, v.pair_occupied);
    assert_eq!(w.pair_inverse, v.pair_inverse);
    assert_eq!(p.transfer, q.transfer);
    assert_eq!(p.asset, q.asset);
    assert_eq!(p.next_pair_index, q.next_pair_index);
}


// Scalar projection on the extracted owned reference, with straight-line arbitrary inputs.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_digest_cell_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let lane: usize = kani::any(); kani::assume(lane < 8);
    assert_eq!(w.sk[lane], v.sk[lane]);
    assert_eq!(w.salt[lane], v.salt[lane]);
    assert_eq!(w.pair_first[lane], v.pair_first[lane]);
    assert_eq!(w.pair_second[lane], v.pair_second[lane]);
    assert_eq!(w.recipient_owner[lane], v.recipient_owner[lane]);
    assert_eq!(w.recipient_salt[lane], v.recipient_salt[lane]);
    assert_eq!(w.change_owner[lane], v.change_owner[lane]);
    assert_eq!(w.change_salt[lane], v.change_salt[lane]);
}


// Scalar projection on the extracted owned reference, with straight-line arbitrary inputs.
#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_public_cell_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    assert_eq!(p.frontier[level][lane], q.frontier[level][lane]);
    assert_eq!(p.empty[level][lane], q.empty[level][lane]);
}

// Final leaf pin with the straight-line arbitrary-input constructor.
#[kani::proof]
#[kani::unwind(9)]
fn raw_word_shipped_equals_reference() {
    let d = any_digest();
    let lane: usize = kani::any();
    kani::assume(lane < 8);
    assert_eq!(raw(&d)[lane], raw_reference(&d)[lane]);
}


#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_public_frontier_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    assert_eq!(p.frontier[level][lane], q.frontier[level][lane]);
}


#[kani::proof]
#[kani::unwind(25)]
#[kani::stub(crate::pool_v1::pair_trace::pair_empty_roots, shared_roots)]
#[kani::stub(crate::pool_v1::pair_forest_copy_builder::raw, raw_reference)]
fn records_public_empty_indexed_reference() {
    unsafe { SHARED_ROOTS = any_digests_21(); }
    let (w, p, v, q) = arbitrary_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    assert_eq!(p.empty[level][lane], q.empty[level][lane]);
}

// Continuation 4: each leaf has its own unstubbed proof.
#[path = "glue_leaves.rs"]
mod glue_leaves;

#[path = "empty_roots.rs"]
mod empty_roots;

#[path = "glue_tree.rs"]
mod glue_tree;

#[path = "glue_append.rs"]
mod glue_append;

// PV_Src audit: the mapper has no value-range precondition. This deliberately
// checks the over-general WitnessOk postcondition on a concrete boundary value.
// No stubs: the actual shipped mapper, including pair_empty_roots, executes.
#[kani::proof]
#[kani::unwind(25)]
fn pv_src_words_range_counterexample() {
    let z = [M31::ZERO; 8];
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: z, salt: z, value: 0,
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: z, second_occupied: M31::ZERO,
                second_commitment: z, second_occupancy_inverse: M31::ZERO,
            },
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 { siblings: [z; 20], index: 0 },
        },
        super_root_siblings: [z; 3], super_root_directions: [false; 3],
    };
    let change = PoolV1OutputNoteWitnessV1 { owner_key: z, salt: z, value: 0 };
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: [0; 32], deployment_domain: [0; 32], sequence: 0,
        next_pair_index: 0, current_root: z, frontier: [z; 20],
    };
    let (w, _) = records(&input, 1 << 30, None, &change, &snapshot, M31::ZERO);
    assert_eq!(w.output_value, 1 << 30);
    assert!(w.output_value < (1 << 30), "PV_Src words is not an unconditional mapper law");
}

// Continuation 5: all-field P6 with the actual root helper and no stubs.
#[path = "pv_srcid3.rs"]
mod pv_srcid3;

// RunJoin12: fixture-shaped unstubbed shipped/reference association.
#[path = "pv_runjoin12.rs"]
mod pv_runjoin12;

#[path = "pv_runjoin12_exact.rs"]
mod pv_runjoin12_exact;

#[path = "pv_runjoin12_raw.rs"]
mod pv_runjoin12_raw;
