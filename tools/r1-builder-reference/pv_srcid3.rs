//! Unstubbed P6 obligations. This module is reachable only through cfg(kani).
//! The shipped side executes pair_empty_roots; the reference uses the pinned
//! frozen table checked by the retained 21 unstubbed fixed-input leaves. No arbitrary table,
//! function replacement, assumption of output equality, or disabled unwind gate.
use super::*;

fn actual_and_reference() -> (RW, RP, RW, RP) {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let empty = super::empty_roots::pv_srcid3_frozen_roots();
    let (v, q) = super::super::records_reference::records_reference_with_roots(
        input, out, recipient, change, snapshot, asset, empty);
    (w, p, v, q)
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_full_mapper() {
    let (w,p,v,q) = actual_and_reference();
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.sk,v.sk); assert_eq!(w.salt,v.salt);
    assert_eq!(w.bits,v.bits); assert_eq!(w.sibs,v.sibs);
    assert_eq!(w.pair_first,v.pair_first); assert_eq!(w.pair_occupied,v.pair_occupied);
    assert_eq!(w.pair_second,v.pair_second); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(w.recipient_owner,v.recipient_owner); assert_eq!(w.recipient_salt,v.recipient_salt);
    assert_eq!(w.change_owner,v.change_owner); assert_eq!(w.change_salt,v.change_salt);
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
    assert_eq!(p.frontier,q.frontier); assert_eq!(p.empty,q.empty);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_mapper_values() {
    let (w,p,v,q) = actual_and_reference();
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.pair_occupied,v.pair_occupied); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_mapper_path() {
    let (w,_,v,_) = actual_and_reference();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 24 && lane < 8);
    assert_eq!(w.bits[level],v.bits[level]);
    assert_eq!(w.sibs[level][lane],v.sibs[level][lane]);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_mapper_digests() {
    let (w,_,v,_) = actual_and_reference();
    let lane: usize = kani::any(); kani::assume(lane < 8);
    assert_eq!(w.sk[lane],v.sk[lane]); assert_eq!(w.salt[lane],v.salt[lane]);
    assert_eq!(w.pair_first[lane],v.pair_first[lane]); assert_eq!(w.pair_second[lane],v.pair_second[lane]);
    assert_eq!(w.recipient_owner[lane],v.recipient_owner[lane]); assert_eq!(w.recipient_salt[lane],v.recipient_salt[lane]);
    assert_eq!(w.change_owner[lane],v.change_owner[lane]); assert_eq!(w.change_salt[lane],v.change_salt[lane]);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_mapper_public() {
    let (_,p,_,q) = actual_and_reference();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    assert_eq!(p.frontier[level][lane],q.frontier[level][lane]);
    assert_eq!(p.empty[level][lane],q.empty[level][lane]);
}

fn checked_common() -> (PoolV1PairForestInputNoteWitnessV1, bool) {
    use crate::pool_v1::{PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1};
    let (input, _, _, _, snapshot, asset) = arbitrary_inputs();
    let nullifier = any_digest();
    let binding = PoolV1PaymentRuntimeBindingV1 {
        pool: snapshot.pool, deployment_domain: snapshot.deployment_domain,
        anchor_sequence: snapshot.sequence, anchor_root: snapshot.current_root, asset_id: asset,
    };
    let context = PoolV1PaymentRelationContextV1 { runtime_binding: binding, spent_nullifiers: &[] };
    let success = crate::pool_v1::pair_trace::validate_common(
        snapshot.pool, snapshot.deployment_domain, snapshot.sequence, snapshot.current_root,
        nullifier, asset, &input.pair, context).is_ok();
    (input, success)
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_common_values() {
    let (input, success) = checked_common();
    if success {
        assert!(input.pair.value > 0 && input.pair.value < (1 << 30));
        assert!(input.pair.membership.index < (1 << 20));
    }
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_common_sibling() {
    let (input, success) = checked_common();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 20 && lane < 8);
    if success { assert!(input.pair.membership.siblings[level][lane].0 < P); }
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_common_pair_words() {
    let (input, success) = checked_common();
    let lane: usize = kani::any(); kani::assume(lane < 8);
    if success {
        assert!(input.pair.pair_leaf.first_commitment[lane].0 < P);
        assert!(input.pair.pair_leaf.second_commitment[lane].0 < P);
    }
}

// Resume: full source association for the dynamic extracted dictionary.
// Both sides execute the actual pure root helper. No fixed table, stubs,
// assumed output equality, or restricted input domain is used.
#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_full_dynamic_mapper() {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = super::records_reference(
        &input, out, recipient.as_ref(), &change, &snapshot, asset);
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.sk,v.sk); assert_eq!(w.salt,v.salt);
    assert_eq!(w.bits,v.bits); assert_eq!(w.sibs,v.sibs);
    assert_eq!(w.pair_first,v.pair_first); assert_eq!(w.pair_occupied,v.pair_occupied);
    assert_eq!(w.pair_second,v.pair_second); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(w.recipient_owner,v.recipient_owner); assert_eq!(w.recipient_salt,v.recipient_salt);
    assert_eq!(w.change_owner,v.change_owner); assert_eq!(w.change_salt,v.change_salt);
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
    assert_eq!(p.frontier,q.frontier); assert_eq!(p.empty,q.empty);
}

// Decomposition of the timed-out dynamic full gate, still without stubs.
fn dynamic_records() -> (RW, RP, RW, RP) {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = super::records_reference(
        &input, out, recipient.as_ref(), &change, &snapshot, asset);
    (w, p, v, q)
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_dynamic_transfer() {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    kani::assume(recipient.is_some());
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = super::records_reference(
        &input, out, recipient.as_ref(), &change, &snapshot, asset);
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.sk,v.sk); assert_eq!(w.salt,v.salt);
    assert_eq!(w.bits,v.bits); assert_eq!(w.sibs,v.sibs);
    assert_eq!(w.pair_first,v.pair_first); assert_eq!(w.pair_occupied,v.pair_occupied);
    assert_eq!(w.pair_second,v.pair_second); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(w.recipient_owner,v.recipient_owner); assert_eq!(w.recipient_salt,v.recipient_salt);
    assert_eq!(w.change_owner,v.change_owner); assert_eq!(w.change_salt,v.change_salt);
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
    assert_eq!(p.frontier,q.frontier); assert_eq!(p.empty,q.empty);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_dynamic_withdrawal() {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    kani::assume(recipient.is_none());
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = super::records_reference(
        &input, out, recipient.as_ref(), &change, &snapshot, asset);
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.sk,v.sk); assert_eq!(w.salt,v.salt);
    assert_eq!(w.bits,v.bits); assert_eq!(w.sibs,v.sibs);
    assert_eq!(w.pair_first,v.pair_first); assert_eq!(w.pair_occupied,v.pair_occupied);
    assert_eq!(w.pair_second,v.pair_second); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(w.recipient_owner,v.recipient_owner); assert_eq!(w.recipient_salt,v.recipient_salt);
    assert_eq!(w.change_owner,v.change_owner); assert_eq!(w.change_salt,v.change_salt);
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
    assert_eq!(p.frontier,q.frontier); assert_eq!(p.empty,q.empty);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_dynamic_witness() {
    let (w, p, v, q) = dynamic_records();
    assert_eq!(w.input_value,v.input_value);
    assert_eq!(w.output_value,v.output_value);
    assert_eq!(w.change_value,v.change_value);
    assert_eq!(w.sk,v.sk); assert_eq!(w.salt,v.salt);
    assert_eq!(w.bits,v.bits); assert_eq!(w.sibs,v.sibs);
    assert_eq!(w.pair_first,v.pair_first); assert_eq!(w.pair_occupied,v.pair_occupied);
    assert_eq!(w.pair_second,v.pair_second); assert_eq!(w.pair_inverse,v.pair_inverse);
    assert_eq!(w.recipient_owner,v.recipient_owner); assert_eq!(w.recipient_salt,v.recipient_salt);
    assert_eq!(w.change_owner,v.change_owner); assert_eq!(w.change_salt,v.change_salt);

}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_dynamic_public() {
    let (w, p, v, q) = dynamic_records();
    assert_eq!(p.transfer,q.transfer); assert_eq!(p.asset,q.asset);
    assert_eq!(p.next_pair_index,q.next_pair_index);
    assert_eq!(p.frontier,q.frontier); assert_eq!(p.empty,q.empty);
}

#[kani::proof]
#[kani::unwind(33)]
fn pv_srcid3_dynamic_path_cell() {
    let (w, p, v, q) = dynamic_records();
    let level: usize = kani::any(); let lane: usize = kani::any();
    kani::assume(level < 24 && lane < 8);
    assert_eq!(w.bits[level], v.bits[level]);
    assert_eq!(w.sibs[level][lane], v.sibs[level][lane]);
}
