//! Unstubbed P6 obligations. This module is reachable only through cfg(kani).
//! Both sides execute the shipped pair_empty_roots helper. No arbitrary table,
//! function replacement, assumption of output equality, or disabled unwind gate.
use super::*;

fn actual_and_reference() -> (RW, RP, RW, RP) {
    let (input, out, recipient, change, snapshot, asset) = arbitrary_inputs();
    let (w, p) = records(&input, out, recipient.as_ref(), &change, &snapshot, asset);
    let (v, q) = records_reference(&input, out, recipient.as_ref(), &change, &snapshot, asset);
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
