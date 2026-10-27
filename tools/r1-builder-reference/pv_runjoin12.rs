//! Parent is cfg(kani). No stubs and no assumed callee result.
use super::*;
fn digest(seed: u32) -> Digest {
    core::array::from_fn(|i| M31(seed + 17 * i as u32 + 1))
}
// Generalizes the fixture's first input commitment and snapshot bytes; all
// deterministic mapper-relevant fixture controls are fixed exactly.
fn inputs(transfer: bool) -> (PoolV1PairForestInputNoteWitnessV1, u32, Option<PoolV1OutputNoteWitnessV1>, PoolV1OutputNoteWitnessV1, PoolV1PairLiveSnapshotV1) {
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: digest(10), salt: digest(100), value: 1000,
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: any_digest(), second_occupied: M31(1),
                second_commitment: digest(900), second_occupancy_inverse: M31(kani::any()),
            }, selected_second: false,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|l| digest(2000 + 20*l as u32)), index: 0x5_4321,
            },
        }, super_root_siblings: [digest(3000),digest(3100),digest(3200)],
        super_root_directions: [true,false,true],
    };
    let recipient = if transfer {Some(PoolV1OutputNoteWitnessV1 {owner_key:digest(300),salt:digest(400),value:600})} else {None};
    let change=PoolV1OutputNoteWitnessV1 {owner_key: digest(if transfer {500} else {700}),salt:digest(if transfer {600} else {800}),value:if transfer {400} else {750}};
    let snapshot=PoolV1PairLiveSnapshotV1 {pool:[1;32],deployment_domain:[5;32],sequence:0,next_pair_index:0,current_root:any_digest(),frontier:any_digests_20()};
    (input,if transfer {600} else {250},recipient,change,snapshot)
}
fn compare(transfer: bool, part: u8) {
    let (input,out,rec,chg,snap)=inputs(transfer);
    let (w,p)=records(&input,out,rec.as_ref(),&chg,&snap,M31(77));
    let (v,q)=super::records_reference(&input,out,rec.as_ref(),&chg,&snap,M31(77));
    if part == 0 || part == 1 {
        assert_eq!(w.input_value,v.input_value);assert_eq!(w.output_value,v.output_value);assert_eq!(w.change_value,v.change_value);
        assert_eq!(w.sk,v.sk);assert_eq!(w.salt,v.salt);assert_eq!(w.pair_first,v.pair_first);assert_eq!(w.pair_second,v.pair_second);
        assert_eq!(w.pair_occupied,v.pair_occupied);assert_eq!(w.pair_inverse,v.pair_inverse);
        assert_eq!(w.recipient_owner,v.recipient_owner);assert_eq!(w.recipient_salt,v.recipient_salt);
        assert_eq!(w.change_owner,v.change_owner);assert_eq!(w.change_salt,v.change_salt);
    }
    if part == 0 || part == 2 {assert_eq!(w.bits,v.bits);assert_eq!(w.sibs,v.sibs);}
    if part == 0 || part == 3 {assert_eq!(p.transfer,q.transfer);assert_eq!(p.asset,q.asset);assert_eq!(p.next_pair_index,q.next_pair_index);assert_eq!(p.frontier,q.frontier);assert_eq!(p.empty,q.empty);}
}
#[kani::proof]
#[kani::unwind(33)]
fn transfer_all() {compare(true,0);}
#[kani::proof]
#[kani::unwind(33)]
fn withdrawal_all() {compare(false,0);}
#[kani::proof]
#[kani::unwind(33)]
fn transfer_fields() {compare(true,1);}
#[kani::proof]
#[kani::unwind(33)]
fn transfer_path() {compare(true,2);}
#[kani::proof]
#[kani::unwind(33)]
fn transfer_public() {compare(true,3);}
#[kani::proof]
#[kani::unwind(33)]
fn withdrawal_fields() {compare(false,1);}
#[kani::proof]
#[kani::unwind(33)]
fn withdrawal_path() {compare(false,2);}
#[kani::proof]
#[kani::unwind(33)]
fn withdrawal_public() {compare(false,3);}

// Independently frozen source table, already covered by the 21 source-parent
// cells. Compare the actual shipped root computation with a fixed input to
// the owned reference; neither callee is stubbed.
mod fixed_roots {
 include!("../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs");
}
fn compare_fixed_roots(transfer: bool) {
 let (input,out,rec,chg,snap)=inputs(transfer);
 let (w,p)=records(&input,out,rec.as_ref(),&chg,&snap,M31(77));
 let empty=fixed_roots::POOL_V1_PAIR_EMPTY_ROOTS_V1.map(|row| row.map(M31));
 let (v,q)=super::super::records_reference::records_reference_with_roots(input,out,rec,chg,snap,M31(77),empty);
 let part=0;
    if part == 0 || part == 1 {
        assert_eq!(w.input_value,v.input_value);assert_eq!(w.output_value,v.output_value);assert_eq!(w.change_value,v.change_value);
        assert_eq!(w.sk,v.sk);assert_eq!(w.salt,v.salt);assert_eq!(w.pair_first,v.pair_first);assert_eq!(w.pair_second,v.pair_second);
        assert_eq!(w.pair_occupied,v.pair_occupied);assert_eq!(w.pair_inverse,v.pair_inverse);
        assert_eq!(w.recipient_owner,v.recipient_owner);assert_eq!(w.recipient_salt,v.recipient_salt);
        assert_eq!(w.change_owner,v.change_owner);assert_eq!(w.change_salt,v.change_salt);
    }
    if part == 0 || part == 2 {assert_eq!(w.bits,v.bits);assert_eq!(w.sibs,v.sibs);}
    if part == 0 || part == 3 {assert_eq!(p.transfer,q.transfer);assert_eq!(p.asset,q.asset);assert_eq!(p.next_pair_index,q.next_pair_index);assert_eq!(p.frontier,q.frontier);assert_eq!(p.empty,q.empty);}
}
#[kani::proof]
#[kani::unwind(33)]
fn transfer_fixed_roots() {compare_fixed_roots(true);}
#[kani::proof]
#[kani::unwind(33)]
fn withdrawal_fixed_roots() {compare_fixed_roots(false);}
