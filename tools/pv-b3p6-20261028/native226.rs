//! Native differential and no-stub bounded source checks for the owned serializer.
use aspis_core::field::M31;
use aspis_statement::pool_v1::{
    pair_forest_semantic_terminal::r0::Public,
    pair_terminal::PoolV1PairVerifiedAfterstateV1,
    pair_tree_profile::{PoolV1PairLiveSnapshotV1, PoolV1PairLatePublicStatementV1},
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
};
use crate::reference226::{Source, public_bytes};

#[cfg(kani)]
fn digest() -> [M31; 8] {
    let x: [u32; 8] = kani::any();
    x.map(M31)
}
#[cfg(kani)]
fn arbitrary_source(withdrawal: bool) -> Source {
    let t = PoolV1PairLatePublicStatementV1 {
        live_snapshot: PoolV1PairLiveSnapshotV1 {
            pool: kani::any(), deployment_domain: kani::any(), sequence: kani::any(),
            next_pair_index: kani::any(), current_root: digest(),
            frontier: core::array::from_fn(|_| digest()),
        },
        candidate_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: kani::any(), next_root: digest(),
            next_frontier: core::array::from_fn(|_| digest()),
        },
    };
    if withdrawal {
        Source::Withdrawal(PoolV1WithdrawalPublicV1 {
            pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
            anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
            amount: kani::any(), destination_token_account: kani::any(), change_commitment: digest(),
        }, t)
    } else {
        Source::Transfer(PoolV1PrivateTransferPublicV1 {
            pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
            anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
            recipient_commitment: digest(), change_commitment: digest(),
        }, t)
    }
}

#[cfg(kani)]
fn check(source: Source) {
    let actual = match source {
        Source::Transfer(p, t) => Public::Transfer(&p, &t).public_bytes(),
        Source::Withdrawal(p, t) => Public::Withdrawal(&p, &t).public_bytes(),
    };
    let expected = public_bytes(source);
    match (actual, expected) {
        (Ok(bytes), Ok((chunks, n))) => {
            assert_eq!(bytes.len(), n);
            assert!(n == 1427 || n == 1455);
            let index: u16 = kani::any();
            let i = usize::from(index);
            kani::assume(i < n);
            assert_eq!(bytes[i], chunks[i / 64][i % 64]);
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        _ => assert!(false, "complete Result mismatch"),
    }
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(65)]
fn transfer() { check(arbitrary_source(false)); }
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(65)]
fn withdrawal() { check(arbitrary_source(true)); }

#[cfg(test)]
fn fixture(withdrawal: bool) -> Source {
    let words = |seed: u32| core::array::from_fn(|i| M31(seed + i as u32));
    let t = PoolV1PairLatePublicStatementV1 {
        live_snapshot: PoolV1PairLiveSnapshotV1 {
            pool: [7;32], deployment_domain: [11;32], sequence: 17,
            next_pair_index: 0x0123_4567_89ab_cdef,
            current_root: words(23), frontier: core::array::from_fn(|i| words(100 + 8*i as u32)),
        },
        candidate_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 31, next_root: words(37),
            next_frontier: core::array::from_fn(|i| words(300 + 8*i as u32)),
        },
    };
    if withdrawal {
        Source::Withdrawal(PoolV1WithdrawalPublicV1 {
            pool: [41;32], deployment_domain: [43;32], anchor_sequence: 47,
            anchor_root: words(53), nullifier: words(61), asset_id: M31(67),
            amount: 71, destination_token_account: [73;32], change_commitment: words(79),
        },t)
    } else {
        Source::Transfer(PoolV1PrivateTransferPublicV1 {
            pool: [83;32], deployment_domain: [89;32], anchor_sequence: 97,
            anchor_root: words(101), nullifier: words(109), asset_id: M31(127),
            recipient_commitment: words(131), change_commitment: words(139),
        },t)
    }
}
#[cfg(test)]
fn finite(source: Source) {
    let native = match source {
        Source::Transfer(p,t) => Public::Transfer(&p,&t).public_bytes(),
        Source::Withdrawal(p,t) => Public::Withdrawal(&p,&t).public_bytes(),
    };
    let reference = public_bytes(source).map(|(chunks,n)| {
        let mut v=Vec::new();
        for i in 0..n { v.push(chunks[i/64][i%64]); }
        v
    });
    assert_eq!(native,reference);
}
#[test]
fn same_input_finite226() {
    for withdrawal in [false,true] {
        let p=fixture(withdrawal); finite(p);
        let bad=match p {
            Source::Transfer(mut p,t) => {p.asset_id=M31(u32::MAX); Source::Transfer(p,t)},
            Source::Withdrawal(mut p,t) => {p.amount=u32::MAX; Source::Withdrawal(p,t)},
        }; finite(bad);
    }
}
