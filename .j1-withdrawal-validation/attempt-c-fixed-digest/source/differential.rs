use aspis_withdrawal_validation_extract::{
    aspis_core::field::{M31, P},
    pool_v1::payment_relation::{
        validate_pool_v1_withdrawal_public_v1 as validate,
        PoolV1PaymentStatementFormatError as Error, PoolV1WithdrawalPublicV1 as Public,
    },
    poseidon2::Digest,
};

mod original {
    use super::{Digest, M31, P};
    use aspis_withdrawal_validation_extract::{
        pool_v1::{
            payment_relation::{PoolV1PaymentStatementFormatError, PoolV1WithdrawalPublicV1},
            POOL_V1_LEAF_CAPACITY,
        },
        VALUE_LIMIT,
    };
    include!("original_digest_is_canonical.rs");
    include!("fragments/common_public.rs");
    include!("fragments/validate_common.rs");
    include!("fragments/withdrawal_common.rs");
    include!("fragments/validate_withdrawal.rs");
    pub fn check(digest: &Digest) -> bool {
        digest_is_canonical(digest)
    }
}

mod changed {
    use super::{Digest, P};
    include!("fragments/digest_is_canonical.rs");
    pub fn check(digest: &Digest) -> bool {
        digest_is_canonical(digest)
    }
}

fn public() -> Public {
    Public {
        pool: [1; 32],
        deployment_domain: [2; 32],
        anchor_sequence: 0,
        anchor_root: [M31(0); 8],
        nullifier: [M31(0); 8],
        asset_id: M31(0),
        amount: 1,
        destination_token_account: [3; 32],
        change_commitment: [M31(0); 8],
    }
}

#[test]
fn each_digest_coordinate_matches_original_at_boundaries() {
    for fill in [0, P - 1] {
        let good = [M31(fill); 8];
        assert!(original::check(&good));
        assert!(changed::check(&good));
        for i in 0..8 {
            for value in [0, 1, P - 1, P, u32::MAX] {
                let mut digest = good;
                digest[i] = M31(value);
                assert_eq!(changed::check(&digest), original::check(&digest));
                assert_eq!(changed::check(&digest), value < P);
                for position in 0..3 {
                    let mut p = public();
                    match position {
                        0 => p.anchor_root = digest,
                        1 => p.nullifier = digest,
                        _ => p.change_commitment = digest,
                    }
                    assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
                }
            }
        }
    }
}

#[test]
fn validator_amount_and_error_order_match_original() {
    for amount in [0, 1, (1 << 30) - 1, 1 << 30, P - 1, P, u32::MAX] {
        let mut p = public();
        p.amount = amount;
        assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
        assert_eq!(validate(&p), if amount > 0 && amount < 1 << 30 {
            Ok(())
        } else {
            Err(Error::InvalidWithdrawalAmount)
        });
        p.pool = [0; 32];
        assert_eq!(validate(&p), Err(Error::ZeroRequiredBinding));
        assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
    }
    let mut p = public();
    p.amount = 0;
    p.asset_id = M31(P);
    assert_eq!(validate(&p), Err(Error::NonCanonicalAssetId));
    assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
    p.asset_id = M31(0);
    p.change_commitment[7] = M31(P);
    assert_eq!(validate(&p), Err(Error::InvalidWithdrawalAmount));
    assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
    p.amount = 1;
    p.destination_token_account = [0; 32];
    assert_eq!(validate(&p), Err(Error::InvalidDestination));
    assert_eq!(validate(&p), original::validate_pool_v1_withdrawal_public_v1(&p));
}
