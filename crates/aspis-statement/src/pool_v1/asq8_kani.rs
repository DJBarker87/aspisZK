//! P6: exhaustive symbolic equivalence, including invalid public records.
use super::*;

fn digest() -> Digest {
    [M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any()),
     M31(kani::any()), M31(kani::any()), M31(kani::any()), M31(kani::any())]
}

fn request(public: PoolV1PairForestTerminalPaymentV1) -> PoolV1PairForestTerminalRequestV1 {
    PoolV1PairForestTerminalRequestV1 {
        verifier_profile: kani::any(), verifier_release: kani::any(),
        pool_program: kani::any(), public,
    }
}

#[kani::proof]
#[kani::unwind(321)]
fn transfer_encoder_equivalence() {
    let p = PoolV1PrivateTransferPublicV1 {
        pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
        anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
        recipient_commitment: digest(), change_commitment: digest(),
    };
    let r = request(PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p));
    assert_eq!(encode_pool_v1_pair_forest_terminal_request_v1(&r),
        encode_pool_v1_pair_forest_terminal_request_reference_v1(&r));
}

#[kani::proof]
#[kani::unwind(321)]
fn withdrawal_encoder_equivalence() {
    let p = PoolV1WithdrawalPublicV1 {
        pool: kani::any(), deployment_domain: kani::any(), anchor_sequence: kani::any(),
        anchor_root: digest(), nullifier: digest(), asset_id: M31(kani::any()),
        amount: kani::any(), destination_token_account: kani::any(), change_commitment: digest(),
    };
    let r = request(PoolV1PairForestTerminalPaymentV1::Withdrawal(p));
    assert_eq!(encode_pool_v1_pair_forest_terminal_request_v1(&r),
        encode_pool_v1_pair_forest_terminal_request_reference_v1(&r));
}
