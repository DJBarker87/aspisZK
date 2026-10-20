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

// The Pool strips the four hint bytes before this fixed-size codec. This
// harness covers the exact bytes subsequently supplied to verifier stage 2.
#[kani::proof]
#[kani::unwind(321)]
fn accepted_request_reencodes_exactly() {
    let bytes: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES] = kani::any();
    if let Ok(r) = decode_pool_v1_pair_forest_terminal_request_v1(&bytes) {
        assert_eq!(encode_pool_v1_pair_forest_terminal_request_reference_v1(&r), Ok(bytes));
    }
}

#[kani::proof]
#[kani::unwind(321)]
fn request_decoder_equivalence() {
    let bytes: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES] = kani::any();
    assert_eq!(decode_pool_v1_pair_forest_terminal_request_v1(&bytes),
        decode_pool_v1_pair_forest_terminal_request_reference_v1(&bytes));
}

// Checks the entire fused normalization, including all parser/encoder errors.
// No assumption of successful decoding or canonical encoding is supplied.
#[kani::proof]
#[kani::unwind(321)]
fn shipped_pipeline_normalization_equivalence() {
    let bytes: [u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES] = kani::any();
    let shipped = decode_pool_v1_pair_forest_terminal_request_v1(&bytes)
        .and_then(|r| encode_pool_v1_pair_forest_terminal_request_v1(&r));
    assert_eq!(shipped, normalize_pool_v1_pair_forest_terminal_request_reference_v1(&bytes));
}

// P6 library-model evidence for the fixed four-byte slice/array header
// comparisons in the extracted codec. All lengths up to the admitted ASQ8
// input size are covered, not only successful four-byte comparisons.
#[kani::proof]
#[kani::unwind(321)]
fn slice_array_header_comparison_model() {
    let bytes: [u8; 320] = kani::any();
    let header: [u8; 4] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 320);
    let slice = &bytes[..len];
    assert_eq!(slice == header, slice == &header[..]);
    assert_eq!(slice != header, slice != &header[..]);
}
