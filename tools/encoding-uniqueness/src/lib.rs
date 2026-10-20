//! Native regressions against unchanged frozen R1/Pool decoder implementations.
#[cfg(test)]
mod tests {
    use aspis_core::{field::{M31, QM31, WideExact, P}, Digest32};
    use aspis_r1_cost_probe::{transport::Variant, verifier};
    use aspis_statement::{decode_digest_canonical, pool_v1::*};
    use solana_program::{hash::hashv, pubkey::Pubkey};
    use std::sync::OnceLock;

    const PUBLIC: &[u8] = include_bytes!("../../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-1023/r1-s2-public-asf8.bin");
    const PROOF: &[u8] = include_bytes!("../../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-1023/r1-s2-proof.bin");
    const BAD: [u32; 4] = [P, P + 1, 0x8000_0000, u32::MAX];
    #[derive(Clone, Copy)]
    struct Sha;
    impl Digest32 for Sha {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] { hashv(parts).to_bytes() }
    }
    fn word(bytes: &mut [u8], offset: usize, value: u32) {
        bytes[offset..offset+4].copy_from_slice(&value.to_le_bytes());
    }
    fn statement() -> PoolV1PairForestTerminalStatementV1 {
        decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap()
    }
    fn request(withdrawal: bool) -> PoolV1PairForestTerminalRequestV1 {
        let PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } = statement() else { panic!() };
        let public = if withdrawal {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: public.pool, deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence, anchor_root: public.anchor_root,
                nullifier: public.nullifier, asset_id: public.asset_id, amount: 1,
                destination_token_account: [9;32], change_commitment: public.change_commitment,
            })
        } else { PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) };
        PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [1;32], verifier_release: [2;32], pool_program: [3;32], public,
        }
    }
    fn checkpoint() -> &'static Vec<u8> {
        static C: OnceLock<Vec<u8>> = OnceLock::new();
        C.get_or_init(|| verifier::tx1(statement().semantic_public(), PUBLIC, PROOF, 10, Sha, None).unwrap())
    }

    #[test]
    fn scalar_towers_reject_noncanonical_components() {
        for value in [0, 1, P-1, P, P+1, 0x8000_0000, u32::MAX] {
            assert_eq!(M31::from_le_bytes(value.to_le_bytes()).map(|x| x.0), (value<P).then_some(value));
            for limb in 0..8 {
                let mut bytes = [0;32]; word(&mut bytes, 4*limb, value);
                assert_eq!(decode_digest_canonical(&bytes).is_ok(), value<P);
                assert_eq!(WideExact::from_le_bytes(&bytes).is_some(), value<P);
                if limb<4 { assert_eq!(QM31::from_le_bytes(&bytes[..16]).is_some(), value<P); }
            }
        }
    }

    #[test]
    fn asf8_every_public_field_limb_rejects_noncanonical_words() {
        assert_eq!(encode_pool_v1_pair_forest_terminal_statement_v1(&statement()).unwrap().as_slice(), PUBLIC);
        // Historical anchor; live root + 20 frontier nodes; candidate root +
        // 20 frontier nodes; payment anchor/nullifier/asset; recipient/change.
        let ranges = [112..144, 304..976, 992..1664, 1744..1812, 1816..1880];
        let mut mutations = 0;
        for range in ranges { for offset in range.step_by(4) { for value in BAD {
            let mut bytes=PUBLIC.to_vec(); word(&mut bytes, offset, value);
            assert!(decode_pool_v1_pair_forest_terminal_statement_v1(&bytes).is_err(), "offset={offset} value={value}");
            mutations+=1;
        } } }
        assert_eq!(mutations, 1508);
    }

    #[test]
    fn asq8_both_variants_reject_noncanonical_field_limbs_and_amounts() {
        let mut mutations=0;
        for withdrawal in [false,true] {
            let r=request(withdrawal);
            let baseline=encode_pool_v1_pair_forest_terminal_request_v1(&r).unwrap();
            assert_eq!(decode_pool_v1_pair_forest_terminal_request_v1(&baseline),Ok(r));
            // Payment offset 104: anchor + nullifier + asset; change; transfer recipient.
            let mut offsets:Vec<_>=(184..252).step_by(4).chain((288..320).step_by(4)).collect();
            if !withdrawal { offsets.extend((256..288).step_by(4)); }
            for offset in offsets { for value in BAD {
                let mut bytes=baseline; word(&mut bytes,offset,value);
                assert!(decode_pool_v1_pair_forest_terminal_request_v1(&bytes).is_err(), "withdrawal={withdrawal} offset={offset}");
                mutations+=1;
            } }
            for amount in [1<<30, P, 0x8000_0000, u32::MAX] {
                let mut bytes=baseline; word(&mut bytes,252,amount);
                assert!(decode_pool_v1_pair_forest_terminal_request_v1(&bytes).is_err());
            }
        }
        assert_eq!(mutations,232);
    }

    #[test]
    fn raw_destination_is_preserved_and_transcript_visible() {
        let mut r=request(true);
        let mut accepted=Vec::new();
        for value in [0, P, 0x8000_0000, u32::MAX] {
            let PoolV1PairForestTerminalPaymentV1::Withdrawal(ref mut p)=r.public else {panic!()};
            word(&mut p.destination_token_account,0,value);
            let bytes=encode_pool_v1_pair_forest_terminal_request_v1(&r).unwrap();
            assert_eq!(decode_pool_v1_pair_forest_terminal_request_v1(&bytes),Ok(r));
            assert_eq!(encode_pool_v1_pair_forest_terminal_request_v1(&decode_pool_v1_pair_forest_terminal_request_v1(&bytes).unwrap()).unwrap(),bytes);
            let PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=r.public else {panic!()};
            let s=PoolV1PairForestTerminalStatementV1::Withdrawal{common:*statement().common(),public:p};
            let asf=encode_pool_v1_pair_forest_terminal_statement_v1(&s).unwrap();
            accepted.push((r,hashv(&[&asf]).to_bytes()));
        }
        for a in 0..accepted.len() {for b in a+1..accepted.len() {
            assert_ne!(accepted[a].0,accepted[b].0);
            assert_ne!(accepted[a].1,accepted[b].1);
        }}
    }

    #[test]
    fn marker_rejects_alternate_nullifier_encodings_before_seed_derivation() {
        let program=Pubkey::new_from_array([41;32]); let master=Pubkey::new_from_array([42;32]);
        let canonical=[0;32];
        assert!(aspis_pool::pool_v1_pair_forest_nullifier_marker_address(&program,&master,&canonical).is_ok());
        for limb in 0..8 {for value in BAD {
            let mut bytes=canonical;word(&mut bytes,4*limb,value);
            assert!(aspis_pool::pool_v1_pair_forest_nullifier_marker_address(&program,&master,&bytes).is_err());
        }}
    }

    #[test]
    fn saved_proof_accepts_and_checkpoint_rejects_every_noncanonical_field_word() {
        let ck=checkpoint();
        verifier::tx2(PUBLIC,PROOF,ck,Sha,None).unwrap();
        verifier::resume(ck,PROOF,PUBLIC,Variant::S2,Sha).unwrap();
        // 176..320: gamma/kappa/alpha/rho. 320..408: raw query indices.
        // 408..end: semantic alphas, z, claim/rhs, power, weights.
        let end=ck.len()-32;
        let mut mutations=0;
        for offset in (176..320).step_by(4).chain((408..end).step_by(4)) {for value in BAD {
            let mut bytes=ck.clone();word(&mut bytes,offset,value);
            let checksum=hashv(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]).to_bytes();
            bytes[end..].copy_from_slice(&checksum);
            // Repair checksum so rejection tests the scalar parser, not checksum binding.
            assert!(matches!(verifier::resume(&bytes,PROOF,PUBLIC,Variant::S2,Sha),Err(verifier::Error::Checkpoint)), "offset={offset}");
            mutations+=1;
        }}
        assert_eq!(mutations,1472);
        // Raw account/domain bindings are part of public bytes even though
        // semantic_public() projects them away. Replaying a checkpoint fails.
        let mut different_public=PUBLIC.to_vec();different_public[8]^=1;
        assert!(matches!(verifier::resume(ck,PROOF,&different_public,Variant::S2,Sha),Err(verifier::Error::Checkpoint)));
    }
    #[test]
    fn pool_checkpoint_root_identity_asset_and_raw_sequence() {
        let checkpoint=PoolV1PairForestCheckpointV1 {
            bump: 255, master: [41;32], deployment_domain: [42;32],
            checkpoint_sequence: 1, global_root: [M31::ZERO;8], lane_sequences: [0;8],
        };
        let base=encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint).unwrap();
        assert_eq!(decode_pool_v1_pair_forest_checkpoint_v1(&base),Ok(checkpoint));
        for limb in 0..8 {for value in BAD {
            let mut bytes=base;word(&mut bytes,80+4*limb,value);
            assert!(decode_pool_v1_pair_forest_checkpoint_v1(&bytes).is_err());
        }}
        // Checkpoint sequence is an integer seed, never a single M31 limb.
        for value in [u64::from(P),u64::from(P)+1,1<<31,u64::MAX] {
            let mut bytes=base;bytes[72..80].copy_from_slice(&value.to_le_bytes());
            let decoded=decode_pool_v1_pair_forest_checkpoint_v1(&bytes).unwrap();
            assert_eq!(decoded.checkpoint_sequence,value);
            assert_eq!(encode_pool_v1_pair_forest_checkpoint_v1(&decoded).unwrap(),bytes);
        }
        let identity=PoolIdentityV1 {
            pool:[41;32],asset_mint:[43;32],token_program:[44;32],
            asset_id:M31::ONE,deployment_domain:[42;32],
        };
        let base=encode_pool_identity_v1(&identity);
        assert_eq!(decode_pool_identity_v1(&base),Ok(identity));
        for value in BAD {
            let mut bytes=base;word(&mut bytes,104,value);
            assert!(decode_pool_identity_v1(&bytes).is_err());
        }
    }

}
