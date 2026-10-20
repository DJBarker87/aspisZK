    // Injected into the existing test module of a disposable source copy only.
    #[test]
    fn r20_hint_reorder_variant_and_stale_request_reject_before_cpi() {
        let program_id = Pubkey::new_unique();
        let (fixture, instruction, _) = system_marker_terminal_transfer_fixture(program_id);
        let mut cases = Vec::new();
        let mut hint = instruction.clone();
        let last = hint.len() - 1;
        hint[last] = 1; // Unused transfer vault hint must be zero.
        cases.push((fixture.clone(), hint, "hint"));
        let mut reordered = fixture.clone();
        reordered.swap(0, 1); // Different discriminated Pool account types.
        cases.push((reordered, instruction.clone(), "account order"));
        let mut variant = instruction.clone();
        variant[5] = aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal as u8;
        cases.push((fixture.clone(), variant, "outer variant with ASCP payload"));
        // This original request was well-formed for checkpoint sequence 0.
        // Supply a canonical newer checkpoint account, so the old statement
        // is stale relative to the authenticated account, not merely a bad byte.
        let mut newer = fixture;
        let mut cp = aspis_statement::pool_v1::decode_pool_v1_pair_forest_checkpoint_v1(&newer[1].data).unwrap();
        cp.checkpoint_sequence = 1;
        let (key, bump) = pool_v1_pair_forest_checkpoint_address(&program_id, &newer[0].key, 1);
        cp.bump = bump;
        newer[1].key = key;
        newer[1].data = encode_pool_v1_pair_forest_checkpoint_v1(&cp).unwrap().to_vec();
        let mut m = aspis_statement::pool_v1::decode_pool_v1_pair_forest_master_v1(&newer[0].data).unwrap();
        m.next_checkpoint_sequence = 2;
        newer[0].data = encode_pool_v1_pair_forest_master_v1(&m).unwrap().to_vec();
        cases.push((newer, instruction, "old sequence against newer supplied checkpoint"));
        for (mut accounts, bytes, label) in cases {
            let before: Vec<_> = accounts.iter().map(|a| (a.data.clone(), a.lamports)).collect();
            assert!(reject_before_cpi(&program_id, &mut accounts, &bytes).is_err(), "{label}");
            assert_eq!(before, accounts.iter().map(|a| (a.data.clone(), a.lamports)).collect::<Vec<_>>(), "{label}");
        }
    }

    #[test]
    fn r20_strip_reencode_is_exact_for_both_payment_variants() {
        let program_id = Pubkey::new_unique();
        let (_, data, _) = system_marker_terminal_transfer_fixture(program_id);
        let (body, _) = split_pair_forest_terminal_bump_hints_v1(&data).unwrap();
        let transfer = decode_pool_v1_pair_forest_terminal_request_v1(body).unwrap();
        let p = match transfer.public { PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p) => p, _ => unreachable!() };
        let withdrawal = PoolV1PairForestTerminalRequestV1 { public:
            PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: p.pool, deployment_domain: p.deployment_domain,
                anchor_sequence: p.anchor_sequence, anchor_root: p.anchor_root,
                nullifier: p.nullifier, asset_id: p.asset_id, amount: 25,
                destination_token_account: [99;32], change_commitment: p.change_commitment,
            }), ..transfer };
        for request in [transfer, withdrawal] {
            let encoded = encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap();
            for n in 0..=255u8 {
                let hints = PoolV1PairForestTerminalBumpHintsV1 {
                    current_page: n, next_page: n.wrapping_add(1),
                    vault_authority: n.wrapping_add(2), vault_token_account: n.wrapping_add(3),
                };
                let pool_data = encode_pair_forest_terminal_instruction_data_v1(&encoded, hints);
                let (stripped, decoded_hints) = split_pair_forest_terminal_bump_hints_v1(&pool_data).unwrap();
                assert_eq!(decoded_hints, hints);
                assert_eq!(stripped, encoded);
                let decoded = decode_pool_v1_pair_forest_terminal_request_v1(stripped).unwrap();
                assert_eq!(decoded, request);
                assert_eq!(encode_pool_v1_pair_forest_terminal_request_v1(&decoded).unwrap(), encoded);
            }
        }
        for n in 0..4 { assert!(split_pair_forest_terminal_bump_hints_v1(&[0;4][..n]).is_err()); }
    }
