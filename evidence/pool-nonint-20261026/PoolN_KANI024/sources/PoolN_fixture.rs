fn PoolN_fixture(tag:u8)->Vec<u8> {
 use aspis_core::field::M31;
 use aspis_statement::pool_v1::*;
 use crate::instruction::*;
 let d=[M31(1);8];
 let initial=crate::state::PoolInitializationV1{asset_mint:[9;32],token_program:crate::vault::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),asset_id:M31(4),deployment_domain:[5;32],verifier_policy:VerifierPolicyV1{flags:1,registry_program:[6;32],registry_authority:[0;32],policy_binding:[7;32]}};
 if tag==0 { return encode_initialize_instruction_v1(&initial).unwrap().to_vec(); }
 if tag==5 { return crate::pair_forest::encode_pair_forest_initialize_instruction_v1(&initial).unwrap().to_vec(); }
 if tag==6||tag==7 {let mut v=vec![0u8;80];v[..4].copy_from_slice(if tag==6{b"ASDI"}else{b"AS8D"});v[4]=1;v[40]=1;return v;}
 let envelope=HistoricalAnchorEnvelopeV1{transition_kind:PoolV1TransitionKind::PrivateTransfer,pool:[1;32],deployment_domain:[2;32],anchor_sequence:7,anchor_root:d,nullifier:d,verifier_profile:[3;32],verifier_release:[4;32]};
 let public=PoolV1PrivateTransferPublicV1{pool:envelope.pool,deployment_domain:envelope.deployment_domain,anchor_sequence:envelope.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),recipient_commitment:d,change_commitment:d};
 if tag==8 {let request=PoolV1PairForestTerminalRequestV1{verifier_profile:[3;32],verifier_release:[4;32],pool_program:[5;32],public:PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)};let mut v=encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap().to_vec();v.extend_from_slice(&[0;4]);return v;}
 if tag==4 {let payload=encode_pool_v1_private_transfer_public_v1(&public).unwrap();return crate::settle_prepared_instruction::encode_settle_prepared_instruction_v1(PoolV1TransitionKind::PrivateTransfer,&payload).unwrap().to_vec();}
 if tag==2 {let mut e=envelope;e.transition_kind=PoolV1TransitionKind::Withdrawal;let w=WithdrawalStatementV1{pool:e.pool,deployment_domain:e.deployment_domain,anchor_sequence:e.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),amount:25,destination_token_account:[5;32],change_commitment:d};return encode_withdrawal_instruction_v1(&e,&w).unwrap().to_vec();}
 let t=PrivateTransferStatementV1{pool:envelope.pool,deployment_domain:envelope.deployment_domain,anchor_sequence:envelope.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),recipient_commitment:d,change_commitment:d};
 let spend=encode_private_transfer_instruction_v1(&envelope,&t).unwrap();
 if tag==3 {return crate::prepared_settlement_instruction::encode_prepare_settlement_instruction_v1(PoolV1TransitionKind::PrivateTransfer,11,12,&spend).unwrap().to_vec();}
 spend.to_vec()
}
