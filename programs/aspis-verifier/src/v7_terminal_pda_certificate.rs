//! Default-off creation of an immutable terminal PDA bump certificate.
//!
//! Canonical bump search happens once in this proof-preparation instruction.
//! The terminal Pool/verifier path accepts only this verifier-owned image and
//! replays each derivation with `create_program_address`, so its work is fixed
//! without trusting a caller-selected alternate bump.

use aspis_statement::pool_v1::{
    decode_pool_v1_terminal_pda_certificate_v1, PoolV1TerminalPdaCertificateV1,
    POOL_V1_NULLIFIER_MARKER_SEED, POOL_V1_ROOT_HISTORY_PAGE_SEED,
    POOL_V1_TERMINAL_PDA_BUMP_CHECKPOINT, POOL_V1_TERMINAL_PDA_BUMP_CURRENT_PAGE,
    POOL_V1_TERMINAL_PDA_BUMP_ENTRY, POOL_V1_TERMINAL_PDA_BUMP_LANE,
    POOL_V1_TERMINAL_PDA_BUMP_MARKER, POOL_V1_TERMINAL_PDA_BUMP_MASTER,
    POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE, POOL_V1_TERMINAL_PDA_BUMP_REGISTRY,
    POOL_V1_TERMINAL_PDA_BUMP_REGISTRY_PROGRAMDATA, POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY,
    POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN, POOL_V1_TERMINAL_PDA_BUMP_VERIFIER_PROGRAMDATA,
    POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
    V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};
use solana_sdk_ids::bpf_loader_upgradeable;

use crate::lifecycle::{proof_account_finalized, uploaded_proof_bounds};

const PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
const PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
const PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";
const VERIFIER_REGISTRY_V2_SEED: &[u8] = b"aspis-verifier-registry-v2";
const VERIFIER_ENTRY_V2_SEED: &[u8] = b"aspis-verifier-entry-v2";
const VAULT_AUTHORITY_SEED: &[u8] = b"aspis-pool-vault-authority-v1";
const VAULT_TOKEN_SEED: &[u8] = b"aspis-pool-vault-token-v1";

fn require_created_address(
    recorded: [u8; 32],
    seeds: &[&[u8]],
    program_id: &Pubkey,
) -> ProgramResult {
    let created = Pubkey::create_program_address(seeds, program_id)
        .map_err(|_| ProgramError::InvalidSeeds)?;
    if created.to_bytes() != recorded {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(())
}

/// Validate every address with the recorded bump using exactly one PDA
/// attempt. Canonicality of those bumps is established only by
/// [`process_initialize_terminal_pda_certificate_v1`], which independently
/// executes Solana's descending canonical search before persisting the image.
pub fn validate_terminal_pda_certificate_single_attempt_v1(
    certificate: &PoolV1TerminalPdaCertificateV1,
) -> ProgramResult {
    let pool_program = Pubkey::new_from_array(certificate.pool_program);
    let master = Pubkey::new_from_array(certificate.master);
    let mint = Pubkey::new_from_array(certificate.asset_mint);
    let lane = Pubkey::new_from_array(certificate.selected_lane);
    let registry_program = Pubkey::new_from_array(certificate.registry_program);
    let verifier_program = Pubkey::new_from_array(certificate.verifier_program);
    let loader = bpf_loader_upgradeable::id();

    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_MASTER]];
    require_created_address(
        certificate.master,
        &[PAIR_FOREST_MASTER_SEED, mint.as_ref(), &b],
        &pool_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_CHECKPOINT]];
    require_created_address(
        certificate.checkpoint,
        &[
            PAIR_FOREST_CHECKPOINT_SEED,
            master.as_ref(),
            &certificate.checkpoint_sequence.to_le_bytes(),
            &b,
        ],
        &pool_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_LANE]];
    require_created_address(
        certificate.selected_lane,
        &[
            PAIR_FOREST_LANE_SEED,
            master.as_ref(),
            &[certificate.lane_id],
            &b,
        ],
        &pool_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_CURRENT_PAGE]];
    require_created_address(
        certificate.current_history_page,
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            lane.as_ref(),
            &certificate.current_page_number.to_le_bytes(),
            &b,
        ],
        &pool_program,
    )?;
    if certificate.rollover() {
        let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE]];
        require_created_address(
            certificate.next_history_page,
            &[
                POOL_V1_ROOT_HISTORY_PAGE_SEED,
                lane.as_ref(),
                &certificate.next_page_number.to_le_bytes(),
                &b,
            ],
            &pool_program,
        )?;
    }
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_MARKER]];
    require_created_address(
        certificate.nullifier_marker,
        &[
            POOL_V1_NULLIFIER_MARKER_SEED,
            master.as_ref(),
            &certificate.canonical_nullifier,
            &b,
        ],
        &pool_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_REGISTRY]];
    require_created_address(
        certificate.registry,
        &[VERIFIER_REGISTRY_V2_SEED, master.as_ref(), &b],
        &registry_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_REGISTRY_PROGRAMDATA]];
    require_created_address(
        certificate.registry_programdata,
        &[registry_program.as_ref(), &b],
        &loader,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_ENTRY]];
    require_created_address(
        certificate.registry_entry,
        &[
            VERIFIER_ENTRY_V2_SEED,
            master.as_ref(),
            &certificate.profile_binding,
            &certificate.release_binding,
            &b,
        ],
        &registry_program,
    )?;
    let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VERIFIER_PROGRAMDATA]];
    require_created_address(
        certificate.verifier_programdata,
        &[verifier_program.as_ref(), &b],
        &loader,
    )?;
    if certificate.withdrawal() {
        let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY]];
        require_created_address(
            certificate.vault_authority,
            &[VAULT_AUTHORITY_SEED, master.as_ref(), &b],
            &pool_program,
        )?;
        let b = [certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN]];
        require_created_address(
            certificate.vault_token,
            &[VAULT_TOKEN_SEED, master.as_ref(), &b],
            &pool_program,
        )?;
    }
    Ok(())
}

fn require_canonical_bumps(certificate: &PoolV1TerminalPdaCertificateV1) -> ProgramResult {
    let pool_program = Pubkey::new_from_array(certificate.pool_program);
    let master = Pubkey::new_from_array(certificate.master);
    let mint = Pubkey::new_from_array(certificate.asset_mint);
    let lane = Pubkey::new_from_array(certificate.selected_lane);
    let registry_program = Pubkey::new_from_array(certificate.registry_program);
    let verifier_program = Pubkey::new_from_array(certificate.verifier_program);
    let loader = bpf_loader_upgradeable::id();
    let require = |recorded: [u8; 32], bump: u8, found: (Pubkey, u8)| -> ProgramResult {
        if found.0.to_bytes() != recorded || found.1 != bump {
            Err(ProgramError::InvalidSeeds)
        } else {
            Ok(())
        }
    };
    require(
        certificate.master,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_MASTER],
        Pubkey::find_program_address(&[PAIR_FOREST_MASTER_SEED, mint.as_ref()], &pool_program),
    )?;
    require(
        certificate.checkpoint,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_CHECKPOINT],
        Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master.as_ref(),
                &certificate.checkpoint_sequence.to_le_bytes(),
            ],
            &pool_program,
        ),
    )?;
    require(
        certificate.selected_lane,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_LANE],
        Pubkey::find_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master.as_ref(),
                &[certificate.lane_id],
            ],
            &pool_program,
        ),
    )?;
    require(
        certificate.current_history_page,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_CURRENT_PAGE],
        Pubkey::find_program_address(
            &[
                POOL_V1_ROOT_HISTORY_PAGE_SEED,
                lane.as_ref(),
                &certificate.current_page_number.to_le_bytes(),
            ],
            &pool_program,
        ),
    )?;
    if certificate.rollover() {
        require(
            certificate.next_history_page,
            certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE],
            Pubkey::find_program_address(
                &[
                    POOL_V1_ROOT_HISTORY_PAGE_SEED,
                    lane.as_ref(),
                    &certificate.next_page_number.to_le_bytes(),
                ],
                &pool_program,
            ),
        )?;
    }
    require(
        certificate.nullifier_marker,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_MARKER],
        Pubkey::find_program_address(
            &[
                POOL_V1_NULLIFIER_MARKER_SEED,
                master.as_ref(),
                &certificate.canonical_nullifier,
            ],
            &pool_program,
        ),
    )?;
    require(
        certificate.registry,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_REGISTRY],
        Pubkey::find_program_address(
            &[VERIFIER_REGISTRY_V2_SEED, master.as_ref()],
            &registry_program,
        ),
    )?;
    require(
        certificate.registry_programdata,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_REGISTRY_PROGRAMDATA],
        Pubkey::find_program_address(&[registry_program.as_ref()], &loader),
    )?;
    require(
        certificate.registry_entry,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_ENTRY],
        Pubkey::find_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master.as_ref(),
                &certificate.profile_binding,
                &certificate.release_binding,
            ],
            &registry_program,
        ),
    )?;
    require(
        certificate.verifier_programdata,
        certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VERIFIER_PROGRAMDATA],
        Pubkey::find_program_address(&[verifier_program.as_ref()], &loader),
    )?;
    if certificate.withdrawal() {
        require(
            certificate.vault_authority,
            certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY],
            Pubkey::find_program_address(&[VAULT_AUTHORITY_SEED, master.as_ref()], &pool_program),
        )?;
        require(
            certificate.vault_token,
            certificate.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN],
            Pubkey::find_program_address(&[VAULT_TOKEN_SEED, master.as_ref()], &pool_program),
        )?;
    }
    Ok(())
}

/// Persist a canonical certificate once. Instruction data is the exact APD8
/// image; accounts are `[new_certificate_signer, sealed_proof]`.
pub fn process_initialize_terminal_pda_certificate_v1(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    let [certificate_account, proof_account] = accounts else {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    if certificate_account.owner != verifier_program
        || certificate_account.executable
        || !certificate_account.is_signer
        || !certificate_account.is_writable
        || certificate_account.data_len() != POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES
        || proof_account.owner != verifier_program
        || proof_account.executable
        || proof_account.is_signer
        || proof_account.is_writable
        || certificate_account.key == proof_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    {
        let proof_data = proof_account.try_borrow_data()?;
        let (_, end) = uploaded_proof_bounds(&proof_data)?;
        if !proof_account_finalized(&proof_data) || end != proof_data.len() {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    let certificate = decode_pool_v1_terminal_pda_certificate_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if certificate.proof_account != proof_account.key.to_bytes()
        || certificate.verifier_program != verifier_program.to_bytes()
        || certificate.profile_binding != V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING
        || certificate.release_binding != V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING
    {
        return Err(ProgramError::InvalidArgument);
    }
    require_canonical_bumps(&certificate)?;
    // Independently replay the exact single-attempt relation that terminal
    // consumers will use before making the immutable program-owned write.
    validate_terminal_pda_certificate_single_attempt_v1(&certificate)?;
    let mut destination = certificate_account.try_borrow_mut_data()?;
    if destination.iter().any(|byte| *byte != 0) {
        return Err(ProgramError::AccountAlreadyInitialized);
    }
    destination.copy_from_slice(instruction_data);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{
        encode_pool_v1_terminal_pda_certificate_v1, POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER,
        POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL,
    };
    use solana_program::clock::Epoch;

    fn canonical_certificate(
        pool_program: Pubkey,
        registry_program: Pubkey,
        verifier_program: Pubkey,
        proof: Pubkey,
    ) -> PoolV1TerminalPdaCertificateV1 {
        let mint = Pubkey::new_unique();
        let (master, master_bump) =
            Pubkey::find_program_address(&[PAIR_FOREST_MASTER_SEED, mint.as_ref()], &pool_program);
        let checkpoint_sequence = 9u64;
        let (checkpoint, checkpoint_bump) = Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master.as_ref(),
                &checkpoint_sequence.to_le_bytes(),
            ],
            &pool_program,
        );
        let lane_id = 3;
        let (lane, lane_bump) = Pubkey::find_program_address(
            &[PAIR_FOREST_LANE_SEED, master.as_ref(), &[lane_id]],
            &pool_program,
        );
        let current_page_number = 4u64;
        let next_page_number = 5u64;
        let (current_page, current_bump) = Pubkey::find_program_address(
            &[
                POOL_V1_ROOT_HISTORY_PAGE_SEED,
                lane.as_ref(),
                &current_page_number.to_le_bytes(),
            ],
            &pool_program,
        );
        let (next_page, next_bump) = Pubkey::find_program_address(
            &[
                POOL_V1_ROOT_HISTORY_PAGE_SEED,
                lane.as_ref(),
                &next_page_number.to_le_bytes(),
            ],
            &pool_program,
        );
        let canonical_nullifier = [1u8; 32];
        let (marker, marker_bump) = Pubkey::find_program_address(
            &[
                POOL_V1_NULLIFIER_MARKER_SEED,
                master.as_ref(),
                &canonical_nullifier,
            ],
            &pool_program,
        );
        let (registry, registry_bump) = Pubkey::find_program_address(
            &[VERIFIER_REGISTRY_V2_SEED, master.as_ref()],
            &registry_program,
        );
        let loader = bpf_loader_upgradeable::id();
        let (registry_programdata, registry_programdata_bump) =
            Pubkey::find_program_address(&[registry_program.as_ref()], &loader);
        let (entry, entry_bump) = Pubkey::find_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master.as_ref(),
                &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
                &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            ],
            &registry_program,
        );
        let (verifier_programdata, verifier_programdata_bump) =
            Pubkey::find_program_address(&[verifier_program.as_ref()], &loader);
        let (vault_authority, vault_authority_bump) =
            Pubkey::find_program_address(&[VAULT_AUTHORITY_SEED, master.as_ref()], &pool_program);
        let (vault_token, vault_token_bump) =
            Pubkey::find_program_address(&[VAULT_TOKEN_SEED, master.as_ref()], &pool_program);
        PoolV1TerminalPdaCertificateV1 {
            flags: POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER
                | POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL,
            proof_account: proof.to_bytes(),
            pool_program: pool_program.to_bytes(),
            master: master.to_bytes(),
            asset_mint: mint.to_bytes(),
            checkpoint: checkpoint.to_bytes(),
            checkpoint_sequence,
            selected_lane: lane.to_bytes(),
            lane_id,
            current_history_page: current_page.to_bytes(),
            current_page_number,
            next_history_page: next_page.to_bytes(),
            next_page_number,
            nullifier_marker: marker.to_bytes(),
            canonical_nullifier,
            registry_program: registry_program.to_bytes(),
            registry: registry.to_bytes(),
            registry_programdata: registry_programdata.to_bytes(),
            registry_entry: entry.to_bytes(),
            verifier_program: verifier_program.to_bytes(),
            verifier_programdata: verifier_programdata.to_bytes(),
            vault_authority: vault_authority.to_bytes(),
            vault_token: vault_token.to_bytes(),
            profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            bumps: [
                master_bump,
                checkpoint_bump,
                lane_bump,
                current_bump,
                next_bump,
                marker_bump,
                registry_bump,
                registry_programdata_bump,
                entry_bump,
                verifier_programdata_bump,
                vault_authority_bump,
                vault_token_bump,
            ],
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    #[test]
    fn canonical_init_is_once_and_wrong_bump_fails_closed() {
        let verifier = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let registry = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let certificate_key = Pubkey::new_unique();
        let certificate = canonical_certificate(pool, registry, verifier, proof_key);
        let encoded = encode_pool_v1_terminal_pda_certificate_v1(&certificate).unwrap();
        let mut proof_data = [0u8; 40];
        proof_data[..4].copy_from_slice(b"ASPU");
        let mut certificate_data = [0u8; POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES];
        let mut proof_lamports = 1;
        let mut certificate_lamports = 1;
        let certificate_account = account(
            &certificate_key,
            &verifier,
            &mut certificate_lamports,
            &mut certificate_data,
            true,
            true,
        );
        let proof_account = account(
            &proof_key,
            &verifier,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            process_initialize_terminal_pda_certificate_v1(
                &verifier,
                &[certificate_account.clone(), proof_account.clone()],
                &encoded,
            ),
            Ok(())
        );
        assert_eq!(
            process_initialize_terminal_pda_certificate_v1(
                &verifier,
                &[certificate_account, proof_account],
                &encoded,
            ),
            Err(ProgramError::AccountAlreadyInitialized)
        );

        let mut wrong = certificate;
        wrong.bumps[POOL_V1_TERMINAL_PDA_BUMP_MASTER] ^= 1;
        assert_eq!(
            require_canonical_bumps(&wrong),
            Err(ProgramError::InvalidSeeds)
        );
        assert_eq!(
            validate_terminal_pda_certificate_single_attempt_v1(&wrong),
            Err(ProgramError::InvalidSeeds)
        );
    }
}
