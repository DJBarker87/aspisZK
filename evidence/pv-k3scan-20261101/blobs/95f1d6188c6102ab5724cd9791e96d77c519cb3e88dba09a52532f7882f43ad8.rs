//! Compact selected-verifier dispatch for the inactive eight-lane terminal.
//!
//! ASQ8 deliberately carries only registry identity, the Pool program id and
//! the 216-byte payment public input.  The verifier reconstructs the exact
//! ASF8 statement from the canonical read-only master/checkpoint/lane account
//! bytes and the proof-carried candidate afterstate, then returns exact ASR8.

extern crate alloc;

use alloc::{boxed::Box, vec, vec::Vec};

use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_result_v1, encode_pool_v1_pair_forest_terminal_request_v1,
    encode_pool_v1_pair_forest_terminal_result_v1, PoolV1PairForestTerminalRequestV1,
    PoolV1PairForestTerminalResultV1, POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction},
    program,
    program_error::ProgramError,
    pubkey::Pubkey,
};
use solana_sdk_ids::{bpf_loader, bpf_loader_upgradeable, loader_v4};

#[cfg(not(feature = "r1-split-checkpoint"))]
use crate::pair_dispatch::derive_pair_verifier_account_claim_v1;
use crate::{
    error::PoolV1ProgramError,
    registry::{authenticate_verifier_selection_v1, VerifierSelectionV1},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AuthenticatedPairForestResultV1 {
    value: Box<PoolV1PairForestTerminalResultV1>,
    exact_bytes: Box<[u8]>,
}

impl AuthenticatedPairForestResultV1 {
    pub(crate) fn value(&self) -> &PoolV1PairForestTerminalResultV1 {
        &self.value
    }

    pub(crate) fn exact_bytes(&self) -> &[u8] {
        &self.exact_bytes
    }

    #[cfg(test)]
    pub(crate) fn for_test(value: PoolV1PairForestTerminalResultV1) -> Self {
        let exact_bytes =
            aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_result_v1(&value)
                .expect("test result must be canonical")
                .to_vec()
                .into_boxed_slice();
        Self {
            value: Box::new(value),
            exact_bytes,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PlannedPairForestDispatchV1 {
    selected_verifier: Pubkey,
    request_bytes: Vec<u8>,
}

fn supported_loader(owner: &Pubkey) -> bool {
    owner == &bpf_loader::id()
        || owner == &bpf_loader_upgradeable::id()
        || owner == &loader_v4::id()
}

fn require_verifier_program(account: &AccountInfo<'_>, selected: &Pubkey) -> ProgramResult {
    if account.key != selected
        || !account.executable
        || account.is_signer
        || account.is_writable
        || !supported_loader(account.owner)
    {
        return Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into());
    }
    Ok(())
}

/// R1 buffer ownership does not authenticate the selected verifier. Registry
/// selection still does that; only its separate checkpoint must be owned by it.
fn proof_transport_verifier(
    verifier_program: &AccountInfo<'_>,
    proof: &AccountInfo<'_>,
    verifier_checkpoint: Option<&AccountInfo<'_>>,
) -> Result<Pubkey, ProgramError> {
    #[cfg(feature = "r1-split-checkpoint")]
    {
        let checkpoint = verifier_checkpoint.ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof.key == verifier_program.key
            || proof.executable
            || proof.is_signer
            || proof.is_writable
            || checkpoint.owner != verifier_program.key
            || checkpoint.executable
            || checkpoint.is_signer
            || checkpoint.is_writable
            || checkpoint.key == proof.key
            || checkpoint.key == verifier_program.key
        {
            return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
        }
        // The verifier checks the exact checkpoint size and authenticated bytes.
        Ok(*verifier_program.key)
    }
    #[cfg(not(feature = "r1-split-checkpoint"))]
    {
        if verifier_checkpoint.is_some() {
            return Err(ProgramError::InvalidArgument);
        }
        let claim = derive_pair_verifier_account_claim_v1(verifier_program, proof)?;
        Ok(Pubkey::new_from_array(claim.verifier_program))
    }
}

fn require_checkpoint_distinct(
    verifier_checkpoint: Option<&AccountInfo<'_>>,
    master: &AccountInfo<'_>,
    forest_checkpoint: &AccountInfo<'_>,
    lane: &AccountInfo<'_>,
    registry_accounts: &[AccountInfo<'_>],
) -> ProgramResult {
    if let Some(checkpoint) = verifier_checkpoint {
        if [master.key, forest_checkpoint.key, lane.key].contains(&checkpoint.key)
            || registry_accounts
                .iter()
                .any(|account| account.key == checkpoint.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn plan_pair_forest_terminal_dispatch_v1(
    pool_program: &Pubkey,
    master: &AccountInfo<'_>,
    checkpoint: &AccountInfo<'_>,
    lane: &AccountInfo<'_>,
    policy: &aspis_statement::pool_v1::VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'_>],
    verifier_program: &AccountInfo<'_>,
    proof: &AccountInfo<'_>,
    verifier_checkpoint: Option<&AccountInfo<'_>>,
    request: &PoolV1PairForestTerminalRequestV1,
    current_slot: u64,
) -> Result<PlannedPairForestDispatchV1, ProgramError> {
    let request_bytes = encode_pool_v1_pair_forest_terminal_request_v1(request)
        .map_err(|_| ProgramError::InvalidInstructionData)?
        .to_vec();
    plan_pair_forest_terminal_dispatch_with_bytes_v1(
        pool_program,
        master,
        checkpoint,
        lane,
        policy,
        registry_accounts,
        verifier_program,
        proof,
        verifier_checkpoint,
        request,
        current_slot,
        request_bytes,
    )
}

#[allow(clippy::too_many_arguments)]
fn plan_pair_forest_terminal_dispatch_with_bytes_v1(
    pool_program: &Pubkey,
    master: &AccountInfo<'_>,
    checkpoint: &AccountInfo<'_>,
    lane: &AccountInfo<'_>,
    policy: &aspis_statement::pool_v1::VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'_>],
    verifier_program: &AccountInfo<'_>,
    proof: &AccountInfo<'_>,
    verifier_checkpoint: Option<&AccountInfo<'_>>,
    request: &PoolV1PairForestTerminalRequestV1,
    current_slot: u64,
    request_bytes: Vec<u8>,
) -> Result<PlannedPairForestDispatchV1, ProgramError> {
    if request.pool_program != pool_program.to_bytes() {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    let selected = proof_transport_verifier(verifier_program, proof, verifier_checkpoint)?;
    require_verifier_program(verifier_program, &selected)?;
    require_checkpoint_distinct(
        verifier_checkpoint,
        master,
        checkpoint,
        lane,
        registry_accounts,
    )?;
    let authenticated = authenticate_verifier_selection_v1(
        master.key,
        policy,
        registry_accounts,
        VerifierSelectionV1 {
            verifier_program: selected.to_bytes(),
            profile_binding: request.verifier_profile,
            release_binding: request.verifier_release,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        },
        current_slot,
    )?;
    if !authenticated.matches_verifier_owner(verifier_program.owner) {
        return Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into());
    }
    if !authenticated.matches(
        master.key.to_bytes(),
        selected.to_bytes(),
        request.verifier_profile,
        request.verifier_release,
        POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    ) {
        return Err(PoolV1ProgramError::VerifierSelectionMismatch.into());
    }
    let account_keys = [proof.key, master.key, checkpoint.key, lane.key];
    for (index, key) in account_keys.iter().enumerate() {
        if account_keys[..index].iter().any(|previous| previous == key) {
            return Err(ProgramError::InvalidArgument);
        }
    }
    if master.owner != pool_program
        || master.executable
        || master.is_signer
        || checkpoint.owner != pool_program
        || checkpoint.executable
        || checkpoint.is_signer
        || lane.owner != pool_program
        || lane.executable
        || lane.is_signer
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(PlannedPairForestDispatchV1 {
        selected_verifier: selected,
        request_bytes,
    })
}

trait PairForestVerifierRuntimeV1 {
    fn clear_return_data(&mut self);
    fn invoke(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'_>],
    ) -> ProgramResult;
    fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)>;
}

struct SolanaPairForestVerifierRuntimeV1;

impl PairForestVerifierRuntimeV1 for SolanaPairForestVerifierRuntimeV1 {
    fn clear_return_data(&mut self) {
        program::set_return_data(&[]);
    }

    fn invoke(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'_>],
    ) -> ProgramResult {
        program::invoke(instruction, account_infos)
    }

    fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
        program::get_return_data()
    }
}

fn invoke_pair_forest_terminal_with_runtime_v1<'info, R: PairForestVerifierRuntimeV1>(
    plan: PlannedPairForestDispatchV1,
    proof: &AccountInfo<'info>,
    master: &AccountInfo<'info>,
    checkpoint: &AccountInfo<'info>,
    lane: &AccountInfo<'info>,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    verifier_checkpoint: Option<&AccountInfo<'info>>,
    runtime: &mut R,
) -> Result<AuthenticatedPairForestResultV1, ProgramError> {
    require_verifier_program(verifier_program, &plan.selected_verifier)?;
    #[cfg(feature = "r1-split-checkpoint")]
    proof_transport_verifier(verifier_program, proof, verifier_checkpoint)?;
    #[cfg(not(feature = "r1-split-checkpoint"))]
    {
        if proof.owner != &plan.selected_verifier || proof.is_writable || proof.is_signer {
            return Err(PoolV1ProgramError::InvalidVerifierProofAccount.into());
        }
        if verifier_checkpoint.is_some() {
            return Err(ProgramError::InvalidArgument);
        }
    }
    require_checkpoint_distinct(
        verifier_checkpoint,
        master,
        checkpoint,
        lane,
        registry_accounts,
    )?;
    #[cfg(feature = "pair-forest-verifier-lane-invariant-audit")]
    let [registry, entry] = registry_accounts
    else {
        return Err(if registry_accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    #[cfg(feature = "pair-forest-verifier-lane-invariant-audit")]
    let mut cpi_accounts = vec![
        AccountMeta::new_readonly(*proof.key, false),
        AccountMeta::new_readonly(*master.key, false),
        AccountMeta::new_readonly(*checkpoint.key, false),
        AccountMeta::new_readonly(*lane.key, false),
        AccountMeta::new_readonly(*registry.key, false),
        AccountMeta::new_readonly(*entry.key, false),
    ];
    #[cfg(not(feature = "pair-forest-verifier-lane-invariant-audit"))]
    let mut cpi_accounts = vec![
        AccountMeta::new_readonly(*proof.key, false),
        AccountMeta::new_readonly(*master.key, false),
        AccountMeta::new_readonly(*checkpoint.key, false),
        AccountMeta::new_readonly(*lane.key, false),
    ];
    if let Some(checkpoint) = verifier_checkpoint {
        cpi_accounts.push(AccountMeta::new_readonly(*checkpoint.key, false));
    }
    let instruction = Instruction {
        program_id: plan.selected_verifier,
        accounts: cpi_accounts,
        data: plan.request_bytes,
    };
    #[cfg(feature = "pair-forest-verifier-lane-invariant-audit")]
    let mut infos = vec![
        proof.clone(),
        master.clone(),
        checkpoint.clone(),
        lane.clone(),
        registry.clone(),
        entry.clone(),
        verifier_program.clone(),
    ];
    #[cfg(not(feature = "pair-forest-verifier-lane-invariant-audit"))]
    let mut infos = vec![
        proof.clone(),
        master.clone(),
        checkpoint.clone(),
        lane.clone(),
        verifier_program.clone(),
    ];
    if let Some(checkpoint) = verifier_checkpoint {
        infos.insert(infos.len() - 1, checkpoint.clone());
    }
    runtime.clear_return_data();
    runtime.invoke(&instruction, &infos)?;
    let (returned_program, returned_data) = runtime
        .get_return_data()
        .ok_or(PoolV1ProgramError::MissingVerifierReturnData)?;
    if returned_program != plan.selected_verifier {
        return Err(PoolV1ProgramError::InvalidVerifierReturnProgram.into());
    }
    if returned_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES {
        return Err(PoolV1ProgramError::InvalidVerifierReturnData.into());
    }
    let result = decode_pool_v1_pair_forest_terminal_result_v1(&returned_data)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?;
    Ok(AuthenticatedPairForestResultV1 {
        value: Box::new(result),
        exact_bytes: returned_data.into_boxed_slice(),
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn dispatch_pair_forest_terminal_readonly_v1<'info>(
    pool_program: &Pubkey,
    master: &AccountInfo<'info>,
    checkpoint: &AccountInfo<'info>,
    lane: &AccountInfo<'info>,
    policy: &aspis_statement::pool_v1::VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    verifier_checkpoint: Option<&AccountInfo<'info>>,
    request: &PoolV1PairForestTerminalRequestV1,
    current_slot: u64,
) -> Result<AuthenticatedPairForestResultV1, ProgramError> {
    let plan = plan_pair_forest_terminal_dispatch_v1(
        pool_program,
        master,
        checkpoint,
        lane,
        policy,
        registry_accounts,
        verifier_program,
        proof,
        verifier_checkpoint,
        request,
        current_slot,
    )?;
    let mut runtime = SolanaPairForestVerifierRuntimeV1;
    invoke_pair_forest_terminal_with_runtime_v1(
        plan,
        proof,
        master,
        checkpoint,
        lane,
        registry_accounts,
        verifier_program,
        verifier_checkpoint,
        &mut runtime,
    )
}

/// Audit-only full-statement CPI transport. Registry/profile/release and all
/// account checks are identical to ASQ8; only the exact verifier instruction
/// bytes differ.
#[cfg(feature = "pair-forest-full-asf8-audit")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn dispatch_pair_forest_terminal_full_asf8_readonly_v1<'info>(
    pool_program: &Pubkey,
    master: &AccountInfo<'info>,
    checkpoint: &AccountInfo<'info>,
    lane: &AccountInfo<'info>,
    policy: &aspis_statement::pool_v1::VerifierPolicyV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    verifier_checkpoint: Option<&AccountInfo<'info>>,
    request: &PoolV1PairForestTerminalRequestV1,
    current_slot: u64,
    statement_bytes: &[u8],
) -> Result<AuthenticatedPairForestResultV1, ProgramError> {
    if statement_bytes.len()
        != aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
        || !statement_bytes
            .starts_with(&aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let plan = plan_pair_forest_terminal_dispatch_with_bytes_v1(
        pool_program,
        master,
        checkpoint,
        lane,
        policy,
        registry_accounts,
        verifier_program,
        proof,
        verifier_checkpoint,
        request,
        current_slot,
        statement_bytes.to_vec(),
    )?;
    let mut runtime = SolanaPairForestVerifierRuntimeV1;
    invoke_pair_forest_terminal_with_runtime_v1(
        plan,
        proof,
        master,
        checkpoint,
        lane,
        registry_accounts,
        verifier_program,
        verifier_checkpoint,
        &mut runtime,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_terminal_result_v1, encode_verifier_registry_entry_v1,
        encode_verifier_registry_v1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
    };
    use solana_program::clock::Epoch;

    use crate::registry::{pool_v1_verifier_entry_address, pool_v1_verifier_registry_address};

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            false,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    struct MockRuntime {
        returned: Option<(Pubkey, Vec<u8>)>,
        invoked: Option<Instruction>,
    }

    #[test]
    fn proof_transport_preserves_feature_specific_account_contract() {
        let verifier_key = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let checkpoint_key = Pubkey::new_unique();
        let foreign_owner = Pubkey::new_unique();
        let loader = bpf_loader::id();
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let mut checkpoint_lamports = 1;
        let mut verifier_data = [];
        let mut proof_data = vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + 1];
        proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&1u32.to_le_bytes());
        let mut checkpoint_data = [7; 3];
        let verifier = account(
            &verifier_key,
            &loader,
            &mut verifier_lamports,
            &mut verifier_data,
            false,
            true,
        );
        let proof = account(
            &proof_key,
            &verifier_key,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let checkpoint = account(
            &checkpoint_key,
            &verifier_key,
            &mut checkpoint_lamports,
            &mut checkpoint_data,
            false,
            false,
        );
        let mut foreign_proof = proof.clone();
        foreign_proof.owner = &foreign_owner;

        #[cfg(not(feature = "r1-split-checkpoint"))]
        {
            assert_eq!(
                proof_transport_verifier(&verifier, &proof, None),
                Ok(verifier_key)
            );
            assert!(proof_transport_verifier(&verifier, &foreign_proof, None).is_err());
            assert!(proof_transport_verifier(&verifier, &proof, Some(&checkpoint)).is_err());
            proof.try_borrow_mut_data().unwrap()[8] = 1;
            assert!(proof_transport_verifier(&verifier, &proof, None).is_err());
        }
        #[cfg(feature = "r1-split-checkpoint")]
        {
            // No lifecycle magic, authority, or owner is a proof-buffer premise.
            foreign_proof.try_borrow_mut_data().unwrap().fill(0x55);
            assert_eq!(
                proof_transport_verifier(&verifier, &foreign_proof, Some(&checkpoint)),
                Ok(verifier_key)
            );
            assert!(proof_transport_verifier(&verifier, &foreign_proof, None).is_err());
            for kind in 0..6 {
                let mut invalid = checkpoint.clone();
                match kind {
                    0 => invalid.owner = &foreign_owner,
                    1 => invalid.is_writable = true,
                    2 => invalid.is_signer = true,
                    3 => invalid.executable = true,
                    4 => invalid.key = &proof_key,
                    _ => invalid.key = &verifier_key,
                }
                assert!(
                    proof_transport_verifier(&verifier, &foreign_proof, Some(&invalid)).is_err()
                );
            }
            for kind in 0..4 {
                let mut invalid = foreign_proof.clone();
                match kind {
                    0 => invalid.is_writable = true,
                    1 => invalid.is_signer = true,
                    2 => invalid.executable = true,
                    _ => invalid.key = &verifier_key,
                }
                assert!(proof_transport_verifier(&verifier, &invalid, Some(&checkpoint)).is_err());
            }
        }
    }

    #[derive(Clone, Copy)]
    enum ControlledReturn {
        InvokeError,
        Missing,
        WrongProgram,
        WrongLength,
        Malformed,
    }

    struct ControlledRuntime {
        mode: ControlledReturn,
        returned: Option<(Pubkey, Vec<u8>)>,
    }

    fn canonical_result_for(instruction: &Instruction) -> Vec<u8> {
        encode_pool_v1_pair_forest_terminal_result_v1(&PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: instruction.accounts[1].pubkey.to_bytes(),
            selected_lane_account: instruction.accounts[3].pubkey.to_bytes(),
            output_lane: 1,
            nullifier: [M31::ONE; 8],
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: 1,
                next_root: [M31(2); 8],
                next_frontier: core::array::from_fn(|_| [M31::ZERO; 8]),
            },
        })
        .unwrap()
        .to_vec()
    }

    impl PairForestVerifierRuntimeV1 for MockRuntime {
        fn clear_return_data(&mut self) {
            self.returned = None;
        }

        fn invoke(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'_>],
        ) -> ProgramResult {
            assert_eq!(infos.len(), instruction.accounts.len() + 1);
            for (meta, info) in instruction.accounts.iter().zip(infos) {
                assert_eq!(&meta.pubkey, info.key);
            }
            assert_eq!(infos.last().unwrap().key, &instruction.program_id);
            self.invoked = Some(instruction.clone());
            self.returned = Some((instruction.program_id, canonical_result_for(instruction)));
            Ok(())
        }

        fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
            self.returned.clone()
        }
    }

    impl PairForestVerifierRuntimeV1 for ControlledRuntime {
        fn clear_return_data(&mut self) {
            self.returned = None;
        }

        fn invoke(&mut self, instruction: &Instruction, _: &[AccountInfo<'_>]) -> ProgramResult {
            if matches!(self.mode, ControlledReturn::InvokeError) {
                return Err(ProgramError::InvalidAccountData);
            }
            if matches!(self.mode, ControlledReturn::Missing) {
                return Ok(());
            }
            let mut bytes = canonical_result_for(instruction);
            let program = if matches!(self.mode, ControlledReturn::WrongProgram) {
                Pubkey::new_unique()
            } else {
                instruction.program_id
            };
            if matches!(self.mode, ControlledReturn::WrongLength) {
                bytes.pop();
            } else if matches!(self.mode, ControlledReturn::Malformed) {
                bytes.fill(0xff);
            }
            self.returned = Some((program, bytes));
            Ok(())
        }

        fn get_return_data(&mut self) -> Option<(Pubkey, Vec<u8>)> {
            self.returned.clone()
        }
    }

    #[test]
    fn selected_verifier_requires_exact_readonly_executable_supported_loader_account() {
        let selected = Pubkey::new_unique();
        let supported = [
            bpf_loader::id(),
            bpf_loader_upgradeable::id(),
            loader_v4::id(),
        ];
        for loader in supported {
            let mut lamports = 1;
            let mut data = [];
            let verifier = account(&selected, &loader, &mut lamports, &mut data, false, true);
            assert_eq!(require_verifier_program(&verifier, &selected), Ok(()));
        }

        let unsupported = Pubkey::new_unique();
        let mut lamports = 1;
        let mut data = [];
        let mut verifier = account(
            &selected,
            &unsupported,
            &mut lamports,
            &mut data,
            false,
            true,
        );
        assert_eq!(
            require_verifier_program(&verifier, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
        let legacy_loader = bpf_loader::id();
        verifier.owner = &legacy_loader;
        verifier.executable = false;
        assert_eq!(
            require_verifier_program(&verifier, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
        verifier.executable = true;
        verifier.is_writable = true;
        assert_eq!(
            require_verifier_program(&verifier, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
        verifier.is_writable = false;
        verifier.is_signer = true;
        assert_eq!(
            require_verifier_program(&verifier, &selected),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
        verifier.is_signer = false;
        assert_eq!(
            require_verifier_program(&verifier, &Pubkey::new_unique()),
            Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())
        );
    }

    #[test]
    fn verifier_cpi_failures_and_malformed_return_data_leave_all_inputs_unchanged() {
        let selected = Pubkey::new_unique();
        let loader = bpf_loader::id();
        let proof_key = Pubkey::new_unique();
        let master_key = Pubkey::new_unique();
        let checkpoint_key = Pubkey::new_unique();
        let lane_key = Pubkey::new_unique();
        let registry_key = Pubkey::new_unique();
        let entry_key = Pubkey::new_unique();
        let pool_program = Pubkey::new_unique();
        let registry_program = Pubkey::new_unique();
        let mut proof_lamports = 1;
        let mut master_lamports = 1;
        let mut checkpoint_lamports = 1;
        let mut lane_lamports = 1;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_data = [1u8; 3];
        let mut master_data = [2u8; 3];
        let mut checkpoint_data = [3u8; 3];
        let mut lane_data = [4u8; 3];
        let mut registry_data = [5u8; 3];
        let mut entry_data = [6u8; 3];
        let mut verifier_data = [];
        let before = (
            proof_data,
            master_data,
            checkpoint_data,
            lane_data,
            registry_data,
            entry_data,
        );
        let proof = account(
            &proof_key,
            &selected,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let master = account(
            &master_key,
            &pool_program,
            &mut master_lamports,
            &mut master_data,
            false,
            false,
        );
        let checkpoint = account(
            &checkpoint_key,
            &pool_program,
            &mut checkpoint_lamports,
            &mut checkpoint_data,
            false,
            false,
        );
        let lane = account(
            &lane_key,
            &pool_program,
            &mut lane_lamports,
            &mut lane_data,
            true,
            false,
        );
        let registry = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
            false,
            false,
        );
        let entry = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
            false,
            false,
        );
        let verifier = account(
            &selected,
            &loader,
            &mut verifier_lamports,
            &mut verifier_data,
            false,
            true,
        );
        let verifier_checkpoint_key = Pubkey::new_unique();
        let mut verifier_checkpoint_lamports = 1;
        let mut verifier_checkpoint_data = [7u8; 3];
        let verifier_checkpoint = account(
            &verifier_checkpoint_key,
            &selected,
            &mut verifier_checkpoint_lamports,
            &mut verifier_checkpoint_data,
            false,
            false,
        );
        let split_checkpoint =
            cfg!(feature = "r1-split-checkpoint").then_some(&verifier_checkpoint);
        let plan = PlannedPairForestDispatchV1 {
            selected_verifier: selected,
            request_bytes: vec![0u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES],
        };

        for (mode, expected) in [
            (
                ControlledReturn::InvokeError,
                ProgramError::InvalidAccountData,
            ),
            (
                ControlledReturn::Missing,
                PoolV1ProgramError::MissingVerifierReturnData.into(),
            ),
            (
                ControlledReturn::WrongProgram,
                PoolV1ProgramError::InvalidVerifierReturnProgram.into(),
            ),
            (
                ControlledReturn::WrongLength,
                PoolV1ProgramError::InvalidVerifierReturnData.into(),
            ),
            (
                ControlledReturn::Malformed,
                PoolV1ProgramError::InvalidVerifierReturnData.into(),
            ),
        ] {
            let mut runtime = ControlledRuntime {
                mode,
                returned: Some((Pubkey::new_unique(), vec![9u8; 17])),
            };
            assert_eq!(
                invoke_pair_forest_terminal_with_runtime_v1(
                    plan.clone(),
                    &proof,
                    &master,
                    &checkpoint,
                    &lane,
                    &[registry.clone(), entry.clone()],
                    &verifier,
                    split_checkpoint,
                    &mut runtime,
                ),
                Err(expected)
            );
        }
        drop((proof, master, checkpoint, lane, registry, entry, verifier));
        assert_eq!(
            (
                proof_data,
                master_data,
                checkpoint_data,
                lane_data,
                registry_data,
                entry_data,
            ),
            before
        );
    }

    #[test]
    fn compact_dispatch_authenticates_selection_and_forwards_readonly_accounts() {
        let pool_program = Pubkey::new_unique();
        let master_key = Pubkey::new_unique();
        let checkpoint_key = Pubkey::new_unique();
        let lane_key = Pubkey::new_unique();
        let registry_program = Pubkey::new_unique();
        let verifier_key = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let profile = [9u8; 32];
        let release = [10u8; 32];
        let policy = VerifierPolicyV1 {
            flags: 0,
            registry_program: registry_program.to_bytes(),
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        };
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &master_key).0;
        let entry_key =
            pool_v1_verifier_entry_address(&registry_program, &master_key, &profile, &release).0;
        let mut registry_data = encode_verifier_registry_v1(&VerifierRegistryV1 {
            bump: 0,
            flags: 0,
            pool: master_key.to_bytes(),
            authority: policy.registry_authority,
            policy_binding: policy.policy_binding,
            generation: 1,
            minimum_activation_delay_slots: 1,
        })
        .unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            bump: 0,
            status: VerifierEntryStatusV1::Active,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
            pool: master_key.to_bytes(),
            policy_binding: policy.policy_binding,
            verifier_program: verifier_key.to_bytes(),
            profile_binding: profile,
            release_binding: release,
            activation_slot: 0,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        })
        .unwrap();
        let mut proof_data = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + 1];
        proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&1u32.to_le_bytes());
        let mut empty_master = [0u8; 1];
        let mut empty_checkpoint = [0u8; 1];
        let mut empty_lane = [0u8; 1];
        let mut empty_verifier = [];
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut master_lamports = 1;
        let mut checkpoint_lamports = 1;
        let mut lane_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let loader = bpf_loader::id();
        let registry = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
            false,
            false,
        );
        let entry = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
            false,
            false,
        );
        let master = account(
            &master_key,
            &pool_program,
            &mut master_lamports,
            &mut empty_master,
            false,
            false,
        );
        let checkpoint = account(
            &checkpoint_key,
            &pool_program,
            &mut checkpoint_lamports,
            &mut empty_checkpoint,
            false,
            false,
        );
        let lane = account(
            &lane_key,
            &pool_program,
            &mut lane_lamports,
            &mut empty_lane,
            true,
            false,
        );
        let verifier = account(
            &verifier_key,
            &loader,
            &mut verifier_lamports,
            &mut empty_verifier,
            false,
            true,
        );
        let foreign_owner = Pubkey::new_unique();
        if cfg!(feature = "r1-split-checkpoint") {
            proof_data = vec![0x51, 0x52, 0x53]; // No sealed ASPU lifecycle header.
        }
        let proof_owner = if cfg!(feature = "r1-split-checkpoint") {
            &foreign_owner
        } else {
            &verifier_key
        };
        let proof = account(
            &proof_key,
            proof_owner,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let verifier_checkpoint_key = Pubkey::new_unique();
        let mut verifier_checkpoint_lamports = 1;
        let mut verifier_checkpoint_data = [7u8; 3];
        let verifier_checkpoint = account(
            &verifier_checkpoint_key,
            &verifier_key,
            &mut verifier_checkpoint_lamports,
            &mut verifier_checkpoint_data,
            false,
            false,
        );
        let split_checkpoint =
            cfg!(feature = "r1-split-checkpoint").then_some(&verifier_checkpoint);
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: profile,
            verifier_release: release,
            pool_program: pool_program.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                PoolV1PrivateTransferPublicV1 {
                    pool: master_key.to_bytes(),
                    deployment_domain: [2; 32],
                    anchor_sequence: 0,
                    anchor_root: [M31::ZERO; 8],
                    nullifier: [M31::ONE; 8],
                    asset_id: M31(3),
                    recipient_commitment: [M31(4); 8],
                    change_commitment: [M31(5); 8],
                },
            ),
        };
        let plan = plan_pair_forest_terminal_dispatch_v1(
            &pool_program,
            &master,
            &checkpoint,
            &lane,
            &policy,
            &[registry.clone(), entry.clone()],
            &verifier,
            &proof,
            split_checkpoint,
            &request,
            1,
        )
        .unwrap();
        assert_eq!(
            plan.request_bytes.len(),
            POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
        );
        #[cfg(feature = "r1-split-checkpoint")]
        for alias in [
            master.key,
            checkpoint.key,
            lane.key,
            registry.key,
            entry.key,
        ] {
            let mut invalid = verifier_checkpoint.clone();
            invalid.key = alias;
            assert!(plan_pair_forest_terminal_dispatch_v1(
                &pool_program,
                &master,
                &checkpoint,
                &lane,
                &policy,
                &[registry.clone(), entry.clone()],
                &verifier,
                &proof,
                Some(&invalid),
                &request,
                1,
            )
            .is_err());
            let mut untouched_runtime = MockRuntime {
                returned: None,
                invoked: None,
            };
            assert!(invoke_pair_forest_terminal_with_runtime_v1(
                plan.clone(),
                &proof,
                &master,
                &checkpoint,
                &lane,
                &[registry.clone(), entry.clone()],
                &verifier,
                Some(&invalid),
                &mut untouched_runtime,
            )
            .is_err());
            assert!(untouched_runtime.invoked.is_none());
        }
        let mut runtime = MockRuntime {
            returned: None,
            invoked: None,
        };
        let authenticated = invoke_pair_forest_terminal_with_runtime_v1(
            plan,
            &proof,
            &master,
            &checkpoint,
            &lane,
            &[registry.clone(), entry.clone()],
            &verifier,
            split_checkpoint,
            &mut runtime,
        )
        .unwrap();
        assert_eq!(authenticated.value().master_account, master_key.to_bytes());
        let invoked = runtime.invoked.unwrap();
        #[cfg(feature = "pair-forest-verifier-lane-invariant-audit")]
        assert_eq!(
            invoked.accounts.len(),
            6 + usize::from(cfg!(feature = "r1-split-checkpoint"))
        );
        #[cfg(feature = "r1-split-checkpoint")]
        assert_eq!(invoked.accounts[6].pubkey, verifier_checkpoint_key);
        #[cfg(not(feature = "pair-forest-verifier-lane-invariant-audit"))]
        assert_eq!(invoked.accounts.len(), 4);
        assert!(invoked
            .accounts
            .iter()
            .all(|meta| !meta.is_writable && !meta.is_signer));
        assert_eq!(invoked.data.len(), 320);

        let mut wrong = request;
        wrong.verifier_release[0] ^= 1;
        assert!(plan_pair_forest_terminal_dispatch_v1(
            &pool_program,
            &master,
            &checkpoint,
            &lane,
            &policy,
            &[registry, entry],
            &verifier,
            &proof,
            split_checkpoint,
            &wrong,
            1,
        )
        .is_err());
    }

    const _: () = assert!(POOL_V1_PAIR_TREE_DEPTH == 20);
}
