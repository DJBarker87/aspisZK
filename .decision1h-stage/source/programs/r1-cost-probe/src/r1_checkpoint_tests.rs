//! Native G9 regressions using an existing private-leaf-salt S2 proof.
//!
//! AccountInfo models the runtime owner/flags/data presented to the program;
//! it does not prove System Program creation or historical write provenance.
//! Authentic checkpoints require that provenance plus the release writer guard.
//! The checkpoint checksum is unkeyed and is not a forgery barrier.

use super::*;
use aspis_statement::pool_v1::{
    encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
    encode_pool_v1_pair_forest_master_v1, encode_verifier_registry_entry_v1,
    encode_verifier_registry_entry_v2, encode_verifier_registry_v1, encode_verifier_registry_v2,
    PoolIdentityV1, VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1,
    VerifierRegistryEntryV2, VerifierRegistryV1, VerifierRegistryV2,
    POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use std::{cell::Cell, sync::OnceLock};

const PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/research/100bit-spend-path-20261013/evidence/",
    "p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin"
));
const PUBLIC: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/research/100bit-spend-path-20261013/evidence/",
    "p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin"
));

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    hashv(parts).to_bytes()
}

thread_local! {
    static HASH_CALLS: Cell<usize> = const { Cell::new(0) };
}

fn counted_sha256(parts: &[&[u8]]) -> [u8; 32] {
    HASH_CALLS.with(|calls| calls.set(calls.get() + 1));
    sha256(parts)
}

#[derive(Clone, Copy)]
struct TestDigest;
impl aspis_core::Digest32 for TestDigest {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] { sha256(parts) }
}

#[derive(Clone, Copy)]
struct CountedDigest;
impl aspis_core::Digest32 for CountedDigest {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] { counted_sha256(parts) }
}

struct TestAccount {
    key: Pubkey,
    owner: Pubkey,
    lamports: u64,
    data: Vec<u8>,
    signer: bool,
    writable: bool,
    executable: bool,
}

impl TestAccount {
    fn new(owner: Pubkey, data: Vec<u8>, writable: bool) -> Self {
        Self {
            key: Pubkey::new_unique(),
            owner,
            lamports: 1,
            data,
            signer: false,
            writable,
            executable: false,
        }
    }

    fn info(&mut self) -> AccountInfo<'_> {
        AccountInfo::new(
            &self.key,
            self.signer,
            self.writable,
            &mut self.lamports,
            &mut self.data,
            &self.owner,
            self.executable,
            0,
        )
    }
}

struct Stage1Fixture {
    program: Pubkey,
    accounts: [TestAccount; 3],
}

impl Stage1Fixture {
    fn new() -> Self {
        let statement = decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
        let mut proof = encode_pool_v1_pair_verified_afterstate_v1(
            &statement.common().lane_transition.candidate_afterstate,
        )
        .unwrap()
        .to_vec();
        proof.extend_from_slice(PROOF);
        let program = Pubkey::new_unique();
        Self {
            program,
            accounts: [
                TestAccount::new(Pubkey::new_unique(), proof, false),
                TestAccount::new(Pubkey::new_unique(), PUBLIC.to_vec(), false),
                TestAccount::new(
                    program,
                    vec![0; verifier::checkpoint_size(Variant::S2)],
                    true,
                ),
            ],
        }
    }

    fn run(&mut self, k: u8) -> ProgramResult {
        let accounts: Vec<_> = self.accounts.iter_mut().map(TestAccount::info).collect();
        stage1(&self.program, &accounts, &[3, k])
    }

    fn reject_without_writes(&mut self, error: ProgramError) {
        let before: Vec<_> = self.accounts.iter().map(|a| a.data.clone()).collect();
        let lamports: Vec<_> = self.accounts.iter().map(|a| a.lamports).collect();
        assert_eq!(self.run(11), Err(error));
        for (index, account) in self.accounts.iter().enumerate() {
            assert_eq!(account.data, before[index], "account {index} changed");
            assert_eq!(account.lamports, lamports[index]);
        }
    }
}

fn saved_checkpoint() -> &'static [u8] {
    static CHECKPOINT: OnceLock<Vec<u8>> = OnceLock::new();
    CHECKPOINT.get_or_init(|| {
        let mut fixture = Stage1Fixture::new();
        fixture.run(11).unwrap();
        fixture.accounts[2].data.clone()
    })
}

fn assert_hash_binding_rejection(proof: &[u8], public: &[u8], checkpoint: &[u8], calls: usize) {
    HASH_CALLS.with(|count| count.set(0));
    assert!(matches!(
        verifier::resume(checkpoint, proof, public, Variant::S2, CountedDigest),
        Err(verifier::Error::Checkpoint)
    ));
    HASH_CALLS.with(|count| assert_eq!(count.get(), calls));
    HASH_CALLS.with(|count| count.set(0));
    assert_eq!(
        verifier::tx2_authenticated(public, proof, checkpoint, CountedDigest, None),
        Err(verifier::Error::Checkpoint)
    );
    HASH_CALLS.with(|count| assert_eq!(count.get(), calls));
}

#[test]
fn stage1_accepts_foreign_readonly_raw_buffers_and_only_writes_checkpoint() {
    assert_eq!(PROOF.len(), 124_343);
    assert_eq!(PUBLIC.len(), 1_880);
    assert_eq!(verifier::checkpoint_size(Variant::S2), 1_768);
    for k in [10, 11] {
        let mut fixture = Stage1Fixture::new();
        assert_ne!(fixture.accounts[0].owner, fixture.program);
        assert_ne!(fixture.accounts[1].owner, fixture.program);
        let before: Vec<_> = fixture.accounts.iter().map(|a| a.data.clone()).collect();
        fixture.run(k).unwrap();
        assert_eq!(fixture.accounts[0].data, before[0]);
        assert_eq!(fixture.accounts[1].data, before[1]);
        assert!(fixture.accounts.iter().all(|a| a.lamports == 1));
        let checkpoint = &fixture.accounts[2].data;
        assert_eq!(&checkpoint[..8], b"R1P2CKP2");
        assert_eq!(checkpoint[9], k);
        assert_eq!(&checkpoint[16..48], &sha256(&[PROOF]));
        assert_eq!(&checkpoint[48..80], &sha256(&[PUBLIC]));
        assert_eq!(
            verifier::tx2(PUBLIC, PROOF, checkpoint, TestDigest, None),
            Ok(())
        );
        assert_eq!(
            verifier::tx2_authenticated(PUBLIC, PROOF, checkpoint, TestDigest, None),
            Ok(())
        );
        // A second stage1 must not replace an already initialized checkpoint.
        fixture.reject_without_writes(ProgramError::AccountAlreadyInitialized);
    }
}

#[test]
fn stage1_rejects_occupied_checkpoint() {
    for offset in [0, 80, 1_767] {
        let mut fixture = Stage1Fixture::new();
        fixture.accounts[2].data[offset] = 1;
        fixture.reject_without_writes(ProgramError::AccountAlreadyInitialized);
    }
}

#[test]
fn stage1_rejects_checkpoint_wrong_size() {
    for length in [0, 1_767, 1_769] {
        let mut fixture = Stage1Fixture::new();
        fixture.accounts[2].data.resize(length, 0);
        fixture.reject_without_writes(ProgramError::InvalidAccountData);
    }
}

#[test]
fn stage1_rejects_checkpoint_wrong_owner() {
    let mut fixture = Stage1Fixture::new();
    fixture.accounts[2].owner = Pubkey::new_unique();
    fixture.reject_without_writes(ProgramError::InvalidAccountData);
}

#[test]
fn stage1_rejects_all_account_alias_pairs() {
    for (left, right) in [(0, 1), (0, 2), (1, 2)] {
        let mut fixture = Stage1Fixture::new();
        fixture.accounts[right].key = fixture.accounts[left].key;
        fixture.reject_without_writes(ProgramError::InvalidArgument);
    }
}

#[test]
fn stage1_rejects_proof_buffer_flags() {
    for flag in 0..3 {
        let mut fixture = Stage1Fixture::new();
        let account = &mut fixture.accounts[0];
        match flag {
            0 => account.writable = true,
            1 => account.signer = true,
            _ => account.executable = true,
        }
        fixture.reject_without_writes(ProgramError::InvalidAccountData);
    }
}

#[test]
fn stage1_rejects_public_buffer_flags() {
    for flag in 0..3 {
        let mut fixture = Stage1Fixture::new();
        let account = &mut fixture.accounts[1];
        match flag {
            0 => account.writable = true,
            1 => account.signer = true,
            _ => account.executable = true,
        }
        fixture.reject_without_writes(ProgramError::InvalidAccountData);
    }
}

#[test]
fn stage1_rejects_checkpoint_flags() {
    for flag in 0..3 {
        let mut fixture = Stage1Fixture::new();
        let account = &mut fixture.accounts[2];
        match flag {
            0 => account.writable = false,
            1 => account.signer = true,
            _ => account.executable = true,
        }
        fixture.reject_without_writes(ProgramError::InvalidAccountData);
    }
}

#[test]
fn stage1_rejects_truncated_or_extended_raw_buffers() {
    for account in [0, 1] {
        for extend in [false, true] {
            let mut fixture = Stage1Fixture::new();
            if extend {
                fixture.accounts[account].data.push(0);
            } else {
                fixture.accounts[account].data.pop();
            }
            fixture.reject_without_writes(ProgramError::InvalidAccountData);
        }
    }
}

#[test]
fn stage1_rejects_candidate_that_disagrees_with_public() {
    let mut fixture = Stage1Fixture::new();
    let scanned = scan_proof_buffer(&fixture.accounts[0].data).unwrap();
    let mut candidate = *scanned.candidate_afterstate;
    candidate.next_root[0] = candidate.next_root[0].add(M31::ONE);
    fixture.accounts[0].data[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
        .copy_from_slice(&encode_pool_v1_pair_verified_afterstate_v1(&candidate).unwrap());
    fixture.reject_without_writes(ProgramError::InvalidAccountData);
}

#[test]
fn checkpoint_borrow_conflict_returns_error_without_panicking() {
    let mut fixture = Stage1Fixture::new();
    let accounts: Vec<_> = fixture.accounts.iter_mut().map(TestAccount::info).collect();
    let _held = accounts[2].try_borrow_mut_data().unwrap();
    assert_eq!(
        stage1(&fixture.program, &accounts, &[3, 11]),
        Err(ProgramError::AccountBorrowFailed)
    );
}

#[test]
fn stage2_checkpoint_guard_requires_readonly_owner_and_exact_size() {
    let program = Pubkey::new_unique();
    let mut account = TestAccount::new(program, saved_checkpoint().to_vec(), false);
    assert_eq!(
        require_verifier_checkpoint(&account.info(), &program, false),
        Ok(())
    );
    for change in 0..5 {
        let mut account = TestAccount::new(program, saved_checkpoint().to_vec(), false);
        match change {
            0 => account.owner = Pubkey::new_unique(),
            1 => account.writable = true,
            2 => account.signer = true,
            3 => account.executable = true,
            _ => {
                account.data.pop();
            }
        }
        assert_eq!(
            require_verifier_checkpoint(&account.info(), &program, false),
            Err(ProgramError::InvalidAccountData)
        );
    }
}

#[test]
fn stage2_authentication_rejects_all_seven_account_alias_pairs() {
    let program = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    for left in 0..7 {
        for right in left + 1..7 {
            let mut accounts: [TestAccount; 7] = core::array::from_fn(|index| {
                let owner = match index {
                    1..=3 => pool,
                    6 => program,
                    _ => Pubkey::new_unique(),
                };
                let data = if index == 6 {
                    vec![0; verifier::checkpoint_size(Variant::S2)]
                } else {
                    Vec::new()
                };
                TestAccount::new(owner, data, false)
            });
            accounts[right].key = accounts[left].key;
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            // Exercise the actual authentication prefix, before decoding Pool
            // accounts. Index 2 (Pool checkpoint) must differ from index 6.
            assert!(matches!(
                authenticate_asq8_accounts(&program, &infos, &pool, 0, 0),
                Err(ProgramError::InvalidArgument)
            ));
        }
    }
}

/// Construct only the inputs to the reconstruction helper. Registry policy,
/// owners, PDAs and account history are deliberately outside this unit test.
fn reconstruction_inputs(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> (PoolV1PairForestTerminalRequestV1, AuthenticatedAsq8Accounts) {
    let common = statement.common();
    let snapshot = common.lane_transition.live_snapshot;
    let (public, asset_id) = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => (
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*public),
            public.asset_id,
        ),
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => (
            PoolV1PairForestTerminalPaymentV1::Withdrawal(*public),
            public.asset_id,
        ),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: PROFILE_BINDING,
        verifier_release: RELEASE_BINDING,
        pool_program: AUDIT_POOL_PROGRAM,
        public,
    };
    let authenticated = AuthenticatedAsq8Accounts {
        master_account: common.master_account,
        checkpoint_account: common.checkpoint_account,
        selected_lane_account: common.selected_lane_account,
        master: Box::new(PoolV1PairForestMasterV1 {
            bump: 0, // Reconstruction-only input; this helper does not authenticate PDAs.
            identity: PoolIdentityV1 {
                pool: snapshot.pool,
                asset_mint: [1; 32],
                token_program: [2; 32],
                asset_id,
                deployment_domain: snapshot.deployment_domain,
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: [3; 32],
                registry_authority: [4; 32],
                policy_binding: AUDIT_POLICY_BINDING,
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: true,
            next_checkpoint_sequence: common.checkpoint_sequence + 1,
            last_checkpoint_lane_sequences: [0; POOL_V1_PAIR_FOREST_LANE_COUNT],
        }),
        checkpoint: Box::new(PoolV1PairForestCheckpointV1 {
            bump: 0, // Reconstruction-only input; this helper does not authenticate PDAs.
            master: common.master_account,
            deployment_domain: snapshot.deployment_domain,
            checkpoint_sequence: common.checkpoint_sequence,
            global_root: common.historical_global_anchor,
            lane_sequences: [0; POOL_V1_PAIR_FOREST_LANE_COUNT],
        }),
        selected_lane: Box::new(PoolV1PairForestLaneStateV1 {
            bump: 0, // Reconstruction-only input; this helper does not authenticate PDAs.
            master: common.master_account,
            lane_id: common.output_lane,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: snapshot.next_pair_index,
                root: snapshot.current_root,
                frontier: snapshot.frontier,
            },
        }),
        live_snapshot: Box::new(snapshot),
    };
    (request, authenticated)
}

#[test]
fn changed_candidate_is_reconstructed_into_public_hash_binding() {
    let checkpoint = saved_checkpoint();
    let mut fixture = Stage1Fixture::new();
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
    let (request, authenticated) = reconstruction_inputs(&statement);
    let scanned = scan_proof_buffer(&fixture.accounts[0].data).unwrap();
    assert_eq!(scanned.proof_length, PROOF.len());
    let original =
        reconstruct_asq8_statement(&request, &authenticated, &scanned.candidate_afterstate)
            .unwrap();
    assert_eq!(
        encode_pool_v1_pair_forest_terminal_statement_v1(&original)
            .unwrap()
            .as_slice(),
        PUBLIC
    );

    let mut candidate = *scanned.candidate_afterstate;
    candidate.next_root[0] = candidate.next_root[0].add(M31::ONE);
    fixture.accounts[0].data[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
        .copy_from_slice(&encode_pool_v1_pair_verified_afterstate_v1(&candidate).unwrap());
    let changed = scan_proof_buffer(&fixture.accounts[0].data).unwrap();
    let reconstructed =
        reconstruct_asq8_statement(&request, &authenticated, &changed.candidate_afterstate)
            .unwrap();
    let public = encode_pool_v1_pair_forest_terminal_statement_v1(&reconstructed).unwrap();
    assert_ne!(public.as_slice(), PUBLIC);
    let proof = &fixture.accounts[0].data[POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES..];
    assert_eq!(proof, PROOF);
    // The proof hash does not cover the candidate prefix. Actual ASQ8
    // reconstruction puts that prefix into ASF8, so the public hash rejects it.
    assert_hash_binding_rejection(proof, &public, checkpoint, 2);
}

#[test]
fn resume_and_authenticated_tx2_reject_changed_proof_bytes() {
    let checkpoint = saved_checkpoint();
    let mut proof = PROOF.to_vec();
    // An opaque semantic byte passes shape parsing; the whole-proof hash fails.
    proof[verifier::HEADER] ^= 1;
    assert_hash_binding_rejection(&proof, PUBLIC, checkpoint, 1);
}

#[test]
fn resume_and_authenticated_tx2_reject_changed_public_bytes() {
    let checkpoint = saved_checkpoint();
    let mut public = PUBLIC.to_vec();
    public[0] ^= 1;
    assert_hash_binding_rejection(PROOF, &public, checkpoint, 2);
}

#[test]
fn resume_and_authenticated_tx2_reject_raw_checkpoint_mutations() {
    let original = saved_checkpoint();
    for (offset, calls) in [
        (0, 0),
        (8, 0),
        (10, 0),
        (11, 0),
        (16, 1),
        (48, 2),
        (80, 3),
        (1_767, 3),
    ] {
        let mut checkpoint = original.to_vec();
        checkpoint[offset] ^= 1;
        assert_hash_binding_rejection(PROOF, PUBLIC, &checkpoint, calls);
    }
    let mut checkpoint = original.to_vec();
    checkpoint[9] = 23;
    assert_hash_binding_rejection(PROOF, PUBLIC, &checkpoint, 0);
    checkpoint.pop();
    assert_hash_binding_rejection(PROOF, PUBLIC, &checkpoint, 0);
}

#[test]
fn unkeyed_checksum_does_not_establish_checkpoint_provenance() {
    let mut checkpoint = saved_checkpoint().to_vec();
    checkpoint[9] = 0;
    let end = checkpoint.len() - 32;
    let checksum = sha256(&[b"UNPROVED:R1:checkpoint", &checkpoint[..end]]);
    checkpoint[end..].copy_from_slice(&checksum);
    let (_, accumulator) =
        verifier::resume(&checkpoint, PROOF, PUBLIC, Variant::S2, TestDigest).unwrap();
    assert_eq!(accumulator.next, 0);
    // Only resume acceptance is asserted. This is not a tx1-produced checkpoint
    // or an assertion of tx2 acceptance; runtime ownership guards are essential.
    let mut fixture = Stage1Fixture::new();
    fixture.accounts[2].data = checkpoint;
    fixture.reject_without_writes(ProgramError::AccountAlreadyInitialized);
}

/// Canonical SDK address/bump pairs model the owning programs' initializers.
/// Tests exercise account authentication only; no proof generation is involved.
struct PdaFixture {
    program: Pubkey,
    pool: Pubkey,
    lane: u8,
    accounts: [TestAccount; 7],
}

impl PdaFixture {
    fn new(immutable_deployment: bool) -> Self {
        let program = Pubkey::new_unique();
        let pool = Pubkey::new_from_array(AUDIT_POOL_PROGRAM);
        let registry_program = Pubkey::new_from_array(AUDIT_REGISTRY_PROGRAM);
        let mint = Pubkey::new_unique();
        let (master_key, master_bump) =
            Pubkey::find_program_address(&[PAIR_FOREST_MASTER_SEED, mint.as_ref()], &pool);
        let lane = 3;
        let (lane_key, lane_bump) = Pubkey::find_program_address(
            &[PAIR_FOREST_LANE_SEED, master_key.as_ref(), &[lane]],
            &pool,
        );
        let sequence = 7u64;
        let (checkpoint_key, checkpoint_bump) = Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_key.as_ref(),
                &sequence.to_le_bytes(),
            ],
            &pool,
        );
        let master = PoolV1PairForestMasterV1 {
            bump: master_bump,
            identity: PoolIdentityV1 {
                pool: master_key.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: Pubkey::new_unique().to_bytes(),
                asset_id: M31(17),
                deployment_domain: [5; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                    | if immutable_deployment {
                        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT
                    } else {
                        0
                    },
                registry_program: registry_program.to_bytes(),
                registry_authority: [0; 32],
                policy_binding: AUDIT_POLICY_BINDING,
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: true,
            next_checkpoint_sequence: sequence + 1,
            last_checkpoint_lane_sequences: [0; POOL_V1_PAIR_FOREST_LANE_COUNT],
        };
        let empty = v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
        let lane_state = PoolV1PairForestLaneStateV1 {
            bump: lane_bump,
            master: master_key.to_bytes(),
            lane_id: lane,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: empty[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| empty[level]),
            },
        };
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: checkpoint_bump,
            master: master_key.to_bytes(),
            deployment_domain: master.identity.deployment_domain,
            checkpoint_sequence: sequence,
            global_root: [M31(1); 8],
            lane_sequences: [0; POOL_V1_PAIR_FOREST_LANE_COUNT],
        };
        let registry_seed = if immutable_deployment {
            VERIFIER_REGISTRY_V2_SEED
        } else {
            VERIFIER_REGISTRY_SEED
        };
        let entry_seed = if immutable_deployment {
            VERIFIER_ENTRY_V2_SEED
        } else {
            VERIFIER_ENTRY_SEED
        };
        let (registry_key, registry_bump) =
            Pubkey::find_program_address(&[registry_seed, master_key.as_ref()], &registry_program);
        let (entry_key, entry_bump) = Pubkey::find_program_address(
            &[
                entry_seed,
                master_key.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
            ],
            &registry_program,
        );
        let (registry_data, entry_data) = if immutable_deployment {
            let loader = bpf_loader_upgradeable::id();
            let (registry_programdata, registry_programdata_bump) =
                Pubkey::find_program_address(&[registry_program.as_ref()], &loader);
            let (verifier_programdata, verifier_programdata_bump) =
                Pubkey::find_program_address(&[program.as_ref()], &loader);
            let registry = VerifierRegistryV2 {
                bump: registry_bump,
                programdata_bump: registry_programdata_bump,
                flags: POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
                pool: master_key.to_bytes(),
                authority: [0; 32],
                policy_binding: AUDIT_POLICY_BINDING,
                generation: 1,
                minimum_activation_delay_slots: 1,
                registry_program: registry_program.to_bytes(),
                loader_program: loader.to_bytes(),
                programdata_address: registry_programdata.to_bytes(),
                executable_hash: [0xa5; 32],
            };
            let entry = VerifierRegistryEntryV2 {
                bump: entry_bump,
                programdata_bump: verifier_programdata_bump,
                status: VerifierEntryStatusV1::Active,
                statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
                pool: master_key.to_bytes(),
                verifier_program: program.to_bytes(),
                profile_binding: PROFILE_BINDING,
                release_binding: RELEASE_BINDING,
                loader_program: loader.to_bytes(),
                programdata_address: verifier_programdata.to_bytes(),
                executable_hash: [0x5a; 32],
                expected_upgrade_authority: [0; 32],
                activation_slot: 0,
                retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
                policy_binding: AUDIT_POLICY_BINDING,
            };
            (
                encode_verifier_registry_v2(&registry).unwrap().to_vec(),
                encode_verifier_registry_entry_v2(&entry).unwrap().to_vec(),
            )
        } else {
            let registry = VerifierRegistryV1 {
                bump: registry_bump,
                flags: POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
                pool: master_key.to_bytes(),
                authority: [0; 32],
                policy_binding: AUDIT_POLICY_BINDING,
                generation: 1,
                minimum_activation_delay_slots: 1,
            };
            let entry = VerifierRegistryEntryV1 {
                bump: entry_bump,
                status: VerifierEntryStatusV1::Active,
                statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
                pool: master_key.to_bytes(),
                verifier_program: program.to_bytes(),
                profile_binding: PROFILE_BINDING,
                release_binding: RELEASE_BINDING,
                activation_slot: 0,
                retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
                policy_binding: AUDIT_POLICY_BINDING,
            };
            (
                encode_verifier_registry_v1(&registry).unwrap().to_vec(),
                encode_verifier_registry_entry_v1(&entry).unwrap().to_vec(),
            )
        };
        let mut accounts = [
            TestAccount::new(Pubkey::new_unique(), Vec::new(), false),
            TestAccount::new(
                pool,
                encode_pool_v1_pair_forest_master_v1(&master)
                    .unwrap()
                    .to_vec(),
                false,
            ),
            TestAccount::new(
                pool,
                encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                    .unwrap()
                    .to_vec(),
                false,
            ),
            TestAccount::new(
                pool,
                encode_pool_v1_pair_forest_lane_state_v1(&lane_state, &empty)
                    .unwrap()
                    .to_vec(),
                false,
            ),
            TestAccount::new(registry_program, registry_data, false),
            TestAccount::new(registry_program, entry_data, false),
            TestAccount::new(
                program,
                vec![0; verifier::checkpoint_size(Variant::S2)],
                false,
            ),
        ];
        accounts[1].key = master_key;
        accounts[2].key = checkpoint_key;
        accounts[3].key = lane_key;
        accounts[4].key = registry_key;
        accounts[5].key = entry_key;
        Self {
            program,
            pool,
            lane,
            accounts,
        }
    }

    fn authenticate(&mut self) -> Result<AuthenticatedAsq8Accounts, ProgramError> {
        let infos: Vec<_> = self.accounts.iter_mut().map(TestAccount::info).collect();
        authenticate_asq8_accounts(&self.program, &infos, &self.pool, self.lane, 0)
    }
}

#[test]
fn canonical_stored_bumps_authenticate_both_registry_branches() {
    for immutable in [false, true] {
        let mut fixture = PdaFixture::new(immutable);
        let authenticated = fixture.authenticate().unwrap();
        assert_eq!(authenticated.master.bump, fixture.accounts[1].data[7]);
        assert_eq!(authenticated.checkpoint.bump, fixture.accounts[2].data[7]);
        assert_eq!(
            authenticated.selected_lane.bump,
            fixture.accounts[3].data[72]
        );
    }
}

#[test]
fn authentication_rejects_each_wrong_stored_bump_without_fallback() {
    for immutable in [false, true] {
        let mut fixture = PdaFixture::new(immutable);
        fixture.authenticate().unwrap();
        let locations: &[(usize, usize)] = if immutable {
            &[
                (1, 7),
                (2, 7),
                (3, 72),
                (4, 7),
                (4, 248),
                (5, 312),
                (5, 313),
            ]
        } else {
            &[(1, 7), (2, 7), (3, 72), (4, 6), (5, 7)]
        };
        for &(account, offset) in locations {
            let original = fixture.accounts[account].data[offset];
            fixture.accounts[account].data[offset] ^= 1;
            assert!(
                matches!(
                    fixture.authenticate(),
                    Err(ProgramError::InvalidAccountData)
                ),
                "accepted altered bump in account {account} at {offset}, immutable={immutable}"
            );
            fixture.accounts[account].data[offset] = original;
        }
        fixture.authenticate().unwrap();
    }
}

#[test]
fn authentication_rejects_wrong_owners_and_old_account_versions() {
    for immutable in [false, true] {
        let mut fixture = PdaFixture::new(immutable);
        fixture.authenticate().unwrap();
        for account in 1..=5 {
            let owner = fixture.accounts[account].owner;
            fixture.accounts[account].owner = Pubkey::new_unique();
            assert!(matches!(
                fixture.authenticate(),
                Err(ProgramError::InvalidAccountData)
            ));
            fixture.accounts[account].owner = owner;
            let version = fixture.accounts[account].data[4];
            fixture.accounts[account].data[4] -= 1;
            assert!(matches!(
                fixture.authenticate(),
                Err(ProgramError::InvalidAccountData)
            ));
            fixture.accounts[account].data[4] = version;
        }
        fixture.authenticate().unwrap();
    }
}

#[test]
fn manual_lane_decoder_preserves_bump_and_rejects_remaining_reserved_bytes() {
    let fixture = PdaFixture::new(true);
    let mut bytes = fixture.accounts[3].data.clone();
    assert_eq!(
        decode_lane_from_pool_release(&bytes).unwrap().bump,
        bytes[72]
    );
    for offset in 73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES {
        bytes[offset] = 1;
        assert!(matches!(
            decode_lane_from_pool_release(&bytes),
            Err(ProgramError::InvalidAccountData)
        ));
        bytes[offset] = 0;
    }
}

#[test]
fn measured_core_call_counts_include_zero_progress_checkpoint() {
    // These are measurements of this saved fixture and the concrete HashFn,
    // not a universal source theorem or an instrumentation of PDA syscalls.
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
    let public = match &statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public } => {
            Public::Transfer(public, &common.lane_transition)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { common, public } => {
            Public::Withdrawal(public, &common.lane_transition)
        }
    };
    for k in [10, 11] {
        HASH_CALLS.with(|count| count.set(0));
        let checkpoint = verifier::tx1(public, PUBLIC, PROOF, k, CountedDigest, None).unwrap();
        HASH_CALLS.with(|count| assert_eq!(count.get(), 118 + 21 * k));
        HASH_CALLS.with(|count| count.set(0));
        verifier::tx2_authenticated(PUBLIC, PROOF, &checkpoint, CountedDigest, None).unwrap();
        HASH_CALLS.with(|count| assert_eq!(count.get(), 3 + 21 * (22 - k)));
    }
    // Unkeyed checksum plus arbitrary account bytes admits next=0 at resume.
    // All 22 query openings run. Repeating valid equations still satisfies the
    // final relation for this honest proof, despite the checkpoint not being
    // a tx1 output. This does not bypass the account-provenance requirement.
    let mut checkpoint = saved_checkpoint().to_vec();
    checkpoint[9] = 0;
    let end = checkpoint.len() - 32;
    let checksum = sha256(&[b"UNPROVED:R1:checkpoint", &checkpoint[..end]]);
    checkpoint[end..].copy_from_slice(&checksum);
    HASH_CALLS.with(|count| count.set(0));
    assert_eq!(
        verifier::tx2_authenticated(PUBLIC, PROOF, &checkpoint, CountedDigest, None),
        Ok(())
    );
    HASH_CALLS.with(|count| assert_eq!(count.get(), 465));
}
