//! Native G9 regressions using an existing private-leaf-salt S2 proof.
//!
//! AccountInfo models the runtime owner/flags/data presented to the program;
//! it does not prove System Program creation or historical write provenance.
//! Authentic checkpoints require that provenance plus the release writer guard.
//! The checkpoint checksum is unkeyed and is not a forgery barrier.

use super::*;
use aspis_statement::pool_v1::{PoolIdentityV1, VerifierPolicyV1};
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
        verifier::resume(checkpoint, proof, public, Variant::S2, counted_sha256),
        Err(verifier::Error::Checkpoint)
    ));
    HASH_CALLS.with(|count| assert_eq!(count.get(), calls));
    HASH_CALLS.with(|count| count.set(0));
    assert_eq!(
        verifier::tx2_authenticated(public, proof, checkpoint, counted_sha256, None),
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
            verifier::tx2(PUBLIC, PROOF, checkpoint, sha256, None),
            Ok(())
        );
        assert_eq!(
            verifier::tx2_authenticated(PUBLIC, PROOF, checkpoint, sha256, None),
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
            master: common.master_account,
            deployment_domain: snapshot.deployment_domain,
            checkpoint_sequence: common.checkpoint_sequence,
            global_root: common.historical_global_anchor,
            lane_sequences: [0; POOL_V1_PAIR_FOREST_LANE_COUNT],
        }),
        selected_lane: Box::new(PoolV1PairForestLaneStateV1 {
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
        verifier::resume(&checkpoint, PROOF, PUBLIC, Variant::S2, sha256).unwrap();
    assert_eq!(accumulator.next, 0);
    // Only resume acceptance is asserted. This is not a tx1-produced checkpoint
    // or an assertion of tx2 acceptance; runtime ownership guards are essential.
    let mut fixture = Stage1Fixture::new();
    fixture.accounts[2].data = checkpoint;
    fixture.reject_without_writes(ProgramError::AccountAlreadyInitialized);
}
