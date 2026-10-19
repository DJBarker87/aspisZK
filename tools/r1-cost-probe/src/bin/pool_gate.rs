#![recursion_limit = "512"]

use std::{
    env,
    fs::{self, OpenOptions},
    os::unix::fs::{OpenOptionsExt, PermissionsExt},
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    encode_pair_forest_terminal_instruction_data_v1, pool_v1_pair_forest_nullifier_marker_address,
    pool_v1_pair_forest_terminal_bump_hints_v1, POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES,
    pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_master_address,
    pool_v1_root_page_address, pool_v1_vault_authority_address,
    pool_v1_vault_token_account_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
#[cfg(feature = "private-leaf-salts")]
use aspis_prover::state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets};
use aspis_prover::{
    r0_fixture::statement_public,
    v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1, HOST_HASH,
};
use aspis_r1_cost_probe::{prover, transport::Variant, verifier};
use aspis_registry::{
    encode_initialize_registry_v2, encode_schedule_profile_v2, encode_simple_mutation_v2,
    pool_v1_verifier_entry_v2_address, pool_v1_verifier_registry_v2_address,
    RegistryMutationOpcodeV1,
};
use aspis_statement::pool_v1::root_history::{
    append_root_history_page_bytes_v1, initialize_root_history_page_bytes_v1, root_history_location,
};
use aspis_statement::{
    derive_owner_key, encode_digest_canonical,
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1, decode_pool_v1_nullifier_marker,
        decode_pool_v1_pair_forest_lane_state_v1, decode_pool_v1_pair_forest_terminal_statement_v1,
        decode_pool_v1_pair_verified_afterstate_v1, decode_verifier_registry_entry_v2,
        decode_verifier_registry_v2, encode_pool_v1_nullifier_marker,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1,
        encode_pool_v1_pair_verified_afterstate_v1, pool_v1_note_commitment, pool_v1_nullifier,
        pool_v1_pair_forest_output_lane_v1, pool_v1_tree_parent, IncrementalMerkleTreeV1,
        PoolIdentityV1, PoolV1NullifierMarkerV1, PoolV1OutputNoteWitnessV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestWithdrawalWitnessV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PaymentRelationContextV1,
        PoolV1PaymentRuntimeBindingV1, PoolV1WithdrawalPublicV1, VerifierEntryStatusV1,
        VerifierPolicyV1, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
        POOL_V1_PAIR_FOREST_TERMINAL_VERSION, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_ROOT_HISTORY_CAPACITY,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
        POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
    },
    poseidon2::Digest,
};
use litesvm::LiteSVM;
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v0, v1, v1::TransactionConfig, VersionedMessage};
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const PRIORITY_FEE_LAMPORTS: u64 = 10_000;
const LOADED_ACCOUNTS_DATA_SIZE_LIMIT: u32 = 8 * 1024 * 1024;
const HEAP_SIZE: u32 = 256 * 1024;
const GOVERNANCE_SLOT: u64 = 100;
const ACTIVATION_SLOT: u64 = 120;
const PROFILE_SLOT: u64 = 150;
const TXV1_TARGET_BYTES: usize = 4_096;
const TXV0_TARGET_BYTES: usize = 1_232;

const POOL_PROGRAM_BYTES: [u8; 32] = [0x41; 32];
const VERIFIER_PROGRAM_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0x44; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [7; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [5; 32];
const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x45; 32];
const PUBLIC_ACCOUNT_BYTES: [u8; 32] = [0x46; 32];
const DESTINATION_TOKEN_ACCOUNT_BYTES: [u8; 32] = [0x49; 32];
const DESTINATION_TOKEN_OWNER_BYTES: [u8; 32] = [0x4a; 32];
const LEGACY_SPL_TOKEN_PROGRAM_ID: &str = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";
const LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES: usize = 82;
const LEGACY_SPL_TOKEN_ACCOUNT_BYTES: usize = 165;
const WITHDRAWAL_AMOUNT: u64 = 250;
const VAULT_BALANCE_BEFORE: u64 = 10_000;
const DESTINATION_BALANCE_BEFORE: u64 = 17;
const SYSTEM_PROGRAM_ID: &str = "11111111111111111111111111111111";
const BPF_LOADER_UPGRADEABLE_ID: &str = "BPFLoaderUpgradeab1e11111111111111111111111";
const WRONG_RELEASE_BINDING: [u8; 32] = [0xee; 32];
const R1_CHECKPOINT_BYTES: usize = 1_768;
/// TxV1 upload chunk (PREREG-PROOF-SIZE-2 item 6): the largest lifecycle
/// write chunk (tag 5 || u32 offset || chunk, payer and upload authority
/// signing, this driver's compute-budget settings) that serializes within the
/// 4,096-byte TxV1 limit. Measured: overhead 329 bytes, maximum chunk 3,767
/// (evidence/proof-size-20261019/receipts/upload-probe, REPORT.md section 4;
/// re-measured in evidence/format-adopt-20261019).
const LIFECYCLE_UPLOAD_CHUNK_BYTES: usize = 3_767;
/// Legacy TxV1 chunk, selectable with `--upload-chunk legacy`.
const LEGACY_LIFECYCLE_UPLOAD_CHUNK_BYTES: usize = 900;
const TXV0_UPLOAD_CHUNK_BYTES: usize = 800;
static LEGACY_UPLOAD_CHUNK: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[cfg(not(feature = "private-leaf-salts"))]
const PROFILE_BINDING: [u8; 32] = [
    0x78, 0x17, 0x1b, 0x56, 0x9e, 0xa7, 0xbc, 0xe5, 0x97, 0x63, 0xa2, 0xb5, 0x78, 0x81, 0x06, 0xa7,
    0x49, 0xbe, 0xd7, 0x47, 0x75, 0x6c, 0xf2, 0xd2, 0x00, 0x69, 0x99, 0x37, 0x92, 0x19, 0x13, 0xe9,
];
#[cfg(not(feature = "private-leaf-salts"))]
const RELEASE_BINDING: [u8; 32] = [
    0x45, 0x90, 0xcd, 0x06, 0x35, 0x37, 0xb3, 0xb0, 0x2f, 0xae, 0xb1, 0x0d, 0x9a, 0x7f, 0x39, 0x99,
    0x3f, 0xbe, 0x4b, 0xb6, 0x20, 0x30, 0x53, 0x32, 0x8d, 0x60, 0x0d, 0xbd, 0x48, 0x1c, 0xe0, 0x34,
];
#[cfg(feature = "private-leaf-salts")]
const PROFILE_BINDING: [u8; 32] = [
    0x57, 0x94, 0x73, 0x13, 0xd2, 0x32, 0x64, 0x1a, 0xd8, 0x15, 0x7d, 0x66, 0xbf, 0xaf, 0xfa, 0xb1,
    0x1e, 0x4c, 0x3a, 0x99, 0x33, 0x1d, 0x18, 0xf4, 0x4b, 0xfa, 0xca, 0xb6, 0x89, 0x97, 0x37, 0xd3,
];
#[cfg(feature = "private-leaf-salts")]
const RELEASE_BINDING: [u8; 32] = [
    0xe2, 0x94, 0xaf, 0xbc, 0x14, 0xef, 0x6a, 0xfe, 0x76, 0xb8, 0x47, 0xde, 0xf4, 0x44, 0x52, 0xf8,
    0x4c, 0xc3, 0x72, 0x80, 0x64, 0x65, 0x76, 0x07, 0xb5, 0x44, 0xa5, 0x39, 0xca, 0x9b, 0x32, 0x3a,
];

struct Args {
    pool_program: PathBuf,
    verifier_program: PathBuf,
    registry_program: PathBuf,
    evidence: PathBuf,
    task_dir: PathBuf,
    reuse: Option<(PathBuf, PathBuf)>,
    mask_entropy: MaskEntropy,
    scenario: Scenario,
    runtime_compute_limit: u64,
    transport: Transport,
    populated_pairs: u32,
    operation: Operation,
    tx_version: TxVersion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TxVersion {
    V0,
    V1,
}

impl TxVersion {
    fn label(self) -> &'static str {
        match self {
            Self::V0 => "v0",
            Self::V1 => "v1",
        }
    }

    fn display_name(self) -> &'static str {
        match self {
            Self::V0 => "TxV0",
            Self::V1 => "TxV1",
        }
    }

    fn target_bytes(self) -> usize {
        match self {
            Self::V0 => TXV0_TARGET_BYTES,
            Self::V1 => TXV1_TARGET_BYTES,
        }
    }

    fn upload_chunk_bytes(self) -> usize {
        match self {
            Self::V0 => TXV0_UPLOAD_CHUNK_BYTES,
            Self::V1 if LEGACY_UPLOAD_CHUNK.load(std::sync::atomic::Ordering::Relaxed) => LEGACY_LIFECYCLE_UPLOAD_CHUNK_BYTES,
            Self::V1 => LIFECYCLE_UPLOAD_CHUNK_BYTES,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Transport {
    Asq8,
    Asf8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Transfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MaskEntropy {
    Fixture,
    Os,
}

impl MaskEntropy {
    fn label(self) -> &'static str {
        match self {
            Self::Fixture => "fixture",
            Self::Os => "os",
        }
    }

    fn source_label(self) -> &'static str {
        match self {
            Self::Fixture => "deterministic-fixture-source",
            Self::Os => "OS getrandom via StateOnlyAttemptSecrets::generate",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scenario {
    Success,
    ProofRejection,
    WrongRelease,
    StaleLane,
    Replay,
    MalformedResult,
    MutatedResult,
    WithdrawalCpiFailure,
}

impl Scenario {
    fn expects_first_terminal_success(self) -> bool {
        matches!(self, Self::Success | Self::Replay)
    }

    fn uses_result_double(self) -> bool {
        matches!(self, Self::MalformedResult | Self::MutatedResult)
    }

    fn verifier_cpi_expected(self) -> bool {
        !matches!(self, Self::WrongRelease)
    }

    fn label(self) -> &'static str {
        match self {
            Self::Success => "success",
            Self::ProofRejection => "proof-rejection",
            Self::WrongRelease => "wrong-release",
            Self::StaleLane => "stale-lane",
            Self::Replay => "replay-nullifier",
            Self::MalformedResult => "malformed-result",
            Self::MutatedResult => "mutated-result",
            Self::WithdrawalCpiFailure => "withdrawal-cpi-failure",
        }
    }
}

fn parse_args() -> Result<Args> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() >= 6,
        "usage: pool_gate <aspis_pool.so> <r1_cost_probe.so> <aspis_registry.so> \
         <evidence.json> <fresh-output-dir> <transfer|withdrawal> \
         [success|proof-rejection|wrong-release|stale-lane|replay|withdrawal-cpi-failure] \
         [--pairs N] [--reuse proof.bin public.bin] [--tx-version v0|v1] \
         [--mask-entropy fixture|os] [--upload-chunk txv1-max|legacy] \
         (options may follow in either order)"
    );
    let operation = match args[5].as_str() {
        "transfer" => Operation::Transfer,
        "withdrawal" => Operation::Withdrawal,
        _ => bail!("operation must be transfer or withdrawal"),
    };
    let mut scenario = None;
    let mut reuse = None;
    let mut mask_entropy = MaskEntropy::Fixture;
    let mut saw_mask_entropy = false;
    let mut pairs = 13u32;
    let mut saw_pairs = false;
    let mut tx_version = TxVersion::V1;
    let mut saw_tx_version = false;
    let mut saw_upload_chunk = false;
    let mut next_arg = 6;
    while next_arg < args.len() {
        match args[next_arg].as_str() {
            "--reuse" => {
                ensure!(reuse.is_none(), "--reuse may be specified only once");
                ensure!(
                    next_arg + 2 < args.len(),
                    "expected --reuse proof.bin public.bin"
                );
                reuse = Some((
                    PathBuf::from(&args[next_arg + 1]),
                    PathBuf::from(&args[next_arg + 2]),
                ));
                next_arg += 3;
            }
            "--mask-entropy" => {
                ensure!(
                    !saw_mask_entropy,
                    "--mask-entropy may be specified only once"
                );
                ensure!(
                    next_arg + 1 < args.len(),
                    "expected --mask-entropy fixture|os"
                );
                mask_entropy = match args[next_arg + 1].as_str() {
                    "fixture" => MaskEntropy::Fixture,
                    "os" => MaskEntropy::Os,
                    _ => bail!("--mask-entropy must be fixture or os"),
                };
                saw_mask_entropy = true;
                next_arg += 2;
            }
            "--pairs" => {
                ensure!(!saw_pairs, "--pairs may be specified only once");
                ensure!(next_arg + 1 < args.len(), "expected --pairs N");
                pairs = args[next_arg + 1]
                    .parse::<u32>()
                    .context("parse --pairs as an integer")?;
                ensure!(pairs <= 1023, "--pairs must be at most 1023");
                saw_pairs = true;
                next_arg += 2;
            }
            "--tx-version" => {
                ensure!(!saw_tx_version, "--tx-version may be specified only once");
                ensure!(next_arg + 1 < args.len(), "expected --tx-version v0|v1");
                tx_version = match args[next_arg + 1].as_str() {
                    "v0" => TxVersion::V0,
                    "v1" => TxVersion::V1,
                    _ => bail!("--tx-version must be v0 or v1"),
                };
                saw_tx_version = true;
                next_arg += 2;
            }
            "--upload-chunk" => {
                ensure!(!saw_upload_chunk, "--upload-chunk may be specified only once");
                ensure!(next_arg + 1 < args.len(), "expected --upload-chunk txv1-max|legacy");
                let legacy = match args[next_arg + 1].as_str() {
                    "txv1-max" => false,
                    "legacy" => true,
                    _ => bail!("--upload-chunk must be txv1-max or legacy"),
                };
                LEGACY_UPLOAD_CHUNK.store(legacy, std::sync::atomic::Ordering::Relaxed);
                saw_upload_chunk = true;
                next_arg += 2;
            }
            value if !value.starts_with("--") && scenario.is_none() => {
                scenario = Some(match value {
                    "success" => Scenario::Success,
                    "proof-rejection" => Scenario::ProofRejection,
                    "wrong-release" => Scenario::WrongRelease,
                    "stale-lane" => Scenario::StaleLane,
                    "replay" | "nullifier" => Scenario::Replay,
                    "withdrawal-cpi-failure" => Scenario::WithdrawalCpiFailure,
                    _ => bail!("unsupported Pool-path scenario: {value}"),
                });
                next_arg += 1;
            }
            value => bail!("unexpected or duplicate pool_gate argument: {value}"),
        }
    }
    let scenario = scenario.unwrap_or(Scenario::Success);
    ensure!(
        scenario != Scenario::WithdrawalCpiFailure || operation == Operation::Withdrawal,
        "withdrawal-cpi-failure requires withdrawal operation"
    );
    ensure!(
        mask_entropy != MaskEntropy::Os || reuse.is_none(),
        "--mask-entropy os cannot be combined with --reuse"
    );
    #[cfg(not(feature = "private-leaf-salts"))]
    ensure!(
        mask_entropy != MaskEntropy::Os,
        "--mask-entropy os requires the private-leaf-salts feature"
    );
    let evidence = PathBuf::from(&args[3]);
    let task_dir = PathBuf::from(&args[4]);
    let runtime_compute_limit = u64::from(COMPUTE_UNIT_LIMIT);
    let transport = Transport::Asq8;
    let populated_pairs = pairs;
    Ok(Args {
        pool_program: PathBuf::from(&args[0]),
        verifier_program: PathBuf::from(&args[1]),
        registry_program: PathBuf::from(&args[2]),
        evidence,
        task_dir,
        reuse,
        mask_entropy,
        scenario,
        runtime_compute_limit,
        transport,
        populated_pairs,
        operation,
        tx_version,
    })
}

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32 + 1) % P))
}

fn strict_lane_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32) % P))
}

fn deterministic_anchor_and_nullifier() -> Result<(Digest, Digest)> {
    let nullifier_key = digest(10);
    let salt = digest(100);
    let asset_id = M31(77);
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
    let mut anchor = PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
        .map_err(|error| anyhow!("construct deterministic input pair: {error:?}"))?
        .leaf_digest()
        .map_err(|error| anyhow!("hash deterministic input pair: {error:?}"))?;
    let membership_index = 0x5_4321u64;
    for level in 0..20 {
        let sibling = digest(2_000 + 20 * level as u32);
        anchor = if ((membership_index >> level) & 1) == 0 {
            pool_v1_tree_parent(&anchor, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &anchor)
        };
    }
    for (sibling, direction) in [digest(3_000), digest(3_100), digest(3_200)]
        .into_iter()
        .zip([true, false, true])
    {
        anchor = if direction {
            pool_v1_tree_parent(&sibling, &anchor)
        } else {
            pool_v1_tree_parent(&anchor, &sibling)
        };
    }
    Ok((anchor, pool_v1_nullifier(&nullifier_key, &salt)))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Sha256::digest(bytes).into();
    bytes_hex(&digest)
}

fn bytes_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn write_new_file(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .with_context(|| format!("create {} without overwriting", path.display()))?;
    std::io::Write::write_all(&mut file, bytes)?;
    file.sync_all()?;
    Ok(())
}

fn retained_task_key(path: &Path) -> Result<Keypair> {
    if path.exists() {
        let mode = fs::metadata(path)?.permissions().mode() & 0o777;
        ensure!(
            mode & 0o077 == 0,
            "retained task key {} is not private",
            path.display()
        );
        let encoded = fs::read_to_string(path)
            .with_context(|| format!("read retained key {}", path.display()))?;
        return Keypair::try_from_base58_string(encoded.trim())
            .map_err(|error| anyhow!("decode retained task key {}: {error}", path.display()));
    }
    let key = Keypair::new();
    write_new_file(path, key.to_base58_string().as_bytes())?;
    Ok(key)
}

fn initialized_mint_data(supply: u64, decimals: u8) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1;
    data
}

fn initialized_token_data(mint: LegacyPubkey, owner: LegacyPubkey, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
    data[..32].copy_from_slice(&mint.to_bytes());
    data[32..64].copy_from_slice(&owner.to_bytes());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1;
    data
}

fn token_amount(account: &Account) -> Result<u64> {
    ensure!(
        account.data.len() == LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        "wrong legacy token account length"
    );
    Ok(u64::from_le_bytes(account.data[64..72].try_into()?))
}

fn put_account(
    svm: &mut LiteSVM,
    key: LegacyPubkey,
    owner: LegacyPubkey,
    data: Vec<u8>,
) -> Result<()> {
    let lamports = svm.minimum_balance_for_rent_exemption(data.len()).max(1);
    svm.set_account(
        address(&key),
        Account {
            lamports,
            data,
            owner: address(&owner),
            executable: false,
            rent_epoch: u64::MAX,
        },
    )
    .map_err(|error| anyhow!("set account {key}: {error}"))?;
    Ok(())
}

fn meta(key: LegacyPubkey, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(address(&key), false)
    } else {
        AccountMeta::new_readonly(address(&key), false)
    }
}

fn signer_meta(key: LegacyPubkey, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(address(&key), true)
    } else {
        AccountMeta::new_readonly(address(&key), true)
    }
}

fn transaction(
    svm: &LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
    version: TxVersion,
) -> Result<VersionedTransaction> {
    transaction_with_signers(svm, payer, instruction, &[], version)
}

fn transaction_with_signers(
    svm: &LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
    additional_signers: &[&Keypair],
    version: TxVersion,
) -> Result<VersionedTransaction> {
    let recent_blockhash = svm.latest_blockhash();
    let message = match version {
        TxVersion::V1 => {
            let config = TransactionConfig::empty()
                .with_priority_fee(PRIORITY_FEE_LAMPORTS)
                .with_compute_unit_limit(COMPUTE_UNIT_LIMIT)
                .with_loaded_accounts_data_size_limit(LOADED_ACCOUNTS_DATA_SIZE_LIMIT)
                .with_heap_size(HEAP_SIZE);
            VersionedMessage::V1(v1::Message::try_compile_with_config(
                &payer.pubkey(),
                &[instruction],
                recent_blockhash,
                config,
            )?)
        }
        TxVersion::V0 => {
            let instructions = [
                ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_UNIT_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_SIZE),
                ComputeBudgetInstruction::set_loaded_accounts_data_size_limit(
                    LOADED_ACCOUNTS_DATA_SIZE_LIMIT,
                ),
                instruction,
            ];
            VersionedMessage::V0(v0::Message::try_compile(
                &payer.pubkey(),
                &instructions,
                &[],
                recent_blockhash,
            )?)
        }
    };
    let mut signers = Vec::with_capacity(additional_signers.len() + 1);
    signers.push(payer);
    signers.extend_from_slice(additional_signers);
    Ok(VersionedTransaction::try_new(message, &signers)?)
}

fn snapshot(svm: &LiteSVM, keys: &[LegacyPubkey]) -> Vec<Option<Account>> {
    keys.iter()
        .map(|key| svm.get_account(&address(key)))
        .collect()
}

#[derive(Debug)]
struct TxMeasurement {
    bytes: usize,
    compute_units: u64,
    logs: Vec<String>,
    error: Option<String>,
    return_program: Address,
    return_data: Vec<u8>,
}

fn present_account<'a>(account: &'a Option<Account>, name: &str) -> Result<&'a Account> {
    account
        .as_ref()
        .with_context(|| format!("missing expected account {name}"))
}

fn execute_success(
    svm: &mut LiteSVM,
    tx: VersionedTransaction,
    name: &str,
) -> Result<TxMeasurement> {
    let bytes = wincode::serialize(&tx)?.len();
    let target = transaction_target_bytes(&tx);
    ensure!(
        bytes <= target,
        "{name}: transaction is {bytes} bytes, above its {target}-byte target"
    );
    let simulated = svm.simulate_transaction(tx.clone()).map_err(|failed| {
        anyhow!(
            "{name}: expected-success simulation failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    let executed = svm.send_transaction(tx).map_err(|failed| {
        anyhow!(
            "{name}: expected-success execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    ensure!(
        simulated.meta == executed,
        "{name}: simulation/execution differ"
    );
    Ok(TxMeasurement {
        bytes,
        compute_units: executed.compute_units_consumed,
        logs: executed.logs,
        error: None,
        return_program: executed.return_data.program_id,
        return_data: executed.return_data.data,
    })
}

fn execute_success_with_signers(
    svm: &mut LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
    additional_signers: &[&Keypair],
    name: &str,
    version: TxVersion,
) -> Result<TxMeasurement> {
    let tx = transaction_with_signers(svm, payer, instruction, additional_signers, version)?;
    execute_success(svm, tx, name)
}

fn execute_failure(
    svm: &mut LiteSVM,
    tx: VersionedTransaction,
    name: &str,
) -> Result<TxMeasurement> {
    let bytes = wincode::serialize(&tx)?.len();
    let target = transaction_target_bytes(&tx);
    ensure!(
        bytes <= target,
        "{name}: transaction is {bytes} bytes, above its {target}-byte target"
    );
    let simulated = svm
        .simulate_transaction(tx.clone())
        .map_err(|failed| failed)
        .expect_err("failure simulation unexpectedly succeeded");
    let executed = svm
        .send_transaction(tx)
        .map_err(|failed| failed)
        .expect_err("failure execution unexpectedly succeeded");
    ensure!(
        simulated.err == executed.err && simulated.meta == executed.meta,
        "{name}: failed simulation/execution differ"
    );
    ensure!(
        executed.meta.return_data.data.is_empty(),
        "{name}: rejection retained return data"
    );
    Ok(TxMeasurement {
        bytes,
        compute_units: executed.meta.compute_units_consumed,
        logs: executed.meta.logs,
        error: Some(format!("{:?}", executed.err)),
        return_program: executed.meta.return_data.program_id,
        return_data: executed.meta.return_data.data,
    })
}

fn transaction_target_bytes(tx: &VersionedTransaction) -> usize {
    match &tx.message {
        VersionedMessage::Legacy(_) => TXV0_TARGET_BYTES,
        VersionedMessage::V0(_) => TXV0_TARGET_BYTES,
        VersionedMessage::V1(_) => TXV1_TARGET_BYTES,
    }
}

#[derive(Default)]
struct LifecycleUploadStats {
    upload_count: usize,
    upload_serialized_bytes: usize,
    lifecycle_serialized_bytes: usize,
    max_compute_units: u64,
}

fn lifecycle_instruction(
    verifier_program: LegacyPubkey,
    target: LegacyPubkey,
    authority: LegacyPubkey,
    data: Vec<u8>,
) -> Instruction {
    Instruction {
        program_id: address(&verifier_program),
        accounts: vec![meta(target, true), signer_meta(authority, false)],
        data,
    }
}

fn lifecycle_write_data(offset: usize, payload: &[u8]) -> Vec<u8> {
    let mut data = Vec::with_capacity(5 + payload.len());
    data.push(5);
    data.extend_from_slice(&(offset as u32).to_le_bytes());
    data.extend_from_slice(payload);
    data
}

fn lifecycle_upload(
    svm: &mut LiteSVM,
    payer: &Keypair,
    authority: &Keypair,
    verifier_program: LegacyPubkey,
    target: LegacyPubkey,
    kind: u8,
    body: &[u8],
    writable_body_len: usize,
    name: &str,
    version: TxVersion,
) -> Result<LifecycleUploadStats> {
    ensure!(
        writable_body_len <= body.len(),
        "{name}: writable body exceeds allocation"
    );
    let mut stats = LifecycleUploadStats::default();
    let init = lifecycle_instruction(
        verifier_program,
        target,
        legacy(authority.pubkey().to_bytes()),
        vec![4, kind],
    );
    let init_tx = transaction_with_signers(svm, payer, init, &[authority], version)?;
    let init_measurement = execute_success(svm, init_tx, &format!("{name}-init"))?;
    stats.lifecycle_serialized_bytes += init_measurement.bytes;
    stats.max_compute_units = stats.max_compute_units.max(init_measurement.compute_units);

    for (chunk_index, chunk) in body[..writable_body_len]
        .chunks(version.upload_chunk_bytes())
        .enumerate()
    {
        let offset = chunk_index * version.upload_chunk_bytes();
        let data = lifecycle_write_data(offset, chunk);
        let write = lifecycle_instruction(
            verifier_program,
            target,
            legacy(authority.pubkey().to_bytes()),
            data,
        );
        let write_tx = transaction_with_signers(svm, payer, write, &[authority], version)?;
        let measurement = execute_success(svm, write_tx, &format!("{name}-write-{chunk_index}"))?;
        stats.upload_count += 1;
        stats.upload_serialized_bytes += measurement.bytes;
        stats.lifecycle_serialized_bytes += measurement.bytes;
        stats.max_compute_units = stats.max_compute_units.max(measurement.compute_units);
    }

    let finalize = lifecycle_instruction(
        verifier_program,
        target,
        legacy(authority.pubkey().to_bytes()),
        vec![6],
    );
    let finalize_tx = transaction_with_signers(svm, payer, finalize, &[authority], version)?;
    let finalize_measurement = execute_success(svm, finalize_tx, &format!("{name}-finalize"))?;
    stats.lifecycle_serialized_bytes += finalize_measurement.bytes;
    stats.max_compute_units = stats
        .max_compute_units
        .max(finalize_measurement.compute_units);
    Ok(stats)
}

fn assert_lifecycle_failure_rollback(
    svm: &mut LiteSVM,
    tx: VersionedTransaction,
    protected: &[LegacyPubkey],
    name: &str,
) -> Result<TxMeasurement> {
    let before = snapshot(svm, protected);
    let measurement = execute_failure(svm, tx, name)?;
    ensure!(
        snapshot(svm, protected) == before,
        "{name}: protected accounts changed after rejection"
    );
    Ok(measurement)
}

fn assert_program_rejection(
    measurement: &TxMeasurement,
    program: Address,
    name: &str,
) -> Result<()> {
    let program_id = program.to_string();
    ensure!(
        measurement.compute_units > 0,
        "{name}: rejection did not consume program compute units"
    );
    ensure!(
        measurement
            .logs
            .iter()
            .any(|line| line.contains(&program_id) && line.contains("failed")),
        "{name}: expected program rejection, got {:?} with logs:\n{}",
        measurement.error,
        measurement.logs.join("\n")
    );
    ensure!(
        !measurement
            .error
            .as_deref()
            .is_some_and(|error| error.contains("AlreadyProcessed")),
        "{name}: duplicate transaction was mistaken for program rejection"
    );
    Ok(())
}

fn failed_lifecycle_instruction_unchanged(
    svm: &mut LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
    additional_signers: &[&Keypair],
    protected: &[LegacyPubkey],
    name: &str,
    version: TxVersion,
) -> Result<TxMeasurement> {
    svm.expire_blockhash();
    let program_id = instruction.program_id;
    let tx = transaction_with_signers(svm, payer, instruction, additional_signers, version)?;
    let measurement = assert_lifecycle_failure_rollback(svm, tx, protected, name)?;
    assert_program_rejection(&measurement, program_id, name)?;
    Ok(measurement)
}

fn load_payload(
    path: &PathBuf,
    expected_afterstate: &[u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES],
) -> Result<(Vec<u8>, &'static str)> {
    let fixture = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    let (payload, kind) = if fixture.len() >= POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        && fixture[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..]
    {
        (fixture, "complete-proof-account-payload")
    } else {
        let mut payload =
            Vec::with_capacity(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + fixture.len());
        payload.extend_from_slice(expected_afterstate);
        payload.extend_from_slice(&fixture);
        (payload, "compact-proof-body")
    };
    ensure!(
        payload.len() > POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "proof payload is shorter than the 688-byte candidate afterstate plus proof"
    );
    ensure!(
        payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..],
        "fixture candidate afterstate does not match this deterministic lane transition"
    );
    decode_pool_v1_pair_verified_afterstate_v1(&payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES])
        .map_err(|error| anyhow!("decode fixture candidate afterstate: {error:?}"))?;
    Ok((payload, kind))
}

struct GovernanceEvidence {
    registry_key: LegacyPubkey,
    entry_key: LegacyPubkey,
    registry_image: Vec<u8>,
    entry_image: Vec<u8>,
    registry_hash: [u8; 32],
    verifier_hash: [u8; 32],
    wrong_registry_hash: TxMeasurement,
    initialize: TxMeasurement,
    wrong_verifier_hash: TxMeasurement,
    schedule: TxMeasurement,
    activate: TxMeasurement,
    freeze: TxMeasurement,
}

fn tx_measurement_json(measurement: &TxMeasurement, version: TxVersion) -> serde_json::Value {
    serde_json::json!({
        "serialized_transaction_bytes": measurement.bytes,
        "serialized_transaction_target_bytes": version.target_bytes(),
        "serialized_transaction_target_headroom_bytes": version.target_bytes() - measurement.bytes,
        "compute_units": measurement.compute_units,
        "error": measurement.error,
        "return_program": measurement.return_program.to_string(),
        "return_data_bytes": measurement.return_data.len(),
        "return_data_sha256": sha256_hex(&measurement.return_data),
        "logs": measurement.logs,
    })
}

#[allow(clippy::too_many_arguments)]
fn initialize_registry_v2(
    svm: &mut LiteSVM,
    payer: &Keypair,
    authority: &Keypair,
    registry_program: LegacyPubkey,
    registry_artifact: &[u8],
    verifier_program: LegacyPubkey,
    verifier_artifact: &[u8],
    pool: LegacyPubkey,
    tx_version: TxVersion,
) -> Result<GovernanceEvidence> {
    let system_program = LegacyPubkey::from_str(SYSTEM_PROGRAM_ID)?;
    let loader = LegacyPubkey::from_str(BPF_LOADER_UPGRADEABLE_ID)?;
    let registry_programdata =
        LegacyPubkey::find_program_address(&[registry_program.as_ref()], &loader).0;
    let verifier_programdata =
        LegacyPubkey::find_program_address(&[verifier_program.as_ref()], &loader).0;
    let registry_key = pool_v1_verifier_registry_v2_address(&registry_program, &pool).0;
    let entry_key = pool_v1_verifier_entry_v2_address(
        &registry_program,
        &pool,
        &PROFILE_BINDING,
        &RELEASE_BINDING,
    )
    .0;
    let registry_hash: [u8; 32] = Sha256::digest(registry_artifact).into();
    let verifier_hash: [u8; 32] = Sha256::digest(verifier_artifact).into();

    svm.warp_to_slot(GOVERNANCE_SLOT);
    let governance_keys = [registry_key, entry_key];
    let pristine = snapshot(svm, &governance_keys);
    ensure!(
        pristine.iter().all(Option::is_none),
        "Registry V2 fixture PDAs must start absent"
    );

    let mut wrong_registry_hash_bytes = registry_hash;
    wrong_registry_hash_bytes[0] ^= 1;
    let init_accounts = || {
        vec![
            meta(registry_key, true),
            signer_meta(legacy(authority.pubkey().to_bytes()), false),
            signer_meta(legacy(payer.pubkey().to_bytes()), true),
            meta(system_program, false),
            meta(registry_program, false),
            meta(registry_programdata, false),
        ]
    };
    let wrong_init = Instruction {
        program_id: address(&registry_program),
        accounts: init_accounts(),
        data: encode_initialize_registry_v2(
            pool.to_bytes(),
            POLICY_BINDING_BYTES,
            ACTIVATION_SLOT - GOVERNANCE_SLOT,
            wrong_registry_hash_bytes,
        )
        .to_vec(),
    };
    let wrong_registry_hash = execute_failure(
        svm,
        transaction_with_signers(svm, payer, wrong_init, &[authority], tx_version)?,
        "registry-v2-wrong-registry-code-hash",
    )?;
    ensure!(
        snapshot(svm, &governance_keys) == pristine,
        "wrong Registry executable hash changed V2 state"
    );

    svm.expire_blockhash();
    let init = Instruction {
        program_id: address(&registry_program),
        accounts: init_accounts(),
        data: encode_initialize_registry_v2(
            pool.to_bytes(),
            POLICY_BINDING_BYTES,
            ACTIVATION_SLOT - GOVERNANCE_SLOT,
            registry_hash,
        )
        .to_vec(),
    };
    let initialize = execute_success(
        svm,
        transaction_with_signers(svm, payer, init, &[authority], tx_version)?,
        "registry-v2-initialize",
    )?;
    let after_init = snapshot(svm, &governance_keys);
    ensure!(
        after_init[0].is_some() && after_init[1].is_none(),
        "V2 initialize did not create exactly ASR2"
    );

    let schedule_accounts = || {
        vec![
            meta(registry_key, true),
            meta(entry_key, true),
            signer_meta(legacy(authority.pubkey().to_bytes()), false),
            signer_meta(legacy(payer.pubkey().to_bytes()), true),
            meta(system_program, false),
            meta(verifier_program, false),
            meta(verifier_programdata, false),
        ]
    };
    let mut wrong_verifier_hash_bytes = verifier_hash;
    wrong_verifier_hash_bytes[0] ^= 1;
    svm.expire_blockhash();
    let wrong_schedule = Instruction {
        program_id: address(&registry_program),
        accounts: schedule_accounts(),
        data: encode_schedule_profile_v2(
            0,
            verifier_program.to_bytes(),
            PROFILE_BINDING,
            RELEASE_BINDING,
            POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
            ACTIVATION_SLOT,
            wrong_verifier_hash_bytes,
        )
        .to_vec(),
    };
    let wrong_verifier_hash = execute_failure(
        svm,
        transaction_with_signers(svm, payer, wrong_schedule, &[authority], tx_version)?,
        "registry-v2-wrong-verifier-code-hash",
    )?;
    ensure!(
        snapshot(svm, &governance_keys) == after_init,
        "wrong verifier executable hash changed V2 state"
    );

    svm.expire_blockhash();
    let schedule_instruction = Instruction {
        program_id: address(&registry_program),
        accounts: schedule_accounts(),
        data: encode_schedule_profile_v2(
            0,
            verifier_program.to_bytes(),
            PROFILE_BINDING,
            RELEASE_BINDING,
            POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
            ACTIVATION_SLOT,
            verifier_hash,
        )
        .to_vec(),
    };
    let schedule = execute_success(
        svm,
        transaction_with_signers(svm, payer, schedule_instruction, &[authority], tx_version)?,
        "registry-v2-schedule",
    )?;

    svm.warp_to_slot(ACTIVATION_SLOT);
    svm.expire_blockhash();
    let activate_instruction = Instruction {
        program_id: address(&registry_program),
        accounts: vec![
            meta(registry_key, true),
            meta(entry_key, true),
            signer_meta(legacy(authority.pubkey().to_bytes()), false),
        ],
        data: encode_simple_mutation_v2(RegistryMutationOpcodeV1::Activate, 1)
            .map_err(|error| anyhow!("encode V2 activate: {error:?}"))?
            .to_vec(),
    };
    let activate = execute_success(
        svm,
        transaction_with_signers(svm, payer, activate_instruction, &[authority], tx_version)?,
        "registry-v2-activate",
    )?;

    svm.expire_blockhash();
    let freeze_instruction = Instruction {
        program_id: address(&registry_program),
        accounts: vec![
            meta(registry_key, true),
            signer_meta(legacy(authority.pubkey().to_bytes()), false),
        ],
        data: encode_simple_mutation_v2(RegistryMutationOpcodeV1::Freeze, 2)
            .map_err(|error| anyhow!("encode V2 freeze: {error:?}"))?
            .to_vec(),
    };
    let freeze = execute_success(
        svm,
        transaction_with_signers(svm, payer, freeze_instruction, &[authority], tx_version)?,
        "registry-v2-freeze",
    )?;

    let registry_account = svm
        .get_account(&address(&registry_key))
        .context("load finalized ASR2")?;
    let entry_account = svm
        .get_account(&address(&entry_key))
        .context("load finalized ASE2")?;
    let registry = decode_verifier_registry_v2(&registry_account.data)
        .map_err(|error| anyhow!("decode finalized ASR2: {error:?}"))?;
    let entry = decode_verifier_registry_entry_v2(&entry_account.data)
        .map_err(|error| anyhow!("decode finalized ASE2: {error:?}"))?;
    ensure!(
        registry.flags == POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE
            && registry.authority == REGISTRY_AUTHORITY_BYTES
            && registry.generation == 3
            && registry.registry_program == registry_program.to_bytes()
            && registry.programdata_address == registry_programdata.to_bytes()
            && registry.executable_hash == registry_hash,
        "finalized ASR2 does not carry the exact immutable Registry certificate"
    );
    ensure!(
        entry.status == VerifierEntryStatusV1::Active
            && entry.verifier_program == verifier_program.to_bytes()
            && entry.profile_binding == PROFILE_BINDING
            && entry.release_binding == RELEASE_BINDING
            && entry.programdata_address == verifier_programdata.to_bytes()
            && entry.executable_hash == verifier_hash
            && entry.expected_upgrade_authority == [0u8; 32]
            && entry.activation_slot == ACTIVATION_SLOT
            && entry.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        "finalized ASE2 does not carry the exact active verifier certificate"
    );

    svm.warp_to_slot(PROFILE_SLOT);
    Ok(GovernanceEvidence {
        registry_key,
        entry_key,
        registry_image: registry_account.data,
        entry_image: entry_account.data,
        registry_hash,
        verifier_hash,
        wrong_registry_hash,
        initialize,
        wrong_verifier_hash,
        schedule,
        activate,
        freeze,
    })
}

fn main() -> Result<()> {
    let args = parse_args()?;
    ensure!(
        !args.task_dir.exists(),
        "refusing to reuse task output directory {}",
        args.task_dir.display()
    );
    fs::create_dir(&args.task_dir)
        .with_context(|| format!("create fresh task directory {}", args.task_dir.display()))?;
    ensure!(
        !args.evidence.exists(),
        "refusing to overwrite {}",
        args.evidence.display()
    );
    let pool_artifact = fs::read(&args.pool_program)
        .with_context(|| format!("read {}", args.pool_program.display()))?;
    let production_verifier_artifact = fs::read(&args.verifier_program)
        .with_context(|| format!("read {}", args.verifier_program.display()))?;
    let registry_artifact = fs::read(&args.registry_program)
        .with_context(|| format!("read {}", args.registry_program.display()))?;
    let result_double_artifact = production_verifier_artifact.clone();
    let selected_verifier_artifact = &production_verifier_artifact;

    let pool_program = legacy(POOL_PROGRAM_BYTES);
    let verifier_program = LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?;
    let registry_program = legacy(REGISTRY_PROGRAM_BYTES);
    let mint = legacy([0x42; 32]);
    let (master_key, master_bump) = pool_v1_pair_forest_master_address(&pool_program, &mint);
    let (historical_global_anchor, nullifier) = deterministic_anchor_and_nullifier()?;

    let policy = VerifierPolicyV1 {
        flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
            | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
        registry_program: REGISTRY_PROGRAM_BYTES,
        registry_authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
    };
    let master = PoolV1PairForestMasterV1 {
        bump: master_bump,
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: LegacyPubkey::from_str(LEGACY_SPL_TOKEN_PROGRAM_ID)?.to_bytes(),
            asset_id: M31(77),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        },
        verifier_policy: policy,
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 43,
        last_checkpoint_lane_sequences: [0; 8],
    };

    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow!("derive output lane: {error:?}"))?;
    let (lane_key, lane_bump) =
        pool_v1_pair_forest_lane_address(&pool_program, &master_key, output_lane)?;
    let mut tree = IncrementalMerkleTreeV1 {
        next_leaf_index: 0,
        root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
    };
    let mut all_lane_roots = vec![tree.root];
    for leaf in 0..args.populated_pairs {
        tree = tree
            .append_one_with_empty_roots(
                strict_lane_digest(20_000 + 32 * leaf),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow!("populate deterministic output lane: {error:?}"))?
            .0;
        all_lane_roots.push(tree.root);
    }
    let lane = PoolV1PairForestLaneStateV1 {
        bump: lane_bump,
        master: master_key.to_bytes(),
        lane_id: output_lane,
        tree,
    };

    let checkpoint_sequence = 42u64;
    let (checkpoint_key, checkpoint_bump) =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, checkpoint_sequence);
    let checkpoint = PoolV1PairForestCheckpointV1 {
        bump: checkpoint_bump,
        master: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        checkpoint_sequence,
        global_root: historical_global_anchor,
        lane_sequences: [0; 8],
    };

    let live_snapshot = PoolV1PairLiveSnapshotV1 {
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        sequence: lane.tree.next_leaf_index,
        next_pair_index: lane.tree.next_leaf_index,
        current_root: lane.tree.root,
        frontier: lane.tree.frontier,
    };
    let prepared = prepare_v7_pair_forest_transfer_fixture_v1(
        master_key.to_bytes(),
        checkpoint_key.to_bytes(),
        lane_key.to_bytes(),
        checkpoint_sequence,
        DEPLOYMENT_DOMAIN_BYTES,
        live_snapshot,
    )
    .map_err(|error| anyhow!("prepare deterministic R1 fixture: {error:?}"))?;
    ensure!(
        prepared.public.anchor_root == historical_global_anchor
            && prepared.public.nullifier == nullifier
            && prepared.transition.live_snapshot == live_snapshot,
        "prepared fixture diverges from legacy deterministic input or live lane"
    );
    ensure!(
        prepared.public.recipient_commitment
            == pool_v1_note_commitment(&digest(300), 600, M31(77), &digest(400))
            && prepared.public.change_commitment
                == pool_v1_note_commitment(&digest(500), 400, M31(77), &digest(600)),
        "prepared transfer outputs differ from the legacy deterministic fixture"
    );
    let prepared_common = prepared.statement.common();
    ensure!(
        prepared_common.master_account == master_key.to_bytes()
            && prepared_common.checkpoint_account == checkpoint_key.to_bytes()
            && prepared_common.selected_lane_account == lane_key.to_bytes()
            && prepared_common.checkpoint_sequence == checkpoint_sequence
            && prepared_common.historical_global_anchor == historical_global_anchor
            && prepared_common.output_lane == output_lane,
        "prepared ASF8 statement identities differ from live fixture accounts"
    );
    let context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: prepared.public.pool,
            deployment_domain: prepared.public.deployment_domain,
            anchor_sequence: prepared.public.anchor_sequence,
            anchor_root: prepared.public.anchor_root,
            asset_id: prepared.public.asset_id,
        },
        spent_nullifiers: &[],
    };
    let compiled_transfer = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &prepared.public,
        &prepared.witness,
        context,
        live_snapshot,
    )
    .map_err(|error| anyhow!("compile prepared transfer witness: {error:?}"))?;
    ensure!(
        compiled_transfer.public_statement == prepared.transition,
        "explicit transfer compilation differs from prepared fixture"
    );

    let (transfer_public, withdrawal_public, payment, terminal_statement, compiled) =
        match args.operation {
            Operation::Transfer => {
                let statement = prepared.statement.clone();
                (
                    prepared.public,
                    None,
                    PoolV1PairForestTerminalPaymentV1::PrivateTransfer(prepared.public),
                    statement,
                    compiled_transfer,
                )
            }
            Operation::Withdrawal => {
                let change = PoolV1OutputNoteWitnessV1 {
                    owner_key: digest(700),
                    salt: digest(800),
                    value: 750,
                };
                let public = PoolV1WithdrawalPublicV1 {
                    pool: prepared.public.pool,
                    deployment_domain: prepared.public.deployment_domain,
                    anchor_sequence: prepared.public.anchor_sequence,
                    anchor_root: prepared.public.anchor_root,
                    nullifier: prepared.public.nullifier,
                    asset_id: prepared.public.asset_id,
                    amount: WITHDRAWAL_AMOUNT as u32,
                    destination_token_account: DESTINATION_TOKEN_ACCOUNT_BYTES,
                    change_commitment: pool_v1_note_commitment(
                        &change.owner_key,
                        change.value,
                        prepared.public.asset_id,
                        &change.salt,
                    ),
                };
                let witness = PoolV1PairForestWithdrawalWitnessV1 {
                    input: prepared.witness.input,
                    change,
                };
                let withdrawal_compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
                    &public,
                    &witness,
                    context,
                    live_snapshot,
                )
                .map_err(|error| anyhow!("compile prepared withdrawal witness: {error:?}"))?;
                let mut common = *prepared.statement.common();
                common.lane_transition = withdrawal_compiled.public_statement;
                let statement = PoolV1PairForestTerminalStatementV1::Withdrawal { common, public };
                (
                    prepared.public,
                    Some(public),
                    PoolV1PairForestTerminalPaymentV1::Withdrawal(public),
                    statement,
                    withdrawal_compiled,
                )
            }
        };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: PROFILE_BINDING,
        verifier_release: if args.scenario == Scenario::WrongRelease {
            WRONG_RELEASE_BINDING
        } else {
            RELEASE_BINDING
        },
        pool_program: pool_program.to_bytes(),
        public: payment,
    };
    let candidate_afterstate = compiled.public_statement.candidate_afterstate;
    let output_pair = match args.operation {
        Operation::Transfer => PoolV1PairLeafWitnessV1::two_outputs(
            transfer_public.recipient_commitment,
            transfer_public.change_commitment,
        ),
        Operation::Withdrawal => PoolV1PairLeafWitnessV1::single_output(
            withdrawal_public
                .context("missing withdrawal public")?
                .change_commitment,
        ),
    }
    .map_err(|error| anyhow!("construct deterministic output pair: {error:?}"))?;
    let output_pair_leaf = output_pair
        .leaf_digest()
        .map_err(|error| anyhow!("hash deterministic output pair: {error:?}"))?;
    let next_tree = lane
        .tree
        .append_one_with_empty_roots(output_pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|error| anyhow!("construct deterministic afterstate: {error:?}"))?
        .0;
    let independently_derived_afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next_tree.next_leaf_index,
        next_root: next_tree.root,
        next_frontier: next_tree.frontier,
    };
    ensure!(
        candidate_afterstate == independently_derived_afterstate,
        "compiled R1 statement differs from independent lane transition"
    );
    let full_public_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&terminal_statement)
        .map_err(|error| anyhow!("encode full ASF8 public statement: {error:?}"))?
        .to_vec();
    ensure!(
        full_public_bytes.len() == 1_880,
        "ASF8 public statement length changed"
    );
    ensure!(
        decode_pool_v1_pair_forest_terminal_statement_v1(&full_public_bytes)
            .map_err(|error| anyhow!("decode generated ASF8: {error:?}"))?
            == terminal_statement,
        "encoded R1 public statement does not round-trip exactly"
    );
    let instruction_data = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|error| anyhow!("encode ASQ8: {error:?}"))?
        .to_vec();
    ensure!(
        instruction_data.len() == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
        "ASQ8 length changed"
    );
    let expected_afterstate = encode_pool_v1_pair_verified_afterstate_v1(&candidate_afterstate)
        .map_err(|error| anyhow!("encode deterministic afterstate: {error:?}"))?;
    ensure!(
        expected_afterstate.len() == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "candidate afterstate length changed"
    );
    ensure!(
        decode_pool_v1_pair_verified_afterstate_v1(&expected_afterstate)
            .map_err(|error| anyhow!("decode generated candidate: {error:?}"))?
            == candidate_afterstate,
        "encoded candidate afterstate does not round-trip exactly"
    );
    let task_dir = &args.task_dir;
    fs::create_dir_all(task_dir)?;
    let proof_sidecar = task_dir.join("r1-s2-proof.bin");
    let public_sidecar = task_dir.join("r1-s2-public-asf8.bin");
    ensure!(
        !proof_sidecar.exists() && !public_sidecar.exists(),
        "refusing to overwrite R1 proof/public sidecars in {}",
        task_dir.display()
    );
    #[allow(unused_mut)]
    let mut mask_nonce_ledger_path: Option<PathBuf> = None;
    let (proof_body, masked_audit, fixture_kind) = if let Some((reuse_proof, reuse_public)) =
        &args.reuse
    {
        let old_public = fs::read(reuse_public)
            .with_context(|| format!("read reused public statement {}", reuse_public.display()))?;
        ensure!(
            old_public == full_public_bytes,
            "reused proof public statement differs from this fixture"
        );
        let old_proof = fs::read(reuse_proof)
            .with_context(|| format!("read reused proof {}", reuse_proof.display()))?;
        ensure!(!old_proof.is_empty(), "reused proof is empty");
        write_new_file(&proof_sidecar, &old_proof)?;
        write_new_file(&public_sidecar, &old_public)?;
        (old_proof, None, "explicit-reuse")
    } else {
        let (proof, audit, fixture_kind) = match args.mask_entropy {
            MaskEntropy::Fixture => {
                let seed = [0x51; 32];
                let (proof, audit) = prover::prove_masked_fixture(
                    statement_public(&terminal_statement),
                    &compiled,
                    Variant::S2,
                    HOST_HASH,
                    &seed,
                )
                .map_err(|error| anyhow!("generate deterministic masked S2 fixture: {error:?}"))?;
                (proof, audit, "generated-masked-s2")
            }
            MaskEntropy::Os => {
                #[cfg(feature = "private-leaf-salts")]
                {
                    let ledger_path = args.task_dir.join("mask-nonce-ledger");
                    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(&ledger_path)
                        .with_context(|| {
                            format!("open durable mask nonce ledger {}", ledger_path.display())
                        })?;
                    let attempt = StateOnlyAttemptSecrets::generate().map_err(|error| {
                        anyhow!("generate fresh OS attempt secrets for masked S2 proof: {error:?}")
                    })?;
                    let (proof, audit) = prover::prove_masked_attempt(
                        statement_public(&terminal_statement),
                        &compiled,
                        Variant::S2,
                        HOST_HASH,
                        attempt,
                        &mut nonce_store,
                    )
                    .map_err(|error| anyhow!("generate OS-masked S2 attempt: {error:?}"))?;
                    mask_nonce_ledger_path = Some(ledger_path);
                    (proof, audit, "generated-os-masked-s2")
                }
                #[cfg(not(feature = "private-leaf-salts"))]
                {
                    bail!("--mask-entropy os requires the private-leaf-salts feature")
                }
            }
        };
        write_new_file(&proof_sidecar, &proof)?;
        write_new_file(&public_sidecar, &full_public_bytes)?;
        (proof, Some(audit), fixture_kind)
    };
    ensure!(!proof_body.is_empty(), "R1 proof body is empty");
    ensure!(
        proof_body.len() == verifier::PROOF_BYTES,
        "R1 S2 proof body has the wrong canonical length"
    );
    let mut payload = Vec::with_capacity(
        POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + proof_body.len() + R1_CHECKPOINT_BYTES,
    );
    payload.extend_from_slice(&expected_afterstate);
    payload.extend_from_slice(&proof_body);
    payload.resize(payload.len() + R1_CHECKPOINT_BYTES, 0);
    ensure!(
        payload.len()
            == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + proof_body.len() + R1_CHECKPOINT_BYTES,
        "ASPU body is not candidate || proof || fixed R1 checkpoint"
    );
    let expected_result = PoolV1PairForestTerminalResultV1 {
        transition_kind: request.public.transition_kind(),
        master_account: master_key.to_bytes(),
        selected_lane_account: lane_key.to_bytes(),
        output_lane,
        nullifier,
        verified_afterstate: candidate_afterstate,
    };
    let expected_result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&expected_result)
        .map_err(|error| anyhow!("encode expected ASR8: {error:?}"))?;
    ensure!(
        payload.len() <= u32::MAX as usize,
        "proof payload too large"
    );
    let proof_key = legacy(PROOF_ACCOUNT_BYTES);
    let public_key = legacy(PUBLIC_ACCOUNT_BYTES);

    let current_history_location = root_history_location(lane.tree.next_leaf_index);
    let next_history_location = root_history_location(lane.tree.next_leaf_index + 1);
    let rollover = current_history_location.page_number != next_history_location.page_number;
    let page_key = pool_v1_root_page_address(
        &pool_program,
        &lane_key,
        current_history_location.page_number,
    )
    .0;
    let next_page_key = rollover.then(|| {
        pool_v1_root_page_address(&pool_program, &lane_key, next_history_location.page_number).0
    });
    // B1: marker = create_with_seed(master, packed SHA-256 seed, Pool).
    let marker_key = pool_v1_pair_forest_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    // B4: Pool-only bump hints appended to ASQ8.
    let terminal_bump_hints = pool_v1_pair_forest_terminal_bump_hints_v1(
        &pool_program,
        &master_key,
        &lane_key,
        lane.tree.next_leaf_index,
        args.operation == Operation::Withdrawal,
    );
    let terminal_instruction_data =
        encode_pair_forest_terminal_instruction_data_v1(&instruction_data, terminal_bump_hints);
    ensure!(
        terminal_instruction_data.len()
            == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES + POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES,
        "terminal instruction data length changed"
    );
    let payer = retained_task_key(&args.task_dir.join("payer-keypair.json"))?;
    let authority = retained_task_key(&args.task_dir.join("authority-keypair.json"))?;
    let mut svm = LiteSVM::new();
    if args.runtime_compute_limit != u64::from(COMPUTE_UNIT_LIMIT) {
        let mut diagnostic_budget = ComputeBudget::new_with_defaults(false);
        diagnostic_budget.compute_unit_limit = args.runtime_compute_limit;
        svm = svm.with_compute_budget(diagnostic_budget);
    }
    svm.add_program(address(&pool_program), &pool_artifact)?;
    svm.add_program(address(&verifier_program), selected_verifier_artifact)?;
    svm.add_program(address(&registry_program), &registry_artifact)?;
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    svm.airdrop(&authority.pubkey(), 1_000_000)
        .map_err(|failed| anyhow!("fund registry authority: {:?}", failed.err))?;
    let governance = initialize_registry_v2(
        &mut svm,
        &payer,
        &authority,
        registry_program,
        &registry_artifact,
        verifier_program,
        selected_verifier_artifact,
        master_key,
        args.tx_version,
    )?;
    let registry_key = governance.registry_key;
    // Wrong-release testing deliberately supplies the valid active ASE2 under
    // a request carrying another release. The Pool must reject its canonical
    // PDA/decoded-release mismatch before verifier CPI.
    let entry_key = governance.entry_key;
    let current_page_first =
        current_history_location.page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
    let current_roots = &all_lane_roots[current_page_first as usize..];
    let mut history_image = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(
        &mut history_image,
        lane_key.to_bytes(),
        current_history_location.page_number,
        current_roots,
    )
    .map_err(|error| anyhow!("initialize populated lane history: {error:?}"))?;
    ensure!(
        all_lane_roots.len() == lane.tree.next_leaf_index as usize + 1,
        "deterministic history/root sequence mismatch"
    );
    let mut history_probe = history_image.clone();
    let mut next_history_probe = None;
    if rollover {
        let mut next = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(
            &mut next,
            lane_key.to_bytes(),
            next_history_location.page_number,
            &[candidate_afterstate.next_root],
        )
        .map_err(|error| anyhow!("initialize expected rollover page: {error:?}"))?;
        next_history_probe = Some(next);
    } else {
        append_root_history_page_bytes_v1(
            &mut history_probe,
            candidate_afterstate.next_pair_index,
            candidate_afterstate.next_root,
        )
        .map_err(|error| anyhow!("candidate does not extend current history page: {error:?}"))?;
    }
    put_account(
        &mut svm,
        master_key,
        pool_program,
        encode_pool_v1_pair_forest_master_v1(&master)
            .map_err(|error| anyhow!("encode master: {error:?}"))?
            .to_vec(),
    )?;
    put_account(
        &mut svm,
        checkpoint_key,
        pool_program,
        encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .map_err(|error| anyhow!("encode checkpoint: {error:?}"))?
            .to_vec(),
    )?;
    put_account(
        &mut svm,
        lane_key,
        pool_program,
        encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|error| anyhow!("encode lane: {error:?}"))?
            .to_vec(),
    )?;
    put_account(&mut svm, page_key, pool_program, history_image.clone())?;
    if let Some(next_page_key) = next_page_key {
        put_account(
            &mut svm,
            next_page_key,
            pool_program,
            vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
        )?;
    }
    let proof_body_len = payload.len();
    let proof_writable_body_len = proof_body_len - R1_CHECKPOINT_BYTES;
    put_account(
        &mut svm,
        proof_key,
        verifier_program,
        vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body_len],
    )?;
    put_account(
        &mut svm,
        public_key,
        verifier_program,
        vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + full_public_bytes.len()],
    )?;

    let proof_upload = lifecycle_upload(
        &mut svm,
        &payer,
        &authority,
        verifier_program,
        proof_key,
        0,
        &payload,
        proof_writable_body_len,
        "proof-upload",
        args.tx_version,
    )?;
    let public_upload = lifecycle_upload(
        &mut svm,
        &payer,
        &authority,
        verifier_program,
        public_key,
        1,
        &full_public_bytes,
        full_public_bytes.len(),
        "public-upload",
        args.tx_version,
    )?;
    let finalized_proof = svm
        .get_account(&address(&proof_key))
        .context("finalized ASPU account missing")?;
    let finalized_public = svm
        .get_account(&address(&public_key))
        .context("finalized ASRU account missing")?;
    ensure!(
        finalized_proof.data[..4] == POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC
            && finalized_proof.data[8..40].iter().all(|byte| *byte == 0)
            && finalized_public.data[..4] == *b"ASRU"
            && finalized_public.data[8..40].iter().all(|byte| *byte == 0),
        "finalized R1 uploads did not seal both account authorities"
    );
    ensure!(
        &finalized_proof.data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..] == payload.as_slice()
            && finalized_public.data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..]
                == full_public_bytes,
        "finalized R1 lifecycle bodies differ from uploaded bytes"
    );
    let lifecycle_upload_chunk_bytes = args.tx_version.upload_chunk_bytes();
    let lifecycle_negative_checks = if args.operation == Operation::Transfer
        && args.scenario == Scenario::Success
    {
        let wrong_authority =
            retained_task_key(&args.task_dir.join("wrong-authority-keypair.txt"))?;
        svm.airdrop(&wrong_authority.pubkey(), 1_000_000)
            .map_err(|failed| anyhow!("fund retained wrong authority: {:?}", failed.err))?;
        let mut checks = Vec::new();

        let tail_key = legacy([0x47; 32]);
        put_account(
            &mut svm,
            tail_key,
            verifier_program,
            vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body_len],
        )?;
        let tail_init = lifecycle_instruction(
            verifier_program,
            tail_key,
            legacy(authority.pubkey().to_bytes()),
            vec![4, 0],
        );
        execute_success_with_signers(
            &mut svm,
            &payer,
            tail_init,
            &[&authority],
            "negative-tail-init",
            args.tx_version,
        )?;

        let crossing = lifecycle_instruction(
            verifier_program,
            tail_key,
            legacy(authority.pubkey().to_bytes()),
            lifecycle_write_data(proof_writable_body_len - 2, &[0xa5; 4]),
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            crossing,
            &[&authority],
            &[tail_key],
            "lifecycle-tail-straddle",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"tail-straddle","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        let direct_tail = lifecycle_instruction(
            verifier_program,
            tail_key,
            legacy(authority.pubkey().to_bytes()),
            lifecycle_write_data(proof_writable_body_len, &[0xa5]),
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            direct_tail,
            &[&authority],
            &[tail_key],
            "lifecycle-tail-injection",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"tail-injection","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        let wrong_auth_write = lifecycle_instruction(
            verifier_program,
            tail_key,
            legacy(wrong_authority.pubkey().to_bytes()),
            lifecycle_write_data(0, &[0xa5]),
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            wrong_auth_write,
            &[&wrong_authority],
            &[tail_key],
            "lifecycle-wrong-authority",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"wrong-authority","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        let repeat_init = lifecycle_instruction(
            verifier_program,
            tail_key,
            legacy(authority.pubkey().to_bytes()),
            vec![4, 0],
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            repeat_init,
            &[&authority],
            &[tail_key],
            "lifecycle-repeat-init",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"repeat-init","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        for (name, data) in [
            ("post-seal-write", lifecycle_write_data(0, &[0xa5])),
            ("repeat-finalize", vec![6]),
        ] {
            let instruction = lifecycle_instruction(
                verifier_program,
                proof_key,
                legacy(authority.pubkey().to_bytes()),
                data,
            );
            let measure = failed_lifecycle_instruction_unchanged(
                &mut svm,
                &payer,
                instruction,
                &[&authority],
                &[proof_key],
                &format!("lifecycle-{name}"),
                args.tx_version,
            )?;
            checks.push(serde_json::json!({"name":name,"compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));
        }

        let malformed_proof_key = legacy([0x48; 32]);
        put_account(
            &mut svm,
            malformed_proof_key,
            verifier_program,
            vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body_len],
        )?;
        let malformed_init = lifecycle_instruction(
            verifier_program,
            malformed_proof_key,
            legacy(authority.pubkey().to_bytes()),
            vec![4, 0],
        );
        execute_success_with_signers(
            &mut svm,
            &payer,
            malformed_init,
            &[&authority],
            "negative-malformed-proof-init",
            args.tx_version,
        )?;
        let malformed_candidate = lifecycle_instruction(
            verifier_program,
            malformed_proof_key,
            legacy(authority.pubkey().to_bytes()),
            lifecycle_write_data(0, &vec![0xff; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]),
        );
        execute_success_with_signers(
            &mut svm,
            &payer,
            malformed_candidate,
            &[&authority],
            "negative-malformed-candidate-write",
            args.tx_version,
        )?;
        let malformed_finalize = lifecycle_instruction(
            verifier_program,
            malformed_proof_key,
            legacy(authority.pubkey().to_bytes()),
            vec![6],
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            malformed_finalize,
            &[&authority],
            &[malformed_proof_key],
            "lifecycle-malformed-candidate-finalize",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"malformed-candidate-finalize","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        let malformed_public_key = legacy([0x4b; 32]);
        put_account(
            &mut svm,
            malformed_public_key,
            verifier_program,
            vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + full_public_bytes.len()],
        )?;
        let malformed_public_init = lifecycle_instruction(
            verifier_program,
            malformed_public_key,
            legacy(authority.pubkey().to_bytes()),
            vec![4, 1],
        );
        execute_success_with_signers(
            &mut svm,
            &payer,
            malformed_public_init,
            &[&authority],
            "negative-malformed-public-init",
            args.tx_version,
        )?;
        for (index, chunk) in vec![0u8; full_public_bytes.len()]
            .chunks(lifecycle_upload_chunk_bytes)
            .enumerate()
        {
            let instruction = lifecycle_instruction(
                verifier_program,
                malformed_public_key,
                legacy(authority.pubkey().to_bytes()),
                lifecycle_write_data(index * lifecycle_upload_chunk_bytes, chunk),
            );
            execute_success_with_signers(
                &mut svm,
                &payer,
                instruction,
                &[&authority],
                "negative-malformed-public-write",
                args.tx_version,
            )?;
        }
        let malformed_public_finalize = lifecycle_instruction(
            verifier_program,
            malformed_public_key,
            legacy(authority.pubkey().to_bytes()),
            vec![6],
        );
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            malformed_public_finalize,
            &[&authority],
            &[malformed_public_key],
            "lifecycle-malformed-public-finalize",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"malformed-public-finalize","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));

        let unsealed_public_key = legacy([0x4c; 32]);
        put_account(
            &mut svm,
            unsealed_public_key,
            verifier_program,
            vec![0; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + full_public_bytes.len()],
        )?;
        let unsealed_init = lifecycle_instruction(
            verifier_program,
            unsealed_public_key,
            legacy(authority.pubkey().to_bytes()),
            vec![4, 1],
        );
        execute_success_with_signers(
            &mut svm,
            &payer,
            unsealed_init,
            &[&authority],
            "negative-unsealed-public-init",
            args.tx_version,
        )?;
        for (index, chunk) in full_public_bytes
            .chunks(lifecycle_upload_chunk_bytes)
            .enumerate()
        {
            let instruction = lifecycle_instruction(
                verifier_program,
                unsealed_public_key,
                legacy(authority.pubkey().to_bytes()),
                lifecycle_write_data(index * lifecycle_upload_chunk_bytes, chunk),
            );
            execute_success_with_signers(
                &mut svm,
                &payer,
                instruction,
                &[&authority],
                "negative-unsealed-public-write",
                args.tx_version,
            )?;
        }
        let unsealed_stage1 = Instruction {
            program_id: address(&verifier_program),
            accounts: vec![meta(proof_key, true), meta(unsealed_public_key, false)],
            data: vec![3, 10],
        };
        let measure = failed_lifecycle_instruction_unchanged(
            &mut svm,
            &payer,
            unsealed_stage1,
            &[],
            &[proof_key, unsealed_public_key],
            "stage1-unsealed-public",
            args.tx_version,
        )?;
        checks.push(serde_json::json!({"name":"unsealed-stage1","compute_units":measure.compute_units,"serialized_bytes":measure.bytes,"program_error":measure.error,"program_invoked":measure.compute_units>0,"rollback":true}));
        checks
    } else {
        Vec::new()
    };

    let proof_prefix_len = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        + proof_body.len();
    let pre_stage1 = svm
        .get_account(&address(&proof_key))
        .context("R1 ASPU account missing before stage 1")?;
    let unchanged_prefix = pre_stage1.data[..proof_prefix_len].to_vec();
    ensure!(
        pre_stage1.data[proof_prefix_len..]
            .iter()
            .all(|&byte| byte == 0),
        "initial R1 checkpoint tail is not zero"
    );
    let stage1_instruction = Instruction {
        program_id: address(&verifier_program),
        accounts: vec![meta(proof_key, true), meta(public_key, false)],
        data: vec![3, 10],
    };
    let stage1_tx = transaction(&svm, &payer, stage1_instruction, args.tx_version)?;
    let stage1_bytes = wincode::serialize(&stage1_tx)?.len();
    let stage1_measurement = execute_success(&mut svm, stage1_tx, "r1-stage1")?;
    let post_stage1 = svm
        .get_account(&address(&proof_key))
        .context("R1 ASPU account missing after stage 1")?;
    ensure!(
        post_stage1.data[..proof_prefix_len] == unchanged_prefix,
        "R1 stage 1 changed ASPU header, candidate, or proof body"
    );
    ensure!(
        post_stage1.data[proof_prefix_len..]
            .iter()
            .any(|&byte| byte != 0),
        "R1 stage 1 left the checkpoint tail unchanged"
    );
    ensure!(
        svm.get_account(&address(&public_key))
            .context("R1 public account missing after stage 1")?
            .data
            == finalized_public.data,
        "R1 stage 1 changed its read-only public statement"
    );
    let stage1_checkpoint_tail = post_stage1.data[proof_prefix_len..].to_vec();
    if args.scenario == Scenario::ProofRejection {
        let mut mutated = svm
            .get_account(&address(&proof_key))
            .context("R1 ASPU account missing before proof mutation")?;
        let proof_byte = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
            + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
            + proof_body.len()
            - 1;
        mutated.data[proof_byte] ^= 1;
        ensure!(
            mutated.data[proof_prefix_len..] == stage1_checkpoint_tail,
            "proof-rejection mutation altered checkpoint tail"
        );
        svm.set_account(address(&proof_key), mutated)?;
    }
    let submitted_proof_account = svm
        .get_account(&address(&proof_key))
        .context("R1 ASPU account missing before Pool terminal")?;
    let submitted_proof_body = &submitted_proof_account.data
        [POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
            ..proof_prefix_len];

    if args.scenario == Scenario::StaleLane {
        ensure!(
            !rollover,
            "stale-lane scenario currently requires same-page history"
        );
        let stale_tree = lane
            .tree
            .append_one_with_empty_roots(strict_lane_digest(0x5a5a), &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|error| anyhow!("construct concurrent stale-lane append: {error:?}"))?
            .0;
        let stale_lane = PoolV1PairForestLaneStateV1 {
            bump: lane.bump,
            master: lane.master,
            lane_id: lane.lane_id,
            tree: stale_tree,
        };
        let mut stale_history = history_image;
        append_root_history_page_bytes_v1(
            &mut stale_history,
            stale_tree.next_leaf_index,
            stale_tree.root,
        )
        .map_err(|error| anyhow!("append concurrent stale-lane history: {error:?}"))?;
        put_account(
            &mut svm,
            lane_key,
            pool_program,
            encode_pool_v1_pair_forest_lane_state_v1(&stale_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                .map_err(|error| anyhow!("encode concurrent stale lane: {error:?}"))?
                .to_vec(),
        )?;
        put_account(&mut svm, page_key, pool_program, stale_history)?;
    }

    let token_program = LegacyPubkey::from_str(LEGACY_SPL_TOKEN_PROGRAM_ID)?;
    if args.scenario == Scenario::WithdrawalCpiFailure {
        ensure!(
            args.operation == Operation::Withdrawal,
            "withdrawal-cpi-failure requires withdrawal operation"
        );
        // The production verifier still runs and returns an honest ASR8. This
        // test-only program replaces Tokenkeg only after Registry V2 setup so
        // the subsequent custody CPI fails and LiteSVM must roll back the
        // marker reservation, lane/history writes, and token state atomically.
        svm.add_program(address(&token_program), &result_double_artifact)?;
    }
    let vault_authority = pool_v1_vault_authority_address(&pool_program, &master_key).0;
    let vault_key = pool_v1_vault_token_account_address(&pool_program, &master_key).0;
    let destination_key = legacy(DESTINATION_TOKEN_ACCOUNT_BYTES);
    if args.operation == Operation::Withdrawal {
        put_account(
            &mut svm,
            mint,
            token_program,
            initialized_mint_data(1_000_000, 6),
        )?;
        put_account(
            &mut svm,
            vault_key,
            token_program,
            initialized_token_data(mint, vault_authority, VAULT_BALANCE_BEFORE),
        )?;
        put_account(
            &mut svm,
            destination_key,
            token_program,
            initialized_token_data(
                mint,
                legacy(DESTINATION_TOKEN_OWNER_BYTES),
                DESTINATION_BALANCE_BEFORE,
            ),
        )?;
        put_account(
            &mut svm,
            vault_authority,
            LegacyPubkey::default(),
            Vec::new(),
        )?;
    }

    let mut protected_keys = vec![master_key, checkpoint_key, lane_key, page_key];
    if let Some(next_page_key) = next_page_key {
        protected_keys.push(next_page_key);
    }
    let marker_snapshot_index = protected_keys.len();
    protected_keys.extend([
        marker_key,
        registry_key,
        governance.entry_key,
        proof_key,
        public_key,
    ]);
    let registry_snapshot_index = marker_snapshot_index + 1;
    let entry_snapshot_index = marker_snapshot_index + 2;
    let proof_snapshot_index = marker_snapshot_index + 3;
    let public_snapshot_index = marker_snapshot_index + 4;
    let token_snapshot_index = protected_keys.len();
    if args.operation == Operation::Withdrawal {
        protected_keys.extend([mint, vault_key, destination_key, vault_authority]);
    }
    let before = snapshot(&svm, &protected_keys);
    let mut instruction_accounts = vec![
        meta(master_key, false),
        meta(checkpoint_key, false),
        meta(lane_key, true),
        meta(page_key, !rollover),
    ];
    if let Some(next_page_key) = next_page_key {
        instruction_accounts.push(meta(next_page_key, true));
    }
    instruction_accounts.extend([
        meta(marker_key, true),
        signer_meta(legacy(payer.pubkey().to_bytes()), true),
        meta(LegacyPubkey::from_str(SYSTEM_PROGRAM_ID)?, false),
        meta(registry_key, false),
        meta(entry_key, false),
        meta(verifier_program, false),
        meta(proof_key, false),
    ]);
    if args.operation == Operation::Withdrawal {
        instruction_accounts.extend([
            meta(mint, false),
            meta(vault_key, true),
            meta(destination_key, true),
            meta(vault_authority, false),
            meta(token_program, false),
        ]);
    }
    let instruction = Instruction {
        program_id: address(&pool_program),
        accounts: instruction_accounts,
        data: terminal_instruction_data.clone(),
    };
    let instruction_account_count = instruction.accounts.len();
    let tx = transaction(&svm, &payer, instruction.clone(), args.tx_version)?;
    let tx_bytes = wincode::serialize(&tx)?.len();
    ensure!(
        tx_bytes <= args.tx_version.target_bytes(),
        "transaction exceeds selected {} target",
        args.tx_version.display_name()
    );

    let expected_lane_image = encode_pool_v1_pair_forest_lane_state_v1(
        &PoolV1PairForestLaneStateV1 {
            bump: lane.bump,
            master: lane.master,
            lane_id: lane.lane_id,
            tree: next_tree,
        },
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|error| anyhow!("encode expected next lane: {error:?}"))?;
    let marker_payload = PoolV1NullifierMarkerV1 {
        transition_kind: request.public.transition_kind(),
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        nullifier,
        retained_anchor_sequence: checkpoint_sequence,
        retained_anchor_root: historical_global_anchor,
        verifier_profile: PROFILE_BINDING,
        verifier_release: request.verifier_release,
    };
    let expected_marker_image = encode_pool_v1_nullifier_marker(&marker_payload)
        .map_err(|error| anyhow!("encode expected marker: {error:?}"))?;
    if args.scenario == Scenario::Replay {
        ensure!(
            !rollover,
            "replay/nullifier measurement requires same-page layout"
        );
    }
    let first_success = args.scenario.expects_first_terminal_success();
    let first_measurement = if first_success {
        execute_success(&mut svm, tx, "pair-forest-terminal")?
    } else {
        execute_failure(&mut svm, tx, "pair-forest-terminal")?
    };
    if first_success {
        ensure!(
            first_measurement.return_program == address(&pool_program)
                && first_measurement.return_data == expected_result_bytes,
            "successful transaction returned the wrong Pool ASR8"
        );
    }
    let after_first = snapshot(&svm, &protected_keys);
    if first_success {
        ensure!(
            before[0] == after_first[0]
                && before[1] == after_first[1]
                && before[registry_snapshot_index] == after_first[registry_snapshot_index]
                && before[entry_snapshot_index] == after_first[entry_snapshot_index]
                && before[proof_snapshot_index] == after_first[proof_snapshot_index]
                && before[public_snapshot_index] == after_first[public_snapshot_index],
            "successful terminal mutated a read-only authenticated account"
        );
        if args.operation == Operation::Withdrawal {
            ensure!(
                before[token_snapshot_index] == after_first[token_snapshot_index]
                    && before[token_snapshot_index + 3] == after_first[token_snapshot_index + 3],
                "successful withdrawal mutated mint or vault authority"
            );
            ensure!(
                token_amount(present_account(
                    &before[token_snapshot_index + 1],
                    "vault before",
                )?)? == VAULT_BALANCE_BEFORE
                    && token_amount(present_account(
                        &after_first[token_snapshot_index + 1],
                        "vault after",
                    )?)? == VAULT_BALANCE_BEFORE - WITHDRAWAL_AMOUNT,
                "withdrawal vault delta was not exact"
            );
            ensure!(
                token_amount(present_account(
                    &before[token_snapshot_index + 2],
                    "destination before",
                )?)? == DESTINATION_BALANCE_BEFORE
                    && token_amount(present_account(
                        &after_first[token_snapshot_index + 2],
                        "destination after",
                    )?)? == DESTINATION_BALANCE_BEFORE + WITHDRAWAL_AMOUNT,
                "withdrawal destination delta was not exact"
            );
        }
        let settled_lane = present_account(&after_first[2], "settled lane")?;
        let settled_history = present_account(&after_first[3], "settled history")?;
        let settled_marker =
            present_account(&after_first[marker_snapshot_index], "settled marker")?;
        ensure!(
            settled_lane.data == expected_lane_image,
            "wrong next lane image"
        );
        ensure!(
            settled_history.data == history_probe,
            "wrong current history image"
        );
        if let Some(expected) = &next_history_probe {
            ensure!(
                present_account(&after_first[4], "settled rollover page")?.data == *expected,
                "wrong rollover history image"
            );
        }
        ensure!(
            settled_marker.data == expected_marker_image,
            "wrong nullifier marker image"
        );
        ensure!(
            decode_pool_v1_pair_forest_lane_state_v1(&settled_lane.data, &POOL_V1_PAIR_EMPTY_ROOTS,)
                .map_err(|error| anyhow!("decode settled lane: {error:?}"))?
                .tree == next_tree,
            "settled lane did not decode to the exact candidate tree"
        );
        ensure!(
            decode_pool_v1_nullifier_marker(&settled_marker.data)
                .map_err(|error| anyhow!("decode settled marker: {error:?}"))?
                == marker_payload,
            "settled marker did not decode to the exact nullifier payload"
        );
    } else {
        ensure!(
            before == after_first,
            "failed terminal mutated protected Pool state"
        );
    }

    let verifier_address = address(&verifier_program).to_string();
    let invoked_verifier = first_measurement
        .logs
        .iter()
        .any(|line| line.contains(&verifier_address) && line.contains("invoke"));
    ensure!(
        invoked_verifier == args.scenario.verifier_cpi_expected(),
        "unexpected selected-verifier CPI presence for {}:\n{}",
        args.scenario.label(),
        first_measurement.logs.join("\n")
    );
    let withdrawal_cpi_failure_trace = if args.scenario == Scenario::WithdrawalCpiFailure {
        let token_address = address(&token_program).to_string();
        let verifier_success_index = first_measurement
            .logs
            .iter()
            .position(|line| line.contains(&verifier_address) && line.contains("success"))
            .context("withdrawal CPI failure: stage2 verifier success log missing")?;
        let token_invoke_index = first_measurement
            .logs
            .iter()
            .position(|line| line.contains(&token_address) && line.contains("invoke"))
            .context("withdrawal CPI failure: injected token program invocation missing")?;
        let token_failure_index = first_measurement
            .logs
            .iter()
            .position(|line| line.contains(&token_address) && line.contains("failed"))
            .context("withdrawal CPI failure: injected token program failure log missing")?;
        ensure!(
            verifier_success_index < token_invoke_index
                && token_invoke_index < token_failure_index,
            "withdrawal CPI failure: verifier stage2 success did not precede injected token-program failure:\n{}",
            first_measurement.logs.join("\n")
        );
        Some(serde_json::json!({
            "stage2_verifier_success_log_index": verifier_success_index,
            "injected_token_invoke_log_index": token_invoke_index,
            "injected_token_failure_log_index": token_failure_index,
            "injected_token_program": token_address,
            "uses_test_only_failing_program_double": true,
            "this_does_not_indicate_a_real_token_program_defect": true,
        }))
    } else {
        None
    };

    let replay_measurement = if args.scenario == Scenario::Replay {
        let replay_before = snapshot(&svm, &protected_keys);
        svm.expire_blockhash();
        let replay_tx = transaction(&svm, &payer, instruction, args.tx_version)?;
        let measurement = execute_failure(&mut svm, replay_tx, "pair-forest-replay")?;
        assert_program_rejection(&measurement, address(&pool_program), "pair-forest-replay")?;
        ensure!(
            snapshot(&svm, &protected_keys) == replay_before,
            "replay rejection changed settled state"
        );
        Some(measurement)
    } else {
        None
    };

    let proof_bytes = Some(proof_body.len());
    let asr2_fixture = args.evidence.with_extension("asr2.bin");
    let ase2_fixture = args.evidence.with_extension("ase2.bin");
    ensure!(
        !asr2_fixture.exists() && !ase2_fixture.exists(),
        "refusing to overwrite Registry V2 fixture sidecars"
    );
    let settled_lane_equals_candidate = after_first[2]
        .as_ref()
        .map(|account| account.data == expected_lane_image)
        .unwrap_or(false);
    let settled_history_equals_expected = after_first[3]
        .as_ref()
        .map(|account| account.data == history_probe)
        .unwrap_or(false);
    let settled_rollover_page_equals_expected = next_history_probe.as_ref().map(|expected| {
        after_first[4]
            .as_ref()
            .map(|account| account.data == *expected)
            .unwrap_or(false)
    });
    let settled_marker_equals_expected = after_first[marker_snapshot_index]
        .as_ref()
        .map(|account| account.data == expected_marker_image)
        .unwrap_or(false);
    let evidence = serde_json::json!({
        "schema": "aspis.r1-s2-pool-gate-litesvm.v1",
        "classification": if first_success {
            "UNPROVED R1 S2 POOL-PATH ACCEPTANCE MEASUREMENT"
        } else {
            "UNPROVED R1 S2 POOL-PATH REJECTION MEASUREMENT"
        },
        "scenario": args.scenario.label(),
        "fixture": {
            "kind": fixture_kind,
            "mask_entropy_option": args.mask_entropy.label(),
            "entropy_source": if fixture_kind == "explicit-reuse" {
                "unknown-original-entropy"
            } else {
                args.mask_entropy.source_label()
            },
            "mask_mode": if fixture_kind == "explicit-reuse" {
                "unknown-from-reused-proof"
            } else {
                "full-mask"
            },
            "mask_nonce_ledger_path": mask_nonce_ledger_path,
            "external_path": args.reuse.as_ref().map(|(proof, _)| proof),
            "proof_sidecar": proof_sidecar,
            "public_sidecar": public_sidecar,
            "proof_source": fixture_kind,
            "payload_bytes": payload.len(),
            "candidate_afterstate_bytes": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "proof_bytes": proof_bytes,
            "payload_sha256": sha256_hex(&payload),
            "proof_sha256": sha256_hex(&proof_body),
            "submitted_proof_sha256": sha256_hex(submitted_proof_body),
            "proof_byte_mutated_by_harness": args.scenario == Scenario::ProofRejection,
            "r1_checkpoint_bytes": R1_CHECKPOINT_BYTES,
            "masked_fixture_audit": masked_audit.map(|audit| serde_json::json!({
                "c1_columns_inactive_balanced": audit.c1_columns_inactive_balanced,
                "mask_only_columns_inactive_balanced": audit.mask_only_columns_inactive_balanced,
                "d_inactive_balanced": audit.d_inactive_balanced,
                "g_inactive_balanced": audit.g_inactive_balanced,
                "h1_padding_inactive_balanced": audit.h1_padding_inactive_balanced,
                "h1_total_balanced": audit.h1_total_balanced,
            })),
            "strict_work_expected": true,
        },
        "registry_v2_governance": {
            "runtime": "LiteSVM 0.16.0",
            "registry_program": registry_program.to_string(),
            "registry_programdata": LegacyPubkey::find_program_address(
                &[registry_program.as_ref()],
                &LegacyPubkey::from_str(BPF_LOADER_UPGRADEABLE_ID)?,
            ).0.to_string(),
            "registry_executable_sha256": bytes_hex(&governance.registry_hash),
            "selected_verifier_executable_sha256": bytes_hex(&governance.verifier_hash),
        "wrong_registry_code_hash_rejection": tx_measurement_json(&governance.wrong_registry_hash, args.tx_version),
            "initialize": tx_measurement_json(&governance.initialize, args.tx_version),
            "wrong_verifier_code_hash_rejection": tx_measurement_json(&governance.wrong_verifier_hash, args.tx_version),
            "schedule": tx_measurement_json(&governance.schedule, args.tx_version),
            "activate": tx_measurement_json(&governance.activate, args.tx_version),
            "freeze": tx_measurement_json(&governance.freeze, args.tx_version),
            "final_registry_pda": governance.registry_key.to_string(),
            "final_entry_pda": governance.entry_key.to_string(),
            "final_registry_magic": "ASR2",
            "final_entry_magic": "ASE2",
            "registry_fixture_path": asr2_fixture,
            "entry_fixture_path": ase2_fixture,
            "registry_fixture_bytes": governance.registry_image.len(),
            "entry_fixture_bytes": governance.entry_image.len(),
            "registry_fixture_sha256": sha256_hex(&governance.registry_image),
            "entry_fixture_sha256": sha256_hex(&governance.entry_image),
            "final_generation": 3,
            "final_authority_zero": true,
            "final_registry_immutable": true,
            "entry_active_at_slot": ACTIVATION_SLOT,
            "programdata_upgrade_authorities": "None, authenticated by Registry V2",
            "failed_hash_checks_preserved_registry_and_entry_byte_exact": true,
        },
        "execution": {
            "runtime": "LiteSVM 0.16.0",
            "network": "none",
            "transaction_version": args.tx_version.label(),
            "transaction_format": match args.tx_version { TxVersion::V0 => "true Solana TxV0 / VersionedMessage::V0", TxVersion::V1 => "true Solana TxV1 / VersionedMessage::V1" },
            "terminal_transport": "ASQ8 / 320-byte compact request",
            "serialized_transaction_bytes": tx_bytes,
            "serialized_transaction_target_bytes": args.tx_version.target_bytes(),
            "serialized_transaction_target_headroom_bytes": args.tx_version.target_bytes() - tx_bytes,
            "instruction_bytes": terminal_instruction_data.len(),
            "terminal_bump_hints": terminal_bump_hints.encode().to_vec(),
            "marker_address_scheme": "b1-create-with-seed(master, 7bit(sha256(aspis-marker-seed-v1||master||nullifier)[..28]), pool)",
            "instruction_account_metas": instruction_account_count,
            "declared_compute_unit_limit": COMPUTE_UNIT_LIMIT,
            "priority_fee_lamports": if args.tx_version == TxVersion::V1 { Some(PRIORITY_FEE_LAMPORTS) } else { None },
            "loaded_accounts_data_size_limit": LOADED_ACCOUNTS_DATA_SIZE_LIMIT,
            "heap_size": HEAP_SIZE,
            "runtime_compute_limit": args.runtime_compute_limit,
            "uploader_lifecycle": {
                "init_write_finalize_abi": [4, 5, 6],
                "proof_kind": 0,
                "public_kind": 1,
                "write_chunk_bytes": lifecycle_upload_chunk_bytes,
                "proof_upload_count": proof_upload.upload_count,
                "public_upload_count": public_upload.upload_count,
                "upload_count": proof_upload.upload_count + public_upload.upload_count,
                "proof_upload_serialized_bytes": proof_upload.upload_serialized_bytes,
                "public_upload_serialized_bytes": public_upload.upload_serialized_bytes,
                "upload_serialized_bytes": proof_upload.upload_serialized_bytes + public_upload.upload_serialized_bytes,
                "all_lifecycle_serialized_bytes": proof_upload.lifecycle_serialized_bytes + public_upload.lifecycle_serialized_bytes,
                "upload_payload_bytes": proof_writable_body_len + full_public_bytes.len(),
                "max_lifecycle_compute_units": proof_upload.max_compute_units.max(public_upload.max_compute_units),
                "payer_separate_from_readonly_signing_authority": payer.pubkey() != authority.pubkey(),
                "proof_authority_sealed": finalized_proof.data[8..40].iter().all(|byte| *byte == 0),
                "public_authority_sealed": true,
                "sealed_bodies_match_uploaded_bytes": true,
                "stage1_reads_finalized_asru": true,
                "negative_checks": lifecycle_negative_checks,
            },
            "stage1_instruction_data": [3, 10],
            "stage1_serialized_transaction_bytes": stage1_bytes,
            "stage1_compute_units": stage1_measurement.compute_units,
            "stage1_error": stage1_measurement.error,
            "stage1_logs": stage1_measurement.logs,
            "stage1_simulation_equals_execution": true,
            "stage1_unchanged_header_candidate_proof": true,
            "stage1_checkpoint_tail_bytes": R1_CHECKPOINT_BYTES,
            "stage1_checkpoint_tail_sha256": sha256_hex(&stage1_checkpoint_tail),
            "proof_rejection_mutation_preserved_checkpoint_tail": args.scenario != Scenario::ProofRejection
                || submitted_proof_account.data[proof_prefix_len..] == stage1_checkpoint_tail,
            "terminal_snapshot_taken_after_stage1": true,
            "runtime_limit_is_diagnostic_override": args.runtime_compute_limit != u64::from(COMPUTE_UNIT_LIMIT),
            "compute_units": first_measurement.compute_units,
            "outcome": if first_success { "accepted" } else { "rejected" },
            "operation": match args.operation { Operation::Transfer => "private-transfer", Operation::Withdrawal => "withdrawal" },
        "populated_pairs_requested": args.populated_pairs,
            "simulation_equals_execution": true,
            "error": first_measurement.error,
            "selected_verifier_cpi_observed_in_logs": invoked_verifier,
            "return_program": first_measurement.return_program.to_string(),
            "return_data_bytes": first_measurement.return_data.len(),
            "return_data_sha256": sha256_hex(&first_measurement.return_data),
            "logs": first_measurement.logs,
            "replay": replay_measurement
                .as_ref()
                .map(|measurement| tx_measurement_json(measurement, args.tx_version)),
            "withdrawal_cpi_failure_trace": withdrawal_cpi_failure_trace,
        },
        "authenticated_path": {
            "pool_program": pool_program.to_string(),
            "verifier_program": verifier_program.to_string(),
            "registry_program": registry_program.to_string(),
            "master": master_key.to_string(),
            "checkpoint": checkpoint_key.to_string(),
            "selected_output_lane": output_lane,
            "selected_lane": lane_key.to_string(),
            "history_page": page_key.to_string(),
            "rollover_history_page": next_page_key.map(|key| key.to_string()),
            "history_mode": if rollover { "rollover" } else { "same-page" },
            "nullifier_marker": marker_key.to_string(),
            "proof_account": proof_key.to_string(),
            "registry_profile_and_release_exact": true,
            "registry_entry_active_at_slot": PROFILE_SLOT,
            "registry_family": "ASR2/ASE2 immutable deployment",
            "registry_code_certificate_matches_loaded_programdata": true,
            "verifier_code_certificate_matches_loaded_programdata": true,
            "proof_owner_is_selected_verifier": true,
            "candidate_afterstate_matches_deterministic_lane_transition": true,
            "populated_lane_pairs_before": lane.tree.next_leaf_index,
            "history_roots_before": current_roots.len()
        },
        "atomicity": {
            "master_unchanged": before[0] == after_first[0],
            "checkpoint_unchanged": before[1] == after_first[1],
            "lane_changed_exactly_on_success": (before[2] != after_first[2]) == first_success,
            "history_changed_exactly_on_success": (before[3] != after_first[3]) == first_success,
            "rollover_page_changed_exactly_on_success": next_page_key.map(|_| (before[4] != after_first[4]) == first_success),
            "nullifier_marker_absent_before": before[marker_snapshot_index].is_none(),
            "nullifier_marker_changed_exactly_on_success": (before[marker_snapshot_index] != after_first[marker_snapshot_index]) == first_success,
            "registry_unchanged": before[registry_snapshot_index] == after_first[registry_snapshot_index],
            "entry_unchanged": before[entry_snapshot_index] == after_first[entry_snapshot_index],
            "proof_unchanged": before[proof_snapshot_index] == after_first[proof_snapshot_index],
            "stage1_public_unchanged": before[public_snapshot_index] == after_first[public_snapshot_index],
            "withdrawal_mint_unchanged": if args.operation == Operation::Withdrawal {
                Some(before[token_snapshot_index] == after_first[token_snapshot_index])
            } else {
                None
            },
            "withdrawal_vault_amount_before": (args.operation == Operation::Withdrawal).then(|| token_amount(present_account(&before[token_snapshot_index + 1], "vault before evidence")?)).transpose()?,
            "withdrawal_vault_amount_after": (args.operation == Operation::Withdrawal).then(|| token_amount(present_account(&after_first[token_snapshot_index + 1], "vault after evidence")?)).transpose()?,
            "withdrawal_destination_amount_before": (args.operation == Operation::Withdrawal).then(|| token_amount(present_account(&before[token_snapshot_index + 2], "destination before evidence")?)).transpose()?,
            "withdrawal_destination_amount_after": (args.operation == Operation::Withdrawal).then(|| token_amount(present_account(&after_first[token_snapshot_index + 2], "destination after evidence")?)).transpose()?,
            "settled_lane_equals_candidate": settled_lane_equals_candidate,
            "settled_history_equals_expected": settled_history_equals_expected,
            "settled_rollover_page_equals_expected": settled_rollover_page_equals_expected,
            "settled_marker_equals_expected": settled_marker_equals_expected,
            "failure_all_accounts_byte_exact": !first_success && before == after_first,
            "replay_preserved_settled_state_byte_exact": (args.scenario == Scenario::Replay).then_some(true),
        },
        "artifacts": {
            "pool": {
                "path": args.pool_program,
                "bytes": pool_artifact.len(),
                "sha256": sha256_hex(&pool_artifact)
            },
            "r1_cost_probe_verifier": {
                "path": args.verifier_program,
                "bytes": production_verifier_artifact.len(),
                "sha256": sha256_hex(&production_verifier_artifact)
            },
            "registry": {
                "path": args.registry_program,
                "bytes": registry_artifact.len(),
                "sha256": sha256_hex(&registry_artifact)
            },
            "selected_verifier": {
                "kind": "UNPROVED R1 S2 cost-probe adapter",
                "bytes": selected_verifier_artifact.len(),
                "sha256": sha256_hex(selected_verifier_artifact)
            },
            "token_program": {
                "program_id": token_program.to_string(),
                "kind": if args.scenario == Scenario::WithdrawalCpiFailure {
                    "test-only failing CPI double installed at Tokenkeg"
                } else {
                    "LiteSVM legacy SPL Token builtin"
                }
            },
        },
        "honest_fixture_contract": {
            "argument": "R1 S2 proof generated here or explicitly reused after exact ASF8 equality",
            "payload_layout": "688-byte candidate || R1 S2 proof || 1,768-byte zero checkpoint tail, inside a 40-byte ASPU header",
            "fixed_proof_account": proof_key.to_string(),
            "fixed_verifier_program": verifier_program.to_string(),
            "fixed_pool_master": master_key.to_string(),
            "requirement": "deterministic fixture statement is constructed from live LiteSVM master/checkpoint/lane identities and snapshot"
        },
        "boundaries": [
            "This is deterministic local LiteSVM evidence. No devnet, mainnet, signing service, or RPC is used.",
            format!(
                "The transaction is a real {} message with the 1.4M compute limit in its budget configuration.",
                args.tx_version.display_name()
            ),
            "A runtime limit above 1.4M is an explicit local diagnostic override and is not deployable evidence.",
            "The R1 protocol is unproved; this harness reports only its deterministic S2 fixture and Pool path measurements.",
            "ASR2/ASE2 are created by real Registry V2 instructions against loader-v3 Program/ProgramData accounts installed by LiteSVM, not hand-encoded terminal fixtures.",
            "withdrawal-cpi-failure installs a test-only failing program at the token program address to exercise rollback after stage2; it is not a claim of a defect in the real token program."
        ]
    });
    if let Some(parent) = args.evidence.parent() {
        fs::create_dir_all(parent)?;
    }
    if args.evidence.exists() {
        bail!("refusing to overwrite {}", args.evidence.display());
    }
    fs::write(&asr2_fixture, &governance.registry_image)?;
    fs::write(&ase2_fixture, &governance.entry_image)?;
    fs::write(&args.evidence, serde_json::to_vec_pretty(&evidence)?)?;
    println!(
        "pair-forest Registry V2 {} PASS: {} CU, {} {} bytes",
        args.scenario.label(),
        first_measurement.compute_units,
        tx_bytes,
        args.tx_version.display_name()
    );
    if let Some(replay) = replay_measurement {
        println!(
            "pair-forest replay rejection PASS: {} CU, {} {} bytes",
            replay.compute_units,
            replay.bytes,
            args.tx_version.display_name()
        );
    }
    println!("asr2_fixture={}", asr2_fixture.display());
    println!("ase2_fixture={}", ase2_fixture.display());
    println!("evidence={}", args.evidence.display());
    Ok(())
}
