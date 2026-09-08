use std::{
    convert::Infallible,
    env, fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::{
    derive_viewing_keypair_v1, encrypt_note_v1,
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_client_v2::{
        select_pair_forest_spend_profile_v2, FinalizedPairForestProfileAccountsV2,
        PairForestSpendProfileRequestV2, PairForestSpendProfileSelectionV2,
        PairForestVerifierRegistryFamilyV2,
    },
    lane_forest_durable_v2::{
        authenticate_forest_lane_account_v2, authenticate_forest_master_account_v2,
    },
    lane_forest_rpc_v2::FinalizedForestAccountV2,
    lane_forest_transaction_v1::{
        build_exact_pair_forest_v1_carrier_transaction_v2,
        build_initialize_terminal_pda_certificate_instruction_v1_4k_v2,
        build_pair_forest_terminal_instruction_v1_4k_v2,
        build_pair_forest_terminal_instruction_with_pda_certificate_v1_4k_v3,
        build_pair_forest_terminal_pda_certificate_v1_4k_v2,
        validate_signed_pair_forest_v1_carrier_transaction_v2, PairForestV1TransactionConfigV2,
    },
    tx_v1_ciphertext_carrier_v2::TxV1CiphertextCarrierV2,
    NoteContextV1, NoteOpeningV1,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_terminal_request_v1, pool_v1_pair_forest_output_lane_v1,
        root_history_location, PoolV1PairForestLaneStateV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use hpke::rand_core::{TryCryptoRng, TryRng};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_keypair::read_keypair_file;
use solana_message::{legacy, VersionedMessage};
use solana_message_v1::VersionedMessage as V1VersionedMessage;
use solana_program::{hash::Hash, pubkey::Pubkey, system_instruction};
use solana_sdk_ids::bpf_loader_upgradeable;
use solana_signature_v1::Signature as V1Signature;
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;
use solana_transaction_v1::versioned::VersionedTransaction as V1VersionedTransaction;

struct OsEntropy;
impl TryRng for OsEntropy {
    type Error = Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut b = [0; 4];
        self.try_fill_bytes(&mut b)?;
        Ok(u32::from_le_bytes(b))
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut b = [0; 8];
        self.try_fill_bytes(&mut b)?;
        Ok(u64::from_le_bytes(b))
    }
    fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Self::Error> {
        getrandom::getrandom(destination).expect("operating-system entropy unavailable");
        Ok(())
    }
}
impl TryCryptoRng for OsEntropy {}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    bundle: String,
    asq8: String,
    payer_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    carrier_test_mode: Option<String>,
    withdrawal_cpi_test_mode: Option<String>,
    compute_unit_limit: Option<u32>,
    terminal_pda_certificate_keypair: Option<String>,
    terminal_pda_certificate_rent_lamports: Option<u64>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Bundle {
    program_id: String,
    proof_account: String,
    finalized_point: Point,
    provider_set_digest_hex: String,
    master: Account,
    lanes: Vec<Account>,
    registry: Account,
    registry_entry: Account,
    secrets_file: String,
    custody: Option<Custody>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Custody {
    mint: Account,
    vault: Account,
    destination: Account,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Point {
    slot: u64,
    block_hash_hex: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Account {
    address: String,
    owner: String,
    executable: bool,
    data_base64: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Secret {
    operation: String,
    recipient_note: Option<Note>,
    change_note: Note,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Note {
    owner_key_hex: String,
    value: u32,
    asset_id: u32,
    salt_hex: String,
}

fn hex32(value: &str, label: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "{label} length");
    let mut out = [0; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&value[i * 2..i * 2 + 2], 16)?;
    }
    Ok(out)
}
fn account(value: &Account) -> Result<FinalizedForestAccountV2> {
    Ok(FinalizedForestAccountV2 {
        address: Pubkey::from_str(&value.address)?.to_bytes(),
        owner: Pubkey::from_str(&value.owner)?.to_bytes(),
        executable: value.executable,
        data: BASE64.decode(&value.data_base64)?,
    })
}
fn note(value: Note) -> Result<NoteOpeningV1> {
    NoteOpeningV1::new(
        hex32(&value.owner_key_hex, "owner")?,
        value.value,
        value.asset_id,
        hex32(&value.salt_hex, "salt")?,
    )
    .map_err(|e| anyhow::anyhow!("invalid output note: {e:?}"))
}
fn resolve(base: &Path, value: &str) -> PathBuf {
    let path = Path::new(value);
    if path.is_absolute() {
        path.to_owned()
    } else {
        base.join(path)
    }
}

const CREATE_PROGRAM_ADDRESS_CU: u64 = 1_500;

fn pda_attempts_from_bump(bump: u8) -> u16 {
    // The canonical descending search includes bump zero. A successful zero
    // is the complete 256-attempt path, not an invalid state.
    256u16 - u16::from(bump)
}

fn expected_terminal_pda_invocations(withdrawal: bool, rollover: bool) -> u64 {
    match (withdrawal, rollover) {
        (false, false) => 18,
        (false, true) => 19,
        (true, false) => 20,
        (true, true) => 21,
    }
}

fn expected_terminal_single_attempts(withdrawal: bool, rollover: bool) -> u64 {
    // Pool: marker twice, plus vault authority/token for withdrawals.
    // Verifier certificate: nine required identities, plus next page for
    // rollover and vault authority/token for withdrawal.
    match (withdrawal, rollover) {
        (false, false) => 11,
        (false, true) => 12,
        (true, false) => 15,
        (true, true) => 16,
    }
}

/// Inventory the exact data-dependent PDA search component of the terminal
/// Pool/verifier call graph before signing. Repeated runtime authentication is
/// represented by `runtimeInvocations`; deriving a unique address once here
/// does not pretend that the on-chain programs derive it only once.
fn terminal_pda_search_audit(
    pool_program: Pubkey,
    asset_mint: Pubkey,
    master_address: Pubkey,
    lane: &PoolV1PairForestLaneStateV1,
    profile: PairForestSpendProfileSelectionV2,
    request: &PoolV1PairForestTerminalRequestV1,
    terminal_accounts: &[Pubkey],
    pda_closure: bool,
) -> Result<serde_json::Value> {
    ensure!(
        profile.registry_family == PairForestVerifierRegistryFamilyV2::ImmutableDeploymentV2,
        "exact PDA CU inventory requires the authenticated Registry V2 family"
    );
    let registry_program = Pubkey::new_from_array(profile.registry_program);
    let verifier_program = Pubkey::new_from_array(profile.verifier_program);
    let checkpoint_sequence = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => public.anchor_sequence,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => public.anchor_sequence,
    };
    let withdrawal = matches!(
        request.public,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(_)
    );
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(lane.tree.next_leaf_index + 1);
    let rollover = current_location.page_number != next_location.page_number;

    let (derived_master, master_bump) =
        aspis_pool::pool_v1_pair_forest_master_address(&pool_program, &asset_mint);
    ensure!(
        derived_master == master_address && terminal_accounts.first() == Some(&master_address),
        "terminal master account mismatch"
    );

    let (_, lane_bump) =
        aspis_pool::pool_v1_pair_forest_lane_address(&pool_program, &master_address, lane.lane_id)
            .map_err(|error| anyhow::anyhow!("derive lane PDA: {error:?}"))?;
    let lane_address =
        aspis_pool::pool_v1_pair_forest_lane_address(&pool_program, &master_address, lane.lane_id)
            .map_err(|error| anyhow::anyhow!("derive lane PDA: {error:?}"))?
            .0;
    let (checkpoint_address, checkpoint_bump) = aspis_pool::pool_v1_pair_forest_checkpoint_address(
        &pool_program,
        &master_address,
        checkpoint_sequence,
    );
    let (current_page, current_page_bump) = aspis_pool::pool_v1_root_page_address(
        &pool_program,
        &lane_address,
        current_location.page_number,
    );
    let next_page = rollover.then(|| {
        aspis_pool::pool_v1_root_page_address(
            &pool_program,
            &lane_address,
            next_location.page_number,
        )
    });
    let canonical_nullifier = encode_digest_canonical(request.public.nullifier());
    let (marker, marker_bump) = aspis_pool::pool_v1_nullifier_marker_address(
        &pool_program,
        &master_address,
        &canonical_nullifier,
    )
    .map_err(|error| anyhow::anyhow!("derive nullifier PDA: {error:?}"))?;
    let (registry, registry_bump) =
        aspis_registry::pool_v1_verifier_registry_v2_address(&registry_program, &master_address);
    let (entry, entry_bump) = aspis_registry::pool_v1_verifier_entry_v2_address(
        &registry_program,
        &master_address,
        &request.verifier_profile,
        &request.verifier_release,
    );
    let loader = bpf_loader_upgradeable::id();
    let (registry_programdata, registry_programdata_bump) =
        Pubkey::find_program_address(&[registry_program.as_ref()], &loader);
    let (verifier_programdata, verifier_programdata_bump) =
        Pubkey::find_program_address(&[verifier_program.as_ref()], &loader);

    ensure!(
        terminal_accounts.contains(&lane_address),
        "terminal lane account mismatch"
    );
    ensure!(
        terminal_accounts.contains(&checkpoint_address),
        "terminal checkpoint account mismatch"
    );
    ensure!(
        terminal_accounts.contains(&current_page),
        "terminal current history page mismatch"
    );
    if let Some((address, _)) = next_page {
        ensure!(
            terminal_accounts.contains(&address),
            "terminal rollover history page mismatch"
        );
    }
    ensure!(
        terminal_accounts.contains(&marker),
        "terminal marker account mismatch"
    );
    ensure!(
        terminal_accounts.contains(&registry),
        "terminal Registry V2 mismatch"
    );
    ensure!(
        terminal_accounts.contains(&entry),
        "terminal Registry V2 entry mismatch"
    );
    ensure!(
        terminal_accounts.contains(&verifier_program),
        "terminal verifier program mismatch"
    );

    let mut records = Vec::new();
    let mut total_runtime_invocations = 0u64;
    let mut total_weighted_attempts = 0u64;
    let mut push =
        |label: &str, address: Pubkey, bump: u8, runtime_invocations: u64| -> Result<()> {
            let attempts = u64::from(pda_attempts_from_bump(bump));
            let weighted_attempts = attempts * runtime_invocations;
            total_runtime_invocations += runtime_invocations;
            total_weighted_attempts += weighted_attempts;
            records.push(json!({
                "label": label,
                "address": address.to_string(),
                "bump": bump,
                "attemptsPerInvocation": attempts,
                "runtimeInvocations": runtime_invocations,
                "weightedAttempts": weighted_attempts,
                "pdaSearchSyscallCu": weighted_attempts * CREATE_PROGRAM_ADDRESS_CU,
            }));
            Ok(())
        };

    push("Pool master", master_address, master_bump, 2)?;
    push("selected lane", lane_address, lane_bump, 3)?;
    push(
        "retained checkpoint",
        checkpoint_address,
        checkpoint_bump,
        2,
    )?;
    push(
        "current lane history page",
        current_page,
        current_page_bump,
        1,
    )?;
    if let Some((address, bump)) = next_page {
        push("rollover lane history page", address, bump, 1)?;
    }
    push("nullifier marker", marker, marker_bump, 2)?;
    push("Registry V2", registry, registry_bump, 2)?;
    push("Registry V2 entry", entry, entry_bump, 2)?;
    push(
        "Registry programdata",
        registry_programdata,
        registry_programdata_bump,
        2,
    )?;
    push(
        "verifier programdata",
        verifier_programdata,
        verifier_programdata_bump,
        2,
    )?;
    if withdrawal {
        let (vault, vault_bump) =
            aspis_pool::pool_v1_vault_token_account_address(&pool_program, &master_address);
        let (authority, authority_bump) =
            aspis_pool::pool_v1_vault_authority_address(&pool_program, &master_address);
        ensure!(
            terminal_accounts.contains(&vault),
            "terminal vault mismatch"
        );
        ensure!(
            terminal_accounts.contains(&authority),
            "terminal vault authority mismatch"
        );
        push("vault token account", vault, vault_bump, 1)?;
        push("vault authority", authority, authority_bump, 1)?;
    }

    let expected_runtime_invocations = expected_terminal_pda_invocations(withdrawal, rollover);
    ensure!(
        total_runtime_invocations == expected_runtime_invocations,
        "PDA runtime inventory drift"
    );
    let fixed_attempts = expected_terminal_single_attempts(withdrawal, rollover);
    Ok(json!({
        "schema":"aspis.v7.terminal-pda-search-audit.v2",
        "registryFamily":"immutable-v2",
        "rollover":rollover,
        "withdrawal":withdrawal,
        "terminalMode":if pda_closure {"authenticated-fixed-bump-certificate"} else {"legacy-runtime-search"},
        "createProgramAddressCuPerAttempt":CREATE_PROGRAM_ADDRESS_CU,
        "records":records,
        "identitySpecificLegacySearchReference":{
            "runtimeInvocations":total_runtime_invocations,
            "weightedAttempts":total_weighted_attempts,
            "pdaSearchSyscallCu":total_weighted_attempts * CREATE_PROGRAM_ADDRESS_CU,
        },
        "terminalVariableFindProgramAddressInvocations":if pda_closure {0} else {total_runtime_invocations},
        "terminalSingleAttemptValidations":if pda_closure {fixed_attempts} else {0},
        "terminalPdaSyscallCu":if pda_closure {
            fixed_attempts * CREATE_PROGRAM_ADDRESS_CU
        } else {
            total_weighted_attempts * CREATE_PROGRAM_ADDRESS_CU
        },
        "terminalPdaSyscallTheoreticalMaximumCu":if pda_closure {
            fixed_attempts * CREATE_PROGRAM_ADDRESS_CU
        } else {
            total_runtime_invocations * 256 * CREATE_PROGRAM_ADDRESS_CU
        },
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pda_attempts_and_terminal_call_shapes_are_exact() {
        assert_eq!(pda_attempts_from_bump(255), 1);
        assert_eq!(pda_attempts_from_bump(1), 255);
        assert_eq!(pda_attempts_from_bump(0), 256);
        assert_eq!(expected_terminal_pda_invocations(false, false), 18);
        assert_eq!(expected_terminal_pda_invocations(false, true), 19);
        assert_eq!(expected_terminal_pda_invocations(true, false), 20);
        assert_eq!(expected_terminal_pda_invocations(true, true), 21);
        assert_eq!(expected_terminal_single_attempts(false, false), 11);
        assert_eq!(expected_terminal_single_attempts(false, true), 12);
        assert_eq!(expected_terminal_single_attempts(true, false), 15);
        assert_eq!(expected_terminal_single_attempts(true, true), 16);
    }
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-live-transfer-terminal <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    let malformed_carrier_test = match input.carrier_test_mode.as_deref() {
        None => false,
        Some("malformed-magic") => {
            ensure!(
                input.schema == "aspis.v7.live-terminal-malformed-carrier-test-input.v1",
                "malformed carrier requires the explicit test schema"
            );
            true
        }
        Some(_) => anyhow::bail!("unsupported carrier test mode"),
    };
    let withdrawal_cpi_compute_exhaustion_test = match input.withdrawal_cpi_test_mode.as_deref() {
        None => false,
        Some("compute-exhaustion") => {
            ensure!(
                input.schema == "aspis.v7.live-terminal-withdrawal-cpi-failure-test-input.v1",
                "withdrawal CPI failure requires the explicit test schema"
            );
            true
        }
        Some(_) => anyhow::bail!("unsupported withdrawal CPI test mode"),
    };
    ensure!(
        (input.schema == "aspis.v7.live-transfer-terminal-input.v1"
            || input.schema == "aspis.v7.live-terminal-input.v1"
            || input.schema == "aspis.v7.live-terminal-pda-closure-input.v1"
            || input.schema == "aspis.v7.live-terminal-malformed-carrier-test-input.v1"
            || input.schema == "aspis.v7.live-terminal-withdrawal-cpi-failure-test-input.v1")
            && input.min_context_slot > 0,
        "wrong input"
    );
    ensure!(
        malformed_carrier_test
            == (input.schema == "aspis.v7.live-terminal-malformed-carrier-test-input.v1"),
        "test schema requires an exact carrier mutation"
    );
    ensure!(
        withdrawal_cpi_compute_exhaustion_test
            == (input.schema == "aspis.v7.live-terminal-withdrawal-cpi-failure-test-input.v1"),
        "withdrawal CPI test schema requires exact compute-exhaustion mode"
    );
    ensure!(
        !(malformed_carrier_test && withdrawal_cpi_compute_exhaustion_test),
        "terminal negative-test modes are mutually exclusive"
    );
    let pda_closure = input.schema == "aspis.v7.live-terminal-pda-closure-input.v1";
    ensure!(
        pda_closure == input.terminal_pda_certificate_keypair.is_some()
            && pda_closure == input.terminal_pda_certificate_rent_lamports.is_some(),
        "PDA closure schema requires exactly one certificate keypair and rent value"
    );
    ensure!(
        !pda_closure || cfg!(feature = "v7-terminal-pda-certificate-audit"),
        "PDA closure input requires the default-off v7-terminal-pda-certificate-audit feature"
    );
    let compute_unit_limit = if withdrawal_cpi_compute_exhaustion_test {
        let limit = input
            .compute_unit_limit
            .context("withdrawal CPI failure mode requires calibrated compute limit")?;
        ensure!(
            (1_150_000..1_300_000).contains(&limit),
            "calibrated withdrawal CPI failure limit is outside the fail-closed range"
        );
        limit
    } else {
        ensure!(
            input.compute_unit_limit.is_none(),
            "custom compute limit requires the explicit withdrawal CPI failure schema"
        );
        1_300_000
    };
    let bundle_path = resolve(input_path.parent().unwrap_or(Path::new(".")), &input.bundle);
    let base = bundle_path.parent().unwrap_or(Path::new("."));
    let bundle: Bundle = serde_json::from_slice(&fs::read(&bundle_path)?)?;
    ensure!(bundle.lanes.len() == 8, "wrong lane count");
    let program = Pubkey::from_str(&bundle.program_id)?;
    let master_account = account(&bundle.master)?;
    let master = authenticate_forest_master_account_v2(
        program.to_bytes(),
        master_account.address,
        &master_account.data,
    )
    .map_err(|e| anyhow::anyhow!("authenticate master: {e:?}"))?;
    let registry = account(&bundle.registry)?;
    let entry = account(&bundle.registry_entry)?;
    let point = aspis_pool_wallet_v1::scan_state::FinalizedChainPointV1::new(
        bundle.finalized_point.slot,
        hex32(&bundle.finalized_point.block_hash_hex, "blockhash")?,
    )
    .map_err(|e| anyhow::anyhow!("point: {e:?}"))?;
    let provider = hex32(&bundle.provider_set_digest_hex, "provider")?;
    let profile = select_pair_forest_spend_profile_v2(
        Pubkey::new_from_array(registry.owner),
        &master.value,
        PairForestSpendProfileRequestV2 {
            profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        },
        &FinalizedPairForestProfileAccountsV2 {
            point,
            context_slot: point.slot(),
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest: provider,
            registry,
            entry,
        },
    )
    .map_err(|e| anyhow::anyhow!("select profile: {e:?}"))?;
    let asq8 = fs::read(resolve(
        input_path.parent().unwrap_or(Path::new(".")),
        &input.asq8,
    ))?;
    let request = decode_pool_v1_pair_forest_terminal_request_v1(&asq8)
        .map_err(|e| anyhow::anyhow!("decode ASQ8: {e:?}"))?;
    let lane_id = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|e| anyhow::anyhow!("output lane: {e:?}"))?;
    let lane_account = account(&bundle.lanes[usize::from(lane_id)])?;
    let lane = authenticate_forest_lane_account_v2(
        program.to_bytes(),
        master.address,
        aspis_pool_wallet_v1::lane_forest_v2::LaneIdV2::new(lane_id)
            .map_err(|e| anyhow::anyhow!("lane: {e:?}"))?,
        lane_account.address,
        &lane_account.data,
    )
    .map_err(|e| anyhow::anyhow!("authenticate lane: {e:?}"))?;
    let payer =
        read_keypair_file(&input.payer_keypair).map_err(|e| anyhow::anyhow!("payer: {e}"))?;
    let proof = Pubkey::from_str(&bundle.proof_account)?;
    let (terminal, pda_closure_initialization) = if pda_closure {
        let certificate_path = resolve(
            input_path.parent().unwrap_or(Path::new(".")),
            input
                .terminal_pda_certificate_keypair
                .as_deref()
                .context("missing certificate keypair")?,
        );
        let certificate_keypair = read_keypair_file(&certificate_path)
            .map_err(|e| anyhow::anyhow!("certificate keypair: {e}"))?;
        ensure!(
            certificate_keypair.pubkey() != payer.pubkey() && certificate_keypair.pubkey() != proof,
            "certificate key aliases payer or proof"
        );
        let certificate = build_pair_forest_terminal_pda_certificate_v1_4k_v2(
            program,
            &master.value,
            &lane.value,
            profile,
            proof,
            &request,
        )
        .map_err(|e| anyhow::anyhow!("build PDA certificate: {e:?}"))?;
        let initialize = build_initialize_terminal_pda_certificate_instruction_v1_4k_v2(
            certificate_keypair.pubkey(),
            &certificate,
        )
        .map_err(|e| anyhow::anyhow!("build PDA certificate initialization: {e:?}"))?;
        let rent = input
            .terminal_pda_certificate_rent_lamports
            .context("missing certificate rent")?;
        ensure!(rent > 0, "certificate rent must be positive");
        let create = system_instruction::create_account(
            &payer.pubkey(),
            &certificate_keypair.pubkey(),
            rent,
            POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES as u64,
            &Pubkey::new_from_array(certificate.verifier_program),
        );
        let blockhash = Hash::from_str(&input.recent_blockhash).context("invalid blockhash")?;
        let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &[create, initialize],
            Some(&payer.pubkey()),
            &blockhash,
        ));
        let transaction = VersionedTransaction::try_new(message, &[&payer, &certificate_keypair])
            .map_err(|e| anyhow::anyhow!("sign certificate initialization: {e}"))?;
        let wire = bincode::serialize(&transaction)?;
        ensure!(
            wire.len() < 1_232,
            "certificate initialization exceeds legacy envelope"
        );
        let wire_base64 = BASE64.encode(&wire);
        let initialization = json!({
            "schema":"aspis.v7.terminal-pda-certificate-initialization-signed.v1",
            "certificateAccount":certificate_keypair.pubkey().to_string(),
            "proofAccount":proof.to_string(),
            "serializedTransactionBytes":wire.len(),
            "signedWireSha256":format!("{:x}",Sha256::digest(&wire)),
            "signature":transaction.signatures[0].to_string(),
            "simulationRequest":{"jsonrpc":"2.0","id":input.request_id+200_000,
                "method":"simulateTransaction","params":[wire_base64,{"encoding":"base64",
                "commitment":"finalized","sigVerify":true,"replaceRecentBlockhash":false,
                "minContextSlot":input.min_context_slot}]},
            "sendRequest":{"jsonrpc":"2.0","id":input.request_id+300_000,
                "method":"sendTransaction","params":[wire_base64,{"encoding":"base64",
                "skipPreflight":true,"preflightCommitment":"finalized","maxRetries":0,
                "minContextSlot":input.min_context_slot}]}
        });
        let terminal = build_pair_forest_terminal_instruction_with_pda_certificate_v1_4k_v3(
            program,
            &master.value,
            &lane.value,
            profile,
            payer.pubkey(),
            proof,
            certificate_keypair.pubkey(),
            &certificate,
            &request,
        )
        .map_err(|e| anyhow::anyhow!("terminal instruction with PDA certificate: {e:?}"))?;
        (terminal, Some(initialization))
    } else {
        let terminal = build_pair_forest_terminal_instruction_v1_4k_v2(
            program,
            &master.value,
            &lane.value,
            profile,
            payer.pubkey(),
            proof,
            &request,
        )
        .map_err(|e| anyhow::anyhow!("terminal instruction: {e:?}"))?;
        (terminal, None)
    };
    let terminal_account_pubkeys = terminal
        .accounts
        .iter()
        .map(|account| account.pubkey)
        .collect::<Vec<_>>();
    let terminal_accounts = terminal_account_pubkeys
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let master_pubkey = Pubkey::new_from_array(master.address);
    let pda_search_audit = terminal_pda_search_audit(
        program,
        Pubkey::new_from_array(master.value.identity.asset_mint),
        master_pubkey,
        &lane.value,
        profile,
        &request,
        &terminal_account_pubkeys,
        pda_closure,
    )?;
    let marker_account = aspis_pool::pool_v1_nullifier_marker_address(
        &program,
        &master_pubkey,
        &encode_digest_canonical(request.public.nullifier()),
    )
    .map_err(|error| anyhow::anyhow!("derive marker: {error:?}"))?
    .0
    .to_string();
    let secrets: Secret = serde_json::from_slice(&fs::read(resolve(base, &bundle.secrets_file))?)?;
    let change = note(secrets.change_note)?;
    let pair_index = lane.value.tree.next_leaf_index;
    let mut rng = OsEntropy;
    let mut seed = [0; 32];
    let (operation, recipient_cipher, change_commitment, change_note_index) = match &request.public
    {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            ensure!(secrets.operation == "transfer", "secret operation mismatch");
            ensure!(
                bundle.custody.is_none(),
                "transfer bundle unexpectedly has custody accounts"
            );
            let recipient = note(secrets.recipient_note.context("recipient missing")?)?;
            let recipient_context = NoteContextV1::new(
                master.address,
                master.value.identity.deployment_domain,
                pair_index * 2,
                encode_digest_canonical(&public.recipient_commitment),
            )
            .map_err(|e| anyhow::anyhow!("recipient context: {e:?}"))?;
            getrandom::getrandom(&mut seed)?;
            let (_, recipient_view) = derive_viewing_keypair_v1(&seed)
                .map_err(|e| anyhow::anyhow!("recipient view: {e:?}"))?;
            let ciphertext =
                encrypt_note_v1(&mut rng, &recipient_view, &recipient_context, &recipient)
                    .map_err(|e| anyhow::anyhow!("encrypt recipient: {e:?}"))?;
            (
                "transfer",
                Some(ciphertext),
                public.change_commitment,
                pair_index * 2 + 1,
            )
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            ensure!(
                secrets.operation == "withdrawal",
                "secret operation mismatch"
            );
            ensure!(
                secrets.recipient_note.is_none(),
                "withdrawal recipient unexpectedly present"
            );
            let custody = bundle
                .custody
                .as_ref()
                .context("withdrawal custody accounts missing")?;
            ensure!(
                custody.mint.address
                    == Pubkey::new_from_array(master.value.identity.asset_mint).to_string(),
                "withdrawal mint mismatch"
            );
            ensure!(
                custody.destination.address
                    == Pubkey::new_from_array(public.destination_token_account).to_string(),
                "withdrawal destination mismatch"
            );
            ensure!(
                terminal
                    .accounts
                    .iter()
                    .any(|meta| meta.pubkey.to_string() == custody.vault.address),
                "withdrawal vault missing from terminal accounts"
            );
            ensure!(
                terminal
                    .accounts
                    .iter()
                    .any(|meta| meta.pubkey.to_string() == custody.destination.address),
                "withdrawal destination missing from terminal accounts"
            );
            ("withdrawal", None, public.change_commitment, pair_index * 2)
        }
    };
    ensure!(
        !withdrawal_cpi_compute_exhaustion_test || operation == "withdrawal",
        "withdrawal CPI failure mode requires a withdrawal statement"
    );
    getrandom::getrandom(&mut seed)?;
    let (_, change_view) =
        derive_viewing_keypair_v1(&seed).map_err(|e| anyhow::anyhow!("change view: {e:?}"))?;
    seed.fill(0);
    let change_context = NoteContextV1::new(
        master.address,
        master.value.identity.deployment_domain,
        change_note_index,
        encode_digest_canonical(&change_commitment),
    )
    .map_err(|e| anyhow::anyhow!("change context: {e:?}"))?;
    let change_cipher = encrypt_note_v1(&mut rng, &change_view, &change_context, &change)
        .map_err(|e| anyhow::anyhow!("encrypt change: {e:?}"))?;
    let carrier = TxV1CiphertextCarrierV2::from_terminal_v2(
        &request,
        proof.to_bytes(),
        0,
        1,
        recipient_cipher,
        change_cipher,
    )
    .map_err(|e| anyhow::anyhow!("carrier: {e:?}"))?;
    let recent = bs58::decode(&input.recent_blockhash).into_vec()?;
    let recent: [u8; 32] = recent
        .try_into()
        .map_err(|_| anyhow::anyhow!("blockhash length"))?;
    let expected = build_exact_pair_forest_v1_carrier_transaction_v2(
        &carrier,
        payer.pubkey(),
        &terminal,
        payer.pubkey(),
        recent,
        PairForestV1TransactionConfigV2 {
            priority_fee_lamports: 0,
            compute_unit_limit,
            loaded_accounts_data_size_limit: 8 * 1024 * 1024,
            heap_size: 256 * 1024,
        },
        &[],
    )
    .map_err(|e| anyhow::anyhow!("build TxV1: {e:?}"))?;
    ensure!(
        expected.required_signatures_v2() == 1,
        "unexpected signatures"
    );
    let mut transaction: V1VersionedTransaction =
        wincode::deserialize(expected.placeholder_signature_wire_v2())?;
    if malformed_carrier_test {
        let V1VersionedMessage::V1(message) = &mut transaction.message else {
            anyhow::bail!("expected TxV1 message")
        };
        ensure!(
            message.instructions.len() == 2
                && message.instructions[0].data.len()
                    == aspis_pool_wallet_v1::tx_v1_ciphertext_carrier_v2::POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2
                && message.instructions[0].data.starts_with(b"ASC8"),
            "unexpected canonical carrier shape"
        );
        message.instructions[0].data[0] ^= 1;
        ensure!(
            message.instructions[0].data[0..4] != *b"ASC8",
            "carrier mutation did not make the magic malformed"
        );
    }
    let message = transaction.message.serialize();
    let signed = payer.sign_message(&message);
    let bytes: [u8; 64] = signed.as_ref().try_into()?;
    transaction.signatures[0] = V1Signature::from(bytes);
    let wire = wincode::serialize(&transaction)?;
    if malformed_carrier_test {
        ensure!(
            validate_signed_pair_forest_v1_carrier_transaction_v2(&expected, &wire).is_err(),
            "malformed carrier unexpectedly passed canonical validation"
        );
    } else {
        validate_signed_pair_forest_v1_carrier_transaction_v2(&expected, &wire)
            .map_err(|e| anyhow::anyhow!("validate signed TxV1: {e:?}"))?;
    }
    ensure!(
        wire.len() < 4096 && wire.len() <= 3500,
        "TxV1 size policy failed"
    );
    let wire64 = BASE64.encode(&wire);
    let signature = transaction.signatures[0].to_string();
    println!(
        "{}",
        json!({"schema":"aspis.v7.live-terminal-signed.v1","operation":operation,"signature":signature,
        "selectedLane":lane_id,"serializedTransactionBytes":wire.len(),"signedWireSha256":format!("{:x}",Sha256::digest(&wire)),
        "instructionCount":2,"terminalInstructionCount":1,
        "ciphertextCarrierRealHpke":!malformed_carrier_test,
        "ciphertextCarrierCanonical":!malformed_carrier_test,
        "carrierTestMode":input.carrier_test_mode,
        "withdrawalCpiTestMode":input.withdrawal_cpi_test_mode,
        "computeUnitLimit":compute_unit_limit,
        "terminalPdaClosureEnabled":pda_closure,
        "pdaCertificateInitialization":pda_closure_initialization,
        "pdaSearchAudit":pda_search_audit,
        "terminalAccounts":terminal_accounts,"markerAccount":marker_account,
        "simulationRequest":{"jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction","params":[wire64,{"encoding":"base64","commitment":"finalized","sigVerify":true,"replaceRecentBlockhash":false,"minContextSlot":input.min_context_slot,"innerInstructions":true}]},
        "sendRequest":{"jsonrpc":"2.0","id":input.request_id+100000,"method":"sendTransaction","params":[wire64,{"encoding":"base64","skipPreflight":true,"preflightCommitment":"finalized","maxRetries":0,"minContextSlot":input.min_context_slot}]}})
    );
    Ok(())
}
