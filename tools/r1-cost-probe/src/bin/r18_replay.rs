//! One before/after current-route SBF CU comparison. Preloaded state is a
//! measurement fixture, not proof of registry provisioning or Pool settlement.
use anyhow::{anyhow, ensure, Context, Result};
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_registry::{pool_v1_verifier_entry_v2_address, pool_v1_verifier_registry_v2_address};
use aspis_statement::pool_v1::*;
use litesvm::LiteSVM;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v0, VersionedMessage};
use solana_program::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    program_utils::limited_deserialize,
    pubkey::Pubkey,
    system_instruction,
};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;
use std::{
    env,
    fmt::Debug,
    fs::{self, OpenOptions},
    io::Write,
    os::unix::fs::OpenOptionsExt,
    path::Path,
    str::FromStr,
    time::Instant,
};

#[path = "r18_replay/readonly_runtime.rs"]
mod readonly_runtime;

const PROGRAM: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const POOL: [u8; 32] = [0x41; 32];
const REGISTRY: [u8; 32] = [0x44; 32];
// Exact private-leaf-salts release bindings in r1_pool_adapter.rs.
const PROFILE: [u8; 32] = [
    0x57, 0x94, 0x73, 0x13, 0xd2, 0x32, 0x64, 0x1a, 0xd8, 0x15, 0x7d, 0x66, 0xbf, 0xaf, 0xfa, 0xb1,
    0x1e, 0x4c, 0x3a, 0x99, 0x33, 0x1d, 0x18, 0xf4, 0x4b, 0xfa, 0xca, 0xb6, 0x89, 0x97, 0x37, 0xd3,
];
const RELEASE: [u8; 32] = [
    0xe2, 0x94, 0xaf, 0xbc, 0x14, 0xef, 0x6a, 0xfe, 0x76, 0xb8, 0x47, 0xde, 0xf4, 0x44, 0x52, 0xf8,
    0x4c, 0xc3, 0x72, 0x80, 0x64, 0x65, 0x76, 0x07, 0xb5, 0x44, 0xa5, 0x39, 0xca, 0x9b, 0x32, 0x3a,
];
const PROOF_SHA: &str = "8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62";
const PUBLIC_SHA: &str = "72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172";
const CHECKPOINT_BYTES: usize = 1768;
const LIMIT: u32 = 1_400_000;
const HEAP: u32 = 262_144;
const LOADED: u32 = 8_388_608;
const SLOT: u64 = 150;
fn sha(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn checked<T, E: Debug>(r: std::result::Result<T, E>) -> Result<T> {
    r.map_err(|e| anyhow!("{e:?}"))
}
fn addr(k: Pubkey) -> Address {
    Address::new_from_array(k.to_bytes())
}
fn key(a: Address) -> Pubkey {
    Pubkey::new_from_array(a.to_bytes())
}
fn write_new(p: &Path, b: &[u8], mode: u32) -> Result<()> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(mode)
        .open(p)?
        .write_all(b)?;
    Ok(())
}
fn write_json(p: &Path, v: &Value) -> Result<()> {
    write_new(
        p,
        &(serde_json::to_string_pretty(v)? + "\n").into_bytes(),
        0o644,
    )
}
fn fresh_key(p: &Path) -> Result<Keypair> {
    let k = Keypair::new();
    write_new(p, k.to_base58_string().as_bytes(), 0o600)?;
    Ok(k)
}
#[derive(Clone)]
struct Image {
    name: &'static str,
    key: Pubkey,
    owner: Pubkey,
    data: Vec<u8>,
}
fn image(name: &'static str, key: Pubkey, owner: Pubkey, data: Vec<u8>) -> Image {
    Image {
        name,
        key,
        owner,
        data,
    }
}
fn images(program: Pubkey, proof: &[u8], public: &[u8]) -> Result<(Vec<Image>, Vec<u8>, Vec<u8>)> {
    ensure!(
        proof.len() == 124343 && sha(proof) == PROOF_SHA,
        "wrong frozen proof"
    );
    ensure!(
        public.len() == 1880 && sha(public) == PUBLIC_SHA,
        "wrong frozen ASF8"
    );
    let statement = checked(decode_pool_v1_pair_forest_terminal_statement_v1(public))?;
    ensure!(
        checked(encode_pool_v1_pair_forest_terminal_statement_v1(&statement))?.as_slice() == public
    );
    let c = *statement.common();
    let s = c.lane_transition.live_snapshot;
    ensure!(c.checkpoint_sequence == 42 && c.output_lane == 3 && s.next_pair_index == 1023);
    ensure!(s.sequence == s.next_pair_index);
    let payment = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public)
        }
    };
    let asset_id = match payment {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p) => p.asset_id,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(p) => p.asset_id,
    };
    let pool = Pubkey::new_from_array(POOL);
    let registry_program = Pubkey::new_from_array(REGISTRY);
    let mint = Pubkey::new_from_array([0x42; 32]);
    let (master_key, master_bump) = pool_v1_pair_forest_master_address(&pool, &mint);
    let (lane_key, lane_bump) = checked(pool_v1_pair_forest_lane_address(
        &pool,
        &master_key,
        c.output_lane,
    ))?;
    let (pool_checkpoint, checkpoint_bump) =
        pool_v1_pair_forest_checkpoint_address(&pool, &master_key, c.checkpoint_sequence);
    ensure!(
        master_key.to_bytes() == c.master_account
            && lane_key.to_bytes() == c.selected_lane_account
            && pool_checkpoint.to_bytes() == c.checkpoint_account
    );
    let master = PoolV1PairForestMasterV1 {
        bump: master_bump,
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: Pubkey::from_str("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA")?
                .to_bytes(),
            asset_id,
            deployment_domain: s.deployment_domain,
        },
        verifier_policy: VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
            registry_program: REGISTRY,
            registry_authority: [0; 32],
            policy_binding: [7; 32],
        },
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 43,
        last_checkpoint_lane_sequences: [0; 8],
    };
    let checkpoint = PoolV1PairForestCheckpointV1 {
        bump: checkpoint_bump,
        master: master_key.to_bytes(),
        deployment_domain: s.deployment_domain,
        checkpoint_sequence: c.checkpoint_sequence,
        global_root: c.historical_global_anchor,
        lane_sequences: [0; 8],
    };
    let lane = PoolV1PairForestLaneStateV1 {
        bump: lane_bump,
        master: master_key.to_bytes(),
        lane_id: c.output_lane,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: s.next_pair_index,
            root: s.current_root,
            frontier: s.frontier,
        },
    };
    let loader = bpf_loader_upgradeable::id();
    let (registry_key, registry_bump) =
        pool_v1_verifier_registry_v2_address(&registry_program, &master_key);
    let (entry_key, entry_bump) =
        pool_v1_verifier_entry_v2_address(&registry_program, &master_key, &PROFILE, &RELEASE);
    let (registry_pd, registry_pd_bump) =
        Pubkey::find_program_address(&[registry_program.as_ref()], &loader);
    let (verifier_pd, verifier_pd_bump) =
        Pubkey::find_program_address(&[program.as_ref()], &loader);
    // Fixed nonzero measurement descriptors, intentionally NOT a certificate of
    // either loaded ELF. Their identical bytes must survive both executions.
    let registry = VerifierRegistryV2 {
        bump: registry_bump,
        programdata_bump: registry_pd_bump,
        flags: POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
        pool: master_key.to_bytes(),
        authority: [0; 32],
        policy_binding: [7; 32],
        generation: 1,
        minimum_activation_delay_slots: 1,
        registry_program: REGISTRY,
        loader_program: loader.to_bytes(),
        programdata_address: registry_pd.to_bytes(),
        executable_hash: [0xa5; 32],
    };
    let entry = VerifierRegistryEntryV2 {
        bump: entry_bump,
        programdata_bump: verifier_pd_bump,
        status: VerifierEntryStatusV1::Active,
        statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        pool: master_key.to_bytes(),
        verifier_program: program.to_bytes(),
        profile_binding: PROFILE,
        release_binding: RELEASE,
        loader_program: loader.to_bytes(),
        programdata_address: verifier_pd.to_bytes(),
        executable_hash: [0x5a; 32],
        expected_upgrade_authority: [0; 32],
        activation_slot: 0,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: [7; 32],
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: PROFILE,
        verifier_release: RELEASE,
        pool_program: POOL,
        public: payment,
    };
    // Reconstruct exactly what the adapter reads from the image carriers.
    let reconstructed = checked(reconstruct_pool_v1_pair_forest_terminal_statement_v1(
        &request,
        PoolV1PairForestTerminalCommonV1 {
            master_account: master.identity.pool,
            checkpoint_account: pool_checkpoint.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane.lane_id,
            checkpoint_sequence: checkpoint.checkpoint_sequence,
            historical_global_anchor: checkpoint.global_root,
            lane_transition: PoolV1PairLatePublicStatementV1 {
                live_snapshot: PoolV1PairLiveSnapshotV1 {
                    pool: master.identity.pool,
                    deployment_domain: master.identity.deployment_domain,
                    sequence: lane.tree.next_leaf_index,
                    next_pair_index: lane.tree.next_leaf_index,
                    current_root: lane.tree.root,
                    frontier: lane.tree.frontier,
                },
                candidate_afterstate: c.lane_transition.candidate_afterstate,
            },
        },
    ))?;
    ensure!(
        checked(encode_pool_v1_pair_forest_terminal_statement_v1(
            &reconstructed
        ))?
        .as_slice()
            == public,
        "image-derived ASF8 mismatch"
    );
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: c.master_account,
        selected_lane_account: c.selected_lane_account,
        output_lane: c.output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: c.lane_transition.candidate_afterstate,
    };
    checked(
        validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement, &result),
    )?;
    let mut proof_image = checked(encode_pool_v1_pair_verified_afterstate_v1(
        &c.lane_transition.candidate_afterstate,
    ))?
    .to_vec();
    ensure!(proof_image.len() == 688);
    proof_image.extend_from_slice(proof);
    let foreign = Pubkey::new_from_array([0x55; 32]);
    Ok((
        vec![
            image(
                "proof",
                Pubkey::new_from_array([0x45; 32]),
                foreign,
                proof_image,
            ),
            image(
                "public",
                Pubkey::new_from_array([0x46; 32]),
                foreign,
                public.to_vec(),
            ),
            image(
                "master",
                master_key,
                pool,
                checked(encode_pool_v1_pair_forest_master_v1(&master))?.to_vec(),
            ),
            image(
                "pool-checkpoint",
                pool_checkpoint,
                pool,
                checked(encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint))?.to_vec(),
            ),
            image(
                "lane",
                lane_key,
                pool,
                checked(encode_pool_v1_pair_forest_lane_state_v1(
                    &lane,
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                ))?
                .to_vec(),
            ),
            image(
                "registry",
                registry_key,
                registry_program,
                checked(encode_verifier_registry_v2(&registry))?.to_vec(),
            ),
            image(
                "entry",
                entry_key,
                registry_program,
                checked(encode_verifier_registry_entry_v2(&entry))?.to_vec(),
            ),
        ],
        checked(encode_pool_v1_pair_forest_terminal_request_v1(&request))?.to_vec(),
        checked(encode_pool_v1_pair_forest_terminal_result_v1(&result))?.to_vec(),
    ))
}

fn legacy_instruction(ix: solana_program::instruction::Instruction) -> Instruction {
    Instruction {
        program_id: addr(ix.program_id),
        data: ix.data,
        accounts: ix
            .accounts
            .into_iter()
            .map(|m| AccountMeta {
                pubkey: addr(m.pubkey),
                is_signer: m.is_signer,
                is_writable: m.is_writable,
            })
            .collect(),
    }
}
fn loaded_program(svm: &LiteSVM, program: Pubkey, elf: &[u8]) -> Result<Value> {
    let loader = bpf_loader_upgradeable::id();
    let (pd, pd_bump) = Pubkey::find_program_address(&[program.as_ref()], &loader);
    let executable = svm
        .get_account(&addr(program))
        .context("missing loaded Program")?;
    let data = svm
        .get_account(&addr(pd))
        .context("missing loaded ProgramData")?;
    ensure!(executable.owner == addr(loader) && executable.executable);
    ensure!(data.owner == addr(loader) && !data.executable);
    let p: UpgradeableLoaderState = checked(limited_deserialize(
        &executable.data,
        executable.data.len() as u64,
    ))?;
    ensure!(
        p == UpgradeableLoaderState::Program {
            programdata_address: pd
        }
    );
    let n = UpgradeableLoaderState::size_of_programdata_metadata();
    ensure!(data.data.len() == n + elf.len() && data.data[n..] == *elf);
    let d: UpgradeableLoaderState = checked(limited_deserialize(&data.data[..n], n as u64))?;
    ensure!(
        d == UpgradeableLoaderState::ProgramData {
            slot: SLOT,
            upgrade_authority_address: None
        }
    );
    Ok(
        json!({"program":program.to_string(),"loader":loader.to_string(),"programdata":pd.to_string(),
        "programdata_bump":pd_bump,"upgrade_authority":null,"slot":SLOT,"program_account_sha256":sha(&executable.data),
        "programdata_sha256":sha(&data.data),"elf_sha256":sha(elf),"registry_registration_proven":false}),
    )
}
fn account_json(key: Address, a: &Account) -> Value {
    json!({"key":key.to_string(),"owner":a.owner.to_string(),"lamports":a.lamports,"executable":a.executable,
        "rent_epoch":a.rent_epoch,"bytes":a.data.len(),"data_sha256":sha(&a.data)})
}
fn snapshot(svm: &LiteSVM, keys: &[Address]) -> Result<Vec<Account>> {
    keys.iter()
        .map(|k| {
            svm.get_account(k)
                .with_context(|| format!("missing account {k}"))
        })
        .collect()
}
struct Measurement {
    total: u64,
    verifier: Option<u64>,
    return_program: Address,
    return_data: Vec<u8>,
}
fn send(
    svm: &mut LiteSVM,
    payer: &Keypair,
    additional: Option<&Keypair>,
    ix: Instruction,
    out: &Path,
    name: &str,
) -> Result<Measurement> {
    let instruction_pin = json!({"program":ix.program_id.to_string(),"bytes":ix.data.len(),"data_sha256":sha(&ix.data),
        "accounts":ix.accounts.iter().map(|m|json!({"key":m.pubkey.to_string(),"signer":m.is_signer,"writable":m.is_writable})).collect::<Vec<_>>()});
    write_new(
        &out.join(format!("{name}.instruction.bin")),
        &ix.data,
        0o644,
    )?;
    let program = ix.program_id;
    let instructions = [
        ComputeBudgetInstruction::set_compute_unit_limit(LIMIT),
        ComputeBudgetInstruction::request_heap_frame(HEAP),
        ComputeBudgetInstruction::set_loaded_accounts_data_size_limit(LOADED),
        ix,
    ];
    let message = VersionedMessage::V0(v0::Message::try_compile(
        &payer.pubkey(),
        &instructions,
        &[],
        svm.latest_blockhash(),
    )?);
    let mut signers = vec![payer];
    if let Some(k) = additional {
        signers.push(k);
    }
    let tx = VersionedTransaction::try_new(message, &signers)?;
    let tx_bytes = wincode::serialize(&tx)?;
    ensure!(tx_bytes.len() <= 1232, "transaction exceeds packet size");
    write_new(
        &out.join(format!("{name}.transaction.bin")),
        &tx_bytes,
        0o644,
    )?;
    let start = Instant::now();
    let (error, m) = match svm.send_transaction(tx) {
        Ok(m) => (None, m),
        Err(f) => (Some(format!("{:?}", f.err)), f.meta),
    };
    let consumed = m.logs.iter().find_map(|l| {
        l.strip_prefix(&format!("Program {program} consumed "))?
            .split_whitespace()
            .next()?
            .parse::<u64>()
            .ok()
    });
    let markers: Vec<_> = m
        .logs
        .windows(2)
        .filter_map(|ls| {
            let phase = ls[0].strip_prefix("Program log: r1:")?;
            let left = ls[1]
                .strip_prefix("Program consumption: ")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()?;
            Some(json!({"phase":phase,"remaining_cu":left}))
        })
        .collect();
    write_json(
        &out.join(format!("{name}.json")),
        &json!({"instruction":instruction_pin,"serialized_bytes":tx_bytes.len(),
        "transaction_sha256":sha(&tx_bytes),"error":error,"compute_units":m.compute_units_consumed,"invoked_program_cu":consumed,
        "wall_seconds":start.elapsed().as_secs_f64(),"logs":m.logs,"phase_markers":markers,"return_program":m.return_data.program_id.to_string(),
        "return_data_bytes":m.return_data.data.len(),"return_data_sha256":sha(&m.return_data.data)}),
    )?;
    write_new(
        &out.join(format!("{name}.return.bin")),
        &m.return_data.data,
        0o644,
    )?;
    ensure!(
        error.is_none(),
        "{name} failed: {error:?}; retained receipt, no fallback"
    );
    Ok(Measurement {
        total: m.compute_units_consumed,
        verifier: consumed,
        return_program: m.return_data.program_id,
        return_data: m.return_data.data,
    })
}
struct Run {
    stage1: Measurement,
    stage2: Measurement,
    checkpoint: Vec<u8>,
    initial: Vec<Value>,
}
fn run(
    label: &str,
    elf: &[u8],
    program: Pubkey,
    inputs: &[Image],
    request: &[u8],
    expected: &[u8],
    payer: &Keypair,
    checkpoint_key: &Keypair,
    out: &Path,
) -> Result<Run> {
    let out = out.join(label);
    fs::create_dir(&out)?;
    let mut svm = LiteSVM::new();
    svm.warp_to_slot(SLOT);
    checked(svm.add_program(addr(program), elf))?;
    write_json(
        &out.join("loaded-program.json"),
        &loaded_program(&svm, program, elf)?,
    )?;
    checked(svm.airdrop(&payer.pubkey(), 1_000_000_000))?;
    for i in inputs {
        checked(svm.set_account(
            addr(i.key),
            Account {
                lamports: svm.minimum_balance_for_rent_exemption(i.data.len()).max(1),
                data: i.data.clone(),
                owner: addr(i.owner),
                executable: false,
                rent_epoch: 0,
            },
        ))?;
    }
    let create = legacy_instruction(system_instruction::create_account(
        &key(payer.pubkey()),
        &key(checkpoint_key.pubkey()),
        svm.minimum_balance_for_rent_exemption(CHECKPOINT_BYTES),
        CHECKPOINT_BYTES as u64,
        &program,
    ));
    send(
        &mut svm,
        payer,
        Some(checkpoint_key),
        create,
        &out,
        "setup-checkpoint",
    )?;
    let cp = svm
        .get_account(&checkpoint_key.pubkey())
        .context("checkpoint not created")?;
    ensure!(cp.owner == addr(program) && !cp.executable && cp.data == vec![0; CHECKPOINT_BYTES]);
    let mut keys: Vec<_> = inputs.iter().map(|i| addr(i.key)).collect();
    keys.push(checkpoint_key.pubkey());
    for (index, k) in keys.iter().enumerate() {
        ensure!(*k != payer.pubkey() && *k != addr(program));
        ensure!(!keys[..index].contains(k));
    }
    let initial_accounts = snapshot(&svm, &keys)?;
    let initial: Vec<_> = keys
        .iter()
        .zip(&initial_accounts)
        .map(|(k, a)| account_json(*k, a))
        .collect();
    write_json(&out.join("initial-accounts.json"), &json!(initial))?;
    let readonly_stage1_state = if label == "after"
        && env::var_os("ASPIS_R16_READONLY_RUNTIME").is_some()
    {
        ensure!(env::var("ASPIS_R16_READONLY_RUNTIME")? == "1");
        Some(svm.clone())
    } else {
        None
    };
    let stage1 = send(
        &mut svm,
        payer,
        None,
        Instruction {
            program_id: addr(program),
            data: vec![3, 10],
            accounts: vec![
                AccountMeta::new_readonly(keys[0], false),
                AccountMeta::new_readonly(keys[1], false),
                AccountMeta::new(checkpoint_key.pubkey(), false),
            ],
        },
        &out,
        "stage1",
    )?;
    let after1 = snapshot(&svm, &keys)?;
    ensure!(
        after1[..inputs.len()] == initial_accounts[..inputs.len()],
        "stage1 changed a non-checkpoint input"
    );
    let cp = &after1[inputs.len()];
    ensure!(
        cp.owner == addr(program)
            && !cp.executable
            && cp.data.len() == CHECKPOINT_BYTES
            && cp.data.iter().any(|b| *b != 0)
    );
    ensure!(
        cp.lamports == initial_accounts[inputs.len()].lamports
            && cp.rent_epoch == initial_accounts[inputs.len()].rent_epoch
    );
    if let Some(state) = readonly_stage1_state {
        readonly_runtime::run_stage1(
            &state, program, &keys, &[keys[0], keys[1], checkpoint_key.pubkey()],
            &after1, payer, &out,
        )?;
    }
    let checkpoint = cp.data.clone();
    write_new(&out.join("checkpoint.bin"), &checkpoint, 0o644)?;
    // Seven read-only accounts, with the verifier checkpoint distinct from ASC8.
    let stage2_keys = [
        keys[0],
        keys[2],
        keys[3],
        keys[4],
        keys[5],
        keys[6],
        checkpoint_key.pubkey(),
    ];
    // Optional candidate-only loader-metadata gate, using independent clones of
    // this exact successful stage1 state. Default CU replay is unchanged.
    let readonly_gate_state = if label == "after"
        && env::var_os("ASPIS_R16_READONLY_RUNTIME").is_some()
    {
        ensure!(env::var("ASPIS_R16_READONLY_RUNTIME")? == "1");
        Some(svm.clone())
    } else {
        None
    };
    let stage2 = send(
        &mut svm,
        payer,
        None,
        Instruction {
            program_id: addr(program),
            data: request.to_vec(),
            accounts: stage2_keys
                .into_iter()
                .map(|k| AccountMeta::new_readonly(k, false))
                .collect(),
        },
        &out,
        "stage2",
    )?;
    ensure!(
        snapshot(&svm, &keys)? == after1,
        "stage2 changed an input account"
    );
    ensure!(
        stage2.return_program == addr(program) && stage2.return_data == expected,
        "ASR8 output mismatch"
    );
    ensure!(
        stage1.verifier.is_some() && stage2.verifier.is_some(),
        "missing verifier CU log"
    );
    if let Some(state) = readonly_gate_state {
        readonly_runtime::run(
            &state, program, &keys, &stage2_keys, request, expected, payer, &out,
        )?;
    }
    Ok(Run {
        stage1,
        stage2,
        checkpoint,
        initial,
    })
}
fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "use the optimized binary");
    ensure!(
        cfg!(feature = "private-leaf-salts"),
        "require private-leaf-salts feature"
    );
    let args: Vec<_> = env::args().collect();
    ensure!(
        args.len() == 6,
        "usage: r18_replay BEFORE.so AFTER.so PROOF.bin PUBLIC.bin FRESH_OUTPUT"
    );
    let before = fs::read(&args[1])?;
    let after = fs::read(&args[2])?;
    let proof = fs::read(&args[3])?;
    let public = fs::read(&args[4])?;
    let before_revision =
        env::var("ASPIS_R18_BEFORE_REVISION").context("baseline source revision required")?;
    let after_revision =
        env::var("ASPIS_R18_AFTER_REVISION").context("candidate source revision required")?;
    ensure!(
        before_revision != after_revision,
        "before/after source revisions must differ"
    );
    let mut build_pins = vec![];
    for variable in [
        "ASPIS_R18_BEFORE_BUILD_RECEIPT",
        "ASPIS_R18_AFTER_BUILD_RECEIPT",
    ] {
        let path = env::var(variable).with_context(|| format!("{variable} required"))?;
        let bytes = fs::read(&path)?;
        let value: Value = serde_json::from_slice(&bytes)?;
        build_pins.push(json!({"path":path,"sha256":sha(&bytes),"receipt":value}));
    }
    let program = Pubkey::from_str(PROGRAM)?;
    let (inputs, request, expected) = images(program, &proof, &public)?;
    let out = Path::new(&args[5]);
    ensure!(!out.exists(), "refusing existing output directory");
    fs::create_dir_all(out)?;
    let payer = fresh_key(&out.join("payer.key"))?;
    let checkpoint_key = fresh_key(&out.join("checkpoint.key"))?;
    let mut features: Vec<_> = LiteSVM::mainnet_feature_set()
        .active()
        .iter()
        .map(|(k, s)| (k.to_string(), *s))
        .collect();
    features.sort();
    let feature_bytes = serde_json::to_vec(&features)?;
    for i in &inputs {
        write_new(&out.join(format!("{}.account.bin", i.name)), &i.data, 0o644)?;
    }
    write_new(&out.join("expected-asr8.bin"), &expected, 0o644)?;
    write_new(&out.join("request-asq8.bin"), &request, 0o644)?;
    write_new(&out.join("runtime-features.json"), &feature_bytes, 0o644)?;
    write_json(
        &out.join("input-manifest.json"),
        &json!({"scope":"current-route verifier CU; preloaded state; no registration or Pool settlement claim",
        "before_source_revision":before_revision,"after_source_revision":after_revision,"build_receipts":build_pins,
        "harness_source_revision":env::var("ASPIS_SOURCE_REVISION")?,"harness_source_sha256":sha(include_bytes!("r18_replay.rs")),
        "readonly_metadata_runtime":{"requested":env::var("ASPIS_R16_READONLY_RUNTIME").ok(),
            "source_sha256":sha(include_bytes!("r18_replay/readonly_runtime.rs")),"candidate_only":true,"signature_verification":false},
        "cargo_lock_sha256":sha(include_bytes!("../../Cargo.lock")),"harness_binary_sha256":sha(&fs::read(env::current_exe()?)?),
        "before_elf_sha256":sha(&before),"after_elf_sha256":sha(&after),"proof_sha256":sha(&proof),"public_sha256":sha(&public),
        "program":PROGRAM,"payer":payer.pubkey().to_string(),"checkpoint":checkpoint_key.pubkey().to_string(),
        "keys_retained":true,"registry_descriptors":"fixed synthetic V2 images, identical across runs; executable hash fields are not artifact certificates",
        "runtime":{"litesvm":"0.16.0","agave":"4.2.1","slot":SLOT,"limit_cu":LIMIT,"heap_bytes":HEAP,"loaded_account_limit":LOADED,"active_features_sha256":sha(&feature_bytes)},
        "setup_excluded_from_delta":true,"pairs_per_elf":1,"checkpoint_origin":"same fresh SVM's successful stage1"}),
    )?;
    let b = run(
        "before",
        &before,
        program,
        &inputs,
        &request,
        &expected,
        &payer,
        &checkpoint_key,
        out,
    )?;
    let a = run(
        "after",
        &after,
        program,
        &inputs,
        &request,
        &expected,
        &payer,
        &checkpoint_key,
        out,
    )?;
    ensure!(
        b.initial == a.initial,
        "before/after initial account images differ"
    );
    ensure!(
        b.checkpoint == a.checkpoint && b.stage2.return_data == a.stage2.return_data,
        "before/after output mismatch"
    );
    write_json(
        &out.join("comparison.json"),
        &json!({"both_admitted_pairs_accepted":true,"initial_images_equal":true,"checkpoint_equal":true,"asr8_equal":true,
        "before":{"stage1":b.stage1.total,"stage2":b.stage2.total,"sum":b.stage1.total+b.stage2.total,"verifier_stage1":b.stage1.verifier,"verifier_stage2":b.stage2.verifier},
        "after":{"stage1":a.stage1.total,"stage2":a.stage2.total,"sum":a.stage1.total+a.stage2.total,"verifier_stage1":a.stage1.verifier,"verifier_stage2":a.stage2.verifier},
        "delta":{"stage1":i128::from(a.stage1.total)-i128::from(b.stage1.total),"stage2":i128::from(a.stage2.total)-i128::from(b.stage2.total),
            "sum":i128::from(a.stage1.total+a.stage2.total)-i128::from(b.stage1.total+b.stage2.total)},"setup_cu_included":false}),
    )?;
    println!(
        "before: {} + {}; after: {} + {}; evidence: {}",
        b.stage1.total,
        b.stage2.total,
        a.stage1.total,
        a.stage2.total,
        out.display()
    );
    Ok(())
}
