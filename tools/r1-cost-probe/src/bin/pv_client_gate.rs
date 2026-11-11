//! Actual runner → pinned ELF gate; preloaded runtime state is a fixture.
//! One before/after current-route SBF CU comparison. Preloaded state is a
//! measurement fixture, not proof of registry provisioning or Pool settlement.
use anyhow::{anyhow, ensure, Context, Result};
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_pool::{pool_v1_vault_authority_address, pool_v1_vault_token_account_address};
use aspis_registry::{pool_v1_verifier_entry_v2_address, pool_v1_verifier_registry_v2_address};
use aspis_statement::pool_v1::root_history::initialize_root_history_page_bytes_v1;
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
fn images(
    pool: Pubkey,
    registry_program: Pubkey,
    program: Pubkey,
    proof: &[u8],
    public: &[u8],
    proof_key: Pubkey,
    public_key: Pubkey,
) -> Result<(Vec<Image>, Vec<u8>, Vec<u8>)> {
    let statement = checked(decode_pool_v1_pair_forest_terminal_statement_v1(public))?;
    ensure!(
        checked(encode_pool_v1_pair_forest_terminal_statement_v1(&statement))?.as_slice() == public
    );
    let c = *statement.common();
    let s = c.lane_transition.live_snapshot;

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
            registry_program: registry_program.to_bytes(),
            registry_authority: [0; 32],
            policy_binding: [7; 32],
        },
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: c.checkpoint_sequence + 1,
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
        registry_program: registry_program.to_bytes(),
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
        pool_program: pool.to_bytes(),
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
            image("proof", proof_key, foreign, proof_image),
            image("public", public_key, foreign, public.to_vec()),
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
fn hex(b: &[u8]) -> String {
    b.iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}
fn instruction(v: &Value) -> Result<Instruction> {
    Ok(Instruction {
        program_id: Address::from_str(v["program"].as_str().unwrap())?,
        data: unhex(v["data"].as_str().unwrap()),
        accounts: v["accounts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| AccountMeta {
                pubkey: Address::from_str(a[0].as_str().unwrap()).unwrap(),
                is_signer: a[1].as_bool().unwrap(),
                is_writable: a[2].as_bool().unwrap(),
            })
            .collect(),
    })
}
fn invoke(binary: &str, q: &Value) -> Result<Value> {
    use std::process::{Command, Stdio};
    let mut c = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    c.stdin
        .take()
        .unwrap()
        .write_all(serde_json::to_string(q)?.as_bytes())?;
    let o = c.wait_with_output()?;
    ensure!(
        o.status.success(),
        "planner failed: {}",
        String::from_utf8_lossy(&o.stderr)
    );
    Ok(serde_json::from_slice(&o.stdout)?)
}
// Same public deposit fixtures as the runner; no prover implementation here.
fn digest(seed: u32) -> aspis_statement::poseidon2::Digest {
    core::array::from_fn(|i| {
        aspis_core::field::M31((seed + 17 * i as u32 + 1) % aspis_core::field::P)
    })
}
fn note(
    n: u32,
) -> (
    aspis_statement::poseidon2::Digest,
    aspis_statement::poseidon2::Digest,
    aspis_statement::poseidon2::Digest,
) {
    let mut found = 0;
    for j in 0..10000 {
        let k = digest(10 + j);
        let salt = digest(100 + j);
        let cm = pool_v1_note_commitment(
            &aspis_statement::derive_owner_key(&k),
            1000,
            aspis_core::field::M31(77),
            &salt,
        );
        let nf = pool_v1_nullifier(&k, &salt);
        if pool_v1_pair_forest_deposit_lane_v1(&cm).unwrap()
            == pool_v1_pair_forest_output_lane_v1(&nf).unwrap()
        {
            if found == n {
                return (k, salt, cm);
            }
            found += 1;
        }
    }
    panic!("fixture exhausted")
}
fn fixture(
    pool: Pubkey,
    mint: Pubkey,
    n: u32,
) -> Result<(
    Pubkey,
    Pubkey,
    Vec<u8>,
    Vec<u8>,
    Vec<aspis_statement::poseidon2::Digest>,
)> {
    let master = pool_v1_pair_forest_master_address(&pool, &mint).0;
    let mut trees: Vec<_> = (0..8)
        .map(|_| IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[20],
            frontier: core::array::from_fn(|i| POOL_V1_PAIR_EMPTY_ROOTS[i]),
        })
        .collect();
    let mut histories = vec![vec![POOL_V1_PAIR_EMPTY_ROOTS[20]]; 8];
    for j in 0..2 {
        let (_, _, cm) = note(j);
        let l = checked(pool_v1_pair_forest_deposit_lane_v1(&cm))? as usize;
        let leaf = checked(checked(PoolV1PairLeafWitnessV1::single_output(cm))?.leaf_digest())?;
        trees[l] =
            checked(trees[l].append_one_with_empty_roots(leaf, &POOL_V1_PAIR_EMPTY_ROOTS))?.0;
        histories[l].push(trees[l].root);
    }
    let mut roots: Vec<_> = trees.iter().map(|t| t.root).collect();
    while roots.len() > 1 {
        roots = roots
            .chunks(2)
            .map(|s| pool_v1_tree_parent(&s[0], &s[1]))
            .collect();
    }
    let (_, _, cm) = note(n);
    let l = checked(pool_v1_pair_forest_deposit_lane_v1(&cm))?;
    let (lane, bump) = checked(pool_v1_pair_forest_lane_address(&pool, &master, l))?;
    let (cp, cpb) = pool_v1_pair_forest_checkpoint_address(&pool, &master, 0);
    let lane_bytes = checked(encode_pool_v1_pair_forest_lane_state_v1(
        &PoolV1PairForestLaneStateV1 {
            bump,
            master: master.to_bytes(),
            lane_id: l,
            tree: trees[l as usize],
        },
        &POOL_V1_PAIR_EMPTY_ROOTS,
    ))?
    .to_vec();
    let cp_bytes = checked(encode_pool_v1_pair_forest_checkpoint_v1(
        &PoolV1PairForestCheckpointV1 {
            bump: cpb,
            master: master.to_bytes(),
            deployment_domain: [5; 32],
            checkpoint_sequence: 0,
            global_root: roots[0],
            lane_sequences: core::array::from_fn(|i| trees[i].next_leaf_index),
        },
    ))?
    .to_vec();
    Ok((
        lane,
        cp,
        lane_bytes,
        cp_bytes,
        histories[l as usize].clone(),
    ))
}
fn put(svm: &mut LiteSVM, k: Pubkey, owner: Pubkey, data: Vec<u8>) -> Result<()> {
    checked(svm.set_account(
        addr(k),
        Account {
            lamports: svm.minimum_balance_for_rent_exemption(data.len()).max(1),
            owner: addr(owner),
            data,
            executable: false,
            rent_epoch: 0,
        },
    ))
}
fn main() -> Result<()> {
    ensure!(
        !cfg!(debug_assertions) && cfg!(feature = "r1p-check"),
        "optimized r1p-check required"
    );
    let args: Vec<_> = env::args().collect();
    ensure!(
        args.len() == 6,
        "RUNNER DEFAULT.so DEVNET.so POOL.so OUTPUT"
    );
    let out = Path::new(&args[5]);
    {
        use std::os::unix::fs::DirBuilderExt;
        fs::DirBuilder::new().mode(0o700).create(out)?;
    }
    let payer = fresh_key(&out.join("payer.key"))?;
    let mint = Pubkey::new_from_array([0x42; 32]);
    let pins = [
        "f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4",
        "63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299",
        "121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548",
    ];
    let elfs: Vec<_> = args[2..5]
        .iter()
        .map(fs::read)
        .collect::<std::io::Result<_>>()?;
    for (b, p) in elfs.iter().zip(pins) {
        ensure!(sha(b) == p, "ELF pin mismatch");
    }
    let mut receipts = vec![];
    for v in 0..2 {
        // The devnet verifier's two deployment-ID slots differ from default.
        // Each proof must bind the pool/registry used by that exact ELF.
        let label = if v == 0 { "default" } else { "devnet" };
        let pool = if v == 0 {
            Pubkey::new_from_array(POOL)
        } else {
            Pubkey::from_str("BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs")?
        };
        let registry_program = if v == 0 {
            Pubkey::new_from_array(REGISTRY)
        } else {
            Pubkey::from_str("9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q")?
        };
        let program = Pubkey::from_str(if v == 0 {
            PROGRAM
        } else {
            "Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA"
        })?;
        let mode_out = out.join(label);
        fs::create_dir(&mode_out)?;
        for n in 0..2 {
            let op = if n == 0 { "transfer" } else { "withdrawal" };
            let dir = mode_out.join(op);
            fs::create_dir(&dir)?;
            let pubkey = fresh_key(&dir.join("public.key"))?;
            let cpkey = fresh_key(&dir.join("checkpoint.key"))?;
            let accounts: Vec<_> = (0..8)
                .map(|i| fresh_key(&dir.join(format!("attempt-{i}.key"))))
                .collect::<Result<_>>()?;
            let (lane, cp, lb, cb, history) = fixture(pool, mint, n)?;
            let destination = Pubkey::new_from_array([0x49; 32]);
            let q = json!({"action":"prove","pool":pool.to_string(),"mint":mint.to_string(),"payer":payer.pubkey().to_string(),"registry":registry_program.to_string(),"verifier":program.to_string(),"note":n,"withdrawal":n==1,"destination":destination.to_string(),"checkpoint":cp.to_string(),"lane_bytes":hex(&lb),"checkpoint_bytes":hex(&cb),"proof_dir":dir.join("proof").to_str().unwrap(),"proof_accounts":accounts.iter().map(|a|a.pubkey().to_string()).collect::<Vec<_>>(),"public_account":pubkey.pubkey().to_string(),"verifier_checkpoint":cpkey.pubkey().to_string()});
            write_json(&dir.join("request.json"), &q)?;
            let plan = invoke(&args[1], &q)?;
            write_json(&dir.join("plan.json"), &plan)?;
            let index = plan["attempt_index"].as_u64().unwrap() as usize;
            let selected = key(accounts[index].pubkey());
            ensure!(plan["proof_account"] == selected.to_string());
            let proof = fs::read(dir.join("proof/proof.bin"))?;
            let public = fs::read(dir.join("proof/statement.bin"))?;
            // Reopen the actual runner's ledger, then the exact adapter: duplicate is fatal
            // before the body, leaves every durable record unchanged, and publishes nothing.
            let ledger_path = dir.join("proof/mask-nonce-ledger");
            let ledger_snapshot = || -> Result<Vec<(String, Vec<u8>)>> {
                let mut x = fs::read_dir(&ledger_path)?
                    .map(|e| {
                        let e = e?;
                        Ok((
                            e.file_name().to_string_lossy().to_string(),
                            fs::read(e.path())?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                x.sort();
                Ok(x)
            };
            let before = ledger_snapshot()?;
            ensure!(before.len() == index + 1);
            for (i, (_, b)) in before.iter().enumerate() {
                ensure!(
                    b.len() == 80 && &b[..16] == b"ASPIS-MASK-V1\0\0\0",
                    "bad ledger record {i}"
                );
            }
            ensure!(before.iter().any(|(_, b)| b[48..80] == selected.to_bytes()));
            let mut ledger =
                aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore::open(
                    &ledger_path,
                )?;
            let f = aspis_prover::r0_fixture::prepare(n == 1);
            let duplicate = aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts(
                f.public(),
                &f.compiled,
                aspis_prover::HOST_HASH,
                &mut ledger,
                |_| selected.to_bytes(),
            );
            ensure!(
                matches!(
                    duplicate,
                    Err(aspis_r1_cost_probe::verifier::Error::Semantic)
                ),
                "duplicate did not fail closed"
            );
            ensure!(
                ledger_snapshot()? == before,
                "duplicate changed durable ledger"
            );
            let (mut inputs, request, expected) = images(
                pool,
                registry_program,
                program,
                &proof[688..],
                &public,
                selected,
                key(pubkey.pubkey()),
            )?;
            ensure!(inputs[0].data == proof);
            // Use exact live snapshots supplied to the operational planner.
            inputs[3].data = cb.clone();
            inputs[4].data = lb.clone();
            {
                let runout = dir.join("execution");
                fs::create_dir(&runout)?;
                let mut svm = LiteSVM::new();
                svm.warp_to_slot(SLOT);
                checked(svm.add_program(addr(program), &elfs[v]))?;
                checked(svm.add_program(addr(pool), &elfs[2]))?;
                write_json(
                    &runout.join("loaded-verifier.json"),
                    &loaded_program(&svm, program, &elfs[v])?,
                )?;
                write_json(
                    &runout.join("loaded-pool.json"),
                    &loaded_program(&svm, pool, &elfs[2])?,
                )?;
                checked(svm.airdrop(&payer.pubkey(), 1_000_000_000))?;
                for i in &inputs {
                    put(&mut svm, i.key, i.owner, i.data.clone())?;
                }
                put(
                    &mut svm,
                    key(cpkey.pubkey()),
                    program,
                    vec![0; CHECKPOINT_BYTES],
                )?;
                let protected: Vec<_> = inputs.iter().map(|i| addr(i.key)).collect();
                let initial = snapshot(&svm, &protected)?;
                send(
                    &mut svm,
                    &payer,
                    None,
                    instruction(&plan["stage1"])?,
                    &runout,
                    "stage1",
                )?;
                ensure!(
                    snapshot(&svm, &protected)? == initial,
                    "stage1 modified readonly inputs"
                );
                let stage2keys = [
                    inputs[0].key,
                    inputs[2].key,
                    inputs[3].key,
                    inputs[4].key,
                    inputs[5].key,
                    inputs[6].key,
                    key(cpkey.pubkey()),
                ];
                let result = send(
                    &mut svm,
                    &payer,
                    None,
                    Instruction {
                        program_id: addr(program),
                        accounts: stage2keys
                            .iter()
                            .map(|k| AccountMeta::new_readonly(addr(*k), false))
                            .collect(),
                        data: request.clone(),
                    },
                    &runout,
                    "stage2",
                )?;
                ensure!(
                    result.return_program == addr(program) && result.return_data == expected,
                    "verifier ASR8 mismatch"
                );
                ensure!(
                    snapshot(&svm, &protected)? == initial,
                    "stage2 modified inputs"
                );
                let page = Pubkey::from_str(plan["page"].as_str().unwrap())?;
                let mut pagebytes = vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
                checked(initialize_root_history_page_bytes_v1(
                    &mut pagebytes,
                    lane.to_bytes(),
                    0,
                    &history,
                ))?;
                put(&mut svm, page, pool, pagebytes)?;
                if n == 1 {
                    install_tokens(&mut svm, pool, mint, destination)?;
                }
                let settled = send(
                    &mut svm,
                    &payer,
                    None,
                    instruction(&plan["settle"])?,
                    &runout,
                    "pool-settle",
                )?;
                ensure!(
                    settled.return_program == addr(pool) && settled.return_data == expected,
                    "Pool ASR8 mismatch"
                );
                let laneafter = svm.get_account(&addr(lane)).unwrap();
                let marker = svm
                    .get_account(&Address::from_str(plan["marker"].as_str().unwrap())?)
                    .unwrap();
                let validation = invoke(
                    &args[1],
                    &json!({"action":"validate_settlement","pool":pool.to_string(),"mint":mint.to_string(),"payer":payer.pubkey().to_string(),"registry":registry_program.to_string(),"verifier":program.to_string(),"note":n,"lane_bytes":hex(&laneafter.data),"marker_bytes":hex(&marker.data),"candidate_bytes":hex(&proof[..688])}),
                )?;
                receipts.push(json!({"operation":op,"verifier":label,"elf_sha256":sha(&elfs[v]),"pool_elf_sha256":sha(&elfs[2]),"accepted":true,"attempts":index+1,"proof_account":selected.to_string(),"proof_sha256":sha(&proof),"statement_sha256":sha(&public),"duplicate_error":"Semantic","duplicate_ledger_unchanged":true,"settlement":validation}));
            }
        }
    }
    write_json(
        &out.join("acceptance.json"),
        &json!({"runs":receipts,"scope":"Actual devnet_spend planner; OS entropy; signed LiteSVM transactions; preloaded account fixtures, not RPC deployment or registry provisioning; retained private task keys and ledgers","elf_pins":pins}),
    )?;
    Ok(())
}
fn install_tokens(
    svm: &mut LiteSVM,
    pool: Pubkey,
    mint: Pubkey,
    destination: Pubkey,
) -> Result<()> {
    let master = pool_v1_pair_forest_master_address(&pool, &mint).0;
    let authority = pool_v1_vault_authority_address(&pool, &master).0;
    let vault = pool_v1_vault_token_account_address(&pool, &master).0;
    let token = Pubkey::from_str("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA")?;
    let mut m = vec![0; 82];
    m[36..44].copy_from_slice(&1_000_000u64.to_le_bytes());
    m[44] = 6;
    m[45] = 1;
    put(svm, mint, token, m)?;
    for (k, owner, amount) in [
        (vault, authority, 10_000u64),
        (destination, Pubkey::new_from_array([0x50; 32]), 0u64),
    ] {
        let mut d = vec![0; 165];
        d[..32].copy_from_slice(&mint.to_bytes());
        d[32..64].copy_from_slice(&owner.to_bytes());
        d[64..72].copy_from_slice(&amount.to_le_bytes());
        d[108] = 1;
        put(svm, k, token, d)?;
    }
    put(svm, authority, Pubkey::default(), vec![])
}
