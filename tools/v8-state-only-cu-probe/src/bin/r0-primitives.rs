//! Paired SBF work/empty-loop calibration; all transactions are local LiteSVM.
use anyhow::{ensure, Result};
use litesvm::LiteSVM;
use serde_json::json;
use sha2::{Digest, Sha256};
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::Instruction;
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;
use std::{fs, path::Path};
fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions));
    let args: Vec<_> = std::env::args().collect();
    let elf = fs::read(&args[1])?;
    let keypath = Path::new(&args[2]);
    let payer = if keypath.exists() {
        let b: Vec<u8> = serde_json::from_slice(&fs::read(keypath)?)?;
        Keypair::try_from(b.as_slice())?
    } else {
        use std::{io::Write, os::unix::fs::OpenOptionsExt};
        let k = Keypair::new();
        fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .mode(0o600)
            .open(keypath)?
            .write_all(serde_json::to_string(&k.to_bytes().to_vec())?.as_bytes())?;
        k
    };
    let names = [
        "EAdd",
        "ESub",
        "ENeg",
        "EMul",
        "ESquare",
        "EMulK",
        "EMulF",
        "EInv",
        "EInvGeneric",
        "KAdd",
        "KSub",
        "KNeg",
        "KMul",
        "KSquare",
        "KMulF",
        "KMulC",
        "KInv",
        "KInvGeneric",
        "FAdd",
        "FSub",
        "FNeg",
        "FMul",
        "FInv",
        "FInvGeneric",
        "FHalf",
        "FMulPow2",
        "ShaCompression",
    ];
    let mut records = Vec::new();
    for (op, name) in names.iter().enumerate() {
        for n in [64u32, 128] {
            let mut costs = [0u64; 2];
            let mut runs = Vec::new();
            for empty in [false, true] {
                let mut svm = LiteSVM::new();
                let program = Address::new_from_array([0x84; 32]);
                svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
                svm.add_program(program, &elf)?;
                let mut data = vec![op as u8, u8::from(empty)];
                data.extend_from_slice(&n.to_le_bytes());
                for limb in [
                    11u32, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
                ] {
                    data.extend_from_slice(&limb.to_le_bytes());
                }
                let ix = Instruction {
                    program_id: program,
                    accounts: vec![],
                    data,
                };
                let tx = Transaction::new_signed_with_payer(
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
                        ix,
                    ],
                    Some(&payer.pubkey()),
                    &[&payer],
                    svm.latest_blockhash(),
                );
                let sim = svm
                    .simulate_transaction(tx.clone())
                    .map_err(|e| anyhow::anyhow!("{name}/{n}/{empty}: {e:?}"))?;
                let exec = svm
                    .send_transaction(tx)
                    .map_err(|e| anyhow::anyhow!("{name}/{n}/{empty}: {e:?}"))?;
                ensure!(
                    sim.meta.compute_units_consumed == exec.compute_units_consumed
                        && sim.meta.logs == exec.logs
                );
                let meters: Vec<u64> = exec
                    .logs
                    .iter()
                    .filter_map(|s| {
                        s.strip_prefix("Program consumption: ")?
                            .split_whitespace()
                            .next()?
                            .parse()
                            .ok()
                    })
                    .collect();
                ensure!(meters.len() == 2);
                costs[empty as usize] = meters[0] - meters[1];
                runs.push(json!({"empty":empty,"interval_cu":costs[empty as usize],"harness_cu":exec.compute_units_consumed,"logs":exec.logs,"return_data":exec.return_data.data,"simulation_execution_agree":true}));
            }
            let net = costs[0] as i64 - costs[1] as i64;
            records.push(json!({"primitive":name,"n":n,"net_cu":net,"cu_per_op":net as f64/n as f64,"runs":runs}));
        }
    }
    fs::write(
        &args[3],
        serde_json::to_vec_pretty(
            &json!({"source_revision":std::env::var("ASPIS_SOURCE_REVISION")?,"elf_sha256":format!("{:x}",Sha256::digest(&elf)),"records":records,"note":"N work operations minus type-matched empty loop; SHA is a 32-byte hash (one padded compression) including syscall/marshalling"}),
        )?,
    )?;
    Ok(())
}
