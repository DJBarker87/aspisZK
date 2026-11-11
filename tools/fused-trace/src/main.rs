//! FUTURE-VERSION EXPERIMENT. Runs ONE measurement instruction of the
//! three-account R1 probe program under LiteSVM register tracing and leaves
//! the trace (`*.regs`, 12 u64 per executed instruction, pc last) in the given
//! directory. Diagnostic compute limit; attribution evidence only.
//!
//! usage: aspis-fused-trace <elf> <proof.bin> <public.bin> <tag> <trace-dir>
use anyhow::{anyhow, ensure, Result};
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;
use std::{env, fs};

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build only");
    let args: Vec<_> = env::args().collect();
    ensure!(args.len() == 6, "usage: aspis-fused-trace <elf> <proof> <public> <tag> <trace-dir>");
    let elf = fs::read(&args[1])?;
    let proof = fs::read(&args[2])?;
    let public = fs::read(&args[3])?;
    let tag: u8 = args[4].parse()?;
    ensure!(fs::read_dir(&args[5]).map(|mut d| d.next().is_none()).unwrap_or(true), "trace directory is not empty");
    fs::create_dir_all(&args[5])?;
    // LiteSVM::new() turns register tracing on when this variable is set.
    env::set_var("SBF_TRACE_DIR", &args[5]);
    let program = Address::new_from_array([0xa1; 32]);
    let keys = [Address::new_from_array([0xa2; 32]), Address::new_from_array([0xa3; 32]), Address::new_from_array([0xa4; 32])];
    let payer = Keypair::new();
    let nesting = LiteSVM::mainnet_feature_set().is_active(&agave_feature_set::raise_cpi_nesting_limit_to_8::ID);
    let mut svm = LiteSVM::new().with_compute_budget(ComputeBudget { compute_unit_limit: 200_000_000, heap_size: 256 * 1024, ..ComputeBudget::new_with_defaults(nesting) });
    svm.airdrop(&payer.pubkey(), 1_000_000_000).map_err(|e| anyhow!("airdrop: {e:?}"))?;
    svm.add_program(program, &elf).map_err(|e| anyhow!("load: {e:?}"))?;
    for (key, data) in [(keys[0], proof), (keys[1], public), (keys[2], vec![0u8; 744 + 16 * 64])] {
        svm.set_account(key, Account { lamports: 100_000_000, data, owner: program, executable: false, rent_epoch: 0 })?;
    }
    let ix = Instruction { program_id: program, accounts: vec![AccountMeta::new_readonly(keys[0], false), AccountMeta::new_readonly(keys[1], false), AccountMeta::new(keys[2], false)], data: vec![tag] };
    let instructions = [ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), ComputeBudgetInstruction::request_heap_frame(256 * 1024), ix];
    let tx = Transaction::new_signed_with_payer(&instructions, Some(&payer.pubkey()), &[&payer], svm.latest_blockhash());
    let meta = svm.send_transaction(tx).map_err(|e| anyhow!("transaction failed: {:?}", e.err))?;
    let program_cu = meta.logs.iter().find_map(|l| l.strip_prefix(&format!("Program {program} consumed "))?.split_whitespace().next()?.parse::<u64>().ok());
    println!("tag {tag}: program CU {program_cu:?}, transaction CU {}", meta.compute_units_consumed);
    Ok(())
}
