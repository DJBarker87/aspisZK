//! R20 standalone SVM gate harness.
//!
//! This is a separate driver from the accepted R19 probe. It preserves the
//! same LiteSVM transaction, 256 KiB heap, account, payer, loader, and
//! unchanged-account behavior, while making the one-million acceptance limit
//! distinct from the 100-million diagnostic limit.

use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;

const ACCEPTANCE_LIMIT: u64 = 1_000_000;
const DIAGNOSTIC_LIMIT: u64 = 100_000_000;
const HEAP_BYTES: u32 = 256 * 1024;

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let micro = match args.as_slice() {
        [_, _, _, flag] if flag == "--micro" => true,
        [_, _, _] => false,
        _ => panic!("usage: r20-svm-probe candidate.so fixture-dir [--micro]"),
    };
    let elf = std::fs::read(&args[1]).unwrap();
    let fixture = |name| std::fs::read(format!("{}/{name}", args[2])).unwrap();
    let original = fixture("proof-1.bin");
    let public = fixture("public.bin");
    let transition = fixture("transition.bin");
    let binding = fixture("binding.bin");
    assert_eq!(binding.len(), 32);
    assert!(original.len() > 699 * 16);

    let program = Address::new_from_array([71; 32]);
    let keys = [72, 73, 74].map(|n| Address::new_from_array([n; 32]));
    let limits: &[(&str, u64)] = if micro {
        &[("diagnostic", DIAGNOSTIC_LIMIT)]
    } else {
        &[
            ("acceptance", ACCEPTANCE_LIMIT),
            ("diagnostic", DIAGNOSTIC_LIMIT),
        ]
    };
    let cases: &[&str] = if micro {
        &["honest"]
    } else {
        &["honest", "bad-combined-final"]
    };
    for &(limit_class, limit) in limits {
        for &case in cases {
            let mut proof = original.clone();
            if case == "bad-combined-final" {
                proof[697 * 16] ^= 1;
            }
            let mut budget = ComputeBudget::new_with_defaults(false);
            budget.compute_unit_limit = limit;
            budget.heap_size = HEAP_BYTES;
            let mut svm = LiteSVM::new().with_compute_budget(budget);
            let payer = Keypair::new(); // In-memory simulator identity only.
            svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
            if let Err(error) = svm.add_program(program, &elf) {
                println!(
                    "{}",
                    serde_json::json!({
                        "limit_class": limit_class,
                        "cu_limit": limit,
                        "case": case,
                        "status": "load_error",
                        "load_error": format!("{error:?}"),
                        "heap_bytes": HEAP_BYTES,
                    })
                );
                std::process::exit(2);
            }
            let data = [proof, public.clone(), transition.clone()];
            for (key, bytes) in keys.iter().zip(&data) {
                svm.set_account(
                    *key,
                    Account {
                        lamports: 100_000_000,
                        data: bytes.clone(),
                        owner: program,
                        executable: false,
                        rent_epoch: 0,
                    },
                )
                .unwrap();
            }
            let ix = Instruction {
                program_id: program,
                accounts: keys
                    .iter()
                    .map(|key| AccountMeta::new_readonly(*key, false))
                    .collect(),
                data: binding.clone(),
            };
            let tx = Transaction::new(
                &[&payer],
                Message::new(&[ix], Some(&payer.pubkey())),
                svm.latest_blockhash(),
            );
            let (accepted, error, meta) = match svm.simulate_transaction(tx) {
                Ok(result) => (true, None, result.meta),
                Err(result) => (false, Some(format!("{:?}", result.err)), result.meta),
            };
            for (key, bytes) in keys.iter().zip(&data) {
                assert_eq!(svm.get_account(key).unwrap().data, *bytes);
            }
            let error_text = error.clone().unwrap_or_default();
            let resource_failure = !accepted
                && (error_text.contains("ProgramFailedToComplete")
                    || error_text.contains("ComputationalBudgetExceeded")
                    || error_text.contains("exceeded CUs"));
            let custom_rejection = !accepted && !resource_failure && error_text.contains("Custom(");
            let status = if accepted {
                "accepted"
            } else if resource_failure {
                "resource_failure"
            } else if custom_rejection {
                "custom_rejection"
            } else {
                "other_rejection"
            };
            println!(
                "{}",
                serde_json::json!({
                    "limit_class": limit_class,
                    "cu_limit": limit,
                    "case": case,
                    "status": status,
                    "accepted": accepted,
                    "custom_rejection": custom_rejection,
                    "resource_failure": resource_failure,
                    "error": error,
                    "cu": meta.compute_units_consumed,
                    "heap_bytes": HEAP_BYTES,
                    "logs": meta.logs,
                    "unchanged_accounts": true,
                    "scope": if micro {
                        "arithmetic-only-microbenchmark; never a budget acceptance result"
                    } else {
                        "R20 candidate verifier only; no settlement; security unproved"
                    },
                })
            );
            assert!(!accepted || case == "honest", "corruption accepted");
        }
    }
}
