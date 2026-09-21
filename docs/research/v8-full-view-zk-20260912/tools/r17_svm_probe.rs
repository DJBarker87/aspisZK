//! Local R17 candidate verifier measurement; no RPC or Pool settlement.
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: r17-svm-probe candidate.so fixture-dir");
    let elf = std::fs::read(&args[1]).unwrap();
    let fixture = |name| std::fs::read(format!("{}/{name}", args[2])).unwrap();
    let original = fixture("proof-1.bin");
    let public = fixture("public.bin");
    let transition = fixture("transition.bin");
    let binding = fixture("binding.bin");
    assert_eq!(binding.len(), 32);
    assert!(original.len() > 953 * 16);
    let program = Address::new_from_array([71; 32]);
    let keys = [72, 73, 74].map(|n| Address::new_from_array([n; 32]));
    // Diagnostic budget reports exhaustion separately, never as acceptance.
    for limit in [1_200_000, 1_400_000, 100_000_000] {
        for case in ["honest", "bad-g-final"] {
            let mut proof = original.clone();
            if case == "bad-g-final" { proof[697 * 16] ^= 1; }
            let mut budget = ComputeBudget::new_with_defaults(false);
            budget.compute_unit_limit = limit;
            budget.heap_size = 256 * 1024;
            let mut svm = LiteSVM::new().with_compute_budget(budget);
            let payer = Keypair::new(); // In-memory simulator identity only.
            svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
            if let Err(e) = svm.add_program(program, &elf) {
                println!("{}", serde_json::json!({"load_error":format!("{e:?}")}));
                std::process::exit(2);
            }
            let data = [proof, public.clone(), transition.clone()];
            for (key, bytes) in keys.iter().zip(&data) {
                svm.set_account(*key, Account { lamports: 100_000_000,
                    data: bytes.clone(), owner: program, executable: false, rent_epoch: 0 }).unwrap();
            }
            let ix = Instruction { program_id: program,
                accounts: keys.iter().map(|k| AccountMeta::new_readonly(*k, false)).collect(),
                data: binding.clone() };
            let tx = Transaction::new(&[&payer], Message::new(&[ix], Some(&payer.pubkey())), svm.latest_blockhash());
            let (accepted, error, meta) = match svm.simulate_transaction(tx) {
                Ok(r) => (true, None, r.meta),
                Err(r) => (false, Some(format!("{:?}", r.err)), r.meta),
            };
            for (key, bytes) in keys.iter().zip(&data) {
                assert_eq!(svm.get_account(key).unwrap().data, *bytes);
            }
            println!("{}", serde_json::json!({"case":case,"cu_limit":limit,
                "accepted":accepted,"error":error,"cu":meta.compute_units_consumed,
                "logs":meta.logs,"unchanged_accounts":true,
                "diagnostic_above_transaction_limit":limit>1_400_000,
                "scope":"R17 candidate verifier only; no settlement; security unproved"}));
            assert!(!accepted || case == "honest", "corruption accepted");
        }
    }
}
