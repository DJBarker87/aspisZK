//! Opt-in J1.R13 candidate gate. This tests loader-to-AccountInfo metadata with
//! signature verification DISABLED, including the honest control. A trusted PDA
//! cannot supply an ordinary transaction signature. This is not custody evidence
//! or evidence of a valid signed transaction. No SBF artifact is built here.
use super::*;

pub(super) fn run(
    pristine: &LiteSVM,
    program: Pubkey,
    protected: &[Address],
    stage2_keys: &[Address; 7],
    request: &[u8],
    expected_return: &[u8],
    payer: &Keypair,
    output: &Path,
) -> Result<()> {
    let out = output.join("readonly-metadata-runtime");
    fs::create_dir(&out)?;
    let master = stage2_keys[1];
    let original = snapshot(pristine, protected)?;
    let master_index = protected
        .iter()
        .position(|k| *k == master)
        .context("trusted master absent from protected accounts")?;
    ensure!(original[master_index].owner == Address::new_from_array(POOL));
    ensure!(!original[master_index].executable);
    let mut cases = Vec::new();
    for case in ["control", "wrong-owner", "signer", "writable", "executable"] {
        // Every case starts from identical admitted stage1 images and uses the
        // same signature-verification mode; each negative changes one input.
        let mut svm = pristine.clone().with_sigverify(false);
        let mut metas: Vec<_> = stage2_keys
            .iter()
            .copied()
            .map(|k| AccountMeta::new_readonly(k, false))
            .collect();
        let mut expected_before = original.clone();
        match case {
            "wrong-owner" => {
                expected_before[master_index].owner = Address::new_from_array([0x6d; 32]);
                checked(svm.set_account(master, expected_before[master_index].clone()))?;
            }
            "signer" => metas[1].is_signer = true,
            "writable" => metas[1].is_writable = true,
            "executable" => {
                expected_before[master_index].executable = true;
                checked(svm.set_account(master, expected_before[master_index].clone()))?;
            }
            "control" => {}
            _ => unreachable!(),
        }
        let before = snapshot(&svm, protected)?;
        ensure!(
            before == expected_before,
            "{case}: unexpected account mutation before send"
        );
        let instruction = Instruction {
            program_id: addr(program),
            data: request.to_vec(),
            accounts: metas,
        };
        let instruction_pin = json!({
            "program": instruction.program_id.to_string(),
            "bytes": instruction.data.len(), "data_sha256": sha(&instruction.data),
            "accounts": instruction.accounts.iter().map(|m| json!({
                "key":m.pubkey.to_string(), "signer":m.is_signer,
                "writable":m.is_writable})).collect::<Vec<_>>()});
        let instructions = [
            ComputeBudgetInstruction::set_compute_unit_limit(LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP),
            ComputeBudgetInstruction::set_loaded_accounts_data_size_limit(LOADED),
            instruction,
        ];
        let message_v0 = v0::Message::try_compile(
            &payer.pubkey(),
            &instructions,
            &[],
            svm.latest_blockhash(),
        )?;
        // Correct signature-vector length permits runtime entry; these are
        // deliberately dummy signatures, not forged/validated PDA signatures.
        let signature_count = usize::from(message_v0.header.num_required_signatures);
        let message = VersionedMessage::V0(message_v0);
        let tx = VersionedTransaction {
            signatures: vec![Default::default(); signature_count],
            message,
        };
        let tx_bytes = wincode::serialize(&tx)?;
        ensure!(
            tx_bytes.len() <= 1232,
            "{case}: transaction exceeds packet size"
        );
        write_new(
            &out.join(format!("{case}.transaction.bin")),
            &tx_bytes,
            0o644,
        )?;
        let started = Instant::now();
        let (error, meta) = match svm.send_transaction(tx) {
            Ok(m) => (None, m),
            Err(f) => (Some(format!("{:?}", f.err)), f.meta),
        };
        let after = snapshot(&svm, protected)?;
        let entered = meta
            .logs
            .iter()
            .any(|s| s == &format!("Program {program} invoke [1]"));
        let consumed = meta
            .logs
            .iter()
            .any(|s| s.starts_with(&format!("Program {program} consumed ")));
        let rejected_by_instruction =
            error.as_deref() == Some("InstructionError(3, InvalidAccountData)");
        let pass = entered
            && consumed
            && after == before
            && if case == "control" {
                error.is_none()
                    && meta.return_data.program_id == addr(program)
                    && meta.return_data.data == expected_return
            } else {
                rejected_by_instruction
            };
        let account_pins = |xs: &[Account]| {
            protected
                .iter()
                .zip(xs)
                .map(|(k, a)| account_json(*k, a))
                .collect::<Vec<_>>()
        };
        let receipt = json!({
            "case":case, "passed":pass, "signature_verification":false,
            "dummy_signature_count":signature_count, "valid_signature_claim":false,
            "instruction":instruction_pin, "transaction_sha256":sha(&tx_bytes),
            "transaction_bytes":tx_bytes.len(), "error":error,
            "verifier_invoked":entered, "verifier_consumption_log":consumed,
            "compute_units":meta.compute_units_consumed,
            "wall_seconds":started.elapsed().as_secs_f64(), "logs":meta.logs,
            "before":account_pins(&before), "after":account_pins(&after),
            "protected_accounts_unchanged":after==before,
            "return_program":meta.return_data.program_id.to_string(),
            "return_data_sha256":sha(&meta.return_data.data),
        });
        write_json(&out.join(format!("{case}.json")), &receipt)?;
        cases.push(receipt);
        ensure!(pass, "{case}: loader-metadata gate failed; retained receipt; pre-entry rejection is not a pass");
    }
    write_json(
        &out.join("summary.json"),
        &json!({
            "all_five_cases_passed":true, "cases":cases,
            "scope":"selected R1 adapter copy only; loader metadata with signature verification disabled",
            "signature_verification":false, "custody_claim":false,
            "state_origin":"identical successful candidate stage1, cloned before stage2",
            "elf_and_build_receipt":"../../input-manifest.json plus ../loaded-program.json",
            "source_sha256":sha(include_bytes!("readonly_runtime.rs")),
            "second_copy_aspis_verifier_runtime_gate":"OPEN: requires distinct V7 ASQ8 artifact and fixture",
        }),
    )
}
