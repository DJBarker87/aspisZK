//! LiteSVM program tests for `programs/aspis-upload` and the PIN2 per-payment
//! lifecycle: seed-derived account creation, 16 + 1 uploads at the frozen
//! 3,763-byte chunk in v1 transactions, a stage-1 stand-in, the fixed close
//! transaction, and the payer's lamport accounting.
//!
//! ELFs: `PIN2_UPLOAD_SO` (default `../../target/deploy/aspis_upload.so`) and
//! `PIN2_STUB_VERIFIER_SO` (default `stub-verifier/target/deploy/...`). The
//! stub verifier is a test fixture for W1's not-yet-merged close instruction.

use litesvm::LiteSVM;
use sha2::{Digest, Sha256};
use solana_address::Address;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{
    v1::{Message, TransactionConfig},
    VersionedMessage,
};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;
use std::{env, fs, path::PathBuf};

const UPLOAD: Address = Address::new_from_array([0x55; 32]);
const VERIFIER: Address = Address::new_from_array([0x56; 32]);
const SYSTEM: Address = Address::new_from_array([0; 32]);
const PROOF_BYTES: usize = 58_295;
const STATEMENT_BYTES: usize = 1_880;
const CHECKPOINT_BYTES: usize = 1_768;
const CHUNK: usize = 3_763;
const VERIFIER_CLOSE_TAG: u8 = 7; // fix/pin2-verifier-20261110 271869c946d

fn elf(var: &str, default: &str) -> Vec<u8> {
    let path = env::var(var).map(PathBuf::from).unwrap_or_else(|_| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(default)
    });
    fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}; build it with cargo-build-sbf first", path.display()))
}

/// `Pubkey::create_with_seed`, written out the way the Python client does it.
fn derive(base: &Address, seed: &str, owner: &Address) -> Address {
    assert!(seed.len() <= 32);
    assert!(!owner.as_ref().ends_with(b"ProgramDerivedAddress"));
    let mut h = Sha256::new();
    h.update(base.as_ref());
    h.update(seed.as_bytes());
    h.update(owner.as_ref());
    Address::new_from_array(h.finalize().into())
}

/// System `CreateAccountWithSeed` with base = funder (bincode layout the
/// Python client emits): u32 3, base, u64 seed length, seed, lamports, space, owner.
fn create_with_seed_ix(payer: &Address, to: &Address, seed: &str, lamports: u64, space: u64, owner: &Address) -> Instruction {
    let mut d = 3u32.to_le_bytes().to_vec();
    d.extend_from_slice(payer.as_ref());
    d.extend_from_slice(&(seed.len() as u64).to_le_bytes());
    d.extend_from_slice(seed.as_bytes());
    d.extend_from_slice(&lamports.to_le_bytes());
    d.extend_from_slice(&space.to_le_bytes());
    d.extend_from_slice(owner.as_ref());
    Instruction {
        program_id: SYSTEM,
        accounts: vec![AccountMeta::new(*payer, true), AccountMeta::new(*to, false)],
        data: d,
    }
}

fn seeded(tag: u8, seed: &[u8], tail: &[u8]) -> Vec<u8> {
    let mut d = vec![tag, seed.len() as u8];
    d.extend_from_slice(seed);
    d.extend_from_slice(tail);
    d
}

fn write_ix(target: Address, base: Address, seed: &str, offset: u32, bytes: &[u8]) -> Instruction {
    let mut tail = offset.to_le_bytes().to_vec();
    tail.extend_from_slice(bytes);
    Instruction {
        program_id: UPLOAD,
        accounts: vec![AccountMeta::new(target, false), AccountMeta::new_readonly(base, true)],
        data: seeded(1, seed.as_bytes(), &tail),
    }
}

fn close_ix(program: Address, tag: u8, target: Address, base: Address, seed: &str) -> Instruction {
    Instruction {
        program_id: program,
        accounts: vec![AccountMeta::new(target, false), AccountMeta::new(base, true)],
        data: seeded(tag, seed.as_bytes(), &[]),
    }
}

/// Same v1 configuration as tools/r1-cost-probe devnet_spend.
fn tx(svm: &LiteSVM, payer: &Keypair, extra: &[&Keypair], ixs: &[Instruction]) -> (VersionedTransaction, usize) {
    let conf = TransactionConfig::empty()
        .with_priority_fee(10000)
        .with_compute_unit_limit(1_400_000)
        .with_loaded_accounts_data_size_limit(8 * 1024 * 1024)
        .with_heap_size(256 * 1024);
    let m = Message::try_compile_with_config(&payer.pubkey(), ixs, svm.latest_blockhash(), conf).unwrap();
    let mut signers = vec![payer];
    signers.extend_from_slice(extra);
    let t = VersionedTransaction::try_new(VersionedMessage::V1(m), &signers).unwrap();
    let n = wincode::serialize(&t).unwrap().len();
    (t, n)
}

struct Run {
    svm: LiteSVM,
    payer: Keypair,
}

#[derive(Debug, Clone, Copy)]
struct Landed {
    fee: u64,
    cu: u64,
    bytes: usize,
    payer_delta: i128,
}

impl Run {
    fn new() -> Self {
        let mut svm = LiteSVM::new();
        svm.add_program(UPLOAD, &elf("PIN2_UPLOAD_SO", "../../target/deploy/aspis_upload.so")).unwrap();
        svm.add_program(VERIFIER, &elf("PIN2_STUB_VERIFIER_SO", "stub-verifier/target/deploy/pin2_stub_verifier_close.so")).unwrap();
        let payer = Keypair::new();
        svm.airdrop(&payer.pubkey(), 10_000_000_000).unwrap();
        Run { svm, payer }
    }
    fn balance(&self, a: &Address) -> u64 {
        self.svm.get_balance(a).unwrap_or(0)
    }
    fn send(&mut self, ixs: &[Instruction]) -> Result<Landed, String> {
        self.send_with(&[], ixs)
    }
    fn send_with(&mut self, extra: &[&Keypair], ixs: &[Instruction]) -> Result<Landed, String> {
        self.svm.expire_blockhash();
        let (t, bytes) = tx(&self.svm, &self.payer, extra, ixs);
        assert!(bytes <= 4096, "TxV1 exceeds 4096 bytes: {bytes}");
        let before = self.balance(&self.payer.pubkey());
        match self.svm.send_transaction(t) {
            Ok(m) => Ok(Landed {
                fee: m.fee,
                cu: m.compute_units_consumed,
                bytes,
                payer_delta: self.balance(&self.payer.pubkey()) as i128 - before as i128,
            }),
            Err(e) => Err(format!("{:?} {:?}", e.err, e.meta.logs)),
        }
    }
    fn create(&mut self, seed: &str, space: usize, owner: &Address) -> (Address, u64, Landed) {
        let p = self.payer.pubkey();
        let a = derive(&p, seed, owner);
        let rent = self.svm.minimum_balance_for_rent_exemption(space);
        let l = self.send(&[create_with_seed_ix(&p, &a, seed, rent, space as u64, owner)]).unwrap();
        let acc = self.svm.get_account(&a).unwrap();
        assert_eq!((acc.owner, acc.data.len(), acc.lamports), (*owner, space, rent));
        (a, rent, l)
    }
}

fn pattern(n: usize, salt: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(31).wrapping_add(salt) | 1).collect()
}

/// Per-payment seed scheme from scripts/PIN2_seed_accounts.py:
/// role char + attempt digit + 30 hex chars of a 15-byte per-payment tag.
fn seed(role: char, index: u8, tag: &str) -> String {
    let s = format!("{role}{index}{tag}");
    assert_eq!(s.len(), 32);
    s
}

#[test]
fn full_payment_upload_stage1_close_accounting() {
    let mut r = Run::new();
    let p = r.payer.pubkey();
    let start = r.balance(&p);
    let tag = "0123456789abcdef0123456789abcd";
    // Eight distinct attempt addresses exist before proving.
    let attempts: Vec<Address> = (0..8).map(|k| derive(&p, &seed('p', k, tag), &UPLOAD)).collect();
    for i in 0..8 {
        assert!(!attempts[..i].contains(&attempts[i]));
        assert!(r.svm.get_account(&attempts[i]).is_none());
    }
    let selected = 2u8; // e.g. third attempt succeeded
    let (ps, ss, cs) = (seed('p', selected, tag), seed('s', 0, tag), seed('c', 0, tag));
    let mut landed = Vec::new();
    let (proof_a, proof_rent, l) = r.create(&ps, PROOF_BYTES, &UPLOAD);
    assert_eq!(proof_a, attempts[selected as usize]);
    landed.push(l);
    let (stmt_a, stmt_rent, l) = r.create(&ss, STATEMENT_BYTES, &UPLOAD);
    landed.push(l);
    let proof = pattern(PROOF_BYTES, 7);
    let statement = pattern(STATEMENT_BYTES, 9);
    let mut write_cu = Vec::new();
    let mut max_bytes = 0;
    for (start_off, chunk) in (0..PROOF_BYTES).step_by(CHUNK).zip(proof.chunks(CHUNK)) {
        let l = r.send(&[write_ix(proof_a, p, &ps, start_off as u32, chunk)]).unwrap();
        write_cu.push(l.cu);
        max_bytes = max_bytes.max(l.bytes);
        landed.push(l);
    }
    assert_eq!(write_cu.len(), 16, "frozen proof upload count");
    let l = r.send(&[write_ix(stmt_a, p, &ss, 0, &statement)]).unwrap();
    landed.push(l);
    assert_eq!(r.svm.get_account(&proof_a).unwrap().data, proof, "header-free proof bytes from offset 0");
    assert_eq!(r.svm.get_account(&stmt_a).unwrap().data, statement);
    let (cp_a, cp_rent, l) = r.create(&cs, CHECKPOINT_BYTES, &VERIFIER);
    landed.push(l);
    let stage1 = Instruction {
        program_id: VERIFIER,
        accounts: vec![AccountMeta::new_readonly(proof_a, false), AccountMeta::new_readonly(stmt_a, false), AccountMeta::new(cp_a, false)],
        data: vec![3, 10],
    };
    landed.push(r.send(&[stage1]).unwrap());
    assert!(r.svm.get_account(&cp_a).unwrap().data.iter().all(|&b| b == 0x5a));
    // Fixed close transaction: proof, statement, checkpoint, always in this order.
    let before_close = r.balance(&p);
    let close = [
        close_ix(UPLOAD, 2, proof_a, p, &ps),
        close_ix(UPLOAD, 2, stmt_a, p, &ss),
        close_ix(VERIFIER, VERIFIER_CLOSE_TAG, cp_a, p, &cs),
    ];
    let l = r.send(&close).unwrap();
    landed.push(l);
    let recovered = r.balance(&p) as i128 - before_close as i128 + l.fee as i128;
    assert_eq!(recovered, (proof_rent + stmt_rent + cp_rent) as i128, "close returns exactly the rent");
    for a in [proof_a, stmt_a, cp_a] {
        assert!(r.svm.get_account(&a).map_or(true, |x| x.lamports == 0 && x.data.iter().all(|&b| b == 0)), "account still live");
    }
    let fees: u64 = landed.iter().map(|l| l.fee).sum();
    assert_eq!(start - r.balance(&p), fees, "payer delta == fees only (no marker here: stub has no Pool)");
    for l in &landed {
        assert!(l.payer_delta <= 0 || std::ptr::eq(l, landed.last().unwrap()));
    }
    println!(
        "PIN2-LITESVM {{\"transactions\":{},\"fees\":{},\"recovered\":{},\"rent\":{{\"proof\":{},\"statement\":{},\"checkpoint\":{}}},\"write_cu\":{:?},\"close_tx_cu\":{},\"max_write_tx_bytes\":{},\"close_tx_bytes\":{}}}",
        landed.len(), fees, recovered, proof_rent, stmt_rent, cp_rent, write_cu, l.cu, max_bytes, l.bytes
    );
}

#[test]
fn single_close_cu() {
    let mut r = Run::new();
    let p = r.payer.pubkey();
    let s = "p0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    let (a, rent, _) = r.create(s, PROOF_BYTES, &UPLOAD);
    let before = r.balance(&p);
    let l = r.send(&[close_ix(UPLOAD, 2, a, p, s)]).unwrap();
    assert_eq!(r.balance(&p) + l.fee - before, rent);
    let small = r.send(&[write_ix(p, p, s, 0, &[1])]);
    assert!(small.is_err());
    println!("PIN2-LITESVM-CLOSE {{\"close_cu\":{},\"close_tx_bytes\":{}}}", l.cu, l.bytes);
}

fn expect_err(r: &mut Run, ixs: &[Instruction], needle: &str) {
    let e = r.send(ixs).expect_err("must reject");
    assert!(e.contains(needle), "expected {needle}, got {e}");
}

#[test]
fn rejections_on_the_runtime() {
    let mut r = Run::new();
    let p = r.payer.pubkey();
    let s = "s0bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    let (a, _, _) = r.create(s, 64, &UPLOAD);
    // Bad formats.
    for data in [vec![], vec![0], vec![1], vec![1, 0, 0, 0, 0, 0, 1], seeded(1, &[b'a'; 33], &[0, 0, 0, 0, 1]),
                 seeded(1, &[0xff], &[0, 0, 0, 0, 1]), seeded(1, s.as_bytes(), &[0, 0, 0, 0]), seeded(2, s.as_bytes(), &[0]), vec![7, 1, b'a']] {
        expect_err(&mut r, &[Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new(a, false), AccountMeta::new(p, true)], data }], "InvalidInstructionData");
    }
    // Range and offset overflow.
    expect_err(&mut r, &[write_ix(a, p, s, 60, &[1; 5])], "AccountDataTooSmall");
    expect_err(&mut r, &[write_ix(a, p, s, u32::MAX, &[1])], "AccountDataTooSmall");
    // Wrong seed under the right base.
    expect_err(&mut r, &[write_ix(a, p, "s1bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", 0, &[1])], "InvalidSeeds");
    // Someone else's account: another signer cannot write or close it.
    let mallory = Keypair::new();
    r.svm.airdrop(&mallory.pubkey(), 1_000_000_000).unwrap();
    let m = mallory.pubkey();
    let e = r.send_with(&[&mallory], &[write_ix(a, m, s, 0, &[1])]).unwrap_err();
    assert!(e.contains("InvalidSeeds"), "{e}");
    let e = r.send_with(&[&mallory], &[close_ix(UPLOAD, 2, a, m, s)]).unwrap_err();
    assert!(e.contains("InvalidSeeds"), "{e}");
    // Base present but not signing.
    let unsigned = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new(a, false), AccountMeta::new_readonly(m, false)], data: seeded(1, s.as_bytes(), &[0, 0, 0, 0, 1]) };
    expect_err(&mut r, &[unsigned], "MissingRequiredSignature");
    // Target read-only; base read-only on close.
    let ro = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new_readonly(a, false), AccountMeta::new_readonly(p, true)], data: seeded(1, s.as_bytes(), &[0, 0, 0, 0, 1]) };
    expect_err(&mut r, &[ro], "InvalidAccountData");
    // (The fee payer is always writable, so a read-only base on CLOSE is covered by the unit test.)
    // Wrong owner: a seed account owned by the system program / by the verifier.
    let so = "s0cccccccccccccccccccccccccccccc";
    let (sys_a, _, _) = r.create(so, 64, &VERIFIER);
    let w = derive(&p, so, &UPLOAD);
    assert_ne!(w, sys_a);
    let wrong_owner = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new(sys_a, false), AccountMeta::new_readonly(p, true)], data: seeded(1, so.as_bytes(), &[0, 0, 0, 0, 1]) };
    expect_err(&mut r, &[wrong_owner], "IncorrectProgramId");
    expect_err(&mut r, &[close_ix(UPLOAD, 2, p, p, s)], "");
    // Executable target: the program account itself.
    let exe = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new_readonly(UPLOAD, false), AccountMeta::new_readonly(p, true)], data: seeded(1, s.as_bytes(), &[0, 0, 0, 0, 1]) };
    assert!(r.send(&[exe]).is_err());
    // Alias: target == base.
    let alias = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new(p, true), AccountMeta::new(p, true)], data: seeded(2, s.as_bytes(), &[]) };
    expect_err(&mut r, &[alias], "InvalidArgument");
    // Extra account.
    let extra = Instruction { program_id: UPLOAD, accounts: vec![AccountMeta::new(a, false), AccountMeta::new(p, true), AccountMeta::new_readonly(SYSTEM, false)], data: seeded(2, s.as_bytes(), &[]) };
    expect_err(&mut r, &[extra], "NotEnoughAccountKeys");
    // Nothing above changed the account.
    let acc = r.svm.get_account(&a).unwrap();
    assert_eq!((acc.owner, acc.data, acc.lamports), (UPLOAD, vec![0; 64], r.svm.minimum_balance_for_rent_exemption(64)));
}

#[test]
fn write_after_close_in_same_transaction_rejected_and_no_resurrection() {
    let mut r = Run::new();
    let p = r.payer.pubkey();
    let s = "p0dddddddddddddddddddddddddddddd";
    let (a, rent, _) = r.create(s, 128, &UPLOAD);
    r.send(&[write_ix(a, p, s, 0, &[0xee; 128])]).unwrap();
    // [CLOSE, WRITE] and [CLOSE, CLOSE] fail atomically: the account is unchanged.
    expect_err(&mut r, &[close_ix(UPLOAD, 2, a, p, s), write_ix(a, p, s, 0, &[1])], "IncorrectProgramId");
    expect_err(&mut r, &[close_ix(UPLOAD, 2, a, p, s), close_ix(UPLOAD, 2, a, p, s)], "IncorrectProgramId");
    assert_eq!(r.svm.get_account(&a).unwrap().data, vec![0xee; 128]);
    // [CLOSE, re-create with the same seed, WRITE 1 byte]: the re-created account is fresh zeros.
    let before = r.balance(&p);
    let l = r
        .send(&[close_ix(UPLOAD, 2, a, p, s), create_with_seed_ix(&p, &a, s, rent, 128, &UPLOAD), write_ix(a, p, s, 0, &[1])])
        .unwrap();
    let acc = r.svm.get_account(&a).unwrap();
    let mut want = vec![0; 128];
    want[0] = 1;
    assert_eq!((acc.owner, acc.data, acc.lamports), (UPLOAD, want, rent));
    assert_eq!(before - r.balance(&p), l.fee);
    // [CLOSE, transfer lamports in]: a system account with no data, never the old bytes.
    let mut t = 2u32.to_le_bytes().to_vec();
    t.extend_from_slice(&1_000_000u64.to_le_bytes());
    let transfer = Instruction { program_id: SYSTEM, accounts: vec![AccountMeta::new(p, true), AccountMeta::new(a, false)], data: t };
    r.send(&[close_ix(UPLOAD, 2, a, p, s), transfer]).unwrap();
    let acc = r.svm.get_account(&a).unwrap();
    assert_eq!((acc.owner, acc.data.len()), (SYSTEM, 0));
    expect_err(&mut r, &[write_ix(a, p, s, 0, &[1])], "IncorrectProgramId");
}
