#![cfg(kani)]
#![allow(dead_code)]
use solana_program_error::ProgramError;
type ProgramResult = Result<(), ProgramError>;

// Native stage1:947-949, with ONLY accounts.len() projected to slice metadata.
// No native whole-function call, account indexing, SDK borrow or child is reached.
fn native_cut1(data: &[u8], accounts_len: usize) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts_len != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}
// S2E owned shape1: verbatim, apart from function name.
fn owned_cut1(data: &[u8], accounts: usize) -> ProgramResult {
 if !(data == &[3,10] || data == &[3,11]) || accounts != 3 {
  Err(ProgramError::InvalidInstructionData)
 } else { Ok(()) }
}

// Smallest relation diagnostic. Full heap/SDK fields can be identical and
// untouched; the inherited CutRelated contains no native invocation observation.
// This is deliberately NOT an admitted same-external-input execution pair.
#[kani::proof]
fn S2J_cut1_unbound_invocation() {
    assert_eq!(native_cut1(&[], 3), owned_cut1(&[3,10], 3));
}

// Same original bytes, slice length, count; all heap/SDK state untouched.
// Bounded native source check (lengths 0..3). Lean shape1_port is unbounded.
#[kani::proof]
#[kani::unwind(5)]
fn S2J_cut1_bound_invocation() {
    let bytes: [u8; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);
    let count: usize = kani::any();
    let data = &bytes[..len];
    let native = native_cut1(data, count);
    let owned = owned_cut1(data, count);
    assert_eq!(native, owned);
    assert_eq!(data == &[3,10], data == &[3,10][..]);
    assert_eq!(data == &[3,11], data == &[3,11][..]);
    kani::cover!(native.is_ok());
    kani::cover!(native.is_err());
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, kani::Arbitrary)]
struct AccountRecord {
    key: [u8;32], owner: [u8;32], is_signer: bool, is_writable: bool,
    executable: bool, rent_epoch: u64, data_slot: usize, lamports_slot: usize,
}
// Source :950, type-parametric slice indexing. Full AccountInfo decoding is
// the explicit EntrypointDeserialization premise, not proved by this harness.
fn native_cut2(accounts: &[AccountRecord]) -> &AccountRecord {
    let proof_account = &accounts[0];
    proof_account
}
#[kani::proof]
#[kani::unwind(35)]
fn S2J_cut2_select_original_record() {
    let accounts: [AccountRecord;3] = kani::any();
    let owned = accounts.to_vec();
    let selected = native_cut2(&accounts);
    let owned_selected = owned[0];
    assert!(std::ptr::eq(selected, &accounts[0]));
    assert_eq!(*selected, owned_selected);
    // Original association is index0 even when slots or keys alias.
    assert_eq!(selected.data_slot, accounts[0].data_slot);
    assert_eq!(selected.lamports_slot, accounts[0].lamports_slot);
}

fn native_cut3(accounts: &[AccountRecord]) -> &AccountRecord {
    let public_account = &accounts[1];
    public_account
}
#[kani::proof]
#[kani::unwind(35)]
fn S2J_cut3_preserve_proof_select_public() {
    let accounts: [AccountRecord;3] = kani::any();
    let owned = accounts.to_vec();
    let proof_account = &accounts[0];
    let public_account = native_cut3(&accounts);
    assert!(std::ptr::eq(proof_account, &accounts[0]));
    assert!(std::ptr::eq(public_account, &accounts[1]));
    assert_eq!(*proof_account, owned[0]);
    assert_eq!(*public_account, owned[1]);
}

fn native_cut4(accounts: &[AccountRecord]) -> &AccountRecord {
    let checkpoint_account = &accounts[2];
    checkpoint_account
}
#[kani::proof]
#[kani::unwind(35)]
fn S2J_cut4_preserve_prior_select_checkpoint() {
    let accounts: [AccountRecord;3] = kani::any();
    let owned = accounts.to_vec();
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = native_cut4(&accounts);
    assert!(std::ptr::eq(proof_account, &accounts[0]));
    assert!(std::ptr::eq(public_account, &accounts[1]));
    assert!(std::ptr::eq(checkpoint_account, &accounts[2]));
    assert_eq!(*proof_account, owned[0]);
    assert_eq!(*public_account, owned[1]);
    assert_eq!(*checkpoint_account, owned[2]);
}

fn native_cut5<const N: usize>(accounts: &[&AccountRecord; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}
fn owned_cut5(proof: AccountRecord, public: AccountRecord, cp: AccountRecord) -> ProgramResult {
    if proof.key == public.key || proof.key == cp.key || public.key == cp.key {
        Err(ProgramError::InvalidArgument)
    } else { Ok(()) }
}
#[kani::proof]
#[kani::unwind(35)]
fn S2J_cut5_distinct_keys_original_records() {
    let accounts: [AccountRecord;3] = kani::any();
    let native = native_cut5(&[&accounts[0], &accounts[1], &accounts[2]]);
    let owned = owned_cut5(accounts[0], accounts[1], accounts[2]);
    assert_eq!(native, owned);
    kani::cover!(native.is_ok());
    kani::cover!(native == Err(ProgramError::InvalidArgument));
}

fn readonly_buffer_meta_ok(is_signer: bool, is_writable: bool, executable: bool) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn native_cut6(account: &AccountRecord) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn owned_readonly(account: AccountRecord) -> ProgramResult {
    if account.is_signer { Err(ProgramError::InvalidAccountData) }
    else if account.is_writable { Err(ProgramError::InvalidAccountData) }
    else if account.executable { Err(ProgramError::InvalidAccountData) }
    else { Ok(()) }
}
#[kani::proof]
fn S2J_cut6_proof_readonly() {
    let accounts: [AccountRecord;3] = kani::any();
    let before = accounts;
    assert_eq!(native_cut6(&accounts[0]), owned_readonly(accounts[0]));
    assert_eq!(before, accounts);
}
