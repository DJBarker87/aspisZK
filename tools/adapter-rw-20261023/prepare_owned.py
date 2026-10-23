#!/usr/bin/env python3
"""Create owned authentication ports; pin unchanged children separately."""
from pathlib import Path
import re, subprocess, sys
def emit(p, text):
    if "--check" in sys.argv:
        assert p.read_text()==text,str(p)
    else: p.write_text(text)
root=Path(__file__).resolve().parents[2]
p=root/'programs/r1-cost-probe/src/r1_pool_adapter.rs'
s=subprocess.check_output(['git','show','81521c77f7:programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True,cwd=root)
# Original source is retained for the test-only differential harness.
emit(root/'programs/r1-cost-probe/src/r1_pool_adapter_original.rs',s)
header='''//! Owned caller boundary. SDK guards exist only in snapshot/write wrappers.
use super::*;
use aspis_statement::pool_v1::{
    POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES,
    POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES,
};

struct OwnedAccount {
    key: Pubkey,
    owner: Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
    length: Result<usize, ProgramError>,
    bytes: Result<Vec<u8>, ProgramError>,
}
impl OwnedAccount {
    fn key(&self) -> &Pubkey { &self.key }
    fn owner(&self) -> &Pubkey { &self.owner }
    fn data(&self) -> Result<&[u8], ProgramError> {
        match &self.bytes { Ok(bytes) => Ok(bytes), Err(error) => Err(error.clone()) }
    }
    fn data_len(&self) -> Result<usize, ProgramError> { self.length.clone() }
}

// Copy only decoder-admitted lengths; malformed lengths retain their original
// length and a deferred error. No adversarial account length drives allocation.
fn snapshot(account: &AccountInfo<'_>, length1: usize, length2: usize) -> OwnedAccount {
    let (length, bytes) = match account.try_borrow_data() {
        Ok(data) => {
            let length = data.len();
            let bytes = if length == length1 || length == length2 {
                Ok(data.to_vec())
            } else { Err(ProgramError::InvalidAccountData) };
            (Ok(length), bytes)
        }
        Err(error) => (Err(error.clone()), Err(error)),
    };
    OwnedAccount { key: *account.key, owner: *account.owner,
        is_signer: account.is_signer, is_writable: account.is_writable,
        executable: account.executable, length, bytes }
}

fn require_readonly_buffer(account: &OwnedAccount) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn require_readonly_account(account: &OwnedAccount, owner: &Pubkey) -> ProgramResult {
    readonly_meta_ok(account.owner(), owner, account.is_signer, account.is_writable, account.executable)
}
fn require_verifier_checkpoint(account: &OwnedAccount, program_id: &Pubkey, writable: bool) -> ProgramResult {
    if account.owner() != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.data_len()? != verifier::checkpoint_size(Variant::S2) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_distinct_accounts<const N: usize>(accounts: &[&OwnedAccount; N]) -> ProgramResult {
    let mut index = 0;
    while index < N {
        let mut previous = 0;
        while previous < index {
            if accounts[previous].key() == accounts[index].key() {
                return Err(ProgramError::InvalidArgument);
            }
            previous += 1;
        }
        index += 1;
    }
    Ok(())
}
fn require_zero(bytes: &[u8]) -> ProgramResult {
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        index += 1;
    }
    Ok(())
}
'''
a=s.index('#[inline(never)]\nfn authenticate_invariant_release_registry(')
b=s.index('#[inline(never)]\nfn scan_proof_buffer(',a)
auth=s[a:b]
auth=auth.replace("AccountInfo<'_>",'OwnedAccount')
auth=re.sub(r'([a-z_]+)\.key\b',r'\1.key()',auth)
auth=auth.replace('&registry_account.try_borrow_data()?','registry_account.data()?').replace('&entry_account.try_borrow_data()?','entry_account.data()?')
for name in ['master','checkpoint','lane']:
 auth=auth.replace('&'+name+'_account.try_borrow_data()?',name+'_account.data()?')
a=s.index('#[inline(never)]\nfn validate_asq8(');b=s.index('#[inline(never)]\nfn emit_result(',a)
valid=s[a:b].replace("AccountInfo<'_>",'OwnedAccount').replace('    instruction_data: &[u8],','    instruction_data: &[u8],\n    current_slot: Result<u64, ProgramError>,').replace('Clock::get()?.slot','current_slot?').replace('&proof_account.try_borrow_data()?','proof_account.data()?')
a=s.index('#[inline(never)]\nfn stage1(');b=s.index('#[inline(never)]\nfn stage2(',a)
first=s[a:b].replace('fn stage1(','fn stage1_owned(').replace("AccountInfo<'_>",'OwnedAccount').replace('-> ProgramResult {','-> Result<Vec<u8>, ProgramError> {',1)
first=first.replace('    let mut checkpoint_data = checkpoint_account.try_borrow_mut_data()?;\n    if checkpoint_data.iter().any(|byte| *byte != 0) {\n        return Err(ProgramError::AccountAlreadyInitialized);\n    }','    let checkpoint_data = checkpoint_account.data()?;\n    require_zero(checkpoint_data)?;')
first=first.replace('public_account.try_borrow_data()?','public_account.data()?').replace('proof_account.try_borrow_data()?','proof_account.data()?').replace('super::first_decoded','super::super::first_decoded')
first=first[:first.index('    checkpoint_data.copy_from_slice')]+ '    Ok(checkpoint)\n}\n\n'
a=b;b=s.index('#[inline(never)]\npub(super) fn process(',a)
second=s[a:b].replace('fn stage2(','fn stage2_owned(').replace("AccountInfo<'_>",'OwnedAccount').replace('data: &[u8])','data: &[u8], current_slot: Result<u64, ProgramError>)')
# Clear/profiling are in wrapper, before snapshot/clock and owned validation.
a=second.index('    program::set_return_data(&[]);');b=second.index('    let validated',a)
second=second[:a]+second[b:]
second=second.replace('validate_asq8(program_id, accounts, data)?','validate_asq8(program_id, accounts, data, current_slot)?').replace('accounts[0].try_borrow_data()?','accounts[0].data()?').replace('accounts[6].try_borrow_data()?','accounts[6].data()?').replace('super::SolanaDigest','super::super::SolanaDigest').replace('super::observer()','super::super::observer()').replace('super::error','super::super::error')
wrappers='''pub(super) fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let owned = [
        snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        snapshot(&accounts[1], POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES),
        snapshot(&accounts[2], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let checkpoint = stage1_owned(program_id, &owned, data)?;
    accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage1-checkpoint-written"); solana_program::log::sol_log_compute_units(); }
    Ok(())
}

pub(super) fn stage2(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if accounts.len() != 7 || data.get(..4) != Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..]) {
        return Err(ProgramError::InvalidInstructionData);
    }
    program::set_return_data(&[]);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage2-begin"); solana_program::log::sol_log_compute_units(); }
    let owned = [
        snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        snapshot(&accounts[1], POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES),
        snapshot(&accounts[2], POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
        snapshot(&accounts[3], POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES),
        snapshot(&accounts[4], POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES),
        snapshot(&accounts[5], POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES),
        snapshot(&accounts[6], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let current_slot = match Clock::get() { Ok(clock) => Ok(clock.slot), Err(error) => Err(error) };
    stage2_owned(program_id, &owned, data, current_slot)
}
'''
emit(root/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs',header+auth+valid+first+second+wrappers)
a=s.index('#[inline(never)]\nfn stage1(');b=s.index('#[inline(never)]\npub(super) fn process(',a)
emit(p,s[:a]+'''#[path = "r1_pool_adapter_owned.rs"]
mod owned;
use owned::{stage1, stage2};

'''+s[b:]+'''
#[cfg(all(test, feature = "private-leaf-salts"))]
#[path = "adapter_rw_tests.rs"]
mod rw_tests;
''')
