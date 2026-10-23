"""Bind the native snapshot fragment verbatim; all harness code is cfg(kani).
No shipped source is modified. Cargo uses the exact pinned SDK versions.
"""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];S=R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
s=S.read_text();fragment=s[s.index('struct OwnedAccount {'):s.index('\nfn require_readonly_buffer')]
harness='''
#[kani::proof]
#[kani::unwind(34)]
fn S2W_snapshot_proof_account() {
    let mut input: [u8; 58295] = kani::any();
    let i: usize = kani::any();
    kani::assume(i < input.len());
    let original = input[i];
    let key = Pubkey::new_from_array(kani::any());
    let owner = Pubkey::new_from_array(kani::any());
    let signer: bool = kani::any();
    let writable: bool = kani::any();
    let executable: bool = kani::any();
    let mut lamports: u64 = kani::any();
    let old_lamports = lamports;
    let epoch: u64 = kani::any();
    let account = AccountInfo::new(&key, signer, writable, &mut lamports,
        &mut input, &owner, executable, epoch);
    let snap = snapshot(&account, 58295, 58295);
    assert!(snap.key == key && snap.owner == owner);
    assert!(snap.is_signer == signer && snap.is_writable == writable
        && snap.executable == executable);
    assert!(snap.length == Ok(58295));
    let copied = snap.bytes.unwrap();
    assert!(copied.len() == 58295);
    assert!(copied[i] == original);
    assert!(**account.try_borrow_lamports().unwrap() == old_lamports);
    let mut live = account.try_borrow_mut_data().unwrap();
    assert!(live.len() == 58295 && live[i] == original);
    live[i] = original.wrapping_add(1);
    assert!(copied[i] == original);
}
'''
# Whole crate excluded outside Kani; the source fragment itself is unchanged.
p=R/'tools/s2w-20261023/S2W_native/src/lib.rs';p.write_text('#![cfg(kani)]\n#![allow(dead_code, non_snake_case)]\nuse solana_account_info::AccountInfo;\nuse solana_pubkey::Pubkey;\nuse solana_program_error::ProgramError;\n\n'+fragment+'\n'+harness)
e=R/'evidence/s2w-20261023/native-fragment.json';e.write_text(json.dumps({'source':str(S.relative_to(R)),'source_sha256':hashlib.sha256(S.read_bytes()).hexdigest(),'fragment_sha256':hashlib.sha256(fragment.encode()).hexdigest(),'harness_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'qualification':'Verbatim native OwnedAccount and snapshot, standalone cfg(kani) crate, actual SDK calls. Full 58295-byte proof account, arbitrary byte index/content and metadata, fresh zero borrow count. Other account sizes, conflicts, native entry wrapper and runtime join not covered.'},indent=2)+'\n')
