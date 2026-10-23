"""Append a per-operation gate for the exact native checkpoint-write expression."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];p=R/'tools/s2w-20261023/S2W_native/src/lib.rs';s=p.read_text();native=(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text()
line='accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);';assert native.count(line)==1
h='''
fn S2W_write(accounts: &[AccountInfo<'_>], checkpoint: Vec<u8>) -> Result<(),ProgramError> {
    WRITE_EXPRESSION
    Ok(())
}
#[kani::proof]
#[kani::unwind(34)]
fn S2W_checkpoint_write() {
    let mut input: [u8; 1768] = kani::any();
    let source: [u8; 1768] = kani::any();
    let i: usize = kani::any();
    kani::assume(i < source.len());
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
    // Duplicate SDK handles intentionally retain their actual Rc aliasing.
    // The gate checks the destination write only, never a disjoint-account frame.
    let accounts = [account.clone(), account.clone(), account];
    assert!(S2W_write(&accounts, source.to_vec()) == Ok(()));
    let destination = &accounts[2];
    assert!(destination.key == &key && destination.owner == &owner);
    assert!(destination.is_signer == signer && destination.is_writable == writable
        && destination.executable == executable && destination.rent_epoch == epoch);
    assert!(**destination.try_borrow_lamports().unwrap() == old_lamports);
    let read = destination.try_borrow_data().unwrap();
    assert!(read.len() == 1768 && read[i] == source[i]);
    drop(read);
    assert!(destination.try_borrow_mut_data().is_ok());
}
'''.replace('WRITE_EXPRESSION',line)
assert 'fn S2W_write' not in s;p.write_text(s+h)
(R/'evidence/s2w-20261023/write-fragment.json').write_text(json.dumps({'native_expression':line,'native_source_sha256':hashlib.sha256(native.encode()).hexdigest(),'qualification':'Exact source write expression extracted into per-operation harness, real SDK, full1768 arbitrary input/destination, arbitrary metadata, actual Rc aliases. Does not prove whole wrapper, cross-account disjoint frame, or child effects.'},indent=2)+'\n')
