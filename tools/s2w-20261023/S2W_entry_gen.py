"""Append exact native entry snapshot array expressions to selected-cell checks."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[2];s=(r/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text();p=r/'tools/s2w-20261023/S2W_wrapper/src/lib.rs'
base=p.read_text().split('\nconst POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES:usize=688;')[0]
constants='''
const POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES:usize=688;
mod verifier { pub const PROOF_BYTES:usize=57607; }
const POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES:usize=1880;
const CHECKPOINT_TAIL_BYTES:usize=1768;
const POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES:usize=384;
const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES:usize=192;
const POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES:usize=768;
const POOL_V1_VERIFIER_REGISTRY_BYTES:usize=128;
const POOL_V1_VERIFIER_REGISTRY_V2_BYTES:usize=256;
const POOL_V1_VERIFIER_ENTRY_BYTES:usize=192;
const POOL_V1_VERIFIER_ENTRY_V2_BYTES:usize=320;
'''
out=base+constants;fragments={}
for n,count in [(1,3),(2,7)]:
 a=s.index('    let owned = [',s.index('pub(super) fn stage'+str(n)+'('));b=s.index('\n    ];',a)+len('\n    ];');f=s[a:b];fragments[str(n)]=hashlib.sha256(f.encode()).hexdigest();out+=f'\nfn S2W_entry{n}(accounts:&[AccountInfo<\'_>])->[OwnedAccount;{count}] {{\n'+f+'\n    owned\n}\n'
out+='''
fn S2W_entry_check<const N:usize>(lengths:[usize;N], entry:fn(&[AccountInfo<'_>])->[OwnedAccount;N]) {
    let keys:[Pubkey;N]=kani::any(); let owners:[Pubkey;N]=kani::any();
    let accounts:[AccountInfo<'_>;N]=std::array::from_fn(|j| {
        let i:usize=kani::any(); kani::assume(i<lengths[j]);
        S2W_account(&keys[j],&owners[j],lengths[j],i,kani::any())
    });
    let selected:usize=kani::any(); kani::assume(selected<N);
    let original=*accounts[selected].data.borrow();
    let owned=entry(&accounts);
    let view=owned[selected].bytes.as_ref().unwrap();
    assert!(view.0==original);
    assert!(owned[selected].key==keys[selected] && owned[selected].owner==owners[selected]);
    assert!(owned[selected].is_signer==accounts[selected].is_signer);
    assert!(owned[selected].is_writable==accounts[selected].is_writable);
    assert!(owned[selected].executable==accounts[selected].executable);
    assert!(owned[selected].length==Ok(lengths[selected]));
    assert!(accounts[selected].try_borrow_mut_data().is_ok());
}
#[kani::proof]
#[kani::unwind(34)]
fn S2W_entry1_contract() { S2W_entry_check([58295,1880,1768],S2W_entry1); }
#[kani::proof]
#[kani::unwind(34)]
fn S2W_entry2_contract() {
    let registry=if kani::any(){128}else{256};
    let entry=if kani::any(){192}else{320};
    S2W_entry_check([58295,384,192,768,registry,entry,1768],S2W_entry2);
}
'''
if '--check' in sys.argv:
    assert p.read_text()==out, 'Generated entry source mismatch'
    print('Entry snapshot source generation: pass')
    sys.exit(0)
p.write_text(out)
(r/'evidence/s2w-20261023/wrapper-projection-source.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'entry_array_sha256':fragments,'snapshot_body_verbatim':s[s.index('fn snapshot('):s.index('\nfn require_readonly_buffer')] in out,'write_expression_verbatim':'accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);' in out,'interpretation':'SDK selected-cell RefCell model and pure-copy coordinate interpretation. Not a native ABI or full source-to-model refinement theorem.'},indent=2)+'\n')
